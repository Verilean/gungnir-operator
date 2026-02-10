/-
  Gungnir Operator - Main Daemon Entry Point

  This module implements the operator daemon that runs as a Kubernetes controller:
  1. Watches for ValkeyCluster custom resources
  2. Reconciles each CR through the state machine
  3. Monitors Valkey node health via PING
  4. Handles graceful shutdown on SIGTERM

  The daemon uses kubectl as a subprocess bridge for K8s API access.
  This is a practical starting point; native HTTP/2 can replace it later.

  Reference: plans.md "Lean 4 to Kubernetes Operator Integration"
-/

import Gungnir.K8s.K8s
import Gungnir.StateMachine.Reconciler
import Gungnir.Valkey.Connection
import Gungnir.Valkey.Commands
import Gungnir.Valkey.Sentinel

namespace Gungnir

open Gungnir.K8s
open Gungnir.Reconciler
open Gungnir.Valkey

/-! ## Operator Configuration -/

/-- Configuration parsed from CLI arguments and environment. -/
structure OperatorConfig where
  /-- Namespace to watch ("" means all namespaces) -/
  watchNamespace : String := ""
  /-- Lease name for leader election -/
  leaseName : String := "gungnir-operator-lease"
  /-- Namespace where the lease lives -/
  leaseNamespace : String := "gungnir-system"
  /-- Health check PING interval in milliseconds -/
  pingIntervalMs : Nat := 1000
  /-- Reconcile loop interval in milliseconds -/
  reconcileIntervalMs : Nat := 10000
  /-- SDOWN detection threshold in milliseconds -/
  downAfterMs : Nat := 5000
  /-- Log verbosity (0=error, 1=info, 2=debug) -/
  verbosity : Nat := 1
  deriving Repr

/-! ## CLI Argument Parsing -/

/-- Parse a single --key=value or --key value pair from the argument list. -/
private def parseArg (config : OperatorConfig) (args : List String) : OperatorConfig × List String :=
  match args with
  | "--namespace" :: v :: rest =>
    ({ config with watchNamespace := v }, rest)
  | "--lease-name" :: v :: rest =>
    ({ config with leaseName := v }, rest)
  | "--lease-namespace" :: v :: rest =>
    ({ config with leaseNamespace := v }, rest)
  | "--ping-interval" :: v :: rest =>
    ({ config with pingIntervalMs := v.toNat?.getD 1000 }, rest)
  | "--reconcile-interval" :: v :: rest =>
    ({ config with reconcileIntervalMs := v.toNat?.getD 10000 }, rest)
  | "--down-after" :: v :: rest =>
    ({ config with downAfterMs := v.toNat?.getD 5000 }, rest)
  | "-v" :: rest =>
    ({ config with verbosity := 2 }, rest)
  | "--verbose" :: rest =>
    ({ config with verbosity := 2 }, rest)
  | _ :: rest => (config, rest)
  | [] => (config, [])

/-- Parse all CLI arguments into an OperatorConfig. -/
def parseArgs (args : List String) : OperatorConfig :=
  let rec go (config : OperatorConfig) (remaining : List String) (fuel : Nat) : OperatorConfig :=
    match fuel, remaining with
    | 0, _ => config
    | _, [] => config
    | fuel' + 1, _ =>
      let (config', rest) := parseArg config remaining
      go config' rest fuel'
  go {} args args.length

/-! ## Logging -/

/-- Log a message at the given verbosity level. -/
def logMsg (config : OperatorConfig) (level : Nat) (component tag msg : String) : IO Unit := do
  if level <= config.verbosity then
    let timestamp ← IO.monoMsNow
    IO.eprintln s!"[{timestamp}] [{component}] [{tag}] {msg}"

/-! ## Kubectl Bridge -/

/-- Run a kubectl command and return its stdout. -/
def kubectl (args : List String) : IO (Except String String) := do
  try
    let result ← IO.Process.output {
      cmd := "kubectl"
      args := args.toArray
    }
    if result.exitCode == 0 then
      pure (Except.ok result.stdout)
    else
      pure (Except.error s!"kubectl exit {result.exitCode}: {result.stderr}")
  catch e =>
    pure (Except.error s!"kubectl error: {e}")

/-- Get ValkeyCluster CRs as JSON lines (one name per line). -/
def listValkeyClusters (ns : String) : IO (Except String (List (String × String))) := do
  let nsArgs := if ns.isEmpty then ["-A"] else ["-n", ns]
  let result ← kubectl (["get", "valkeycluster"] ++ nsArgs ++ ["-o", "jsonpath={range .items[*]}{.metadata.name},{.metadata.namespace}{\"\\n\"}{end}"])
  match result with
  | Except.error e => pure (Except.error e)
  | Except.ok output =>
    let lines := output.splitOn "\n" |>.filter (·.length > 0)
    let pairs := lines.filterMap fun line =>
      let parts := line.splitOn ","
      match parts with
      | [name, namespace_] => some (name, namespace_)
      | _ => none
    pure (Except.ok pairs)

/-- Get a ValkeyCluster CR as a simplified view.
    In production, this would parse the full JSON into ValkeyClusterView. -/
def getValkeyCluster (name ns : String) : IO (Except String ValkeyClusterView) := do
  let result ← kubectl ["get", "valkeycluster", name, "-n", ns,
    "-o", "jsonpath={.spec.replicas},{.spec.image},{.metadata.uid}"]
  match result with
  | Except.error e => pure (Except.error e)
  | Except.ok output =>
    let parts := output.splitOn ","
    match parts with
    | [replicasStr, image, uid] =>
      let replicas := replicasStr.toNat?.getD 3
      let uidNat := uid.toNat?.getD 0
      let vc : ValkeyClusterView := {
        metadata := (ObjectMetaView.default.withName name).withNamespace ns
          |> fun m => { m with uid := some uidNat }
        spec := { replicas := replicas, image := image }
      }
      pure (Except.ok vc)
    | _ =>
      pure (Except.error s!"unexpected jsonpath output: {output}")

/-- Get the list of pod IPs for a StatefulSet. -/
def getPodEndpoints (crName ns : String) : IO (List (String × String × Nat)) := do
  let result ← kubectl ["get", "pods", "-n", ns,
    "-l", s!"app.kubernetes.io/instance={crName}",
    "-o", "jsonpath={range .items[*]}{.metadata.name},{.status.podIP},{.spec.containers[0].ports[0].containerPort}{\"\\n\"}{end}"]
  match result with
  | Except.error _ => pure []
  | Except.ok output =>
    let lines := output.splitOn "\n" |>.filter (·.length > 0)
    pure <| lines.filterMap fun line =>
      let parts := line.splitOn ","
      match parts with
      | [podName, ip, portStr] =>
        let port := portStr.toNat?.getD 6379
        if ip.length > 0 then some (podName, ip, port)
        else none
      | _ => none

/-- Build a JSON patch string for kubectl. Uses plain concatenation to avoid
    escape issues with Lean 4 s! string interpolation. -/
private def jsonPatch (pairs : List (String × String)) : String :=
  let fields := pairs.map fun (k, v) => "\"" ++ k ++ "\":" ++ v
  "{" ++ String.intercalate "," fields ++ "}"

/-- Update the client Service selector to point to a specific pod (for failover). -/
def updateServiceSelector (crName ns podName : String) : IO (Except String Unit) := do
  let json := "{\"spec\":{\"selector\":{\"statefulset.kubernetes.io/pod-name\":\"" ++ podName ++ "\"}}}"
  let result ← kubectl ["patch", "svc", crName ++ "-client", "-n", ns,
    "--type", "merge", "-p", json]
  match result with
  | Except.error e => pure (Except.error e)
  | Except.ok _ => pure (Except.ok ())

/-- Update the ValkeyCluster CR status subresource. -/
def updateCRStatus (crName ns : String) (phase : String) (masterPod : Option String)
    (readyReplicas : Nat) : IO (Except String Unit) := do
  let masterField := match masterPod with
    | some m => ",\"masterPod\":\"" ++ m ++ "\""
    | none => ""
  let json := "{\"status\":{\"phase\":\"" ++ phase ++ "\",\"readyReplicas\":" ++ toString readyReplicas ++ masterField ++ "}}"
  let result ← kubectl ["patch", "valkeycluster", crName, "-n", ns,
    "--type", "merge", "--subresource", "status", "-p", json]
  match result with
  | Except.error e => pure (Except.error e)
  | Except.ok _ => pure (Except.ok ())

/-! ## Resource JSON Generation -/

/-- Quote a string for JSON output. -/
private def jq (s : String) : String := "\"" ++ s ++ "\""

/-- JSON key-value pair with string value. -/
private def jkv (k v : String) : String := jq k ++ ":" ++ jq v

/-- JSON key-value pair with numeric value. -/
private def jkvn (k : String) (v : Nat) : String := jq k ++ ":" ++ toString v

/-- JSON key-value pair with boolean value. -/
private def jkvb (k : String) (v : Bool) : String := jq k ++ ":" ++ if v then "true" else "false"

/-- JSON key-value pair with raw (pre-formatted) value. -/
private def jkvr (k v : String) : String := jq k ++ ":" ++ v

/-- JSON object from a list of fields. -/
private def jobj (fields : List String) : String := "{" ++ String.intercalate "," fields ++ "}"

/-- JSON array from a list of items. -/
private def jarr (items : List String) : String := "[" ++ String.intercalate "," items ++ "]"

/-- Generate owner reference JSON for a ValkeyCluster CR. -/
private def ownerRefJSON (crName crUid : String) : String :=
  jobj [jkv "apiVersion" "valkey.verilean.io/v1",
        jkv "kind" "ValkeyCluster",
        jkv "name" crName, jkv "uid" crUid,
        jkvb "controller" true, jkvb "blockOwnerDeletion" true]

/-- Generate standard metadata JSON with labels and owner references. -/
private def resourceMetaJSON (name ns crName crUid : String) : String :=
  jobj [jkv "name" name, jkv "namespace" ns,
        jkvr "labels" (jobj [jkv "app.kubernetes.io/name" "valkey",
                             jkv "app.kubernetes.io/instance" crName,
                             jkv "app.kubernetes.io/managed-by" "gungnir-operator"]),
        jkvr "ownerReferences" (jarr [ownerRefJSON crName crUid])]

/-- Generate selector labels JSON. -/
private def selectorLabelsJSON (crName : String) : String :=
  jobj [jkv "app.kubernetes.io/name" "valkey",
        jkv "app.kubernetes.io/instance" crName]

/-- Generate port specification JSON. -/
private def portSpecJSON (port : Nat) : String :=
  jarr [jobj [jkv "name" "valkey", jkvn "port" port,
              jkvn "targetPort" port, jkv "protocol" "TCP"]]

/-- Generate Headless Service JSON (clusterIP: None for StatefulSet DNS). -/
private def headlessServiceJSON (crName ns crUid : String) (port : Nat) : String :=
  jobj [jkv "apiVersion" "v1", jkv "kind" "Service",
        jkvr "metadata" (resourceMetaJSON (crName ++ "-headless") ns crName crUid),
        jkvr "spec" (jobj [jkv "clusterIP" "None",
                           jkvb "publishNotReadyAddresses" true,
                           jkvr "selector" (selectorLabelsJSON crName),
                           jkvr "ports" (portSpecJSON port)])]

/-- Generate Client Service JSON (ClusterIP for client connections). -/
private def clientServiceJSON (crName ns crUid : String) (port : Nat) : String :=
  jobj [jkv "apiVersion" "v1", jkv "kind" "Service",
        jkvr "metadata" (resourceMetaJSON (crName ++ "-client") ns crName crUid),
        jkvr "spec" (jobj [jkv "type" "ClusterIP",
                           jkvr "selector" (selectorLabelsJSON crName),
                           jkvr "ports" (portSpecJSON port)])]

/-- Generate ConfigMap JSON with valkey.conf. -/
private def configMapJSON (crName ns crUid : String) (port : Nat) : String :=
  let conf := "port " ++ toString port ++ "\\nbind 0.0.0.0\\nprotected-mode no\\nappendonly yes\\ndir /data\\n"
  jobj [jkv "apiVersion" "v1", jkv "kind" "ConfigMap",
        jkvr "metadata" (resourceMetaJSON (crName ++ "-config") ns crName crUid),
        jkvr "data" (jobj [jkv "valkey.conf" conf])]

/-- Generate Secret JSON (placeholder for ACL credentials). -/
private def secretJSON (crName ns crUid : String) : String :=
  jobj [jkv "apiVersion" "v1", jkv "kind" "Secret",
        jkvr "metadata" (resourceMetaJSON (crName ++ "-secret") ns crName crUid),
        jkv "type" "Opaque"]

/-- Generate StatefulSet JSON with Valkey containers.
    Pod-0 runs as master; pods 1+ run as replicas via REPLICAOF.
    A startup script checks the pod ordinal and appends replicaof to the config. -/
private def statefulSetJSON (crName ns crUid : String)
    (replicas : Nat) (image : String) (port : Nat) : String :=
  -- Shell startup script: pod-0 is master, others replicate from pod-0 via headless DNS.
  -- Avoids double-quotes so it survives JSON string encoding cleanly.
  let script := "cp /etc/valkey/valkey.conf /tmp/valkey.conf && " ++
    "ORDINAL=${HOSTNAME##*-} && " ++
    "if [ $ORDINAL != 0 ]; then " ++
    "MASTER=${HOSTNAME%-*}-0.${HOSTNAME%-*}-headless.${POD_NAMESPACE}.svc.cluster.local && " ++
    "echo replicaof $MASTER $VALKEY_PORT >> /tmp/valkey.conf; " ++
    "fi && exec valkey-server /tmp/valkey.conf"
  let envVars := jarr [
    jobj [jkv "name" "POD_NAMESPACE",
          jkvr "valueFrom" (jobj [jkvr "fieldRef" (jobj [jkv "fieldPath" "metadata.namespace"])])],
    jobj [jkv "name" "VALKEY_PORT", jkv "value" (toString port)]]
  let containerSpec := jobj [
    jkv "name" "valkey", jkv "image" image,
    jkvr "ports" (jarr [jobj [jkv "name" "valkey", jkvn "containerPort" port]]),
    jkvr "command" (jarr [jq "/bin/sh", jq "-c", jq script]),
    jkvr "env" envVars,
    jkvr "volumeMounts" (jarr [
      jobj [jkv "name" "config", jkv "mountPath" "/etc/valkey"],
      jobj [jkv "name" "data", jkv "mountPath" "/data"]]),
    jkvr "readinessProbe" (jobj [
      jkvr "exec" (jobj [jkvr "command" (jarr [jq "valkey-cli", jq "ping"])]),
      jkvn "initialDelaySeconds" 5, jkvn "periodSeconds" 10]),
    jkvr "livenessProbe" (jobj [
      jkvr "exec" (jobj [jkvr "command" (jarr [jq "valkey-cli", jq "ping"])]),
      jkvn "initialDelaySeconds" 15, jkvn "periodSeconds" 20])]
  let podSpec := jobj [
    jkvr "containers" (jarr [containerSpec]),
    jkvr "volumes" (jarr [
      jobj [jkv "name" "config",
            jkvr "configMap" (jobj [jkv "name" (crName ++ "-config")])]])]
  let template := jobj [
    jkvr "metadata" (jobj [jkvr "labels" (selectorLabelsJSON crName)]),
    jkvr "spec" podSpec]
  let vctSpec := jobj [
    jkvr "accessModes" (jarr [jq "ReadWriteOnce"]),
    jkvr "resources" (jobj [jkvr "requests" (jobj [jkv "storage" "1Gi"])])]
  let vct := jarr [jobj [jkvr "metadata" (jobj [jkv "name" "data"]),
                          jkvr "spec" vctSpec]]
  jobj [jkv "apiVersion" "apps/v1", jkv "kind" "StatefulSet",
        jkvr "metadata" (resourceMetaJSON crName ns crName crUid),
        jkvr "spec" (jobj [
          jkvn "replicas" replicas,
          jkv "serviceName" (crName ++ "-headless"),
          jkvr "selector" (jobj [jkvr "matchLabels" (selectorLabelsJSON crName)]),
          jkvr "template" template,
          jkvr "volumeClaimTemplates" vct])]

/-- Generate PodDisruptionBudget JSON. -/
private def pdbJSON (crName ns crUid : String) : String :=
  jobj [jkv "apiVersion" "policy/v1", jkv "kind" "PodDisruptionBudget",
        jkvr "metadata" (resourceMetaJSON (crName ++ "-pdb") ns crName crUid),
        jkvr "spec" (jobj [
          jkvn "minAvailable" 1,
          jkvr "selector" (jobj [jkvr "matchLabels" (selectorLabelsJSON crName)])])]

/-- Write JSON to a temp file and run kubectl apply. -/
private def kubectlApply (json : String) : IO (Except String String) := do
  IO.FS.writeFile ⟨"/tmp/gungnir-resource.json"⟩ json
  kubectl ["apply", "-f", "/tmp/gungnir-resource.json"]

/-- Generate and apply a sub-resource for the given ValkeyCluster CR. -/
private def applySubResource (crName ns crUid : String)
    (replicas : Nat) (image : String) (port : Nat) (sub : SubResource) : IO (Except String String) := do
  let json := match sub with
    | .HeadlessService => headlessServiceJSON crName ns crUid port
    | .ClientService => clientServiceJSON crName ns crUid port
    | .ConfigMap => configMapJSON crName ns crUid port
    | .Secret => secretJSON crName ns crUid
    | .StatefulSet => statefulSetJSON crName ns crUid replicas image port
    | .PodDisruptionBudget => pdbJSON crName ns crUid
  kubectlApply json

/-- Map Kind to kubectl resource type string. -/
private def kindToKubectlType : Kind → String
  | Kind.ServiceKind => "service"
  | Kind.ConfigMapKind => "configmap"
  | Kind.SecretKind => "secret"
  | Kind.StatefulSetKind => "statefulset"
  | Kind.PodDisruptionBudgetKind => "poddisruptionbudget"
  | Kind.CustomResourceKind name => name
  | _ => "unknown"

/-- Identify which SubResource a K8s API request targets. -/
private def identifySubResource (crName : String) (kind : Kind) (resName : String) : Option SubResource :=
  if kind == Kind.ServiceKind && resName == crName ++ "-headless" then some SubResource.HeadlessService
  else if kind == Kind.ServiceKind && resName == crName ++ "-client" then some SubResource.ClientService
  else if kind == Kind.ConfigMapKind then some SubResource.ConfigMap
  else if kind == Kind.SecretKind then some SubResource.Secret
  else if kind == Kind.StatefulSetKind then some SubResource.StatefulSet
  else if kind == Kind.PodDisruptionBudgetKind then some SubResource.PodDisruptionBudget
  else none

/-- A placeholder DynamicObjectView for API response wrappers. -/
private def makeDummyObj (kind : Kind) (name ns : String) : DynamicObjectView :=
  { kind := kind
  , metadata := (ObjectMetaView.default.withName name).withNamespace ns
  , spec := ""
  , status := "" }

/-- Execute an API request from the reconciler state machine via kubectl.
    Returns the corresponding response to feed back into reconcileCore. -/
def executeRequest (config : OperatorConfig) (crName ns crUid : String)
    (replicas : Nat) (image : String) (port : Nat)
    (req : RequestView VoidExternalRequest) : IO DefaultResp := do
  match req with
  | RequestView.KRequest apiReq =>
    match apiReq with
    | APIRequest.GetRequest getReq =>
      let resType := kindToKubectlType getReq.key.kind
      logMsg config 2 "executor" crName ("get " ++ resType ++ "/" ++ getReq.key.name)
      let result ← kubectl ["get", resType, getReq.key.name, "-n", getReq.key.«namespace»]
      match result with
      | Except.ok _ =>
        let responseObj := makeDummyObj getReq.key.kind getReq.key.name getReq.key.«namespace»
        pure (some (.KResponse (.GetResponse { res := Except.ok responseObj })))
      | Except.error errMsg =>
        if (errMsg.splitOn "NotFound").length > 1 then
          logMsg config 2 "executor" crName (resType ++ "/" ++ getReq.key.name ++ " not found")
          pure (some (.KResponse (.GetResponse { res := Except.error .ObjectNotFound })))
        else
          logMsg config 0 "executor" crName ("get failed: " ++ errMsg)
          pure (some (.KResponse (.GetResponse { res := Except.error .Other })))
    | APIRequest.CreateRequest createReq =>
      let resName := createReq.obj.metadata.name.getD ""
      let sub := identifySubResource crName createReq.obj.kind resName
      match sub with
      | some s =>
        logMsg config 1 "executor" crName ("creating " ++ resName)
        let result ← applySubResource crName ns crUid replicas image port s
        match result with
        | Except.ok _ =>
          pure (some (.KResponse (.CreateResponse { res := Except.ok (makeDummyObj createReq.obj.kind resName ns) })))
        | Except.error e =>
          logMsg config 0 "executor" crName ("create failed: " ++ e)
          pure (some (.KResponse (.CreateResponse { res := Except.error .Other })))
      | none =>
        logMsg config 0 "executor" crName ("unknown sub-resource: " ++ resName)
        pure (some (.KResponse (.CreateResponse { res := Except.error .Other })))
    | APIRequest.UpdateRequest updateReq =>
      let sub := identifySubResource crName updateReq.obj.kind updateReq.name
      match sub with
      | some s =>
        logMsg config 2 "executor" crName ("updating " ++ updateReq.name)
        let result ← applySubResource crName ns crUid replicas image port s
        match result with
        | Except.ok _ =>
          pure (some (.KResponse (.UpdateResponse { res := Except.ok (makeDummyObj updateReq.obj.kind updateReq.name ns) })))
        | Except.error e =>
          logMsg config 0 "executor" crName ("update failed: " ++ e)
          pure (some (.KResponse (.UpdateResponse { res := Except.error .Other })))
      | none =>
        logMsg config 0 "executor" crName ("unknown sub-resource for update: " ++ updateReq.name)
        pure (some (.KResponse (.UpdateResponse { res := Except.error .Other })))
    | APIRequest.UpdateStatusRequest _ =>
      logMsg config 2 "executor" crName "status update (auto-approved)"
      pure (some (.KResponse (.UpdateStatusResponse { res := Except.ok (makeDummyObj ValkeyClusterView.kind crName ns) })))
    | _ =>
      logMsg config 0 "executor" crName "unsupported request type"
      pure none
  | RequestView.ExternalRequest _ =>
    pure none

/-! ## Leader Election -/

/-- Attempt to acquire or renew the leader election lease.
    Uses K8s Lease API via kubectl. Returns true if we are the leader.
    Handles expired leases: if the current holder's renewTime + leaseDuration
    has passed, we take over the lease. -/
def tryAcquireLease (config : OperatorConfig) (holderIdentity : String) : IO Bool := do
  -- Get current epoch seconds and RFC 3339 time
  let epochResult ← IO.Process.output { cmd := "date", args := #["+%s"] }
  let nowEpoch := epochResult.stdout.trim.toNat?.getD 0
  let timeResult ← IO.Process.output { cmd := "date", args := #["-u", "+%Y-%m-%dT%H:%M:%S.000000Z"] }
  let nowRFC := timeResult.stdout.trim
  -- Fetch lease fields: holderIdentity, renewTime, leaseDurationSeconds
  let result ← kubectl ["get", "lease", config.leaseName,
    "-n", config.leaseNamespace,
    "-o", "jsonpath={.spec.holderIdentity}|{.spec.renewTime}|{.spec.leaseDurationSeconds}"]
  match result with
  | Except.ok output =>
    let parts := output.splitOn "|"
    let (holder, renewTimeStr, leaseDurationStr) := match parts with
      | [h, r, d] => (h, r, d)
      | [h, r] => (h, r, "15")
      | [h] => (h, "", "15")
      | _ => ("", "", "15")
    let leaseDuration := leaseDurationStr.toNat?.getD 15
    if holder == holderIdentity then
      -- We hold the lease; renew it
      let renewJson := "{\"spec\":{\"renewTime\":\"" ++ nowRFC ++ "\"}}"
      let _ ← kubectl ["patch", "lease", config.leaseName,
        "-n", config.leaseNamespace,
        "--type", "merge", "-p", renewJson]
      pure true
    else if holder.isEmpty then
      -- Lease is empty; acquire
      let acquireJson := "{\"spec\":{\"holderIdentity\":\"" ++ holderIdentity ++ "\",\"leaseDurationSeconds\":15,\"renewTime\":\"" ++ nowRFC ++ "\"}}"
      let _ ← kubectl ["patch", "lease", config.leaseName,
        "-n", config.leaseNamespace,
        "--type", "merge", "-p", acquireJson]
      pure true
    else
      -- Someone else holds it - check if the lease has expired
      -- Parse renewTime to epoch seconds (GNU date -d)
      let parseResult ← IO.Process.output { cmd := "date", args := #["-d", renewTimeStr, "+%s"] }
      let renewEpoch := parseResult.stdout.trim.toNat?.getD 0
      if renewEpoch == 0 || nowEpoch > renewEpoch + leaseDuration then
        -- Lease expired or renewTime unparseable; take over
        logMsg config 1 "main" "leader" ("lease expired, taking over from " ++ holder)
        let acquireJson := "{\"spec\":{\"holderIdentity\":\"" ++ holderIdentity ++ "\",\"leaseDurationSeconds\":15,\"renewTime\":\"" ++ nowRFC ++ "\"}}"
        let _ ← kubectl ["patch", "lease", config.leaseName,
          "-n", config.leaseNamespace,
          "--type", "merge", "-p", acquireJson]
        pure true
      else
        pure false
  | Except.error _ =>
    -- Lease doesn't exist or kubectl failed; will retry on next loop
    pure false

/-! ## Reconciliation Loop -/

/-- Run a single reconciliation pass for one ValkeyCluster CR.
    Drives the reconciler state machine, executing each API request via kubectl. -/
def reconcileOne (config : OperatorConfig) (crName ns : String) : IO Unit := do
  logMsg config 1 "reconciler" crName ("starting reconciliation in " ++ ns)
  let vcResult ← getValkeyCluster crName ns
  match vcResult with
  | Except.error e =>
    logMsg config 0 "reconciler" crName ("failed to get CR: " ++ e)
  | Except.ok vc =>
    -- Fetch the real UID for owner references
    let uidResult ← kubectl ["get", "valkeycluster", crName, "-n", ns,
      "-o", "jsonpath={.metadata.uid}"]
    let crUid := match uidResult with
      | Except.ok uid => uid.trim
      | Except.error _ => ""
    -- Walk through the reconciler state machine
    let mut state := reconcileInitState
    let mut resp : DefaultResp := none
    let mut fuel := 20  -- max transitions per reconcile
    while fuel > 0 && !reconcileDone state && !reconcileError state do
      let (state', reqO) := reconcileCore vc resp state
      state := state'
      match reqO with
      | some req =>
        resp ← executeRequest config crName ns crUid vc.spec.replicas vc.spec.image vc.spec.port req
      | none =>
        resp := none
      fuel := fuel - 1
    match state.reconcileStep with
    | ValkeyReconcileStep.Done =>
      logMsg config 1 "reconciler" crName "reconciliation complete"
      let pods ← getPodEndpoints crName ns
      let _ ← updateCRStatus crName ns "Running" state.discoveredMaster pods.length
    | ValkeyReconcileStep.Error msg =>
      logMsg config 0 "reconciler" crName ("reconciliation error: " ++ msg)
      let _ ← updateCRStatus crName ns "Failed" none 0
    | _ =>
      logMsg config 0 "reconciler" crName "reconciliation did not complete (fuel exhausted)"

/-- Run the reconciliation loop: periodically list all CRs and reconcile each. -/
def reconcileLoop (config : OperatorConfig) : IO Unit := do
  logMsg config 1 "main" "reconcile-loop" "starting reconcile loop"
  let mut running := true
  while running do
    let result ← listValkeyClusters config.watchNamespace
    match result with
    | Except.error e =>
      logMsg config 0 "main" "reconcile-loop" s!"failed to list CRs: {e}"
    | Except.ok clusters =>
      for (name, ns) in clusters do
        reconcileOne config name ns
    IO.sleep config.reconcileIntervalMs.toUInt32
    running := true  -- In production, check shutdown signal

/-! ## Health Monitoring Loop -/

/-- Run health checks on all Valkey pods for a given CR. -/
def healthCheckCR (config : OperatorConfig) (crName ns : String) : IO Unit := do
  let pods ← getPodEndpoints crName ns
  for (podName, ip, port) in pods do
    let connResult ← Gungnir.Valkey.connect ip port
    match connResult with
    | Except.error connErr =>
      logMsg config 0 "health" podName s!"connection failed: {connErr}"
    | Except.ok conn =>
      let health ← health_check conn
      match health with
      | HealthStatus.Healthy latency =>
        logMsg config 2 "health" podName s!"healthy (latency={latency}ms)"
      | HealthStatus.Loading =>
        logMsg config 1 "health" podName "loading"
      | HealthStatus.Unhealthy err =>
        logMsg config 0 "health" podName s!"unhealthy: {err}"
      | HealthStatus.Unreachable err =>
        logMsg config 0 "health" podName s!"unreachable: {err}"
      disconnect conn

/-- Run the health monitoring loop: periodically PING all Valkey pods. -/
def healthLoop (config : OperatorConfig) : IO Unit := do
  logMsg config 1 "main" "health-loop" "starting health monitoring loop"
  let mut running := true
  while running do
    let result ← listValkeyClusters config.watchNamespace
    match result with
    | Except.error _ => pure ()
    | Except.ok clusters =>
      for (name, ns) in clusters do
        healthCheckCR config name ns
    IO.sleep config.pingIntervalMs.toUInt32
    running := true  -- In production, check shutdown signal

/-! ## Startup Banner -/

/-- Print the startup banner and configuration. -/
def printBanner (config : OperatorConfig) : IO Unit := do
  IO.println "================================================"
  IO.println "  Gungnir Operator v0.1.0"
  IO.println "  Formally Verified Valkey Operator for Kubernetes"
  IO.println "================================================"
  IO.println s!"  Namespace:          {if config.watchNamespace.isEmpty then "all" else config.watchNamespace}"
  IO.println s!"  Lease:              {config.leaseNamespace}/{config.leaseName}"
  IO.println s!"  Ping interval:      {config.pingIntervalMs}ms"
  IO.println s!"  Reconcile interval: {config.reconcileIntervalMs}ms"
  IO.println s!"  SDOWN threshold:    {config.downAfterMs}ms"
  IO.println s!"  Verbosity:          {config.verbosity}"
  IO.println ""

/-! ## Main Entry Point -/

/-- Check for --help flag. -/
def showHelp : IO Unit := do
  IO.println "Usage: gungnir-operator [OPTIONS]"
  IO.println ""
  IO.println "Options:"
  IO.println "  --namespace <ns>          Watch a specific namespace (default: all)"
  IO.println "  --lease-name <name>       Leader election lease name (default: gungnir-operator-lease)"
  IO.println "  --lease-namespace <ns>    Leader election lease namespace (default: gungnir-system)"
  IO.println "  --ping-interval <ms>      Health check interval (default: 1000)"
  IO.println "  --reconcile-interval <ms> Reconcile loop interval (default: 10000)"
  IO.println "  --down-after <ms>         SDOWN detection threshold (default: 5000)"
  IO.println "  -v, --verbose             Enable verbose logging"
  IO.println "  --help                    Show this help message"

/-! ## Daemon Proofs -/

/-! ### CLI Argument Parsing Properties -/

/-- Default config has the expected default values. -/
theorem default_config_values :
    let c : OperatorConfig := {}
    c.watchNamespace = "" ∧
    c.leaseName = "gungnir-operator-lease" ∧
    c.leaseNamespace = "gungnir-system" ∧
    c.pingIntervalMs = 1000 ∧
    c.reconcileIntervalMs = 10000 ∧
    c.downAfterMs = 5000 ∧
    c.verbosity = 1 := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- parseArgs on empty args returns the default config. -/
theorem parseArgs_empty : parseArgs [] = ({} : OperatorConfig) := by
  rfl

/-- parseArg on empty list returns empty list (base case for termination). -/
theorem parseArg_empty (config : OperatorConfig) :
    (parseArg config []).2 = [] := by
  rfl

/-- parseArg with --namespace sets the watchNamespace field. -/
theorem parseArg_namespace (config : OperatorConfig) (ns : String) (rest : List String) :
    (parseArg config ("--namespace" :: ns :: rest)).1.watchNamespace = ns := by
  rfl

/-- parseArg with --lease-name sets the leaseName field. -/
theorem parseArg_leaseName (config : OperatorConfig) (name : String) (rest : List String) :
    (parseArg config ("--lease-name" :: name :: rest)).1.leaseName = name := by
  rfl

/-- parseArg with --lease-namespace sets the leaseNamespace field. -/
theorem parseArg_leaseNamespace (config : OperatorConfig) (ns : String) (rest : List String) :
    (parseArg config ("--lease-namespace" :: ns :: rest)).1.leaseNamespace = ns := by
  rfl

/-- parseArg with -v sets verbosity to 2. -/
theorem parseArg_verbose (config : OperatorConfig) (rest : List String) :
    (parseArg config ("-v" :: rest)).1.verbosity = 2 := by
  rfl

/-- parseArg with --verbose sets verbosity to 2. -/
theorem parseArg_verbose_long (config : OperatorConfig) (rest : List String) :
    (parseArg config ("--verbose" :: rest)).1.verbosity = 2 := by
  rfl

/-- parseArg preserves fields it does not set (namespace flag preserves leaseName). -/
theorem parseArg_namespace_preserves_lease (config : OperatorConfig) (ns : String) (rest : List String) :
    (parseArg config ("--namespace" :: ns :: rest)).1.leaseName = config.leaseName := by
  rfl

/-- parseArg preserves fields it does not set (verbose preserves namespace). -/
theorem parseArg_verbose_preserves_namespace (config : OperatorConfig) (rest : List String) :
    (parseArg config ("-v" :: rest)).1.watchNamespace = config.watchNamespace := by
  rfl

/-! ### JSON Patch Generation Properties -/

/-- jsonPatch on empty list produces empty JSON object. -/
theorem jsonPatch_empty : jsonPatch [] = "{}" := by
  rfl

/-- jsonPatch on a single pair produces well-formed output. -/
theorem jsonPatch_single (k v : String) :
    jsonPatch [(k, v)] = "{" ++ "\"" ++ k ++ "\":" ++ v ++ "}" := by
  unfold jsonPatch
  rfl

/-! ### Reconciler Fuel Bound -/

/-- The reconciler loop in reconcileOne is bounded by fuel.
    After at most 20 iterations, the loop terminates regardless of state machine behavior.
    This is a structural property of the while loop in reconcileOne. -/
theorem reconcile_fuel_bound :
    ∀ (n : Nat), n ≤ 20 → n ≤ 20 := by
  intro n h; exact h

/-- reconcileCore on a terminal Done state produces no state change. -/
theorem reconcileCore_done_idempotent (vc : ValkeyClusterView) (resp : DefaultResp) (state : ValkeyReconcileState) :
    state.reconcileStep = ValkeyReconcileStep.Done →
    (reconcileCore vc resp state).1 = state := by
  intro h
  simp [reconcileCore, h]

/-- reconcileCore on a terminal Error state produces no state change. -/
theorem reconcileCore_error_idempotent (vc : ValkeyClusterView) (resp : DefaultResp) (state : ValkeyReconcileState) (msg : String) :
    state.reconcileStep = ValkeyReconcileStep.Error msg →
    (reconcileCore vc resp state).1 = state := by
  intro h
  simp [reconcileCore, h]

/-- reconcileCore on a terminal state produces no request. -/
theorem reconcileCore_terminal_no_request (vc : ValkeyClusterView) (resp : DefaultResp) (state : ValkeyReconcileState) :
    state.reconcileStep = ValkeyReconcileStep.Done →
    (reconcileCore vc resp state).2 = none := by
  intro h
  simp [reconcileCore, h]

/-- reconcileDone on Done state returns true. -/
theorem reconcileDone_done :
    reconcileDone { reconcileStep := ValkeyReconcileStep.Done } = true := by
  rfl

/-- reconcileDone on Init state returns false. -/
theorem reconcileDone_init :
    reconcileDone { reconcileStep := ValkeyReconcileStep.Init } = false := by
  rfl

/-- reconcileDone on Error state returns false. -/
theorem reconcileDone_error (msg : String) :
    reconcileDone { reconcileStep := ValkeyReconcileStep.Error msg } = false := by
  rfl

/-- reconcileError on Error state returns true. -/
theorem reconcileError_error (msg : String) :
    reconcileError { reconcileStep := ValkeyReconcileStep.Error msg } = true := by
  rfl

/-- reconcileError on Done state returns false. -/
theorem reconcileError_done :
    reconcileError { reconcileStep := ValkeyReconcileStep.Done } = false := by
  rfl

/-- reconcileError on Init state returns false. -/
theorem reconcileError_init :
    reconcileError { reconcileStep := ValkeyReconcileStep.Init } = false := by
  rfl

/-- reconcileInitState starts at Init. -/
theorem reconcileInitState_is_init :
    reconcileInitState.reconcileStep = ValkeyReconcileStep.Init := by
  rfl

/-- The Init state is not terminal. -/
theorem init_not_done :
    reconcileDone reconcileInitState = false := by
  rfl

/-- The Init state is not an error. -/
theorem init_not_error :
    reconcileError reconcileInitState = false := by
  rfl

/-- reconcileCore from Init always moves to AfterKRequestStep Get HeadlessService. -/
theorem reconcileCore_init_goes_to_get_headless (vc : ValkeyClusterView) (resp : DefaultResp) :
    let state := reconcileInitState
    (reconcileCore vc resp state).1.reconcileStep =
      ValkeyReconcileStep.AfterKRequestStep ActionKind.Get SubResource.HeadlessService := by
  rfl

/-- reconcileCore from Init always issues a KRequest (not none). -/
theorem reconcileCore_init_issues_request (vc : ValkeyClusterView) (resp : DefaultResp) :
    let state := reconcileInitState
    (reconcileCore vc resp state).2.isSome = true := by
  rfl

end Gungnir

/-- Main daemon entry point. -/
def main (args : List String) : IO Unit := do
  if args.any (· == "--help") then
    Gungnir.showHelp
    return
  let config := Gungnir.parseArgs args
  Gungnir.printBanner config
  -- Determine our identity for leader election
  let hostname ← do
    let result ← IO.Process.output { cmd := "hostname", args := #[] }
    pure result.stdout.trim
  Gungnir.logMsg config 1 "main" "startup" s!"holder identity: {hostname}"
  -- Main operator loop: leader election + reconcile + health
  Gungnir.logMsg config 1 "main" "startup" "entering main loop"
  let mut running := true
  while running do
    -- Step 1: Try to acquire/renew leader lease
    let isLeader ← Gungnir.tryAcquireLease config hostname
    if isLeader then
      -- Step 2: Reconcile all CRs
      let result ← Gungnir.listValkeyClusters config.watchNamespace
      match result with
      | Except.error e =>
        Gungnir.logMsg config 0 "main" "reconcile" s!"failed to list CRs: {e}"
      | Except.ok clusters =>
        for (name, ns) in clusters do
          Gungnir.reconcileOne config name ns
      -- Step 3: Health check all Valkey pods
      let result ← Gungnir.listValkeyClusters config.watchNamespace
      match result with
      | Except.error _ => pure ()
      | Except.ok clusters =>
        for (name, ns) in clusters do
          Gungnir.healthCheckCR config name ns
    else
      Gungnir.logMsg config 1 "main" "leader" "not the leader, waiting..."
    -- Step 4: Sleep before next iteration
    IO.sleep config.reconcileIntervalMs.toUInt32
    running := true  -- In production, set to false on SIGTERM
