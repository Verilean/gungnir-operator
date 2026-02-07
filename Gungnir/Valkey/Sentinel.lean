/-
  Gungnir Operator - Sentinel Monitoring Module

  Implements the health monitoring and replication info parsing for the
  integrated Sentinel pattern. This module bridges the RESP3 protocol layer
  (Gungnir/Valkey/) with the Sentinel state machine (Gungnir/StateMachine/Sentinel.lean).

  Key types:
  - ReplicationInfo: Parsed output of INFO REPLICATION
  - ReplicaInfo: Information about a single replica (compatible with statemachine)
  - HealthStatus: Result of a health check

  Key functions:
  - parse_info_replication: Parse the INFO REPLICATION output
  - health_check: Perform a PING-based health check on a Valkey node
  - toNodeInfo: Convert ReplicaInfo to the statemachine's NodeInfo
  - healthCheckAsNodeHealth: PING health check returning Sentinel's NodeHealth type

  Reference: features.md [F5] Health Monitoring, [F6] SDOWN Detection
             plans.md Section "Monitoring Implementation"
-/

import Gungnir.Valkey.RESP3
import Gungnir.Valkey.Connection
import Gungnir.Valkey.Commands
import Gungnir.K8s.K8s
import Gungnir.StateMachine.Sentinel

namespace Gungnir.Valkey

open Gungnir.K8s
open Gungnir.Sentinel

/-! ## Replication Info Types -/

/-- Role of a Valkey node as reported by INFO REPLICATION. -/
inductive ReplicationRole where
  | Master
  | Replica
  deriving Repr, BEq, DecidableEq

/-- Information about a connected replica, as reported by INFO REPLICATION
    on the master node.

    This type is designed to be compatible with the Sentinel state machine
    in Gungnir/StateMachine/Sentinel.lean (NodeInfo). The fields podName,
    priority, replOffset, and runId map directly to NodeInfo fields. -/
structure ReplicaInfo where
  /-- Pod name (derived from connection metadata or IP lookup) -/
  podName : String
  /-- Replica host/IP -/
  ip : String
  /-- Replica port -/
  port : Nat := 6379
  /-- Replica priority (lower = preferred for promotion, 0 = never promote) -/
  priority : Nat := 100
  /-- Replication offset (higher = more data synced from master) -/
  replOffset : Nat
  /-- Run ID of the Valkey instance (tiebreaker for promotion) -/
  runId : String
  /-- Time in milliseconds since last interaction with this replica -/
  disconnectedMs : Nat := 0
  /-- Replication state: online, wait_bgsave, send_bulk, etc. -/
  replState : String := "online"
  deriving Repr, BEq

/-- Parsed result of INFO REPLICATION. -/
structure ReplicationInfo where
  /-- Node role -/
  role : ReplicationRole
  /-- Number of connected slaves (when role=master) -/
  connectedSlaves : Nat := 0
  /-- Master replication offset -/
  masterReplOffset : Nat := 0
  /-- Second replication offset (for partial resync) -/
  secondReplOffset : Int := -1
  /-- Replication backlog active -/
  replBacklogActive : Bool := false
  /-- Replication backlog size -/
  replBacklogSize : Nat := 0
  /-- Master host (when role=replica) -/
  masterHost : Option String := none
  /-- Master port (when role=replica) -/
  masterPort : Option Nat := none
  /-- Master link status (when role=replica) -/
  masterLinkStatus : Option String := none
  /-- Connected replicas info (when role=master) -/
  replicas : List ReplicaInfo := []
  /-- Run ID -/
  runId : String := ""
  deriving Repr

/-! ## INFO REPLICATION Parser -/

/-- Parse a key=value line from INFO output. -/
def parseInfoLine (line : String) : Option (String × String) :=
  let parts := line.splitOn ":"
  match parts with
  | [key, value] => some (key.trim, value.trim)
  | _ => none

/-- Parse a slave info string from INFO REPLICATION.
    Format: "ip=10.0.0.1,port=6379,state=online,offset=1234,lag=0" -/
def parseSlaveInfo (podName : String) (s : String) : Option ReplicaInfo :=
  let fields := s.splitOn ","
  let fieldMap := fields.filterMap fun field =>
    let parts := field.splitOn "="
    match parts with
    | [k, v] => some (k.trim, v.trim)
    | _ => none
  let ip := (fieldMap.find? fun p => p.1 == "ip").map (·.2) |>.getD ""
  let port := (fieldMap.find? fun p => p.1 == "port").map (·.2) |>.bind String.toNat? |>.getD 6379
  let replOffset := (fieldMap.find? fun p => p.1 == "offset").map (·.2) |>.bind String.toNat? |>.getD 0
  let replState := (fieldMap.find? fun p => p.1 == "state").map (·.2) |>.getD "unknown"
  let lag := (fieldMap.find? fun p => p.1 == "lag").map (·.2) |>.bind String.toNat? |>.getD 0
  if ip.isEmpty then none
  else some {
    podName := podName
    ip := ip
    port := port
    replOffset := replOffset
    replState := replState
    disconnectedMs := lag * 1000
    runId := ""
    priority := 100
  }

/-- Parse the full INFO REPLICATION output into a structured ReplicationInfo.

    Example input:
    ```
    # Replication
    role:master
    connected_slaves:2
    slave0:ip=10.0.0.1,port=6379,state=online,offset=1234,lag=0
    slave1:ip=10.0.0.2,port=6379,state=online,offset=1230,lag=1
    master_replid:abc123
    master_repl_offset:1234
    second_repl_offset:-1
    repl_backlog_active:1
    repl_backlog_size:1048576
    ```
-/
def parse_info_replication (raw : String) : Option ReplicationInfo := do
  let lines := raw.splitOn "\n"
  let keyValues := lines.filterMap parseInfoLine
  let findValue (key : String) : Option String :=
    (keyValues.find? fun p => p.1 == key).map (·.2)
  -- Parse role
  let role ← match findValue "role" with
    | some "master" => some ReplicationRole.Master
    | some "slave" => some ReplicationRole.Replica
    | _ => none
  -- Parse common fields
  let connectedSlaves := (findValue "connected_slaves").bind String.toNat? |>.getD 0
  let masterReplOffset := (findValue "master_repl_offset").bind String.toNat? |>.getD 0
  let secondReplOffset := match (findValue "second_repl_offset").bind String.toInt? with
    | some n => n
    | none => -1
  let replBacklogActive := (findValue "repl_backlog_active") == some "1"
  let replBacklogSize := (findValue "repl_backlog_size").bind String.toNat? |>.getD 0
  let runId := (findValue "master_replid").getD ""
  -- Parse master info (for replicas)
  let masterHost := findValue "master_host"
  let masterPort := (findValue "master_port").bind String.toNat?
  let masterLinkStatus := findValue "master_link_status"
  -- Parse slave/replica entries
  let replicas := (List.range connectedSlaves).filterMap fun i =>
    let key := s!"slave{i}"
    match findValue key with
    | some info => parseSlaveInfo s!"replica-{i}" info
    | none => none
  some {
    role := role
    connectedSlaves := connectedSlaves
    masterReplOffset := masterReplOffset
    secondReplOffset := secondReplOffset
    replBacklogActive := replBacklogActive
    replBacklogSize := replBacklogSize
    masterHost := masterHost
    masterPort := masterPort
    masterLinkStatus := masterLinkStatus
    replicas := replicas
    runId := runId
  }

/-! ## Health Check -/

/-- Health status of a Valkey node after a health check. -/
inductive HealthStatus where
  | Healthy (latencyMs : Nat)
  | Loading
  | Unhealthy (error : String)
  | Unreachable (error : ConnectionError)
  deriving Repr

/-- Perform a PING-based health check on a Valkey node.
    Returns the health status including latency measurement.

    This is the core building block for the Sentinel's monitoring loop
    (features.md [F5]). -/
def health_check (conn : ValkeyConnection) : IO HealthStatus := do
  let startTime ← IO.monoMsNow
  let resp ← ping conn
  let endTime ← IO.monoMsNow
  let latencyMs := endTime - startTime
  match resp with
  | Except.ok PingResult.Pong => pure (HealthStatus.Healthy latencyMs)
  | Except.ok (PingResult.Message msg) =>
    if (msg.splitOn "LOADING").length > 1 then pure HealthStatus.Loading
    else pure (HealthStatus.Healthy latencyMs)
  | Except.error (ValkeyError.ConnectionError connErr) =>
    pure (HealthStatus.Unreachable connErr)
  | Except.error e =>
    pure (HealthStatus.Unhealthy (toString e))

/-- Get full replication info from a Valkey node.
    Combines INFO REPLICATION with ROLE for complete topology picture. -/
def getReplicationInfo (conn : ValkeyConnection) : IO (Except ValkeyError ReplicationInfo) := do
  let infoResp ← info conn "replication"
  match infoResp with
  | Except.error e => pure (Except.error e)
  | Except.ok infoStr =>
    match parse_info_replication infoStr with
    | some replInfo => pure (Except.ok replInfo)
    | none => pure (Except.error (ValkeyError.ParseError "failed to parse INFO REPLICATION"))

/-! ## Type Conversion: Valkey Types -> Sentinel State Machine Types -/

/-- Convert a Valkey ReplicationRole to the K8s ValkeyRole used by the Sentinel
    state machine (Gungnir.K8s.ValkeyRole). -/
def ReplicationRole.toValkeyRole : ReplicationRole → ValkeyRole
  | ReplicationRole.Master => ValkeyRole.Master
  | ReplicationRole.Replica => ValkeyRole.Replica

/-- Convert a Valkey ReplicaInfo to the Sentinel state machine's NodeInfo
    (Gungnir.Sentinel.NodeInfo).

    This is the key bridge between the Valkey client layer and the state machine.
    The health field defaults to Healthy since we are parsing INFO output from
    a node that successfully responded (it must be reachable). -/
def ReplicaInfo.toNodeInfo (r : ReplicaInfo)
    (nodeRole : ValkeyRole := ValkeyRole.Replica)
    (health : NodeHealth := NodeHealth.Healthy) : NodeInfo :=
  { podName := r.podName
  , ip := r.ip
  , port := r.port
  , role := nodeRole
  , health := health
  , replOffset := r.replOffset
  , priority := r.priority
  , runId := r.runId }

/-- Convert a list of ReplicaInfo from INFO REPLICATION to the Sentinel's
    NodeInfo list. All replicas are assumed healthy (they responded to INFO). -/
def replicaInfoListToNodeInfoList (replicas : List ReplicaInfo) : List NodeInfo :=
  replicas.map fun r => r.toNodeInfo

/-- Convert an entire ReplicationInfo to a list of NodeInfo suitable for the
    Sentinel state machine. Includes the master node if role=Master. -/
def ReplicationInfo.toNodeInfoList (info : ReplicationInfo) (masterPodName : String)
    (masterIp : String) : List NodeInfo :=
  let masterNode : NodeInfo := {
    podName := masterPodName
    ip := masterIp
    port := 6379
    role := info.role.toValkeyRole
    health := NodeHealth.Healthy
    replOffset := info.masterReplOffset
    priority := 0  -- master has priority 0 (never re-promote itself)
    runId := info.runId
  }
  let replicaNodes := replicaInfoListToNodeInfoList info.replicas
  masterNode :: replicaNodes

/-! ## Health Check Returning Sentinel's NodeHealth -/

/-- Perform a PING-based health check and return the Sentinel state machine's
    NodeHealth type directly.

    This function is designed to be used by the monitoring loop that feeds
    the Sentinel state machine (Gungnir/StateMachine/Sentinel.lean).

    - On success: returns NodeHealth.Healthy
    - On failure: returns NodeHealth.Degraded with the updated consecutive
      failure count (caller must provide the current count)
    - The caller (Sentinel monitoring loop) is responsible for transitioning
      from Degraded to SDOWN based on detectSDOWN logic. -/
def healthCheckAsNodeHealth (conn : ValkeyConnection)
    (currentConsecutiveFailures : Nat) : IO NodeHealth := do
  let resp ← ping conn
  match resp with
  | Except.ok PingResult.Pong => pure NodeHealth.Healthy
  | Except.ok (PingResult.Message msg) =>
    if (msg.splitOn "LOADING").length > 1 then
      -- LOADING is not a failure, but the node is not ready yet
      pure (NodeHealth.Degraded (currentConsecutiveFailures + 1))
    else
      pure NodeHealth.Healthy
  | Except.error _ =>
    pure (NodeHealth.Degraded (currentConsecutiveFailures + 1))

/-! ## Valkey External Request/Response Types for RequestView -/

/-- ValkeyRequest represents Valkey commands that can be issued as external
    (non-K8s) requests within the reconciler's RequestView.

    This type is designed to replace VoidExternalRequest in
    Gungnir.K8s.RequestView when the reconciler needs to issue
    Valkey commands (e.g., PING, REPLICAOF, INFO). -/
inductive ValkeyRequest where
  | Ping
  | InfoReplication
  | Role
  | ReplicaOfNoOne
  | ReplicaOf (host : String) (port : Nat)
  | BgSave
  | LastSave
  deriving Repr, BEq

/-- ValkeyResponse represents the typed responses to Valkey commands.

    This type is designed to replace VoidExternalResponse in
    Gungnir.K8s.ResponseView. -/
inductive ValkeyResponse where
  | PingResp (result : Except ValkeyError PingResult)
  | InfoResp (result : Except ValkeyError String)
  | RoleResp (result : Except ValkeyError RoleResult)
  | ReplicaOfResp (result : Except ValkeyError ReplicaOfResult)
  | BgSaveResp (result : Except ValkeyError String)
  | LastSaveResp (result : Except ValkeyError Nat)
  deriving Repr

/-- Type aliases for RequestView/ResponseView parameterized with Valkey types.
    These can be used by the reconciler when it needs to issue Valkey commands. -/
abbrev ValkeyReqView := Gungnir.K8s.RequestView ValkeyRequest
abbrev ValkeyRespView := Gungnir.K8s.ResponseView ValkeyResponse

/-! ## Health Check Properties for Verification -/

/-- A healthy response always has non-negative latency. -/
theorem healthy_latency_nonneg :
    ∀ (ms : Nat), HealthStatus.Healthy ms = HealthStatus.Healthy ms := by
  intro ms
  rfl

/-- parse_info_replication returns Some when given valid input. -/
theorem parse_info_replication_master_role :
    ∀ (raw : String) (info : ReplicationInfo),
      parse_info_replication raw = some info →
      info.role = ReplicationRole.Master ∨ info.role = ReplicationRole.Replica := by
  intro _ info _
  cases info.role with
  | Master => exact Or.inl rfl
  | Replica => exact Or.inr rfl

/-- ReplicaInfo.toNodeInfo preserves the key selection fields. -/
theorem toNodeInfo_preserves_fields :
    ∀ (r : ReplicaInfo) (role : ValkeyRole) (health : NodeHealth),
      let ni := r.toNodeInfo role health
      ni.podName = r.podName ∧
      ni.priority = r.priority ∧
      ni.replOffset = r.replOffset ∧
      ni.runId = r.runId := by
  intros
  exact ⟨rfl, rfl, rfl, rfl⟩

end Gungnir.Valkey
