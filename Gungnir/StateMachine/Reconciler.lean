/-
  Reconciler.lean - Valkey operator reconciler state machine

  This module defines the reconciler state machine for the Valkey operator,
  following the Anvil pattern (one API call per state transition, always forward
  progress, idempotent re-execution).

  The reconciler manages Kubernetes resources:
  - HeadlessService (for StatefulSet pod discovery)
  - ClientService (for client connections)
  - ConfigMap (valkey.conf)
  - Secret (ACL credentials)
  - StatefulSet (Valkey pods)
  - Status update

  Each resource goes through Get -> Create/Update transitions.

  This module uses the K8s types from Gungnir.K8s for API requests,
  responses, and the ValkeyCluster custom resource.

  Reference: anvil/src/controllers/zookeeper_controller/model/reconciler.rs
             anvil/src/controllers/zookeeper_controller/trusted/step.rs
-/

import Gungnir.K8s.K8s
import Gungnir.StateMachine.StateMachine

namespace Gungnir.Reconciler

open Gungnir.K8s
open Gungnir.StateMachine

-- Helper: determine the next sub-resource to process after the current one.
-- The reconciler processes resources in this fixed order.
def nextSubResource (r : SubResource) : Option SubResource :=
  match r with
  | SubResource.HeadlessService     => some SubResource.ClientService
  | SubResource.ClientService       => some SubResource.ConfigMap
  | SubResource.ConfigMap            => some SubResource.Secret
  | SubResource.Secret               => some SubResource.StatefulSet
  | SubResource.StatefulSet          => some SubResource.PodDisruptionBudget
  | SubResource.PodDisruptionBudget  => none

-- Check if a ValkeyReconcileStep is a terminal state.
def isTerminal (step : ValkeyReconcileStep) : Prop :=
  match step with
  | ValkeyReconcileStep.Done    => True
  | ValkeyReconcileStep.Error _ => True
  | _                           => False

-- Check if a ValkeyReconcileStep is a terminal state (decidable version).
def isTerminalBool (step : ValkeyReconcileStep) : Bool :=
  match step with
  | ValkeyReconcileStep.Done    => true
  | ValkeyReconcileStep.Error _ => true
  | _                           => false

-- Build a GetRequest for a given sub-resource of the specified CR.
def makeGetRequest (vc : ValkeyClusterView) (sub : SubResource) : APIRequest :=
  let crName := vc.metadata.name.getD ""
  let ns := vc.metadata.«namespace».getD ""
  APIRequest.GetRequest (subResourceGetRequest crName ns sub)

-- Helper to build a DynamicObjectView placeholder for resource creation.
private def makePlaceholderObj (kind : Kind) (name : String) (ns : String) : DynamicObjectView :=
  { kind := kind
  , metadata := (ObjectMetaView.default.withName name).withNamespace ns
  , spec := ""
  , status := "" }

-- Helper to build an UpdateStatusRequest for the CR.
private def makeStatusReq (crName : String) (ns : String) : APIRequest :=
  let statusObj := makePlaceholderObj ValkeyClusterView.kind crName ns
  let usReq : Gungnir.K8s.UpdateStatusRequest :=
    { «namespace» := ns, name := crName, obj := statusObj }
  APIRequest.UpdateStatusRequest usReq

-- The core reconciliation transition function.
-- Given the CR, an optional API response, and the current state, produce
-- the next state and an optional API request to issue.
--
-- This follows the Anvil pattern:
-- 1. Init -> Get HeadlessService
-- 2. AfterGet(resource) -> if found, Update; if not found, Create
-- 3. AfterCreate/Update(resource) -> Get next resource (or proceed to health check)
-- 4. Health check -> failover detection -> ... -> UpdateStatus -> Done
def reconcileCore
    (vc : ValkeyClusterView)
    (respO : DefaultResp)
    (state : ValkeyReconcileState)
    : ValkeyReconcileState × DefaultReq :=
  let crName := vc.metadata.name.getD ""
  let ns := vc.metadata.«namespace».getD ""
  match state.reconcileStep with
  | ValkeyReconcileStep.Init =>
    -- Start by getting the headless service
    let state' := { state with reconcileStep := ValkeyReconcileStep.AfterKRequestStep .Get .HeadlessService }
    (state', some (RequestView.KRequest (makeGetRequest vc .HeadlessService)))

  | ValkeyReconcileStep.AfterKRequestStep action resource =>
    match action with
    | ActionKind.Get =>
      match extractKGetResp respO with
      | some (Except.ok obj) =>
        -- Resource exists: issue an update
        let updReq : Gungnir.K8s.UpdateRequest :=
          { «namespace» := ns, name := subResourceName crName resource, obj := obj }
        let req := APIRequest.UpdateRequest updReq
        let state' := { state with reconcileStep := ValkeyReconcileStep.AfterKRequestStep .Update resource }
        (state', some (RequestView.KRequest req))
      | some (Except.error APIError.ObjectNotFound) =>
        -- Resource does not exist: create it
        let newObj := makePlaceholderObj (subResourceKind resource) (subResourceName crName resource) ns
        let creReq : Gungnir.K8s.CreateRequest :=
          { «namespace» := ns, obj := newObj }
        let req := APIRequest.CreateRequest creReq
        let state' := { state with reconcileStep := ValkeyReconcileStep.AfterKRequestStep .Create resource }
        (state', some (RequestView.KRequest req))
      | _ =>
        -- Unexpected response: error
        ({ state with reconcileStep := ValkeyReconcileStep.Error "unexpected get response" }, none)

    | ActionKind.Create =>
      match extractKCreateResp respO with
      | some (Except.ok _createdObj) =>
        -- Successfully created; move to next resource or health check
        match nextSubResource resource with
        | some next =>
          let state' := { state with reconcileStep := ValkeyReconcileStep.AfterKRequestStep .Get next }
          (state', some (RequestView.KRequest (makeGetRequest vc next)))
        | none =>
          -- All resources processed; move to health check
          let state' := { state with reconcileStep := ValkeyReconcileStep.AfterCheckValkeyHealth }
          (state', none)
      | _ =>
        ({ state with reconcileStep := ValkeyReconcileStep.Error "create failed" }, none)

    | ActionKind.Update =>
      match extractKUpdateResp respO with
      | some (Except.ok _updatedObj) =>
        -- Successfully updated; move to next resource or health check
        match nextSubResource resource with
        | some next =>
          let state' := { state with reconcileStep := ValkeyReconcileStep.AfterKRequestStep .Get next }
          (state', some (RequestView.KRequest (makeGetRequest vc next)))
        | none =>
          let state' := { state with reconcileStep := ValkeyReconcileStep.AfterCheckValkeyHealth }
          (state', none)
      | _ =>
        ({ state with reconcileStep := ValkeyReconcileStep.Error "update failed" }, none)

  | ValkeyReconcileStep.AfterCheckValkeyHealth =>
    -- Check nodeHealthMap for SDOWN threshold. If master failed → failover path.
    -- The executor populates nodeHealthMap and failedMaster before feeding back.
    match state.failedMaster with
    | some _ =>
      -- Master SDOWN detected; enter failover path
      let state' := { state with
        reconcileStep := ValkeyReconcileStep.AfterDetectFailure
        failoverInProgress := true }
      (state', none)
    | none =>
      -- All healthy; proceed to status update
      let state' := { state with reconcileStep := ValkeyReconcileStep.AfterUpdateStatus }
      (state', some (RequestView.KRequest (makeStatusReq crName ns)))

  | ValkeyReconcileStep.AfterDetectFailure =>
    -- Failure detected; proceed to replica selection (selection done in executor)
    let state' := { state with reconcileStep := ValkeyReconcileStep.AfterSelectReplica }
    (state', none)

  | ValkeyReconcileStep.AfterSelectReplica =>
    -- Check if a replica was selected by the executor
    match state.selectedReplica with
    | some _ =>
      -- Replica selected; proceed to promotion (promotion done in executor)
      let state' := { state with reconcileStep := ValkeyReconcileStep.AfterPromoteReplica }
      (state', none)
    | none =>
      -- No eligible replica found; error
      ({ state with reconcileStep := ValkeyReconcileStep.Error "no eligible replica for failover" }, none)

  | ValkeyReconcileStep.AfterPromoteReplica =>
    -- Promotion done (by executor); update service to point to new master
    let state' := { state with reconcileStep := ValkeyReconcileStep.AfterUpdateService }
    (state', none)

  | ValkeyReconcileStep.AfterUpdateService =>
    -- Service updated (by executor); proceed to status update
    let state' := { state with
      reconcileStep := ValkeyReconcileStep.AfterUpdateStatus
      failoverInProgress := false }
    (state', some (RequestView.KRequest (makeStatusReq crName ns)))

  | ValkeyReconcileStep.AfterUpdateStatus =>
    match extractKUpdateStatusResp respO with
    | some (Except.ok _) =>
      ({ state with reconcileStep := ValkeyReconcileStep.Done }, none)
    | _ =>
      ({ state with reconcileStep := ValkeyReconcileStep.Error "status update failed" }, none)

  | ValkeyReconcileStep.Done =>
    -- Terminal state: no transition
    (state, none)

  | ValkeyReconcileStep.Error _ =>
    -- Terminal state: no transition
    (state, none)

-- The reconciler as a StateMachine instance.
-- The step type is ValkeyReconcileStep (determines which transition fires),
-- the input is the response from the K8s API, and the output is an optional request.
def reconcilerStateMachine (vc : ValkeyClusterView) :
    StateMachine
      ValkeyReconcileState                           -- State
      DefaultResp                                    -- Input (response)
      (ValkeyClusterView × DefaultResp)              -- ActionInput
      DefaultReq                                     -- Output (request)
      ValkeyReconcileStep                            -- Step
    :=
  { init := fun s => s = reconcileInitState
    stepToAction := fun step =>
      { precondition := fun (_ : ValkeyClusterView × DefaultResp) s =>
          s.reconcileStep = step ∧ ¬isTerminal s.reconcileStep
        transition := fun (vcResp : ValkeyClusterView × DefaultResp) s =>
          let (s', req) := reconcileCore vcResp.1 vcResp.2 s
          (s', req)
      }
    actionInput := fun _step resp => (vc, resp)
  }

end Gungnir.Reconciler
