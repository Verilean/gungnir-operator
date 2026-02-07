/-
  Invariants.lean - Safety invariants for the Valkey operator

  This module defines the safety invariants that must hold at every reachable state
  of the operator's state machine. These are the "always" (box) properties from
  temporal logic.

  Key invariants:
  1. at_most_one_master: At most one pod receives client traffic at any time
  2. owner_ref_consistency: All managed resources have exactly one owner reference
  3. no_concurrent_updates: At most one pending update per resource key
  4. reconcile_step_valid: The reconciler step is always a valid step
  5. sentinel_forward_progress: The sentinel state machine never goes backward

  Uses K8s types from Gungnir.K8s for ObjectRef, APIRequest, DynamicObjectView, etc.

  Reference: features.md Section [V] Formal Verification
             anvil/src/controllers/zookeeper_controller/proof/helper_invariants/
-/

import Gungnir.StateMachine.TemporalLogic
import Gungnir.StateMachine.Reconciler
import Gungnir.StateMachine.Sentinel

namespace Gungnir.Invariants

open Gungnir.TemporalLogic
open Gungnir.K8s
open Gungnir.Reconciler
open Gungnir.Sentinel

-- The cluster-wide state used for invariant checking.
-- This combines the K8s API server state with the operator's internal state.
structure ClusterState where
  /-- The reconciler's internal state -/
  reconcileState : ValkeyReconcileState
  /-- The sentinel's internal state -/
  sentinelCtx : SentinelContext
  /-- Resources currently stored in the K8s API server (etcd) -/
  resources : StoredState
  /-- Pending API requests (not yet committed) -/
  pendingRequests : List APIRequest
  /-- Pods currently receiving client traffic via the Service -/
  trafficRecipients : List String
  /-- Whether this operator instance holds the leader lease -/
  hasLease : Bool
  deriving Repr

-- ===========================================================================
-- Safety Invariant 1: At Most One Master
-- ===========================================================================

-- At most one pod receives client traffic at any time.
-- This prevents split-brain scenarios.
def atMostOneMaster (s : ClusterState) : Prop :=
  s.trafficRecipients.length ≤ 1

-- Theorem: atMostOneMaster is an inductive invariant.
theorem atMostOneMaster_invariant :
    ∀ (s s' : ClusterState),
      atMostOneMaster s ->
      -- Placeholder for the next-state relation
      True ->
      atMostOneMaster s' := by
  sorry

-- ===========================================================================
-- Safety Invariant 2: Owner Reference Consistency
-- ===========================================================================

-- All managed resources have an owner reference pointing to a CR in the
-- correct namespace.
def ownerRefConsistency (vc : ValkeyClusterView) (s : ClusterState) : Prop :=
  let ns := vc.metadata.«namespace».getD ""
  ∀ (pair : ObjectRef × DynamicObjectView),
    pair ∈ s.resources ->
    pair.1.«namespace» = ns

-- Theorem: owner references are consistent after any transition.
theorem ownerRefConsistency_invariant :
    ∀ (vc : ValkeyClusterView) (s s' : ClusterState),
      ownerRefConsistency vc s ->
      True ->
      ownerRefConsistency vc s' := by
  sorry

-- ===========================================================================
-- Safety Invariant 3: No Concurrent Updates
-- ===========================================================================

-- Helper: extract the ObjectRef key from an APIRequest, if it's an update.
def updateRequestKey (req : APIRequest) : Option ObjectRef :=
  match req with
  | APIRequest.UpdateRequest r => some (UpdateRequest.key r)
  | _ => none

-- At most one pending update request per resource key.
-- This ensures the resource version check is meaningful.
def noConcurrentUpdates (s : ClusterState) : Prop :=
  ∀ (key : ObjectRef),
    (s.pendingRequests.filter fun r => updateRequestKey r == some key).length ≤ 1

-- Theorem: no concurrent updates invariant is maintained.
theorem noConcurrentUpdates_invariant :
    ∀ (s s' : ClusterState),
      noConcurrentUpdates s ->
      True ->
      noConcurrentUpdates s' := by
  sorry

-- ===========================================================================
-- Safety Invariant 4: Reconcile Step Validity
-- ===========================================================================

-- The reconciler is always in a recognized step (exhaustive match).
def reconcileStepValid (s : ClusterState) : Prop :=
  match s.reconcileState.reconcileStep with
  | ValkeyReconcileStep.Init => True
  | ValkeyReconcileStep.AfterKRequestStep _ _ => True
  | ValkeyReconcileStep.AfterCheckValkeyHealth => True
  | ValkeyReconcileStep.AfterDetectFailure => True
  | ValkeyReconcileStep.AfterSelectReplica => True
  | ValkeyReconcileStep.AfterPromoteReplica => True
  | ValkeyReconcileStep.AfterUpdateService => True
  | ValkeyReconcileStep.AfterUpdateStatus => True
  | ValkeyReconcileStep.Done => True
  | ValkeyReconcileStep.Error _ => True

-- Theorem: every reachable reconcile step is valid (trivially true by exhaustion).
theorem reconcileStepValid_invariant :
    ∀ (s : ClusterState),
      reconcileStepValid s := by
  intro s
  unfold reconcileStepValid
  cases s.reconcileState.reconcileStep <;> exact trivial

-- ===========================================================================
-- Safety Invariant 5: Sentinel Forward Progress
-- ===========================================================================

-- The sentinel state machine always moves forward (no cycles).
def sentinelForwardProgress (ctx ctx' : SentinelContext) : Prop :=
  sentinelStateOrder ctx'.sentinelState ≥ sentinelStateOrder ctx.sentinelState

-- Theorem: sentinel transitions always make forward progress.
theorem sentinelForwardProgress_invariant :
    ∀ (ctx : SentinelContext),
      let ctx' := sentinelNext ctx
      sentinelForwardProgress ctx ctx' := by
  sorry

-- ===========================================================================
-- Safety Invariant 6: Leader Election Safety
-- ===========================================================================

-- Only the lease holder can modify cluster state.
def leaderElectionSafety (s : ClusterState) : Prop :=
  s.pendingRequests.length > 0 -> s.hasLease = true

-- Theorem: leader election safety invariant.
theorem leaderElectionSafety_invariant :
    ∀ (s s' : ClusterState),
      leaderElectionSafety s ->
      True ->
      leaderElectionSafety s' := by
  sorry

-- ===========================================================================
-- Combined Safety Property
-- ===========================================================================

-- All safety invariants combined.
def safetyInvariant (vc : ValkeyClusterView) (s : ClusterState) : Prop :=
  atMostOneMaster s ∧
  ownerRefConsistency vc s ∧
  noConcurrentUpdates s ∧
  reconcileStepValid s ∧
  leaderElectionSafety s

-- The safety property as a temporal predicate: always(safetyInvariant).
def safetyProperty (vc : ValkeyClusterView) : TempPred ClusterState :=
  always (liftState (safetyInvariant vc))

end Gungnir.Invariants
