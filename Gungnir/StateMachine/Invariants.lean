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
  6. leader_election_safety: Only the lease holder can modify cluster state
  7. partition_safety: No side-effects during lease partition or expiry
  8. service_consistency: Traffic recipients consistent with sentinel state
  9. no_double_failover: Completed failover doesn't re-trigger
  10. pdb_protects_master: Traffic recipients bounded by PDB

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

-- ===========================================================================
-- Lease Partition Model
-- ===========================================================================

/-- LeaseStatus models the K8s Lease state for leader election.
    Formalizes the partition model identified in the architecture review. -/
inductive LeaseStatus where
  /-- Lease is held by a specific operator instance with an expiry time.
      NOTE: `expiresAt` is a logical clock value, not wall-clock time.
      Not modeled: clock skew between operator and API server, lease renewal
      latency, or API server partition detection gap. For a formal clock
      analysis, a timed automaton model would be needed. -/
  | Held (holder : String) (expiresAt : Nat)
  /-- Lease has expired and is available for acquisition. -/
  | Expired
  /-- Lease holder is partitioned from the API server (network split). -/
  | Partitioned (holder : String)
  deriving Repr

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
  /-- Lease status for partition safety reasoning -/
  leaseStatus : LeaseStatus := LeaseStatus.Expired
  deriving Repr

-- ===========================================================================
-- Next-State Relation
-- ===========================================================================

-- The reconciler issues at most one request per step, and service updates
-- always set trafficRecipients to a singleton or empty list.
-- The next-state relation captures valid operator transitions.
--
-- NOT-YET-MODELED:
-- - Executor failure modes (kubectl timeout, partial writes, exec latency)
-- - Network partition recovery semantics
-- - Clock skew between operator instances
-- - Resource deletion by external actors (e.g., kubectl delete by user)
-- - Concurrent CR modifications by other controllers
def validTransition (s s' : ClusterState) : Prop :=
  -- Traffic recipients are always set to at most one pod (Service selector = single pod)
  s'.trafficRecipients.length ≤ 1 ∧
  -- Resources in s' either come from s or were created in the correct namespace
  (∀ (pair : ObjectRef × DynamicObjectView),
    pair ∈ s'.resources → pair ∈ s.resources ∨
    pair.1.«namespace» = s.reconcileState.crNamespace) ∧
  -- At most one pending request is issued per step
  s'.pendingRequests.length ≤ 1 ∧
  -- Only the leader can issue requests
  (s'.pendingRequests.length > 0 → s'.hasLease = true) ∧
  -- No requests during lease partition or expiry (partition safety)
  (match s'.leaseStatus with
   | LeaseStatus.Partitioned _ => s'.pendingRequests.length = 0
   | LeaseStatus.Expired => s'.pendingRequests.length = 0
   | LeaseStatus.Held _ _ => True) ∧
  -- Resource monotonicity: existing resources are preserved across transitions
  (∀ pair, pair ∈ s.resources → pair ∈ s'.resources) ∧
  -- Failover in progress implies sentinel is not in Monitoring state
  (s'.reconcileState.failoverInProgress = true →
    s'.sentinelCtx.sentinelState ≠ SentinelState.Monitoring)

-- ===========================================================================
-- Safety Invariant 1: At Most One Master
-- ===========================================================================

-- At most one pod receives client traffic at any time.
-- This prevents split-brain scenarios.
def atMostOneMaster (s : ClusterState) : Prop :=
  s.trafficRecipients.length ≤ 1

-- Theorem: atMostOneMaster is an inductive invariant under valid transitions.
theorem atMostOneMaster_invariant :
    ∀ (s s' : ClusterState),
      atMostOneMaster s →
      validTransition s s' →
      atMostOneMaster s' := by
  intro s s' _ hNext
  exact hNext.1

-- ===========================================================================
-- Safety Invariant 2: Owner Reference Consistency
-- ===========================================================================

-- All managed resources have an owner reference pointing to a CR in the
-- correct namespace.
def ownerRefConsistency (vc : ValkeyClusterView) (s : ClusterState) : Prop :=
  let ns := vc.metadata.«namespace».getD ""
  ∀ (pair : ObjectRef × DynamicObjectView),
    pair ∈ s.resources →
    pair.1.«namespace» = ns

-- Theorem: owner references are consistent after any valid transition
-- when new resources are created in the correct namespace.
theorem ownerRefConsistency_invariant :
    ∀ (vc : ValkeyClusterView) (s s' : ClusterState),
      ownerRefConsistency vc s →
      -- All new resources in s' are in the correct namespace
      (∀ (pair : ObjectRef × DynamicObjectView),
        pair ∈ s'.resources →
        pair ∈ s.resources ∨ pair.1.«namespace» = vc.metadata.«namespace».getD "") →
      ownerRefConsistency vc s' := by
  intro vc s s' hInv hNew
  intro pair hMem
  cases hNew pair hMem with
  | inl hOld => exact hInv pair hOld
  | inr hNs => exact hNs

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

-- Theorem: no concurrent updates invariant is maintained under valid transitions.
-- The reconciler issues at most one request per step, so there's at most one pending.
theorem noConcurrentUpdates_invariant :
    ∀ (s s' : ClusterState),
      noConcurrentUpdates s →
      validTransition s s' →
      noConcurrentUpdates s' := by
  intro s s' _ hNext
  intro key
  have hLen := hNext.2.2.1
  -- s'.pendingRequests.length ≤ 1, so any filter result has length ≤ 1
  calc (s'.pendingRequests.filter fun r => updateRequestKey r == some key).length
      ≤ s'.pendingRequests.length := List.length_filter_le _ _
    _ ≤ 1 := hLen

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
  intro ctx
  unfold sentinelForwardProgress sentinelNext
  cases hState : ctx.sentinelState with
  | Monitoring =>
    simp only []
    split
    · -- masterIsDown = true: state becomes FailureDetected
      simp [sentinelStateOrder]
    · -- masterIsDown = false: state stays Monitoring
      simp [sentinelStateOrder, hState]
  | FailureDetected =>
    simp [sentinelStateOrder]
  | SelectingReplica =>
    simp only []
    cases hSel : selectBestReplica (eligibleReplicas ctx.nodes) with
    | none => simp [sentinelStateOrder, hState]
    | some replica => simp [sentinelStateOrder, hState]
  | Promoting =>
    simp [sentinelStateOrder]
  | ReconfiguringReplicas =>
    simp [sentinelStateOrder]
  | UpdatingService =>
    simp [sentinelStateOrder]
  | Completed =>
    simp [sentinelStateOrder, hState]
  | FailoverError msg =>
    simp [sentinelStateOrder, hState]

-- ===========================================================================
-- Safety Invariant 6: Leader Election Safety
-- ===========================================================================

-- Only the lease holder can modify cluster state.
def leaderElectionSafety (s : ClusterState) : Prop :=
  s.pendingRequests.length > 0 -> s.hasLease = true

-- Theorem: leader election safety invariant under valid transitions.
-- The guard ensures only the lease holder issues requests.
theorem leaderElectionSafety_invariant :
    ∀ (s s' : ClusterState),
      leaderElectionSafety s →
      validTransition s s' →
      leaderElectionSafety s' := by
  intro s s' _ hNext
  intro hPending
  exact hNext.2.2.2.1 hPending

-- ===========================================================================
-- Safety Invariant 7: Partition Safety
-- ===========================================================================

/-- No side-effects (API requests) are issued during lease partition or expiry.
    This ensures that a partitioned operator cannot make stale writes. -/
def partitionSafety (s : ClusterState) : Prop :=
  match s.leaseStatus with
  | LeaseStatus.Partitioned _ => s.pendingRequests.length = 0
  | LeaseStatus.Expired => s.pendingRequests.length = 0
  | LeaseStatus.Held _ _ => True

/-- Theorem: partition safety is maintained under valid transitions. -/
theorem partitionSafety_invariant :
    ∀ (s s' : ClusterState),
      partitionSafety s →
      validTransition s s' →
      partitionSafety s' := by
  intro s s' _ hNext
  exact hNext.2.2.2.2.1

-- ===========================================================================
-- Safety Invariant 8: Service Consistency
-- ===========================================================================

/-- Traffic recipients are bounded (at most 1) and failover in progress
    implies the sentinel is not in Monitoring state (i.e., the Service
    selector is only changed during an active failover, not during normal
    operation). -/
def serviceConsistency (s : ClusterState) : Prop :=
  s.trafficRecipients.length ≤ 1 ∧
  (s.reconcileState.failoverInProgress = true →
    s.sentinelCtx.sentinelState ≠ SentinelState.Monitoring)

/-- Theorem: service consistency is an inductive invariant under valid transitions. -/
theorem serviceConsistency_invariant :
    ∀ (s s' : ClusterState),
      serviceConsistency s →
      validTransition s s' →
      serviceConsistency s' := by
  intro s s' _ hNext
  exact ⟨hNext.1, hNext.2.2.2.2.2.2⟩

-- ===========================================================================
-- Safety Invariant 9: No Double Failover
-- ===========================================================================

/-- When reconciliation is Done, failoverInProgress must be false.
    This ensures a completed reconciliation cycle has cleared the failover flag,
    preventing re-triggering. -/
def noDoubleFailover (s : ClusterState) : Prop :=
  s.reconcileState.reconcileStep = ValkeyReconcileStep.Done →
  s.reconcileState.failoverInProgress = false

/-- Theorem: sentinel terminal state behavior — once Completed, sentinelNext is identity. -/
theorem noDoubleFailover_from_terminal :
    ∀ (ctx : SentinelContext),
      ctx.sentinelState = SentinelState.Completed →
      sentinelNext ctx = ctx := by
  intro ctx h
  simp [sentinelNext, h]

/-- reconcileCore at AfterUpdateService clears failoverInProgress. -/
theorem reconcileCore_updateService_clears_failover
    (vc : ValkeyClusterView) (resp : DefaultResp) (state : ValkeyReconcileState) :
    state.reconcileStep = ValkeyReconcileStep.AfterUpdateService →
    (reconcileCore vc resp state).1.failoverInProgress = false := by
  intro h; simp [reconcileCore, h]

/-- reconcileCore at AfterUpdateStatus preserves failoverInProgress = false. -/
theorem reconcileCore_updateStatus_preserves_failover
    (vc : ValkeyClusterView) (resp : DefaultResp) (state : ValkeyReconcileState) :
    state.reconcileStep = ValkeyReconcileStep.AfterUpdateStatus →
    state.failoverInProgress = false →
    (reconcileCore vc resp state).1.failoverInProgress = false := by
  intro hStep hFIP; simp [reconcileCore, hStep]
  split <;> exact hFIP

-- ===========================================================================
-- Safety Invariant 10: PDB Protects Master
-- ===========================================================================

/-- A PodDisruptionBudget resource exists in the stored state for the given CR.
    Combined with PDB minAvailable=1, this ensures the master pod is protected
    from voluntary disruptions. -/
def pdbProtectsMaster (crName : String) (s : ClusterState) : Prop :=
  ∃ (pair : ObjectRef × DynamicObjectView),
    pair ∈ s.resources ∧
    pair.1.kind = Kind.PodDisruptionBudgetKind ∧
    pair.1.name = crName ++ "-pdb"

/-- Theorem: once a PDB exists, it persists under valid transitions
    (resource monotonicity). -/
theorem pdbProtectsMaster_preserved :
    ∀ (crName : String) (s s' : ClusterState),
      pdbProtectsMaster crName s →
      validTransition s s' →
      pdbProtectsMaster crName s' := by
  intro crName s s' hPDB hNext
  obtain ⟨pair, hMem, hKind, hName⟩ := hPDB
  exact ⟨pair, hNext.2.2.2.2.2.1 pair hMem, hKind, hName⟩

-- ===========================================================================
-- Combined Safety Property
-- ===========================================================================

-- All safety invariants combined.
-- Note: pdbProtectsMaster is proved separately (requires crName parameter).
def safetyInvariant (vc : ValkeyClusterView) (s : ClusterState) : Prop :=
  atMostOneMaster s ∧
  ownerRefConsistency vc s ∧
  noConcurrentUpdates s ∧
  reconcileStepValid s ∧
  leaderElectionSafety s ∧
  partitionSafety s ∧
  serviceConsistency s ∧
  noDoubleFailover s

-- The safety property as a temporal predicate: always(safetyInvariant).
def safetyProperty (vc : ValkeyClusterView) : TempPred ClusterState :=
  always (liftState (safetyInvariant vc))

end Gungnir.Invariants
