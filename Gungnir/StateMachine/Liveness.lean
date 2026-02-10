/-
  Liveness.lean - Liveness properties for the Valkey operator

  This module defines the liveness properties that the operator must satisfy.
  These are temporal logic properties that ensure the system makes progress
  and eventually reaches desired states.

  Key liveness properties:
  1. failed_master_replaced: A failed master is eventually replaced
  2. eventually_stable_reconciliation (ESR): The Anvil-style property that
     if the desired state is always present, the current state eventually
     matches it permanently
  3. reconcile_terminates: Every reconciliation eventually reaches Done or Error
  4. sdown_detected: A failed node is eventually detected as SDOWN

  Uses K8s types from Gungnir.K8s for ValkeyClusterView, ValkeyReconcileState, etc.

  Reference: anvil/src/controllers/zookeeper_controller/trusted/liveness_theorem.rs
             anvil/src/controllers/zookeeper_controller/proof/liveness/
-/

import Gungnir.StateMachine.TemporalLogic
import Gungnir.StateMachine.Reconciler
import Gungnir.StateMachine.Sentinel
import Gungnir.StateMachine.Invariants

namespace Gungnir.Liveness

open Gungnir.TemporalLogic
open Gungnir.K8s
open Gungnir.Reconciler
open Gungnir.Sentinel
open Gungnir.Invariants

-- ===========================================================================
-- Cluster Specification
-- ===========================================================================

-- The cluster specification combines:
-- - Initial state predicate
-- - Next-state relation (all possible transitions)
-- - Fairness assumptions (weak fairness for reconciler and sentinel actions)
--
-- In TLA+ terms: Spec = Init /\ [][Next]_vars /\ WF(reconcile) /\ WF(sentinel)
def clusterSpec (vc : ValkeyClusterView) : TempPred ClusterState :=
  { pred := fun ex =>
    -- Initial state is valid
    (ex.head.reconcileState = reconcileInitState) ∧
    -- Sentinel starts in monitoring
    (ex.head.sentinelCtx.sentinelState = SentinelState.Monitoring) ∧
    -- The execution represents valid transitions (placeholder)
    True
  }

-- ===========================================================================
-- State Predicates for Liveness
-- ===========================================================================

-- The desired state is specified by the CR.
def desiredStateIs (vc : ValkeyClusterView) : StatePred ClusterState :=
  fun _s => True  -- placeholder: CR is present in the cluster

-- The current state matches the desired state (all sub-resources match).
def currentStateMatches (vc : ValkeyClusterView) : StatePred ClusterState :=
  fun s =>
    -- All expected resources exist
    s.resources.length > 0 ∧
    -- Reconciler has completed
    Gungnir.K8s.reconcileDone s.reconcileState

-- Master is failed (SDOWN detected).
def masterFailed : StatePred ClusterState :=
  fun s => masterIsDown s.sentinelCtx.nodes

-- A new master has been elected (failover completed).
def newMasterElected : StatePred ClusterState :=
  fun s => s.sentinelCtx.sentinelState = SentinelState.Completed

-- A specific node is failed (not responding to PINGs but not yet SDOWN).
-- Uses Degraded (consecutive failures) to distinguish from sdownDetected (SDOWN).
def nodeFailed (podName : String) : StatePred ClusterState :=
  fun s => s.sentinelCtx.nodes.any fun n =>
    n.podName = podName && match n.health with
      | NodeHealth.Degraded _ => true
      | NodeHealth.SDOWN => true
      | _ => false

-- A specific node has been detected as SDOWN.
def sdownDetected (podName : String) : StatePred ClusterState :=
  fun s => s.sentinelCtx.nodes.any fun n =>
    n.podName = podName && n.health == NodeHealth.SDOWN

-- The reconciler is in a terminal state.
def reconcileIsTerminal : StatePred ClusterState :=
  fun s =>
    Gungnir.K8s.reconcileDone s.reconcileState ∨
    Gungnir.K8s.reconcileError s.reconcileState

-- ===========================================================================
-- Liveness Property 1: Failed Master Eventually Replaced
-- ===========================================================================

-- If the master fails, a new master is eventually elected.
-- spec |= [](master_failed) ~> (new_master_elected)
def failedMasterReplaced (vc : ValkeyClusterView) : TempPred ClusterState :=
  (liftState masterFailed).leadsTo (liftState newMasterElected)

-- Theorem: Under the cluster spec, a failed master is eventually replaced.
theorem failedMasterReplaced_holds :
    ∀ (vc : ValkeyClusterView),
      clusterSpec vc ⊨ failedMasterReplaced vc := by
  sorry

-- ===========================================================================
-- Liveness Property 2: Eventually Stable Reconciliation (ESR)
-- ===========================================================================

-- The ESR property from Anvil: if the desired state is always present,
-- then the current state eventually matches it permanently.
--
-- spec |= [](desired vc) ~> [][](current matches desired vc)
--
-- This is the key liveness theorem from the Anvil paper (OSDI'24).
def eventuallyStableReconciliation (vc : ValkeyClusterView) : TempPred ClusterState :=
  (always (liftState (desiredStateIs vc))).leadsTo
    (always (liftState (currentStateMatches vc)))

-- Theorem: ESR holds under the cluster specification.
-- This is the main liveness theorem (analogous to Anvil's liveness_theorem.rs).
theorem esr_holds :
    ∀ (vc : ValkeyClusterView),
      clusterSpec vc ⊨ eventuallyStableReconciliation vc := by
  sorry

-- ===========================================================================
-- Liveness Property 3: Reconcile Terminates
-- ===========================================================================

-- Every reconciliation eventually reaches a terminal state (Done or Error).
def reconcileTerminates : TempPred ClusterState :=
  eventually (liftState reconcileIsTerminal)

-- Theorem: Reconciliation always terminates.
-- Under the cluster spec with valid transitions, the reconciler eventually
-- reaches a terminal state. This requires an additional assumption that
-- the execution eventually takes enough steps (weak fairness of the reconciler action).
-- The proof relies on the fuel bound (30 steps max) in the executor.
theorem reconcileTerminates_holds :
    ∀ (vc : ValkeyClusterView),
      clusterSpec vc ⊨ reconcileTerminates := by
  sorry

-- ===========================================================================
-- Liveness Property 4: SDOWN Detection
-- ===========================================================================

-- If a node is failed (not responding), it is eventually detected as SDOWN.
def failedNodeDetected (podName : String) : TempPred ClusterState :=
  (always (liftState (nodeFailed podName))).leadsTo
    (liftState (sdownDetected podName))

-- Theorem: Failed nodes are eventually detected.
theorem failedNodeDetected_holds :
    ∀ (vc : ValkeyClusterView) (podName : String),
      clusterSpec vc ⊨ failedNodeDetected podName := by
  sorry

-- ===========================================================================
-- Liveness Property 5: Fairness-Based Progress
-- ===========================================================================

-- The reconciler action: precondition is that we're not terminal,
-- effect is that we take one step.
def reconcileAction : ActionPred ClusterState :=
  fun s s' =>
    ¬reconcileIsTerminal s ∧
    reconcileIsTerminal s'

-- Weak fairness for the reconciler.
def reconcilerFairness : TempPred ClusterState :=
  weakFairness reconcileAction

-- The sentinel action: precondition is that we detected a failure,
-- effect is that we complete failover.
def sentinelAction : ActionPred ClusterState :=
  fun s s' =>
    masterFailed s ∧
    newMasterElected s'

-- Weak fairness for the sentinel.
def sentinelFairness : TempPred ClusterState :=
  weakFairness sentinelAction

-- ===========================================================================
-- Combined Liveness Property
-- ===========================================================================

-- The full liveness property for the Valkey operator.
def livenessProperty (vc : ValkeyClusterView) : TempPred ClusterState :=
  (eventuallyStableReconciliation vc).and
    ((failedMasterReplaced vc).and reconcileTerminates)

-- Top-level theorem: the liveness property holds for all ValkeyCluster CRs.
-- This is the Lean 4 equivalent of Anvil's liveness_theorem.
theorem livenessTheorem :
    ∀ (vc : ValkeyClusterView),
      clusterSpec vc ⊨ livenessProperty vc := by
  sorry

-- ===========================================================================
-- Phased Proof Strategy (from Anvil)
-- ===========================================================================

-- The ESR proof follows Anvil's phased invariant strengthening approach.
-- Each phase establishes invariants that "eventually hold" using leads-to reasoning.

-- Phase 0: Base invariants
def phase0Invariant (s : ClusterState) : Prop :=
  reconcileStepValid s

-- Phase I: Reconciler makes progress when not blocked
def phase1Invariant (vc : ValkeyClusterView) (s : ClusterState) : Prop :=
  phase0Invariant s ∧
  (¬reconcileIsTerminal s -> True)

-- Phase II: Reconcile state consistency
def phase2Invariant (vc : ValkeyClusterView) (s : ClusterState) : Prop :=
  phase1Invariant vc s ∧ True

-- Phase III: Request implications
def phase3Invariant (vc : ValkeyClusterView) (s : ClusterState) : Prop :=
  phase2Invariant vc s ∧ True

-- Phase IV: Owner reference invariants
def phase4Invariant (vc : ValkeyClusterView) (s : ClusterState) : Prop :=
  phase3Invariant vc s ∧
  ownerRefConsistency vc s

-- Phase V: No spurious deletion
def phase5Invariant (vc : ValkeyClusterView) (s : ClusterState) : Prop :=
  phase4Invariant vc s ∧ True

-- Phase VI: Resource version tracking
def phase6Invariant (vc : ValkeyClusterView) (s : ClusterState) : Prop :=
  phase5Invariant vc s ∧
  noConcurrentUpdates s

-- Each phase eventually holds (leads-to from previous phase).

theorem phase0_eventually_holds :
    ∀ (vc : ValkeyClusterView),
      clusterSpec vc ⊨ eventually (liftState phase0Invariant) := by
  intro vc ex hSpec
  exact ⟨0, reconcileStepValid_invariant _⟩

theorem phase1_eventually_holds :
    ∀ (vc : ValkeyClusterView),
      clusterSpec vc ⊨ eventually (liftState (phase1Invariant vc)) := by
  sorry

theorem phase6_eventually_holds :
    ∀ (vc : ValkeyClusterView),
      clusterSpec vc ⊨ eventually (liftState (phase6Invariant vc)) := by
  sorry

end Gungnir.Liveness
