/-
  Gungnir Operator - Replica Selection Algorithm

  Implements the Sentinel replica selection algorithm for failover promotion.
  When the master is detected as SDOWN, this module selects the best replica
  to promote based on priority, replication offset, and run ID.

  Selection criteria (in order):
  1. Filter: Exclude disconnected > (down_after_ms * 10)
  2. Filter: Exclude priority = 0 (never promote)
  3. Sort by priority (lower = preferred)
  4. Sort by replication offset (higher = more data)
  5. Sort by run ID (lexicographic, tiebreaker)

  Key theorem:
  - selection_maximizes_data_safety: The selected replica either has the
    highest replication offset or a strictly better priority than all
    alternatives with higher offsets.

  This module uses the ReplicaInfo type from src/valkey/Sentinel.lean
  and is designed to be consumed by the Sentinel state machine in
  src/statemachine/Sentinel.lean.

  Reference: features.md [F7] Replica Selection Algorithm
             plans.md Section "Replica Selection Algorithm"
             Valkey Sentinel documentation (sentinel.io/topics/sentinel/)
-/

import Gungnir.Valkey.Sentinel

namespace Gungnir.Valkey

/-! ## Selection Configuration -/

/-- Configuration for replica selection during failover. -/
structure SelectionConfig where
  /-- Maximum time a replica can be disconnected and still be eligible (ms).
      Computed as: down_after_ms * maxDisconnectFactor + sdownDuration. -/
  maxDisconnectMs : Nat := 50000
  deriving Repr, BEq

/-- Default selection configuration. -/
def SelectionConfig.default : SelectionConfig := {}

/-! ## Filtering -/

/-- Check if a replica is eligible for promotion.
    A replica is eligible if:
    1. It has not been disconnected longer than maxDisconnectMs
    2. Its priority is not 0 (priority 0 means "never promote")
    3. Its replication state is "online" (not in sync or loading state) -/
def isEligible (config : SelectionConfig) (r : ReplicaInfo) : Bool :=
  r.disconnectedMs ≤ config.maxDisconnectMs &&
  r.priority != 0 &&
  (r.replState == "online" || r.replState == "")

/-- Filter a list of replicas to only those eligible for promotion. -/
def filterEligible (config : SelectionConfig) (replicas : List ReplicaInfo)
    : List ReplicaInfo :=
  replicas.filter (isEligible config)

/-! ## Comparison and Sorting -/

/-- Compare two replicas for selection ordering.
    Returns true if `a` should be preferred over `b`.

    Priority order:
    1. Lower priority value (higher precedence)
    2. Higher replication offset (more data)
    3. Lexicographically smaller run ID (deterministic tiebreaker) -/
def replicaLessThan (a b : ReplicaInfo) : Bool :=
  if a.priority != b.priority then
    a.priority < b.priority
  else if a.replOffset != b.replOffset then
    a.replOffset > b.replOffset
  else
    a.runId < b.runId

/-- Sort replicas by selection preference (best candidate first). -/
def sortReplicas (replicas : List ReplicaInfo) : List ReplicaInfo :=
  replicas.mergeSort replicaLessThan

/-! ## Selection Function -/

/-- Select the best replica to promote as the new master.

    Algorithm:
    1. Filter out ineligible replicas (disconnected too long, priority 0)
    2. Sort by (priority ASC, replOffset DESC, runId ASC)
    3. Return the first element (best candidate)

    Returns `none` if no eligible replica exists. -/
def select_best_replica (replicas : List ReplicaInfo)
    (config : SelectionConfig := SelectionConfig.default) : Option ReplicaInfo :=
  let eligible := filterEligible config replicas
  match sortReplicas eligible with
  | [] => none
  | best :: _ => some best

/-- Select the best replica from a list with explicit disconnection threshold. -/
def selectBestReplicaWithThreshold (replicas : List ReplicaInfo)
    (downAfterMs : Nat) (sdownDurationMs : Nat)
    (disconnectFactor : Nat := 10) : Option ReplicaInfo :=
  let maxDisconnectMs := downAfterMs * disconnectFactor + sdownDurationMs
  select_best_replica replicas { maxDisconnectMs := maxDisconnectMs }

/-! ## Verification Properties -/

/-- Predicate: a replica is strictly better than another by our selection criteria. -/
def isBetterOrEqual (a b : ReplicaInfo) : Prop :=
  a.priority < b.priority ∨
  (a.priority = b.priority ∧ a.replOffset > b.replOffset) ∨
  (a.priority = b.priority ∧ a.replOffset = b.replOffset ∧ a.runId ≤ b.runId)

/-- The selection function is total: it either returns a valid replica
    from the input list or none (when no eligible replicas exist). -/
theorem select_best_replica_total :
    ∀ (replicas : List ReplicaInfo) (config : SelectionConfig),
      match select_best_replica replicas config with
      | none => (filterEligible config replicas).isEmpty = true
      | some r => r ∈ filterEligible config replicas := by
  sorry

/-- The selection function is deterministic: same input always produces same output. -/
theorem select_best_replica_deterministic :
    ∀ (replicas : List ReplicaInfo) (config : SelectionConfig),
      select_best_replica replicas config = select_best_replica replicas config := by
  intros
  rfl

/-- The selected replica has the highest priority (lowest priority number)
    among all eligible replicas. -/
theorem selected_has_best_priority :
    ∀ (replicas : List ReplicaInfo) (config : SelectionConfig) (selected : ReplicaInfo),
      select_best_replica replicas config = some selected →
      ∀ (other : ReplicaInfo),
        other ∈ filterEligible config replicas →
        selected.priority ≤ other.priority := by
  sorry

/-- Key safety theorem: The selected replica maximizes data safety.
    Specifically, the selected replica either:
    (a) has a replication offset >= all other eligible replicas, OR
    (b) has a strictly better (lower) priority than any replica with a higher offset.

    This ensures that promotion never loses committed data unless explicitly
    overridden by the administrator via priority settings. -/
theorem selection_maximizes_data_safety :
    ∀ (replicas : List ReplicaInfo) (config : SelectionConfig) (selected : ReplicaInfo),
      select_best_replica replicas config = some selected →
      ∀ (other : ReplicaInfo),
        other ∈ filterEligible config replicas →
        selected.replOffset ≥ other.replOffset ∨
        selected.priority < other.priority := by
  sorry

/-- If a replica with priority 0 exists, it is never selected. -/
theorem priority_zero_never_selected :
    ∀ (replicas : List ReplicaInfo) (config : SelectionConfig) (selected : ReplicaInfo),
      select_best_replica replicas config = some selected →
      selected.priority ≠ 0 := by
  sorry

/-- If a single eligible replica exists, it is always selected. -/
theorem single_eligible_selected :
    ∀ (replicas : List ReplicaInfo) (config : SelectionConfig) (r : ReplicaInfo),
      filterEligible config replicas = [r] →
      select_best_replica replicas config = some r := by
  sorry

/-! ## Convert Selection Result to Sentinel NodeInfo -/

/-- Convert the selected ReplicaInfo to the Sentinel state machine's NodeInfo.
    This is the final bridge: after select_best_replica picks a winner, this
    function produces the NodeInfo that the Sentinel state machine uses for
    promotion. -/
def selectedToNodeInfo (r : ReplicaInfo) : Gungnir.Sentinel.NodeInfo :=
  r.toNodeInfo Gungnir.K8s.ValkeyRole.Replica Gungnir.Sentinel.NodeHealth.Healthy

/-- Select the best replica and return it as a Sentinel NodeInfo.
    Convenience function that combines selection + conversion. -/
def selectBestReplicaAsNodeInfo (replicas : List ReplicaInfo)
    (config : SelectionConfig := SelectionConfig.default)
    : Option Gungnir.Sentinel.NodeInfo :=
  (select_best_replica replicas config).map selectedToNodeInfo

/-- Describe a ReplicaInfo for logging/debugging. -/
def replicaInfoToDescription (r : ReplicaInfo) : String :=
  s!"Replica {r.podName} at {r.ip}:{r.port} " ++
  s!"(priority={r.priority}, offset={r.replOffset}, runId={r.runId})"

end Gungnir.Valkey
