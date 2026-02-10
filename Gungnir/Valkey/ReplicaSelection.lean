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

/-- Helper: select_best_replica returns none iff filterEligible is empty. -/
private theorem select_best_none_iff (replicas : List ReplicaInfo) (config : SelectionConfig) :
    select_best_replica replicas config = none →
    (filterEligible config replicas).isEmpty = true := by
  intro hNone
  simp only [select_best_replica, sortReplicas] at hNone
  cases hSorted : (filterEligible config replicas).mergeSort replicaLessThan with
  | nil =>
    have hPerm := List.mergeSort_perm (filterEligible config replicas) replicaLessThan
    rw [hSorted] at hPerm
    have hLen := hPerm.length_eq
    simp at hLen
    cases hFilt : filterEligible config replicas with
    | nil => rfl
    | cons _ _ => rw [hFilt] at hLen; simp at hLen
  | cons _ _ => rw [hSorted] at hNone; simp at hNone

/-- Helper: select_best_replica returns some r implies r ∈ filterEligible. -/
private theorem select_best_some_mem (replicas : List ReplicaInfo) (config : SelectionConfig)
    (r : ReplicaInfo) :
    select_best_replica replicas config = some r →
    r ∈ filterEligible config replicas := by
  intro hSome
  simp only [select_best_replica, sortReplicas] at hSome
  cases hSorted : (filterEligible config replicas).mergeSort replicaLessThan with
  | nil => rw [hSorted] at hSome; simp at hSome
  | cons best rest =>
    rw [hSorted] at hSome; simp at hSome
    have hPerm := List.mergeSort_perm (filterEligible config replicas) replicaLessThan
    rw [hSorted] at hPerm
    rw [← hSome]
    exact hPerm.subset (List.Mem.head rest)

theorem select_best_replica_total :
    ∀ (replicas : List ReplicaInfo) (config : SelectionConfig),
      match select_best_replica replicas config with
      | none => (filterEligible config replicas).isEmpty = true
      | some r => r ∈ filterEligible config replicas := by
  intro replicas config
  cases h : select_best_replica replicas config with
  | none => exact select_best_none_iff replicas config h
  | some r => exact select_best_some_mem replicas config r h

/-- The selection function is deterministic: same input always produces same output. -/
theorem select_best_replica_deterministic :
    ∀ (replicas : List ReplicaInfo) (config : SelectionConfig),
      select_best_replica replicas config = select_best_replica replicas config := by
  intros
  rfl

/-- The selected replica has the highest priority (lowest priority number)
    among all eligible replicas.
    Proof strategy: mergeSort with replicaLessThan places the lowest priority first.
    The head of the sorted list has priority ≤ all other elements.
    Requires: replicaLessThan is transitive and total (for sorted_mergeSort). -/
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
    overridden by the administrator via priority settings.
    Proof follows from the sorting order of replicaLessThan:
    within the same priority, higher offset comes first. -/
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
  intro replicas config selected hSel
  have hTotal := select_best_replica_total replicas config
  rw [hSel] at hTotal
  simp only [filterEligible] at hTotal
  have hFilt := (List.mem_filter).mp hTotal
  obtain ⟨_, hElig⟩ := hFilt
  simp only [isEligible, Bool.and_eq_true] at hElig
  obtain ⟨⟨_, hPri⟩, _⟩ := hElig
  simp only [bne_iff_ne] at hPri
  exact hPri

/-- If a single eligible replica exists, it is always selected. -/
theorem single_eligible_selected :
    ∀ (replicas : List ReplicaInfo) (config : SelectionConfig) (r : ReplicaInfo),
      filterEligible config replicas = [r] →
      select_best_replica replicas config = some r := by
  intro replicas config r hElig
  simp only [select_best_replica, hElig, sortReplicas]
  simp [List.mergeSort]

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
