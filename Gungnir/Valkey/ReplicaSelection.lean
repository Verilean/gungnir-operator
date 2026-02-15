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
    Returns true if `a` should be preferred over (or equal to) `b`.

    Priority order:
    1. Lower priority value (higher precedence)
    2. Higher replication offset (more data)
    3. Lexicographically smaller or equal run ID (deterministic tiebreaker)

    Uses `≤` (via `!(b.runId < a.runId)`) for the run ID comparison to make
    the comparator total, which is required by `List.sorted_mergeSort`. -/
def replicaLessThan (a b : ReplicaInfo) : Bool :=
  if a.priority != b.priority then
    a.priority < b.priority
  else if a.replOffset != b.replOffset then
    a.replOffset > b.replOffset
  else
    !(b.runId < a.runId)

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

/-- replicaLessThan is total: for any two replicas, at least one direction holds.
    This is required by List.sorted_mergeSort to prove the sorted property.

    Proof sketch: Case split on priority comparison (Nat trichotomy),
    then offset comparison, then runId comparison. The last comparison uses
    `!(b.runId < a.runId)` which gives totality via String ordering linearity. -/
private theorem replicaLessThan_total (a b : ReplicaInfo) :
    replicaLessThan a b = true ∨ replicaLessThan b a = true := by
  simp only [replicaLessThan]
  by_cases hp : a.priority = b.priority
  · -- priorities equal
    have hpf : (a.priority != b.priority) = false := by simpa [bne_iff_ne] using hp
    have hpf' : (b.priority != a.priority) = false := by simpa [bne_iff_ne] using hp.symm
    simp only [hpf, hpf', Bool.false_eq_true, ↓reduceIte]
    by_cases ho : a.replOffset = b.replOffset
    · -- offsets also equal: runId tiebreaker
      have hof : (a.replOffset != b.replOffset) = false := by simpa [bne_iff_ne] using ho
      have hof' : (b.replOffset != a.replOffset) = false := by simpa [bne_iff_ne] using ho.symm
      simp only [hof, hof', Bool.false_eq_true, ↓reduceIte]
      -- Goal: !(b.runId < a.runId) = true ∨ !(a.runId < b.runId) = true
      by_cases hr : b.runId < a.runId
      · right; simp only [Bool.not_eq_true', decide_eq_false_iff_not]; exact String.lt_asymm hr
      · left; simp only [Bool.not_eq_true', decide_eq_false_iff_not]; exact hr
    · -- offsets differ
      by_cases hgt : a.replOffset > b.replOffset
      · left
        have hot : (a.replOffset != b.replOffset) = true := by simpa [bne_iff_ne] using ho
        simp only [hot, ↓reduceIte, decide_eq_true_eq]; omega
      · right
        have hot' : (b.replOffset != a.replOffset) = true := by
          simpa [bne_iff_ne] using (Ne.symm ho)
        simp only [hot', ↓reduceIte, decide_eq_true_eq]; omega
  · -- priorities differ
    by_cases hlt : a.priority < b.priority
    · left
      have hpt : (a.priority != b.priority) = true := by simpa [bne_iff_ne] using hp
      simp only [hpt, ↓reduceIte, decide_eq_true_eq]; exact hlt
    · right
      have hpt' : (b.priority != a.priority) = true := by
        simpa [bne_iff_ne] using (Ne.symm hp)
      simp only [hpt', ↓reduceIte, decide_eq_true_eq]; omega

/-- If replicaLessThan a b = true, then a.priority ≤ b.priority.
    This follows from the definition: replicaLessThan first compares priority,
    and only considers offset/runId when priorities are equal.

    Proof sketch: Unfold replicaLessThan, case split on the `if` branches.
    In the priority-differs branch, a.priority < b.priority implies ≤.
    In the priority-equal branches, equality implies ≤. -/
private theorem replicaLessThan_implies_priority_le (a b : ReplicaInfo) :
    replicaLessThan a b = true → a.priority ≤ b.priority := by
  intro h
  unfold replicaLessThan at h
  by_cases hp : a.priority = b.priority
  · omega
  · have hne : (a.priority != b.priority) = true := by simp [bne_iff_ne, hp]
    simp only [hne, ↓reduceIte, decide_eq_true_eq] at h
    omega

/-- If replicaLessThan a b = true and a.priority = b.priority,
    then a.replOffset ≥ b.replOffset.
    Within the same priority tier, higher offset is preferred.

    Proof sketch: When priorities are equal, the first `if` is false.
    The second `if` compares offsets: if different, a.replOffset > b.replOffset.
    If equal, replOffset equality gives ≥. -/
private theorem replicaLessThan_same_priority_implies_offset (a b : ReplicaInfo) :
    replicaLessThan a b = true → a.priority = b.priority →
    a.replOffset ≥ b.replOffset := by
  intro h hpri
  unfold replicaLessThan at h
  have hne : ¬((a.priority != b.priority) = true) := by simp [bne_iff_ne, hpri]
  simp only [show (a.priority != b.priority) = false from by simpa [bne_iff_ne] using hpri,
             Bool.false_eq_true, ↓reduceIte] at h
  by_cases ho : a.replOffset = b.replOffset
  · omega
  · have hone : (a.replOffset != b.replOffset) = true := by simp [bne_iff_ne, ho]
    simp only [hone, ↓reduceIte, decide_eq_true_eq] at h
    omega

/-- replicaLessThan is transitive, required by List.sorted_mergeSort. -/
private theorem replicaLessThan_trans (a b c : ReplicaInfo) :
    replicaLessThan a b = true → replicaLessThan b c = true →
    replicaLessThan a c = true := by
  intro hab hbc
  have hab_pri := replicaLessThan_implies_priority_le a b hab
  have hbc_pri := replicaLessThan_implies_priority_le b c hbc
  unfold replicaLessThan
  by_cases hac_pri : a.priority = c.priority
  · -- a.priority = c.priority, so a.priority = b.priority = c.priority
    have hpab : a.priority = b.priority := by omega
    have hpbc : b.priority = c.priority := by omega
    have hpf : (a.priority != c.priority) = false := by simpa [bne_iff_ne] using hac_pri
    simp only [hpf, Bool.false_eq_true, ↓reduceIte]
    have hab_off := replicaLessThan_same_priority_implies_offset a b hab hpab
    have hbc_off := replicaLessThan_same_priority_implies_offset b c hbc hpbc
    by_cases hac_off : a.replOffset = c.replOffset
    · have hoff_eq_ab : a.replOffset = b.replOffset := by omega
      have hoff_eq_bc : b.replOffset = c.replOffset := by omega
      have hof : (a.replOffset != c.replOffset) = false := by simpa [bne_iff_ne] using hac_off
      simp only [hof, Bool.false_eq_true, ↓reduceIte]
      -- runId tiebreaker: a.runId ≤ b.runId ≤ c.runId (via !)
      -- Need: !(c.runId < a.runId) = true
      -- From hab: priorities and offsets equal, so hab reduces to !(b.runId < a.runId)
      unfold replicaLessThan at hab hbc
      simp only [show (a.priority != b.priority) = false from by simpa [bne_iff_ne] using hpab,
                 show (a.replOffset != b.replOffset) = false from by simpa [bne_iff_ne] using hoff_eq_ab,
                 show (b.priority != c.priority) = false from by simpa [bne_iff_ne] using hpbc,
                 show (b.replOffset != c.replOffset) = false from by simpa [bne_iff_ne] using hoff_eq_bc,
                 Bool.false_eq_true, ↓reduceIte, Bool.not_eq_true', decide_eq_false_iff_not] at hab hbc
      -- hab : ¬(b.runId < a.runId), hbc : ¬(c.runId < b.runId)
      -- String.le x y = ¬(y < x), so hab means a.runId ≤ b.runId, hbc means b.runId ≤ c.runId
      -- By String.le_trans: a.runId ≤ c.runId, i.e., ¬(c.runId < a.runId)
      simp only [Bool.not_eq_true', decide_eq_false_iff_not]
      exact String.le_trans hab hbc
    · have hot : (a.replOffset != c.replOffset) = true := by simpa [bne_iff_ne] using hac_off
      simp only [hot, ↓reduceIte, decide_eq_true_eq]; omega
  · have hpt : (a.priority != c.priority) = true := by simpa [bne_iff_ne] using hac_pri
    simp only [hpt, ↓reduceIte, decide_eq_true_eq]; omega

/-- Totality in the form required by List.sorted_mergeSort. -/
private theorem replicaLessThan_total_bool (a b : ReplicaInfo) :
    (replicaLessThan a b || replicaLessThan b a) = true := by
  simp only [Bool.or_eq_true]
  exact replicaLessThan_total a b

/-- The selected replica has the highest priority (lowest priority number)
    among all eligible replicas. -/
theorem selected_has_best_priority :
    ∀ (replicas : List ReplicaInfo) (config : SelectionConfig) (selected : ReplicaInfo),
      select_best_replica replicas config = some selected →
      ∀ (other : ReplicaInfo),
        other ∈ filterEligible config replicas →
        selected.priority ≤ other.priority := by
  intro replicas config selected hSel other hOther
  simp only [select_best_replica, sortReplicas] at hSel
  cases hSorted : (filterEligible config replicas).mergeSort replicaLessThan with
  | nil => rw [hSorted] at hSel; simp at hSel
  | cons best rest =>
    rw [hSorted] at hSel; simp at hSel
    -- hSel : best = selected
    -- other is in the sorted list (by permutation)
    have hPerm := List.mergeSort_perm (filterEligible config replicas) replicaLessThan
    rw [hSorted] at hPerm
    have hOtherSorted : other ∈ (best :: rest) := hPerm.symm.subset hOther
    cases List.mem_cons.mp hOtherSorted with
    | inl hEq =>
      -- other = best = selected, so selected.priority ≤ other.priority is trivial
      rw [← hSel, hEq]; exact Nat.le_refl _
    | inr hInRest =>
      have hPW := List.sorted_mergeSort replicaLessThan_trans replicaLessThan_total_bool
                    (filterEligible config replicas)
      rw [hSorted] at hPW
      rw [← hSel]
      exact replicaLessThan_implies_priority_le best other
        (List.rel_of_pairwise_cons hPW hInRest)

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
  intro replicas config selected hSel other hOther
  simp only [select_best_replica, sortReplicas] at hSel
  cases hSorted : (filterEligible config replicas).mergeSort replicaLessThan with
  | nil => rw [hSorted] at hSel; simp at hSel
  | cons best rest =>
    rw [hSorted] at hSel; simp at hSel
    -- hSel : best = selected
    have hPerm := List.mergeSort_perm (filterEligible config replicas) replicaLessThan
    rw [hSorted] at hPerm
    have hOtherSorted : other ∈ (best :: rest) := hPerm.symm.subset hOther
    cases List.mem_cons.mp hOtherSorted with
    | inl hEq =>
      -- other = best = selected
      left; rw [← hSel, hEq]; exact Nat.le_refl _
    | inr hInRest =>
      have hPW := List.sorted_mergeSort replicaLessThan_trans replicaLessThan_total_bool
                    (filterEligible config replicas)
      rw [hSorted] at hPW
      have hLt := List.rel_of_pairwise_cons hPW hInRest
      -- hLt : replicaLessThan best other = true
      rw [← hSel]
      by_cases hpri : best.priority = other.priority
      · -- same priority: offset must be ≥
        left; exact replicaLessThan_same_priority_implies_offset best other hLt hpri
      · -- different priority: best has strictly lower priority
        right
        have hle := replicaLessThan_implies_priority_le best other hLt
        omega

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
