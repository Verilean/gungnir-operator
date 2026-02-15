# Gungnir Operator - TODO

**Updated**: 2026-02-15
**Sorry count**: 5 (down from 19)

## Phase 5: Hardening & Operations

### Automated Failover (F8 + F9) — COMPLETE
- [x] Reconciler state machine: failover states wired in `reconcileCore`
- [x] ValkeyReconcileState: failover tracking fields (nodeHealthMap, failedMaster, selectedReplica, failoverInProgress)
- [x] Main.lean: `kubectlExecValkeyCli` — execute valkey-cli commands via kubectl exec
- [x] Main.lean: `detectMasterFailure` — PING pods, track consecutive failures, detect SDOWN
- [x] Main.lean: `performFailover` — select replica, REPLICAOF NO ONE, reconfigure, update Service
- [x] Main.lean: persistent health state across reconcile iterations (IO.Ref)
- [x] Main.lean: failover theorems (isMasterPod_correct, failover_bounded, sdown_threshold_correct, etc.)

### CI/CD Pipeline — COMPLETE
- [x] `.github/workflows/build.yaml` — Lean 4 build + Docker image + sorry count check
- [x] `.github/workflows/e2e.yaml` — Kind cluster + deploy + E2E tests

### E2E Tests — COMPLETE
- [x] `test/e2e/kind-config.yaml` — Kind cluster config
- [x] `test/e2e/sample-cr.yaml` — ValkeyCluster CR for testing
- [x] `test/e2e/run-all.sh` — Test runner
- [x] `test/e2e/test-basic-deploy.sh` — Verify 6 sub-resources + replication
- [x] `test/e2e/test-scale.sh` — Scale 3→5→3
- [x] `test/e2e/test-failover.sh` — Kill master, verify promotion

### Discharge Sorry Placeholders (5 remaining — target met: ≤ 5)

#### Liveness.lean (4 sorry)
- [x] `phase1_eventually_holds` — follows from phase0 (reconcileStepValid trivially true)
- [x] `phase6_eventually_holds` — initial state has empty resources/pendingRequests
- [x] `livenessTheorem` — composition of esr + failedMasterReplaced + reconcileTerminates
- [ ] `reconcileTerminates_holds` — needs weak fairness in clusterSpec
- [ ] `failedNodeDetected_holds` — needs health monitoring fairness
- [ ] `failedMasterReplaced_holds` — sentinel forward progress + weak fairness → leads-to
- [ ] `esr_holds` — Anvil ESR: phased proof chain (hardest theorem)

#### ReplicaSelection.lean (0 sorry) — FULLY PROVED
- [x] `replicaLessThan_total` — Nat trichotomy + String.lt_asymm/String.le_trans
- [x] `replicaLessThan_trans` — lexicographic transitivity via String.le_trans
- [x] `replicaLessThan_implies_priority_le` — if-then-else case split + omega
- [x] `replicaLessThan_same_priority_implies_offset` — equal priority branch analysis
- [x] `selected_has_best_priority` — sorted_mergeSort + pairwise head property
- [x] `selection_maximizes_data_safety` — priority disjunction from sorted head

#### RESP3.lean (1 sorry — theorem RESTATED with precondition)
- [x] `parse_unparse_roundtrip` — **Fixed**: Added `validRESPValue` precondition excluding embedded CRLF.
  Theorem now correctly stated but proof blocked by `partial def` (needs fuel-based total version).
  Counterexample `SimpleString "\r\n"` no longer applies.

## Completed (Phase 5 prep)

### Proofs discharged (9 sorry → 0)
- [x] `atMostOneMaster_invariant` — via validTransition
- [x] `ownerRefConsistency_invariant` — via namespace preservation
- [x] `noConcurrentUpdates_invariant` — via pendingRequests.length ≤ 1
- [x] `sentinelForwardProgress_invariant` — case split + sentinelStateOrder
- [x] `leaderElectionSafety_invariant` — via validTransition guard
- [x] `phase0_eventually_holds` — reconcileStepValid always true
- [x] `select_best_replica_total` — case split on sortReplicas result + mergeSort perm
- [x] `priority_zero_never_selected` — filterEligible excludes priority 0
- [x] `single_eligible_selected` — mergeSort singleton identity

### Infrastructure
- [x] validTransition next-state relation defined in Invariants.lean
- [x] nodeFailed predicate fixed (uses Degraded, not SDOWN)
- [x] Helper lemmas: select_best_none_iff, select_best_some_mem
- [x] Reconciler failover states wired with actual logic
- [x] ValkeyReconcileState extended with failover fields

## Future (Post Phase 5)

- [ ] F10: Backup/Restore — ValkeyBackup CRD, S3 integration, Job creation
- [ ] F11: TLS — cert-manager integration, cert mounting
- [ ] F11: QoS — resource limits enforcement
- [ ] Verification library integration (Lentil/LeanLTL/LeanMachines)
- [ ] Bridge Main.lean theorems to abstract state machine model
