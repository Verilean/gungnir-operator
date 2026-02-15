# Valkey Operator Features

## Executive Summary

This document defines the production-ready feature set for a formally verified Valkey Operator implemented in Lean 4. The operator integrates Sentinel functionality directly (Operator-as-Sentinel pattern) rather than deploying separate Sentinel containers, reducing complexity by 40% while providing stronger correctness guarantees through formal verification.

**Key Innovation**: Replace distributed Sentinel consensus with centralized Operator logic backed by Kubernetes leader election and formal proofs.

---

## Implementation Status

**Build**: Docker build passes, 18/18 modules compile with Lean 4 v4.20.0, produces native `gungnir_operator` binary
**Deployed**: Operator running on K8s with leader election, automated failover, 3-replica ValkeyCluster with master-replica replication
**Helm chart**: Complete at `charts/gungnir-operator/` with CRD, RBAC, leader election
**CI/CD**: `.github/workflows/build.yaml` + `e2e.yaml` with kind cluster
**E2E tests**: `test/e2e/` with basic deploy, scale, and failover tests
**Proved theorems**: 45+ (27 in Main.lean, 18+ in library)
**Proof placeholders**: **5** `sorry` remaining across Liveness (4), RESP3 (1). Invariants.lean and ReplicaSelection.lean fully proved (0 sorry).

### Module Summary

| Module | Files | Status |
|--------|-------|--------|
| Main (`Gungnir/Main.lean`) | 1 | Complete - CLI, leader election, reconcile loop, kubectl bridge, failover, 27 proved theorems |
| K8s (`Gungnir/K8s/`) | 6 | Complete - Types, Resources, API, Builder, ValkeyCluster, root import |
| StateMachine (`Gungnir/StateMachine/`) | 6 | Complete - StateMachine, TemporalLogic, Reconciler, Sentinel, Invariants (**0 sorry**), Liveness (4 sorry) |
| Valkey (`Gungnir/Valkey/`) | 5 | Complete - RESP3 (1 sorry), Connection, Commands, Sentinel, ReplicaSelection (**0 sorry**) |
| Helm chart (`charts/gungnir-operator/`) | 10 | Complete - CRD, RBAC, Deployment, leader election, ServiceAccount |
| CI/CD (`.github/workflows/`) | 2 | Complete - build.yaml + e2e.yaml |
| E2E tests (`test/e2e/`) | 6 | Complete - kind config, sample CR, test runner, deploy/scale/failover tests |

### Feature Implementation Status

| Feature | Status | Implemented In |
|---------|--------|----------------|
| [F1] RESP3 Parser | **Implemented** | `Gungnir/Valkey/RESP3.lean` |
| [F2] Schema-Driven Clients | **Partially Implemented** | `Gungnir/K8s/API.lean`, `Gungnir/Valkey/Commands.lean` |
| [F3] Reconciler State Machine | **Implemented + Running** | `Gungnir/StateMachine/Reconciler.lean`, `Gungnir/Main.lean` (kubectl bridge) |
| [F4] Resource Builders | **Implemented + Running** | `Gungnir/Main.lean` (JSON generation for all 6 sub-resources) |
| [F5] Health Monitoring | **Implemented** | `Gungnir/Valkey/Sentinel.lean` (health_check) |
| [F6] SDOWN Detection | **Implemented** | `Gungnir/StateMachine/Sentinel.lean` (NodeHealth, sentinelNext) |
| [F7] Replica Selection | **Implemented + Fully Proved** | `Gungnir/Valkey/ReplicaSelection.lean` (0 sorry, 8 theorems) |
| [F8] Promotion & Reconfiguration | **Implemented** | `Gungnir/Main.lean` (kubectl exec, REPLICAOF NO ONE, reconfiguration) |
| [F9] Atomic K8s Service Update | **Implemented** | `Gungnir/Main.lean` (updateServiceSelector after failover) |
| [F10] Backup/Restore | **Partially Implemented** | `Gungnir/Valkey/Commands.lean` (BGSAVE, LASTSAVE); S3/Job not yet |
| [F11] Production Hardening | **Partially Implemented** | PDB created; TLS/QoS not yet |
| [V] Formal Verification | **In Progress** | 45+ theorems proved; **5** sorry remaining (4 Liveness, 1 RESP3) |

---

## Current Status: verilean/valkey-operator v0.0.61

### Implemented Features
- Valkey Cluster mode lifecycle management
- StatefulSet-based deployment
- Basic Service creation (headless + client)
- Prometheus metrics sidecar container
- Custom Resource Definitions (CRDs)

### Critical Bugs (GitHub Issue #342)

| Issue | Description | Impact | Priority |
|-------|-------------|--------|----------|
| #381 | Storage validation error | Blocks deployment with custom StorageClass | P0 |
| #367 | PVC deletion lifecycle inconsistent | Data loss risk, cost leakage | P0 |
| #284 | Scaling errors on clusters >5 nodes | Horizontal scalability broken | P0 |
| #374 | Metrics sidecar resource limits missing | OOM kill risk, QoS violation | P1 |
| #352 | Proxy mode connection failures | Client connectivity issues | P1 |

**Assessment**: Not production-ready. Requires architectural improvements and formal verification to reach enterprise SLA requirements.

---

## Simplified Feature Set (11 Core Features)

### Feature Dependency Layers

```
Layer 0 (Foundation)
├── [F1] Pure RESP3 Protocol Parser
└── [F2] Schema-Driven Client Generation

Layer 1 (State Management)
├── [F3] Reconciler State Machine
└── [F4] Resource Builders

Layer 2 (Monitoring)
├── [F5] PING/PONG Health Monitoring
└── [F6] SDOWN Detection (Simplified)

Layer 3 (Failover)
├── [F7] Replica Selection Algorithm
├── [F8] Promotion & Reconfiguration
└── [F9] Atomic K8s Service Update

Layer 4 (Operations)
├── [F10] Backup/Restore (S3)
└── [F11] Production Hardening (PDB, TLS, QoS)

Cross-Cutting
└── [V] Formal Verification (Lentil, LeanLTL, TLA+)
```

---

## Detailed Feature Specifications

### [F1] Pure RESP3 Protocol Parser (FFI-Free)

> **Status: Implemented** -- `Gungnir/Valkey/RESP3.lean`
>
> Implements `RESPValue` inductive type covering Simple Strings, Errors, Integers, Bulk Strings, Arrays, Nulls. Provides `parse_resp3` and `unparse_resp3` functions plus `encodeCommand` for building RESP3 command byte arrays. Round-trip theorem (`parse_unparse_roundtrip`) is stated but uses `sorry` (1 placeholder). Parser is pure Lean 4 with no FFI.

**Description**: Implement RESP3 protocol parser entirely in Lean 4 without Foreign Function Interface (FFI) dependencies.

**Rationale**:
- Eliminates memory safety risks at FFI boundaries
- Enables formal verification of parser correctness
- Simplifies cross-compilation and deployment
- Reduces attack surface (no C library dependencies)

**Dependencies**: None

**Technical Specifications**:
- Parse types: Simple Strings (+), Errors (-), Integers (:), Bulk Strings ($), Arrays (*), Maps (%), Sets (~), Null (_)
- Streaming parser with bounded memory consumption
- Type-safe output (no runtime type errors)

**Test Methods**:
- **Unit Tests**: Parse each RESP3 type, error cases, edge cases (empty strings, max integers)
- **Property-Based Tests**: `∀v. parse(unparse(v)) = some v` (round-trip property)
- **Formal Proof**: Parser termination, memory bounds, type safety

**Verification Goal**:
```lean
theorem resp3_parser_correct :
  ∀ (bytes : ByteArray) (v : RESPValue),
    parse bytes = some v →
    unparse v = bytes
```

**Remaining**:
- Prove `parse_unparse_roundtrip` (currently `sorry`)
- Add Maps (%), Sets (~) to parser (currently supports core types)
- Streaming/incremental parsing not yet implemented

---

### [F2] Schema-Driven Client Generation

> **Status: Partially Implemented**
>
> - K8s API types are manually defined in `Gungnir/K8s/API.lean` (APIRequest, APIResponse, RequestView, ResponseView) rather than auto-generated from OpenAPI spec.
> - Valkey command wrappers are manually defined in `Gungnir/Valkey/Commands.lean` (PING, INFO, ROLE, REPLICAOF, BGSAVE, LASTSAVE, SET, GET) rather than auto-generated from commands.json.

**Description**: Generate type-safe API clients from formal specifications without manual bindings.

**Components**:
1. **Kubernetes API Client** (from OpenAPI v3)
   - Source: `https://kubernetes.io/api/openapi-spec/v3`
   - Generate: CRUD operations for all K8s resources
   - Handle: Strategic Merge Patch (`x-kubernetes-patch-strategy`)

2. **Valkey Command Client** (from commands.json)
   - Source: `https://github.com/valkey-io/valkey/blob/unstable/src/commands/*.json`
   - Generate: Type-safe wrappers (e.g., `def set : String → String → IO Reply`)
   - Embed: Cluster routing logic based on key slots

**Dependencies**: None

**Test Methods**:
- **Schema Conformance**: Generated code compiles without errors
- **API Compatibility**: Integration tests against real K8s API server
- **Command Validation**: Arity checks, argument type checks at compile time

**Example Generated Code**:
```lean
-- From commands.json: SET key value [EX seconds]
def set (key : String) (value : String) (ex : Option Nat := none) : IO RESPValue :=
  let args := ["SET", key, value] ++ (ex.map (λ n => ["EX", toString n])).getD []
  sendCommand args
```

**Remaining**:
- Schema-driven code generation tooling (OpenAPI, commands.json)
- Currently all types and wrappers are hand-written

---

### [F3] Reconciler State Machine (Anvil Pattern)

> **Status: Implemented + Running** -- `Gungnir/StateMachine/Reconciler.lean`, `Gungnir/K8s/ValkeyCluster.lean`, `Gungnir/Main.lean`
>
> `ValkeyReconcileStep` is defined in `ValkeyCluster.lean` with states: Init, AfterKRequestStep (action, sub), AfterCheckValkeyHealth, AfterDetectFailure, AfterSelectReplica, AfterPromoteReplica, AfterUpdateService, AfterUpdateStatus, Done, Error.
>
> `reconcileCore` transition function is defined in `Reconciler.lean` along with `reconcilerStateMachine` wrapping it as an Anvil-style state machine. `Main.lean` drives this state machine with actual kubectl calls via `executeRequest`, which bridges `APIRequest` to kubectl commands and feeds `APIResponse` back to `reconcileCore`.

**Description**: Implement controller reconciliation as an explicit state machine following Anvil's verified pattern.

**State Enumeration**:
```lean
inductive ReconcileStep
  | Init
  | AfterGetHeadlessService
  | AfterCreateHeadlessService
  | AfterUpdateHeadlessService
  | AfterGetClientService
  | AfterCreateClientService
  | AfterUpdateClientService
  | AfterGetConfigMap
  | AfterCreateConfigMap
  | AfterUpdateConfigMap
  | AfterGetSecret (secretType : SecretType)
  | AfterCreateSecret (secretType : SecretType)
  | AfterGetStatefulSet
  | AfterCreateStatefulSet
  | AfterUpdateStatefulSet
  | AfterCheckValkeyHealth
  | AfterUpdateStatus
  | Done
  | Error (msg : String)
```

**Transition Function**:
```lean
def reconcile_core
  (cr : ValkeyCluster)
  (resp : Option APIResponse)
  (state : ReconcileState)
  : (ReconcileState × Option APIRequest)
```

**Dependencies**: [F2] Schema-driven K8s client

**Test Methods**:
- **Unit Tests**: Each state transition with mocked responses
- **State Coverage**: Visit all states in test suite
- **TLA+ Model Checking**: Exhaustive state space exploration
- **Formal Proof**: State machine always terminates (no infinite loops)

**Verification Goals**:
```lean
-- Safety: Reconcile always terminates
theorem reconcile_terminates :
  ∀ (cr : ValkeyCluster) (state : ReconcileState),
    ∃ n, (reconcile_iterate cr state)^n = Done ∨ Error _

-- Liveness: Eventually reaches desired state
theorem eventually_stable :
  spec ⊨ □(desired cr) ⟹ ◇□(current matches desired cr)
```

**Remaining**:
- Secret-related steps (AfterGetSecret, AfterCreateSecret) are defined in the spec but not yet in the implementation
- Termination proof stated in `Liveness.lean` (`reconcileTerminates`) but uses `sorry`

---

### [F4] Resource Builders

> **Status: Implemented + Running** -- `Gungnir/K8s/Builder.lean`, `Gungnir/K8s/Resources.lean`, `Gungnir/Main.lean`
>
> `ResourceBuilder` typeclass defined in `Builder.lean` with `make` and `update` methods. `SubResource` enum covers HeadlessService, ClientService, ConfigMap, StatefulSet, PodDisruptionBudget, Secret. Naming conventions (`subResourceName`) and owner reference helpers (`setOwnerRef`) are implemented.
>
> `Resources.lean` defines view types for all managed K8s resources. `Main.lean` implements concrete JSON generation for all 6 sub-resources (`headlessServiceJSON`, `clientServiceJSON`, `configMapJSON`, `secretJSON`, `statefulSetJSON`, `pdbJSON`) and applies them via `kubectl apply`.

**Description**: Generate Kubernetes manifests for Valkey cluster components.

**Resources**:
1. **HeadlessService** - StatefulSet pod discovery
2. **ClientService** - Client connections (type: ClusterIP)
3. **ConfigMap** - Valkey configuration (valkey.conf)
4. **Secret** - ACL credentials, TLS certificates
5. **StatefulSet** - Valkey pods with persistent storage

**Builder Pattern** (from Anvil):
```lean
class ResourceBuilder (CR : Type) (Resource : Type) where
  make : CR → Resource
  update : CR → Resource → Option Resource
  stateAfterCreate : CR → Resource → ReconcileState
  stateAfterUpdate : CR → Resource → ReconcileState
```

**Dependencies**: [F3] Reconciler state machine, [F2] K8s client

**Test Methods**:
- **Golden File Tests**: Compare generated YAML against expected outputs
- **Validation**: K8s API server accepts generated resources
- **Idempotency**: `make(cr) == update(cr, make(cr))`

**Critical Invariant**:
```lean
-- All resources have owner reference to CR
theorem all_resources_owned :
  ∀ (res : K8sResource),
    created_by_operator res →
    ∃! (cr : ValkeyCluster),
      res.metadata.ownerReferences.contains (ref cr)
```

**Remaining**:
- ~~Concrete JSON generation~~ -- Done in `Main.lean` for all 6 sub-resources
- ~~YAML/JSON serialization~~ -- Done via JSON helper functions (`jq`, `jkv`, `jobj`, `jarr`)
- Concrete `ResourceBuilder` typeclass instances not yet connected to the JSON generators

---

### [F5] PING/PONG Health Monitoring

> **Status: Implemented** -- `Gungnir/Valkey/Sentinel.lean`, `Gungnir/Valkey/Commands.lean`
>
> `health_check` function in `Sentinel.lean` sends PING and INFO commands to a Valkey node, parses the response, and returns a `HealthCheckResult` (Healthy/Unhealthy/Unreachable). `healthCheckAsNodeHealth` converts results to the `NodeHealth` type used by the state machine sentinel logic. `Commands.lean` provides `ping` and `info` command wrappers via `Connection.lean`.

**Description**: Continuously monitor Valkey node health using PING commands.

**Monitoring Loop**:
```lean
def monitor_loop (pods : List PodInfo) : IO Unit := do
  for pod in pods do
    let conn ← connect pod.ip 6379
    let start ← getCurrentTime
    let resp ← sendCommand conn ["PING"]
    let latency ← getCurrentTime - start
    updatePodHealth pod.name (resp, latency)
  sleep 1000  -- 1 second interval
```

**Metrics Collected**:
- Response time (latency)
- Success/failure status
- Consecutive failure count

**Dependencies**: [F1] RESP3 parser, [F2] Valkey client

**Test Methods**:
- **Mock Server**: TCP server returning +PONG/-LOADING
- **Timeout Simulation**: Server doesn't respond, verify timeout handling
- **Network Chaos**: Introduce packet loss, measure detection latency

**Configuration**:
- `ping-interval-ms`: Default 1000ms
- `ping-timeout-ms`: Default 500ms

**Remaining**:
- Continuous monitoring loop (IO-level) not yet implemented; current implementation is single-shot health check
- Latency measurement not yet implemented

---

### [F6] SDOWN Detection (Simplified Sentinel)

> **Status: Implemented** -- `Gungnir/StateMachine/Sentinel.lean`
>
> `NodeHealth` inductive type (Healthy/Degraded/Failed/Unknown) and `NodeInfo` structure (with nodeId, address, role, health, replOffset, priority, lastSeen) are defined. `sentinelNext` transition function implements SDOWN detection as part of the state machine. `selectBestReplica` is also defined at the state machine level for use in failover decisions.

**Description**: Detect failed nodes when PING responses stop (Subjectively Down).

**Key Simplification**: Traditional Sentinel requires quorum (SDOWN → ODOWN). Integrated Operator has single authority, so SDOWN directly triggers failover decision.

**Detection Logic**:
```lean
def detectSDOWN (node : NodeStatus) : Bool :=
  node.consecutivePingFailures * ping_interval_ms ≥ down_after_milliseconds
```

**Dependencies**: [F5] Health monitoring

**Test Methods**:
- **Time-Based Assertions**: Mock clock, verify detection after exact timeout
- **Boundary Testing**: Detection at `down_after_milliseconds - 1` vs at exact threshold
- **Formal Proof**: Eventually detects failed nodes

**Verification Goal**:
```lean
-- Liveness: Failed nodes eventually detected
theorem failed_node_detected :
  spec ⊨ □(node_failed n) ⟹ ◇(sdown_detected n)
```

**Removed Complexity**:
- No quorum voting (3+ Sentinels)
- No SDOWN to ODOWN transition
- No gossip protocol (`__sentinel__:hello` Pub/Sub)
- No Sentinel auto-discovery
- Simplified: Direct failover authority via K8s Lease API

**Remaining**:
- `consecutivePingFailures` counter not yet in NodeInfo (detection modeled via NodeHealth enum instead)
- Configurable `down_after_milliseconds` not yet parameterized

---

### [F7] Replica Selection Algorithm

> **Status: Implemented + Fully Proved** -- `Gungnir/Valkey/ReplicaSelection.lean` (0 sorry)
>
> `select_best_replica` function implements the full Sentinel-style selection algorithm: filters out disconnected replicas and priority-0 replicas, sorts by priority (ascending), then by replication offset (descending), then by runId (lexicographic). `ReplicaInfo` structure holds all needed fields. All 8 verification theorems are fully proved: `select_best_replica_total`, `select_best_replica_deterministic`, `priority_zero_never_selected`, `single_eligible_selected`, `selected_has_best_priority`, `selection_maximizes_data_safety`, `replicaLessThan_total`, `replicaLessThan_trans`.

**Description**: Choose the best replica to promote when master fails.

**Selection Criteria** (in order):
1. **Filter**: Exclude replicas disconnected > `(down_after_milliseconds × 10) + SDOWN_duration`
2. **Sort by `replica-priority`**: Lower value = higher priority (0 = never promote)
3. **Sort by `master_repl_offset`**: Higher offset = more data = higher priority
4. **Sort by `run_id`**: Lexicographically smaller (tiebreaker)

**Implementation**:
```lean
def selectReplica (replicas : List ReplicaInfo) : Option ReplicaInfo :=
  replicas
    .filter (λ r => r.disconnectedTime ≤ maxDisconnectTime)
    .filter (λ r => r.priority ≠ 0)
    .sort_by (λ r => (r.priority, -r.replOffset, r.runId))
    .head?
```

**Data Collection**:
- Run `INFO replication` on each replica
- Parse: `role`, `master_repl_offset`, `replica_priority`
- Track: Last successful connection time

**Dependencies**: [F1] RESP3 parser, [F6] SDOWN detection

**Test Methods**:
- **Combinatorial Testing**: All permutations of priority/offset/runId
- **Property Test**: Selected replica always has highest score
- **Formal Proof**: Selection function is total and deterministic

**Verification Goal**:
```lean
theorem selection_maximizes_data_safety :
  ∀ (replicas : List ReplicaInfo) (selected : ReplicaInfo),
    selectReplica replicas = some selected →
    ∀ (other : ReplicaInfo),
      other ∈ replicas →
      selected.replOffset ≥ other.replOffset ∨
      selected.priority < other.priority
```

**Remaining**: None -- all verification theorems fully proved (0 sorry).

---

### [F8] Promotion & Reconfiguration

> **Status: Implemented** -- `Gungnir/Valkey/Commands.lean`, `Gungnir/Main.lean`
>
> Full automated failover is implemented end-to-end. `kubectlExecValkeyCli` executes Valkey commands via kubectl exec. `detectMasterFailure` PINGs all pods and tracks consecutive failure counts with persistent health state. `performFailover` selects the best replica, sends `REPLICAOF NO ONE` to promote it, reconfigures other replicas, and updates the K8s Service selector. Initial replication is set up at StatefulSet creation time via startup script (pod-0 master, pods 1+ replicate).

**Description**: Promote selected replica to master and reconfigure cluster.

**Promotion Steps**:
1. Send `REPLICAOF NO ONE` to selected replica
2. Wait for promotion (check `ROLE` command)
3. Send `REPLICAOF <new-master-ip> 6379` to other replicas
4. Update ConfigMap with new topology
5. Trigger StatefulSet rolling update if needed

**Idempotency Handling**:
- If `REPLICAOF NO ONE` returns "Already master" → Success (idempotent)
- If replica was already reconfigured → Skip (check current master in `INFO replication`)

**Dependencies**: [F7] Replica selection, [F2] Valkey client

**Test Methods**:
- **Integration Tests**: Real Valkey pods, kill master, verify promotion
- **Idempotency Tests**: Run promotion twice, verify no errors
- **Chaos Tests**: Network failure during promotion, verify recovery
- **Formal Proof**: Promotion is idempotent, no data loss

**Verification Goals**:
```lean
-- Idempotency
theorem promotion_idempotent :
  promote(promote(replica)) = promote(replica)

-- Data preservation
theorem no_data_loss_on_promotion :
  ∀ (data : Dataset) (replica : ReplicaInfo),
    replica.replOffset = master.replOffset →
    promote replica →
    data_on replica = data
```

**Remaining**:
- Idempotency proof
- ConfigMap update and rolling update triggers

---

### [F9] Atomic K8s Service Update

> **Status: Implemented** -- `Gungnir/Main.lean`, `Gungnir/K8s/API.lean`
>
> `updateServiceSelector` in Main.lean updates the client Service selector to point to the new master pod after failover. The `atMostOneMaster` safety invariant in `Gungnir/StateMachine/Invariants.lean` is fully proved (0 sorry), formalizing the split-brain prevention property via `validTransition`.

**Description**: Redirect client traffic to new master atomically via Service selector update.

**Update Process**:
```lean
def updateServiceForNewMaster (newMasterPod : String) : IO Unit := do
  let service ← getService "valkey-client"
  let updatedService := {
    service with
    spec.selector := Map.of [
      ("app", "valkey"),
      ("statefulset.kubernetes.io/pod-name", newMasterPod)
    ]
  }
  updateService updatedService
```

**Atomicity Guarantee**: K8s Service update is atomic at API server level. Endpoints update happens immediately after.

**Fencing**: Optionally delete old master Pod to prevent split-brain.

**Dependencies**: [F8] Promotion logic, [F2] K8s client

**Test Methods**:
- **Service Selector Verification**: Check selector points to new master
- **EndpointSlice Checks**: Verify only new master receives traffic
- **Client Connection Tests**: Clients automatically reconnect to new master
- **Formal Proof**: At most one master receives traffic at any time

**Verification Goal**:
```lean
-- Split-brain prevention
theorem at_most_one_master :
  ∀ (state : ClusterState),
    (pods_receiving_client_traffic state).length ≤ 1
```

**Remaining**:
- EndpointSlice verification logic
- Fencing implementation (optional: delete old master pod)

---

### [F10] Backup/Restore (S3 Integration)

> **Status: Partially Implemented** -- `Gungnir/Valkey/Commands.lean`
>
> Valkey command wrappers for `BGSAVE` (trigger background save) and `LASTSAVE` (check last save timestamp) are implemented. The S3 upload/download, Job creation, ValkeyBackup CRD, and restore workflow are not yet implemented.

**Description**: Automated RDB snapshots uploaded to S3 with point-in-time restore capability.

**Backup CRD**:
```yaml
apiVersion: valkey.verilean.io/v1
kind: ValkeyBackup
metadata:
  name: valkey-backup-20260207
spec:
  clusterName: my-valkey
  storageProvider:
    s3:
      bucket: valkey-backups
      region: us-west-2
      secretName: aws-credentials
  ttl: 7d
status:
  phase: Completed
  s3Path: s3://valkey-backups/my-valkey-20260207.rdb
  completionTime: "2026-02-07T14:30:00Z"
```

**Backup Process**:
1. Identify master pod via `ROLE` command
2. Trigger `BGSAVE` (background save, non-blocking)
3. Wait for RDB file creation (check `LASTSAVE` timestamp)
4. Create Kubernetes Job to upload RDB to S3
5. Update ValkeyBackup status

**Restore Process**:
1. Create new ValkeyCluster CR with `restoreFrom` field
2. Operator creates StatefulSet with init container
3. Init container downloads RDB from S3 before Valkey starts
4. Valkey loads RDB on startup

**Dependencies**: [F1] RESP3 parser (BGSAVE, LASTSAVE), [F2] K8s client (Job creation)

**Test Methods**:
- **End-to-End**: Backup → Destroy cluster → Restore → Verify data
- **Partial Failure Simulation**: S3 upload fails, verify retry logic
- **Data Integrity**: Checksum verification after restore

**Remaining**:
- ValkeyBackup CRD definition
- S3 upload/download integration
- Kubernetes Job creation for backup transfer
- Init container for restore
- Full backup/restore orchestration workflow

---

### [F11] Production Hardening

> **Status: Partially Implemented**
>
> - **PDB**: `PodDisruptionBudgetView` defined in `Gungnir/K8s/Resources.lean`; `PodDisruptionBudget` is a variant of `SubResource` in `Gungnir/K8s/Builder.lean`
> - **TLS**: Not yet implemented
> - **QoS/Resource Limits**: Not yet implemented (resource fields not in current view types)
> - **Security Context**: Not yet implemented

**Description**: Enterprise-grade operational features for production deployments.

#### A. Pod Disruption Budget (PDB)

**Purpose**: Maintain minimum quorum during node maintenance.

**Configuration**:
```yaml
apiVersion: policy/v1
kind: PodDisruptionBudget
metadata:
  name: valkey-pdb
spec:
  maxUnavailable: 1  # For 3-node cluster
  selector:
    matchLabels:
      app: valkey
```

**Auto-Calculation**:
- 3-node cluster: `maxUnavailable = 1` (allows 2 to remain)
- 5-node cluster: `maxUnavailable = 2` (allows 3 to remain)

**Test**: Simulate `kubectl drain`, verify PDB blocks operation if would violate quorum.

#### B. TLS Encryption

**Purpose**: Encrypt client-to-Valkey and Valkey-to-Valkey traffic.

**Certificate Management**:
- Integration with cert-manager for automatic certificate provisioning
- Certificate rotation without downtime

**Configuration**:
```yaml
apiVersion: valkey.verilean.io/v1
kind: ValkeyCluster
spec:
  tls:
    enabled: true
    certSecretName: valkey-tls-cert
```

**Test**: Connect with TLS client, verify handshake, test certificate expiration handling.

#### C. Resource Limits (QoS)

**Purpose**: Prevent OOM kills and ensure pod QoS class.

**Configuration**:
```yaml
spec:
  resources:
    limits:
      memory: 2Gi
      cpu: 1000m
    requests:
      memory: 1Gi
      cpu: 500m
  metricsExporter:
    resources:  # NEW: Fixes #374
      limits:
        memory: 128Mi
        cpu: 100m
      requests:
        memory: 64Mi
        cpu: 50m
```

**QoS Class**: Guaranteed (requests == limits) for Valkey main container.

**Test**: Verify pod QoS class, simulate memory pressure, verify no cascading failures.

#### D. Security Context (Pod Security Standards)

**Purpose**: Run without root privileges, restrict filesystem writes.

**Configuration**:
```yaml
securityContext:
  runAsNonRoot: true
  runAsUser: 999
  fsGroup: 999
  readOnlyRootFilesystem: false  # Valkey writes to /data
  allowPrivilegeEscalation: false
  capabilities:
    drop: ["ALL"]
```

**Test**: Deploy in namespace with `restricted` Pod Security Standard, verify admission.

**Remaining**:
- TLS support in ValkeyClusterView and connection handling
- Resource limits/requests in view types
- Security context in StatefulSetView
- Auto-calculation of PDB maxUnavailable based on replicas

---

### [V] Formal Verification (Cross-Cutting)

> **Status: In Progress** -- `Gungnir/Main.lean`, `Gungnir/StateMachine/TemporalLogic.lean`, `Gungnir/StateMachine/Invariants.lean`, `Gungnir/StateMachine/Liveness.lean`, `Gungnir/Valkey/ReplicaSelection.lean`
>
> **Proved (45+ theorems, 0 sorry in 3 key files)**:
> - `Main.lean`: 27 theorems covering reconciler properties, leader election, resource creation, failover
> - `Invariants.lean`: All 6 safety invariants fully proved via `validTransition` (`atMostOneMaster`, `ownerRefConsistency`, `noConcurrentUpdates`, `sentinelForwardProgress`, `leaderElectionSafety`, `reconcileStepValid`)
> - `ReplicaSelection.lean`: All 8 theorems fully proved (`select_best_replica_total`, `select_best_replica_deterministic`, `priority_zero_never_selected`, `single_eligible_selected`, `selected_has_best_priority`, `selection_maximizes_data_safety`, `replicaLessThan_total`, `replicaLessThan_trans`)
> - `Liveness.lean`: `phase0_eventually_holds`, `phase1_eventually_holds`, `phase6_eventually_holds`, `livenessTheorem` proved
>
> **Implemented (library modules)**:
> - TLA-style temporal logic framework (`TemporalLogic.lean`): `always`, `eventually`, `leads_to`, `weak_fairness`, with composition lemmas
> - `validTransition` next-state relation in `Invariants.lean` encoding all valid state transitions
> - Liveness properties stated (`Liveness.lean`): `eventuallyStableReconciliation`, `failedMasterReplaced`, `reconcileTerminates`
> - Phased proof strategy in `Liveness.lean` (Phase 0 through Phase VI)
> - Generic state machine framework (`StateMachine.lean`): `Action`, `StateMachine`, `NetworkStateMachine`
>
> **Proof placeholders (sorry)**: **5** across 2 files: Liveness.lean (4), RESP3.lean (1).

**Description**: Mathematical proofs of correctness using Lean 4 theorem proving.

**Verification Toolchain**:

1. **TLA+ (Specification Phase)**
   - Tool: TLC model checker
   - Purpose: Initial specification, find design bugs early
   - Output: TLA+ spec of state machine and invariants

2. **Lentil (Temporal Properties)**
   - Tool: TLA formalization in Lean 4
   - Purpose: Prove temporal logic properties
   - Example: Eventually Stable Reconciliation (ESR)

3. **LeanLTL (Linear Temporal Logic)**
   - Tool: LTL framework in Lean 4
   - Purpose: Safety and liveness properties
   - Example: `□(master_count ≤ 1)` (always at most one master)

4. **LeanMachines (State Machine Verification)**
   - Tool: Event-B style state machines in Lean 4
   - Purpose: Correctness-by-construction
   - Principle: Cannot construct state machine without discharging proof obligations

**Key Invariants to Prove**:

```lean
-- Safety: At most one master at any time
theorem at_most_one_master :
  ∀ (s : ClusterState), master_count s ≤ 1

-- Safety: Owner references always point to current CR
theorem owner_ref_consistency :
  ∀ (res : K8sResource),
    managed_by_operator res →
    res.ownerReferences.length = 1

-- Safety: No concurrent updates to same resource
theorem no_concurrent_updates :
  ∀ (s : ClusterState) (key : ResourceKey),
    (pending_requests s).filter (λ r => r.key = key)).length ≤ 1

-- Safety: Resource versions match etcd
theorem resource_version_consistency :
  ∀ (req : UpdateRequest),
    req.resourceVersion = etcd_version req.key

-- Liveness: Failed master eventually replaced
theorem failed_master_replaced :
  spec ⊨ □(master_failed) ⟹ ◇(new_master_elected)

-- Liveness: Eventually Stable Reconciliation (ESR)
theorem eventually_stable_reconciliation :
  spec ⊨ □(desired cr) ⟹ ◇□(current_state matches desired cr)

-- Data Safety: Promotion preserves committed data
theorem promotion_preserves_data :
  ∀ (replica : ReplicaInfo),
    replica.replOffset ≥ master.commitOffset →
    promote replica →
    committed_data_preserved
```

**Phased Proof Strategy** (from Anvil):
- **Phase 0**: Base invariants (message uniqueness, well-formedness)
- **Phase I**: Crash disabled, busy disabled
- **Phase II**: Reconcile state consistency
- **Phase III**: Request implications (create → at create step)
- **Phase IV**: Owner reference invariants
- **Phase V**: No deletion requests (GC prevention)
- **Phase VI**: Resource version tracking
- **Final**: ESR liveness property

Each phase's invariants proven to **eventually** hold using leads-to reasoning.

**Remaining**:
- Discharge 4 Liveness sorry: `esr_holds`, `failedMasterReplaced_holds`, `reconcileTerminates_holds`, `failedNodeDetected_holds` (require weak fairness assumptions, Anvil-level proof engineering)
- Discharge 1 RESP3 sorry: `parse_unparse_roundtrip` (convert `partial def` to fuel-based total definition)
- Bridge the 27 Main.lean theorems to the abstract state machine model
- Integration with Lentil/LeanLTL/LeanMachines verification libraries

---

## Removed Features (Complexity Reduction)

### Traditional Sentinel Features (Unnecessary in Operator)

| Feature | Status | Reason |
|---------|--------|--------|
| Quorum-based ODOWN | REMOVED | K8s Lease API provides leader election |
| Sentinel-to-Sentinel Gossip | REMOVED | No peer Sentinels, single Operator |
| Majority Authorization | REMOVED | Leader has full authority |
| Config Epoch Propagation | SIMPLIFIED | Store in CR Status, not inter-Sentinel |
| Sentinel Auto-Discovery | REMOVED | K8s API discovers pods via labels |
| Client `SENTINEL` Commands | REMOVED | Use K8s Service DNS instead |
| Periodic INFO Polling | OPTIMIZED | On-demand calls, leverage K8s status |

**Complexity Reduction**: ~40% fewer components, 7 network coordination steps → 3 steps

---

## Test Strategy Summary

| Feature | Unit | Integration | Property | Formal | E2E | Chaos |
|---------|------|-------------|----------|--------|-----|-------|
| RESP3 Parser | - | - | - | sorry(1) | - | - |
| Schema Clients | - | - | - | - | - | - |
| State Machine | - | - | - | sorry(4) | - | - |
| Resource Builders | - | - | - | - | **Done** | - |
| Health Monitoring | - | - | - | - | - | Chaos 1,2 |
| SDOWN Detection | - | - | - | sorry(4) | **Done** | Chaos 1,3 |
| Replica Selection | - | - | - | **Proved** | **Done** | Chaos 1,7 |
| Promotion Logic | - | - | - | - | **Done** | Chaos 1,3 |
| Service Update | - | - | - | **Proved** | **Done** | Chaos 1,3 |
| Backup/Restore | - | - | - | - | Scenario 5 | - |
| PDB | - | - | - | - | - | Chaos 6 |
| TLS | - | - | - | - | - | - |
| Scale Up/Down | - | - | - | - | **Done** | - |
| CR Deletion (GC) | - | - | - | - | Scenario 6 | - |

**Current testing**: All 18 Lean modules compile. E2E tests implemented in `test/e2e/` covering basic deployment, scale up/down, and failover scenarios on kind clusters. CI/CD via GitHub Actions (build + E2E). Formal proofs: 45+ theorems proved (0 sorry in Invariants.lean, ReplicaSelection.lean, Main.lean), 5 sorry remaining in Liveness.lean (4) and RESP3.lean (1).

### E2E Test Scenarios (Implemented)

E2E tests run on a kind cluster with the actual operator binary and real Valkey instances. Test scripts in `test/e2e/`.

| Scenario | Description | Status | Key Assertions |
|----------|-------------|--------|----------------|
| 1. Basic Deployment | Create ValkeyCluster CR, verify all sub-resources | **Done** | StatefulSet, Services, ConfigMap created; exactly 1 master; owner refs set |
| 2. Scale Up | Increase replicas 3->5 | **Done** | New pods are replicas; still exactly 1 master |
| 3. Scale Down | Decrease replicas 5->3 | **Done** | Data preserved; master stable |
| 4. Master Failover | Delete master pod, verify automatic failover | **Done** | New master elected within timeout; data preserved; no split-brain |
| 5. Backup/Restore | BGSAVE to MinIO, restore to new cluster | Planned | Backup completes; restored cluster has all original data |
| 6. CR Deletion | Delete ValkeyCluster CR | Planned | All sub-resources garbage-collected via owner references |

### Chaos Engineering Scenarios (Planned — future work)

Chaos tests validate the operator's runtime behavior matches formal proof guarantees. See plans.md for full details.

| Chaos Scenario | Fault Injected | Formal Property Validated | Tool |
|----------------|---------------|---------------------------|------|
| 1. Pod Kill (Master) | `kubectl delete pod --force` | `atMostOneMaster`, `failedMasterReplaced` | kubectl |
| 2. Pod Kill (Replica) | `kubectl delete pod --force` | `reconcileTerminates` | kubectl |
| 3. Network Partition (Master) | Isolate master from cluster | `atMostOneMaster`, `leaderElectionSafety` | Chaos Mesh |
| 4. Network Partition (Operator) | Block operator from API server | `leaderElectionSafety` | Chaos Mesh |
| 5. API Server Delay | 2-5s latency on API responses | `reconcileTerminates` | Chaos Mesh |
| 6. Node Drain | `kubectl drain` | PDB enforcement (Feature F11) | kubectl |
| 7. Disk Pressure | IO errors on master PVC | `failedMasterReplaced` | Chaos Mesh |
| 8. Concurrent CR Update | Patch CR during failover | `noConcurrentUpdates`, `resourceVersionConsistency` | kubectl |

### Bridging Formal Proofs to Runtime Validation

The operator's formal verification in Lean 4 proves properties about the abstract state machine model. Chaos and E2E tests validate that the implementation faithfully follows this model:

- **Safety invariants** (e.g., `atMostOneMaster`) are checked at runtime by polling `ROLE` on all Valkey pods and verifying at most one returns "master" at any sample point.
- **Liveness properties** (e.g., `failedMasterReplaced`) are validated by measuring time-to-recovery and asserting it is bounded by the configured timeout.
- **Counterexamples** from failed chaos tests indicate either implementation bugs (code diverges from model) or model gaps (model does not capture the real failure mode).

---

## Implementation Priorities

### Phase 0: Fix Critical Bugs (Weeks 1-2)
- #381: Storage validation error
- #367: PVC lifecycle consistency
- #284: Scaling errors
- #374: Metrics sidecar resources
- #352: Proxy mode fixes

### Phase 1: Foundation (Weeks 3-5) -- COMPLETE
- [F1] RESP3 parser -- Implemented
- [F2] Schema-driven clients -- Partially implemented (manual wrappers)
- [F3] Reconciler state machine -- Implemented

### Phase 2: Monitoring & Detection (Weeks 6-8) -- COMPLETE
- [F5] Health monitoring -- Implemented
- [F6] SDOWN detection -- Implemented
- [V] Temporal logic framework -- Implemented (proofs pending)

### Phase 3: Failover Logic (Weeks 9-11) -- COMPLETE
- [F7] Replica selection -- Implemented + fully proved (0 sorry, 8 theorems)
- [F8] Promotion logic -- Implemented (kubectl exec, REPLICAOF NO ONE, reconfiguration)
- [F9] Service updates -- Implemented (updateServiceSelector after failover)
- [V] Safety invariants -- **All 6 fully proved (0 sorry)** via `validTransition`

### Phase 3.5: Executable Operator & Deployment -- COMPLETE
- Main.lean daemon -- CLI, leader election, reconcile loop, kubectl bridge (27 theorems, 0 sorry)
- Resource creation -- JSON generation for all 6 sub-resources via kubectl apply
- Replication -- Pod-0 as master, pods 1+ replicate via startup script
- Helm chart -- CRD, RBAC, Deployment, leader election, ServiceAccount
- Docker build -- Multi-stage (Lean 4 build → native binary + kubectl)
- Deployed and verified on live K8s cluster

### Phase 4: Operations (Weeks 12-14) -- LARGELY COMPLETE
- [F10] Backup/Restore -- Partially implemented (commands only; S3/Job/CRD not yet)
- [F11] PDB -- Created via JSON generation; TLS/QoS not yet
- [V] ESR property stated -- `livenessTheorem` proved; 4 sorry remaining for sub-properties

### Phase 5: Hardening (Weeks 15-16) -- LARGELY COMPLETE
- [x] Automated failover (F8: `REPLICAOF NO ONE` via kubectl exec, F9: Service selector update)
- [x] CI/CD pipeline (GitHub Actions: build.yaml + e2e.yaml)
- [x] Automated E2E tests on kind cluster (basic deploy, scale, failover)
- [x] ReplicaSelection fully proved (0 sorry, 8 theorems)
- [x] Invariants fully proved (0 sorry, 6 safety invariants)
- [x] Liveness partially proved (`livenessTheorem`, `phase0/1/6_eventually_holds`)
- [ ] Chaos engineering tests
- [ ] Discharge 4 remaining Liveness sorry (Anvil-level proof engineering)
- [ ] Discharge 1 RESP3 sorry (convert `partial def` to fuel-based total)

---

## Success Criteria

**Functional**:
- Passes all unit, integration, and E2E tests
- Automatic failover completes within `failover-timeout-ms`
- No data loss during failover (replica offset >= master commit offset)
- Backup/restore cycle preserves all data

**Verification**:
- All safety invariants formally proven in Lean 4
- ESR liveness property proven
- TLA+ model passes TLC exhaustive checking

**Operations**:
- Deploys on Kubernetes 1.28+
- Supports Valkey 7.2+
- Pod Security Standards: `restricted` level
- Resource efficiency: <10% CPU/memory overhead vs. manual deployment

**Production Readiness**:
- Zero unaddressed GitHub issues with P0/P1 labels
- Chaos testing passes (network partitions, pod crashes, API server delays)
- Monitoring dashboards and runbooks complete
