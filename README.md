# Project Gungnir: Formally Verified Valkey Operator

> "Named after the mythological spear that never misses its mark."

**Project Gungnir** is a Kubernetes Operator for [Valkey](https://valkey.io/), designed to provide mathematically guaranteed reliability through **Lean 4** formal verification following the [Anvil](https://github.com/anvil-verifier/anvil) (OSDI'24) patterns.

## Project Status

| Metric | Value |
|--------|-------|
| Lean files | 18 (17 library + 1 Main.lean daemon) |
| Docker build | Passes, produces native `gungnir_operator` binary |
| Helm chart | Complete at `charts/gungnir-operator/` |
| Deployed | Running on K8s with leader election, replication |
| Proved theorems | 73 (38 in Main.lean, 35 in library) |
| Sorry remaining | **0** (4 TCB axioms in RESP3.lean) |
| CRD API group | `valkey.verilean.io/v1` |

### Trusted Computing Base (TCB)

4 axioms in `RESP3.lean` — language-level ByteArray/String properties, not operator logic gaps:
- `utf8_roundtrip`, `byteArray_append_size`, `findCRLF_at_crlf`, `parse_unparse_roundtrip`

### Proved (0 sorry across all files)

- **Invariants.lean**: 10 safety invariants (`atMostOneMaster`, `ownerRefConsistency`, `noConcurrentUpdates`, `sentinelForwardProgress`, `leaderElectionSafety`, `reconcileStepValid`, `partitionSafety`, `serviceConsistency`, `noDoubleFailover`, `pdbProtectsMaster`)
- **Liveness.lean**: 9 liveness theorems (`livenessTheorem`, `esr_holds`, `reconcileTerminates_holds`, `failedMasterReplaced_holds`, `failedNodeDetected_holds`, `reconcileStep_decreases_measure`, `phase0/1/6_eventually_holds`)
- **ReplicaSelection.lean**: 8 theorems (`select_best_replica_total`, `replicaLessThan_total`, `replicaLessThan_trans`, `selected_has_best_priority`, `selection_maximizes_data_safety`, etc.)
- **TemporalLogic.lean**: 4 lemmas (`wf1_rule`, `leadsTo_trans`, `eventually_mono`, `always_suffix`)
- **Main.lean**: 38 theorems covering reconciler properties, leader election, resource creation, CR health map isolation
- **RESP3.lean**: 1 theorem + 4 axioms (TCB)

---

## Architecture

```
┌─────────────────────────────────────┐
│  Gungnir Operator (Lean 4 binary)   │
│  ┌──────────┐  ┌─────────────────┐  │
│  │ Reconciler│  │ Sentinel (FSM)  │  │
│  │  (FSM)   │  │ Health → SDOWN  │  │
│  │ Init→Get │  │ → Select → Pro- │  │
│  │ →Create  │  │   mote → Reconf │  │
│  │ →Update  │  │   → UpdateSvc   │  │
│  │ →Health  │  │   → Done        │  │
│  └──────────┘  └─────────────────┘  │
│  ┌──────────────────────────────┐   │
│  │ kubectl bridge (JSON → exec) │   │
│  └──────────────────────────────┘   │
└─────────────────────────────────────┘
         │ kubectl apply/exec
         ▼
┌─────────────────────────────────────┐
│  Kubernetes Cluster                 │
│  ┌──────────┐ ┌──────────────────┐  │
│  │ CRD:     │ │ Managed:         │  │
│  │ Valkey   │ │ StatefulSet      │  │
│  │ Cluster  │ │ Services (2)     │  │
│  │          │ │ ConfigMap        │  │
│  │          │ │ Secret           │  │
│  │          │ │ PDB              │  │
│  └──────────┘ └──────────────────┘  │
│  ┌──────────────────────────────┐   │
│  │ Valkey Pods (master+replicas)│   │
│  │ Pod-0: master                │   │
│  │ Pod-1..N: REPLICAOF pod-0   │   │
│  └──────────────────────────────┘   │
└─────────────────────────────────────┘
```

## Quick Start

```bash
# Build
lake build gungnir_operator

# Docker
docker build -t gungnir-operator:latest .

# Deploy via Helm
helm install gungnir charts/gungnir-operator/ -n gungnir-system --create-namespace

# Create a ValkeyCluster
kubectl apply -f - <<EOF
apiVersion: valkey.verilean.io/v1
kind: ValkeyCluster
metadata:
  name: my-valkey
  namespace: valkey-test
spec:
  replicas: 3
  image: "valkey/valkey:7.2"
  port: 6379
EOF
```

## Key Features

- **Operator-as-Sentinel**: Integrates Sentinel monitoring directly — no separate Sentinel containers
- **Formally verified**: TLA-style temporal logic proofs in Lean 4
- **Pure Lean 4**: No FFI dependencies, pure RESP3 parser
- **Anvil pattern**: State machine reconciler with one API call per transition
- **Leader election**: K8s Lease API with expiry detection
- **Replication**: Automatic master-replica setup via startup script

## Formal Verification

The operator uses a TLA-style temporal logic framework (`TemporalLogic.lean`) with:
- `always` (□), `eventually` (◇), `leads_to` (~>), `weak_fairness`
- Safety invariants proved as inductive invariants over `validTransition`
- Liveness properties stated as leads-to chains (ESR from Anvil)
- All proofs discharged — 0 sorry, 4 TCB axioms

See [plans.md](plans.md) and [features.md](features.md) for full details.

## Author

**Junji Hashimoto**
* Background: Haskell, Lean 4, Formal Methods, Critical Infrastructure Operations.

---
*Building the shield for data sovereignty.*
