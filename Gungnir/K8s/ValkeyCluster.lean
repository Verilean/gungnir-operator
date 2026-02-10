/-
  Gungnir Operator - ValkeyCluster Custom Resource Definition
  Lean 4 translation following Anvil's zookeeper_controller/trusted/spec_types.rs

  Defines the ValkeyCluster CRD that the operator watches and reconciles:
  - ValkeyClusterView: spec type with metadata, spec, and status
  - ValkeyClusterSpecView: desired cluster configuration
  - ValkeyClusterStatusView: observed cluster state
  - ValkeyClusterPersistenceView: storage configuration

  The well_formed predicate ensures the CR has required fields.
  The controller_owner_ref method generates the owner reference used
  by all managed resources for garbage collection.
-/
import Gungnir.K8s.Types
import Gungnir.K8s.Resources
import Gungnir.K8s.API
import Gungnir.K8s.Builder

namespace Gungnir.K8s

/-! ## ValkeyCluster Spec -/

/-- Persistence configuration for Valkey data storage. -/
structure ValkeyClusterPersistenceView where
  enabled : Bool := true
  storageSize : String := "1Gi"
  storageClassName : Option String := none
  deriving Repr, BEq

/-- TLS configuration for Valkey cluster encryption. -/
structure ValkeyClusterTLSView where
  enabled : Bool := false
  certSecretName : Option String := none
  deriving Repr, BEq

/-- Metrics exporter sidecar configuration. -/
structure ValkeyClusterMetricsView where
  enabled : Bool := false
  resources : Option ResourceRequirementsView := none
  deriving Repr, BEq

/-- Sentinel integration configuration (Operator-as-Sentinel pattern). -/
structure ValkeyClusterSentinelView where
  /-- PING check interval in milliseconds. -/
  pingIntervalMs : Nat := 1000
  /-- Timeout before marking a node as SDOWN, in milliseconds. -/
  downAfterMs : Nat := 5000
  /-- Maximum time to wait for failover to complete, in milliseconds. -/
  failoverTimeoutMs : Nat := 60000
  deriving Repr, BEq

/-- ValkeyClusterSpecView defines the desired state of a Valkey cluster.
    This is the user-facing configuration embedded in the CR. -/
structure ValkeyClusterSpecView where
  /-- Number of Valkey replicas (must be >= 3). -/
  replicas : Nat := 3
  /-- Valkey container image. -/
  image : String := "valkey/valkey:7.2"
  /-- Valkey listen port. -/
  port : Nat := 6379
  /-- Persistence configuration. -/
  persistence : ValkeyClusterPersistenceView := {}
  /-- Resource requirements for the main Valkey container. -/
  resources : Option ResourceRequirementsView := none
  /-- TLS configuration. -/
  tls : ValkeyClusterTLSView := {}
  /-- Metrics exporter configuration. -/
  metrics : ValkeyClusterMetricsView := {}
  /-- Sentinel (monitoring) configuration. -/
  sentinel : ValkeyClusterSentinelView := {}
  /-- Custom labels to apply to all managed resources. -/
  labels : List (String × String) := []
  /-- Custom annotations to apply to all managed resources. -/
  annotations : List (String × String) := []
  /-- Node selector for pod scheduling. -/
  nodeSelector : List (String × String) := []
  deriving Repr

/-! ## ValkeyCluster Status -/

/-- ValkeyRole tracks the role of a Valkey node. -/
inductive ValkeyRole where
  | Master
  | Replica
  | Unknown
  deriving Repr, BEq, DecidableEq

/-- NodeHealthStatus tracks the health of a single Valkey node. -/
structure NodeHealthStatus where
  podName : String
  role : ValkeyRole := ValkeyRole.Unknown
  healthy : Bool := false
  lastPingSuccess : Option Nat := none   -- epoch ms
  consecutivePingFailures : Nat := 0
  replOffset : Option Nat := none
  deriving Repr, BEq

/-- ClusterPhase represents the overall cluster lifecycle phase. -/
inductive ClusterPhase where
  | Creating
  | Running
  | Updating
  | Failing
  | Failed
  deriving Repr, BEq, DecidableEq

/-- ValkeyClusterStatusView defines the observed state of the cluster.
    The operator writes this back to the CR status subresource. -/
structure ValkeyClusterStatusView where
  /-- Current cluster lifecycle phase. -/
  phase : ClusterPhase := ClusterPhase.Creating
  /-- Number of ready replicas. -/
  readyReplicas : Nat := 0
  /-- The pod name that is currently the master. -/
  currentMaster : Option String := none
  /-- Health status of each node. -/
  nodeStatuses : List NodeHealthStatus := []
  /-- Last time the operator successfully reconciled. -/
  lastReconcileTime : Option String := none
  deriving Repr

namespace ValkeyClusterStatusView

def default : ValkeyClusterStatusView := {}

def withReadyReplicas (s : ValkeyClusterStatusView) (n : Nat) : ValkeyClusterStatusView :=
  { s with readyReplicas := n }

def withPhase (s : ValkeyClusterStatusView) (p : ClusterPhase) : ValkeyClusterStatusView :=
  { s with phase := p }

def withCurrentMaster (s : ValkeyClusterStatusView) (m : String) : ValkeyClusterStatusView :=
  { s with currentMaster := some m }

end ValkeyClusterStatusView

/-! ## ValkeyCluster Resource -/

/-- ValkeyClusterView is the specification type for the ValkeyCluster custom resource.
    Follows Anvil's pattern from `ZookeeperClusterView`. -/
structure ValkeyClusterView where
  metadata : ObjectMetaView := ObjectMetaView.default
  spec : ValkeyClusterSpecView := {}
  status : Option ValkeyClusterStatusView := none
  deriving Repr

namespace ValkeyClusterView

/-- The K8s Kind for ValkeyCluster custom resources. -/
def kind : Kind := Kind.CustomResourceKind "valkeycluster"

/-- Check that the CR has required metadata fields. -/
def wellFormed (vc : ValkeyClusterView) : Prop :=
  vc.metadata.name.isSome ∧ vc.metadata.«namespace».isSome ∧ vc.metadata.uid.isSome

/-- The K8s apiVersion string for ValkeyCluster CRD. -/
def apiVersion : String := "valkey.verilean.io/v1"

/-- Generate the controller owner reference for this CR.
    All managed sub-resources must carry this owner ref. -/
def controllerOwnerRef (vc : ValkeyClusterView) : OwnerReferenceView :=
  { apiVersion := ValkeyClusterView.apiVersion
  , blockOwnerDeletion := none
  , controller := some true
  , kind := ValkeyClusterView.kind
  , name := vc.metadata.name.getD ""
  , uid := vc.metadata.uid.getD 0 }

/-- Set/update the status on this CR. -/
def withStatus (vc : ValkeyClusterView) (st : ValkeyClusterStatusView) : ValkeyClusterView :=
  { vc with status := some st }

/-- Get the ObjectRef for this CR. -/
def objectRef (vc : ValkeyClusterView) : ObjectRef :=
  { kind := ValkeyClusterView.kind
  , name := vc.metadata.name.getD ""
  , «namespace» := vc.metadata.«namespace».getD "" }

/-! ### Validation -/

/-- State validation for the ValkeyCluster CR (checked on create and update).
    Mirrors Anvil's `state_validation` pattern. -/
def stateValidation (vc : ValkeyClusterView) : Prop :=
  vc.spec.replicas ≥ 3

/-- Transition validation checks immutable fields between old and new CR versions.
    Mirrors Anvil's `transition_validation` pattern. -/
def transitionValidation (vc : ValkeyClusterView) (old : ValkeyClusterView) : Prop :=
  -- Port is immutable after creation
  vc.spec.port = old.spec.port ∧
  -- Persistence enabled/disabled is immutable
  vc.spec.persistence.enabled = old.spec.persistence.enabled ∧
  -- Storage class is immutable
  vc.spec.persistence.storageClassName = old.spec.persistence.storageClassName

end ValkeyClusterView

/-! ## Reconciler State -/

/-- ValkeyReconcileStep enumerates all states of the reconciler state machine.
    Each state corresponds to either the initial state, a state after an API
    call for a sub-resource, or a terminal state.
    Corresponds to Anvil's `ZookeeperReconcileStep`. -/
inductive ValkeyReconcileStep where
  | Init
  | AfterKRequestStep (action : ActionKind) (sub : SubResource)
  | AfterCheckValkeyHealth
  | AfterDetectFailure
  | AfterSelectReplica
  | AfterPromoteReplica
  | AfterUpdateService
  | AfterUpdateStatus
  | Done
  | Error (msg : String)
  deriving Repr, BEq

/-- ValkeyReconcileState holds the local state of the reconciler during one
    reconciliation round. Corresponds to Anvil's `ZookeeperReconcileState`. -/
structure ValkeyReconcileState where
  reconcileStep : ValkeyReconcileStep := ValkeyReconcileStep.Init
  /-- Cached resource version of the latest ConfigMap (for idempotent updates). -/
  latestConfigMapRv : Option String := none
  /-- The current master pod name discovered during reconciliation. -/
  discoveredMaster : Option String := none
  deriving Repr

/-! ## Reconciler Interface -/

/-- The reconciler's initial state at the start of each reconcile round. -/
def reconcileInitState : ValkeyReconcileState := {}

/-- Check if the reconciler has finished (successfully). -/
def reconcileDone (state : ValkeyReconcileState) : Bool :=
  match state.reconcileStep with
  | .Done => true
  | _ => false

/-- Check if the reconciler has finished with an error. -/
def reconcileError (state : ValkeyReconcileState) : Bool :=
  match state.reconcileStep with
  | .Error _ => true
  | _ => false

end Gungnir.K8s
