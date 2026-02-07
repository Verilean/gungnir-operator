/-
  Gungnir Operator - Kubernetes Resource Definitions
  Lean 4 translation of Anvil's spec types for K8s resources:
  - Pod, Service, ConfigMap, Secret, StatefulSet, PodDisruptionBudget

  Each resource follows Anvil's pattern:
  1. A View structure with metadata + spec + status
  2. Builder methods (withX) for functional construction
  3. State/transition validation predicates for verification
-/
import Gungnir.K8s.Types

namespace Gungnir.K8s

/-! ## API Error -/

/-- APIError enumerates K8s API server error codes.
    Corresponds to Anvil's `APIError` enum. -/
inductive APIError where
  | BadRequest
  | Conflict
  | Forbidden
  | Invalid
  | ObjectNotFound
  | ObjectAlreadyExists
  | NotSupported
  | InternalError
  | Timeout
  | ServerTimeout
  | TransactionAbort
  | Other
  deriving Repr, BEq, DecidableEq

def APIError.isObjectNotFound : APIError → Bool
  | .ObjectNotFound => true
  | _ => false

/-! ## Resource Requirements -/

/-- ResourceRequirementsView models CPU/memory resource requests and limits. -/
structure ResourceRequirementsView where
  limitsCpu : Option String := none
  limitsMemory : Option String := none
  requestsCpu : Option String := none
  requestsMemory : Option String := none
  deriving Repr, BEq

/-! ## Container -/

/-- ContainerPortView models a port exposed by a container. -/
structure ContainerPortView where
  name : Option String := none
  containerPort : Nat
  protocol : Option String := none
  deriving Repr, BEq

/-- VolumeMountView models a volume mount inside a container. -/
structure VolumeMountView where
  name : String
  mountPath : String
  readOnly : Option Bool := none
  subPath : Option String := none
  deriving Repr, BEq

/-- EnvVarView models an environment variable for a container. -/
structure EnvVarView where
  name : String
  value : Option String := none
  deriving Repr, BEq

/-- ContainerView models a K8s container spec. -/
structure ContainerView where
  name : String
  image : Option String := none
  command : Option (List String) := none
  args : Option (List String) := none
  ports : Option (List ContainerPortView) := none
  env : Option (List EnvVarView) := none
  resources : Option ResourceRequirementsView := none
  volumeMounts : Option (List VolumeMountView) := none
  livenessProbe : Option String := none    -- simplified as String for now
  readinessProbe : Option String := none   -- simplified as String for now
  deriving Repr, BEq

/-! ## Volume -/

/-- VolumeView models a K8s volume. -/
structure VolumeView where
  name : String
  configMapName : Option String := none
  secretName : Option String := none
  emptyDir : Bool := false
  deriving Repr, BEq

/-! ## Label Selector -/

/-- LabelSelectorView models a K8s label selector. -/
structure LabelSelectorView where
  matchLabels : Option (List (String × String)) := none
  deriving Repr, BEq

namespace LabelSelectorView

def default : LabelSelectorView := {}

def withMatchLabels (sel : LabelSelectorView) (labels : List (String × String)) : LabelSelectorView :=
  { sel with matchLabels := some labels }

end LabelSelectorView

/-! ## Pod Template -/

/-- PodSecurityContextView models pod-level security settings. -/
structure PodSecurityContextView where
  runAsNonRoot : Option Bool := none
  runAsUser : Option Nat := none
  fsGroup : Option Nat := none
  deriving Repr, BEq

/-- PodSpecView models a K8s PodSpec.
    Corresponds to Anvil's `PodSpecView`. -/
structure PodSpecView where
  containers : List ContainerView := []
  initContainers : Option (List ContainerView) := none
  volumes : Option (List VolumeView) := none
  serviceAccountName : Option String := none
  nodeSelector : Option (List (String × String)) := none
  securityContext : Option PodSecurityContextView := none
  terminationGracePeriodSeconds : Option Nat := none
  hostname : Option String := none
  subdomain : Option String := none
  deriving Repr, BEq

namespace PodSpecView

def default : PodSpecView := {}

def withContainers (ps : PodSpecView) (cs : List ContainerView) : PodSpecView :=
  { ps with containers := cs }

def withVolumes (ps : PodSpecView) (vs : List VolumeView) : PodSpecView :=
  { ps with volumes := some vs }

def withInitContainers (ps : PodSpecView) (cs : List ContainerView) : PodSpecView :=
  { ps with initContainers := some cs }

def withSecurityContext (ps : PodSpecView) (sc : PodSecurityContextView) : PodSpecView :=
  { ps with securityContext := some sc }

end PodSpecView

/-- PodTemplateSpecView models metadata + spec for pod templates. -/
structure PodTemplateSpecView where
  metadata : Option ObjectMetaView := none
  spec : Option PodSpecView := none
  deriving Repr

namespace PodTemplateSpecView

def default : PodTemplateSpecView := {}

def withMetadata (pt : PodTemplateSpecView) (meta : ObjectMetaView) : PodTemplateSpecView :=
  { pt with metadata := some meta }

def withSpec (pt : PodTemplateSpecView) (spec : PodSpecView) : PodTemplateSpecView :=
  { pt with spec := some spec }

end PodTemplateSpecView

/-! ## Pod -/

/-- PodView is the specification type for K8s Pod.
    Corresponds to Anvil's `PodView`. -/
structure PodView where
  metadata : ObjectMetaView := ObjectMetaView.default
  spec : Option PodSpecView := none
  status : Option Unit := none   -- simplified status
  deriving Repr

namespace PodView

def kind : Kind := Kind.PodKind

def withMetadata (p : PodView) (meta : ObjectMetaView) : PodView :=
  { p with metadata := meta }

def withSpec (p : PodView) (spec : PodSpecView) : PodView :=
  { p with spec := some spec }

def stateValidation (p : PodView) : Prop := p.spec.isSome

end PodView

/-! ## Service -/

/-- ServicePortView models a K8s Service port. -/
structure ServicePortView where
  name : Option String := none
  port : Nat := 0
  targetPort : Option Nat := none
  appProtocol : Option String := none
  protocol : Option String := none
  deriving Repr, BEq

namespace ServicePortView

def default : ServicePortView := {}

def withName (sp : ServicePortView) (n : String) : ServicePortView :=
  { sp with name := some n }

def withPort (sp : ServicePortView) (p : Nat) : ServicePortView :=
  { sp with port := p }

def withProtocol (sp : ServicePortView) (proto : String) : ServicePortView :=
  { sp with protocol := some proto }

end ServicePortView

/-- ServiceSpecView models a K8s ServiceSpec. -/
structure ServiceSpecView where
  clusterIP : Option String := none
  serviceType : Option String := none   -- "ClusterIP", "NodePort", "LoadBalancer"
  ports : Option (List ServicePortView) := none
  selector : Option (List (String × String)) := none
  publishNotReadyAddresses : Option Bool := none
  deriving Repr, BEq

namespace ServiceSpecView

def default : ServiceSpecView := {}

def withClusterIP (ss : ServiceSpecView) (ip : String) : ServiceSpecView :=
  { ss with clusterIP := some ip }

def withPorts (ss : ServiceSpecView) (ps : List ServicePortView) : ServiceSpecView :=
  { ss with ports := some ps }

def withSelector (ss : ServiceSpecView) (sel : List (String × String)) : ServiceSpecView :=
  { ss with selector := some sel }

def withPublishNotReadyAddresses (ss : ServiceSpecView) (b : Bool) : ServiceSpecView :=
  { ss with publishNotReadyAddresses := some b }

def withServiceType (ss : ServiceSpecView) (t : String) : ServiceSpecView :=
  { ss with serviceType := some t }

end ServiceSpecView

/-- ServiceView is the specification type for K8s Service.
    Corresponds to Anvil's `ServiceView`. -/
structure ServiceView where
  metadata : ObjectMetaView := ObjectMetaView.default
  spec : Option ServiceSpecView := none
  status : Option Unit := none
  deriving Repr

namespace ServiceView

def kind : Kind := Kind.ServiceKind

def withMetadata (s : ServiceView) (meta : ObjectMetaView) : ServiceView :=
  { s with metadata := meta }

def withSpec (s : ServiceView) (spec : ServiceSpecView) : ServiceView :=
  { s with spec := some spec }

def stateValidation (s : ServiceView) : Prop := s.spec.isSome

end ServiceView

/-! ## ConfigMap -/

/-- ConfigMapView is the specification type for K8s ConfigMap.
    Corresponds to Anvil's `ConfigMapView`. -/
structure ConfigMapView where
  metadata : ObjectMetaView := ObjectMetaView.default
  data : Option (List (String × String)) := none
  deriving Repr

namespace ConfigMapView

def kind : Kind := Kind.ConfigMapKind

def withMetadata (cm : ConfigMapView) (meta : ObjectMetaView) : ConfigMapView :=
  { cm with metadata := meta }

def withData (cm : ConfigMapView) (d : List (String × String)) : ConfigMapView :=
  { cm with data := some d }

def stateValidation (_ : ConfigMapView) : Prop := True

end ConfigMapView

/-! ## Secret -/

/-- SecretType enumerates common K8s Secret types. -/
inductive SecretType where
  | Opaque
  | TLS
  | DockerConfigJson
  deriving Repr, BEq, DecidableEq

/-- SecretView is the specification type for K8s Secret.
    Corresponds to Anvil's `SecretView`. -/
structure SecretView where
  metadata : ObjectMetaView := ObjectMetaView.default
  secretType : SecretType := SecretType.Opaque
  data : Option (List (String × String)) := none
  deriving Repr

namespace SecretView

def kind : Kind := Kind.SecretKind

def withMetadata (s : SecretView) (meta : ObjectMetaView) : SecretView :=
  { s with metadata := meta }

def withData (s : SecretView) (d : List (String × String)) : SecretView :=
  { s with data := some d }

def withSecretType (s : SecretView) (t : SecretType) : SecretView :=
  { s with secretType := t }

def stateValidation (_ : SecretView) : Prop := True

end SecretView

/-! ## Persistent Volume Claim -/

/-- PersistentVolumeClaimView models a K8s PVC. -/
structure PersistentVolumeClaimView where
  metadata : ObjectMetaView := ObjectMetaView.default
  storageClassName : Option String := none
  storageSize : Option String := none
  accessModes : Option (List String) := none
  deriving Repr

namespace PersistentVolumeClaimView

def kind : Kind := Kind.PersistentVolumeClaimKind

def withMetadata (pvc : PersistentVolumeClaimView) (meta : ObjectMetaView) : PersistentVolumeClaimView :=
  { pvc with metadata := meta }

def withStorageClassName (pvc : PersistentVolumeClaimView) (sc : String) : PersistentVolumeClaimView :=
  { pvc with storageClassName := some sc }

def withStorageSize (pvc : PersistentVolumeClaimView) (sz : String) : PersistentVolumeClaimView :=
  { pvc with storageSize := some sz }

def withAccessModes (pvc : PersistentVolumeClaimView) (modes : List String) : PersistentVolumeClaimView :=
  { pvc with accessModes := some modes }

end PersistentVolumeClaimView

/-! ## StatefulSet -/

/-- StatefulSetSpecView models a K8s StatefulSetSpec.
    Corresponds to Anvil's `StatefulSetSpecView`. -/
structure StatefulSetSpecView where
  replicas : Option Nat := none
  selector : LabelSelectorView := LabelSelectorView.default
  serviceName : String := ""
  template : PodTemplateSpecView := PodTemplateSpecView.default
  volumeClaimTemplates : Option (List PersistentVolumeClaimView) := none
  podManagementPolicy : Option String := none  -- "OrderedReady" or "Parallel"
  deriving Repr

namespace StatefulSetSpecView

def default : StatefulSetSpecView := {}

def withReplicas (ss : StatefulSetSpecView) (r : Nat) : StatefulSetSpecView :=
  { ss with replicas := some r }

def withSelector (ss : StatefulSetSpecView) (sel : LabelSelectorView) : StatefulSetSpecView :=
  { ss with selector := sel }

def withServiceName (ss : StatefulSetSpecView) (sn : String) : StatefulSetSpecView :=
  { ss with serviceName := sn }

def withTemplate (ss : StatefulSetSpecView) (t : PodTemplateSpecView) : StatefulSetSpecView :=
  { ss with template := t }

def withVolumeClaimTemplates (ss : StatefulSetSpecView) (vcts : List PersistentVolumeClaimView) : StatefulSetSpecView :=
  { ss with volumeClaimTemplates := some vcts }

def withPodManagementPolicy (ss : StatefulSetSpecView) (policy : String) : StatefulSetSpecView :=
  { ss with podManagementPolicy := some policy }

end StatefulSetSpecView

/-- StatefulSetStatusView models a K8s StatefulSetStatus. -/
structure StatefulSetStatusView where
  readyReplicas : Option Nat := none
  deriving Repr, BEq

/-- StatefulSetView is the specification type for K8s StatefulSet.
    Corresponds to Anvil's `StatefulSetView`. -/
structure StatefulSetView where
  metadata : ObjectMetaView := ObjectMetaView.default
  spec : Option StatefulSetSpecView := none
  status : Option StatefulSetStatusView := none
  deriving Repr

namespace StatefulSetView

def kind : Kind := Kind.StatefulSetKind

def withMetadata (ss : StatefulSetView) (meta : ObjectMetaView) : StatefulSetView :=
  { ss with metadata := meta }

def withSpec (ss : StatefulSetView) (spec : StatefulSetSpecView) : StatefulSetView :=
  { ss with spec := some spec }

def stateValidation (ss : StatefulSetView) : Prop :=
  ss.spec.isSome ∧
  match ss.spec with
  | some s => match s.replicas with
    | some r => r > 0
    | none => True
  | none => True

end StatefulSetView

/-! ## Pod Disruption Budget -/

/-- PDBSpecView models a K8s PodDisruptionBudget spec. -/
structure PDBSpecView where
  maxUnavailable : Option Nat := none
  minAvailable : Option Nat := none
  selector : Option LabelSelectorView := none
  deriving Repr, BEq

/-- PodDisruptionBudgetView is the specification type for K8s PDB. -/
structure PodDisruptionBudgetView where
  metadata : ObjectMetaView := ObjectMetaView.default
  spec : Option PDBSpecView := none
  deriving Repr

namespace PodDisruptionBudgetView

def kind : Kind := Kind.PodDisruptionBudgetKind

def withMetadata (pdb : PodDisruptionBudgetView) (meta : ObjectMetaView) : PodDisruptionBudgetView :=
  { pdb with metadata := meta }

def withSpec (pdb : PodDisruptionBudgetView) (spec : PDBSpecView) : PodDisruptionBudgetView :=
  { pdb with spec := some spec }

def stateValidation (_ : PodDisruptionBudgetView) : Prop := True

end PodDisruptionBudgetView

end Gungnir.K8s
