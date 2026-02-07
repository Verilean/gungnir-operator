/-
  Gungnir Operator - Resource Builder Typeclass
  Lean 4 translation of Anvil's reconciler/spec/resource_builder.rs

  The ResourceBuilder typeclass defines how each K8s resource is:
  1. Fetched (getRequest) - which key to use for the Get API call
  2. Created (make) - how to construct the resource from the CR
  3. Updated (update) - how to update an existing resource from the CR
  4. Transitioned (stateAfterCreate/stateAfterUpdate) - next reconciler state

  This is the core abstraction that connects the reconciler state machine
  to concrete K8s resource management.
-/
import Gungnir.K8s.Types
import Gungnir.K8s.Resources
import Gungnir.K8s.API

namespace Gungnir.K8s

/-- ResourceBuilder defines the interface for constructing and updating K8s resources
    from a custom resource (CR).

    Type parameters:
    - CR: The custom resource type (e.g., ValkeyClusterView)
    - State: The reconciler state type
    - Resource: The K8s resource being built (e.g., ServiceView, StatefulSetView)

    Corresponds to Anvil's `ResourceBuilder<K, T>` trait. -/
class ResourceBuilder (CR : Type) (State : Type) (Resource : Type) where
  /-- Generate the GetRequest key for fetching the current version of this resource. -/
  getRequest : CR → GetRequest

  /-- Create a new resource from the custom resource and current reconciler state.
      Returns `none` on failure. -/
  make : CR → State → Option DynamicObjectView

  /-- Update an existing resource to match the desired state from the CR.
      Takes the current object from the API server.
      Returns `none` if no update is needed or on failure. -/
  update : CR → State → DynamicObjectView → Option DynamicObjectView

  /-- Compute the next reconciler state after a successful Create.
      Returns the new state and an optional next API request. -/
  stateAfterCreate : CR → DynamicObjectView → State → Option (State × Option APIRequest)

  /-- Compute the next reconciler state after a successful Update.
      Returns the new state and an optional next API request. -/
  stateAfterUpdate : CR → DynamicObjectView → State → Option (State × Option APIRequest)

/-! ## SubResource Enumeration -/

/-- SubResource enumerates the K8s resources managed by the Valkey operator.
    Corresponds to Anvil's `SubResource` enum (from step.rs). -/
inductive SubResource where
  | HeadlessService
  | ClientService
  | ConfigMap
  | Secret
  | StatefulSet
  | PodDisruptionBudget
  deriving Repr, BEq, DecidableEq

/-- ActionKind enumerates the CRUD operations on sub-resources.
    Corresponds to Anvil's `ActionKind` enum. -/
inductive ActionKind where
  | Get
  | Create
  | Update
  deriving Repr, BEq, DecidableEq

/-! ## Resource Naming Conventions -/

/-- Generate the standard resource name for a sub-resource, given the CR name. -/
def subResourceName (crName : String) : SubResource → String
  | .HeadlessService => crName ++ "-headless"
  | .ClientService => crName ++ "-client"
  | .ConfigMap => crName ++ "-config"
  | .Secret => crName ++ "-secret"
  | .StatefulSet => crName
  | .PodDisruptionBudget => crName ++ "-pdb"

/-- Get the Kind corresponding to a SubResource. -/
def subResourceKind : SubResource → Kind
  | .HeadlessService => Kind.ServiceKind
  | .ClientService => Kind.ServiceKind
  | .ConfigMap => Kind.ConfigMapKind
  | .Secret => Kind.SecretKind
  | .StatefulSet => Kind.StatefulSetKind
  | .PodDisruptionBudget => Kind.PodDisruptionBudgetKind

/-- Generate a GetRequest for a sub-resource given the CR name and namespace. -/
def subResourceGetRequest (crName ns : String) (sub : SubResource) : GetRequest :=
  { key := { kind := subResourceKind sub
            , name := subResourceName crName sub
            , «namespace» := ns } }

/-! ## Owner Reference Construction -/

/-- Create a controller owner reference from a custom resource's metadata.
    All managed resources must carry this owner reference for garbage collection. -/
def makeControllerOwnerRef (apiVersion : String) (crKind : Kind) (crName : String) (crUid : Uid) : OwnerReferenceView :=
  { apiVersion := apiVersion
  , blockOwnerDeletion := none
  , controller := some true
  , kind := crKind
  , name := crName
  , uid := crUid }

/-- Set the owner reference on any ObjectMetaView. -/
def setOwnerReference (meta : ObjectMetaView) (ownerRef : OwnerReferenceView) : ObjectMetaView :=
  meta.withOwnerReferences [ownerRef]

/-! ## Standard Labels -/

/-- Generate the standard labels for a managed resource. -/
def standardLabels (crName : String) : List (String × String) :=
  [ ("app.kubernetes.io/name", "valkey")
  , ("app.kubernetes.io/instance", crName)
  , ("app.kubernetes.io/managed-by", "gungnir-operator") ]

end Gungnir.K8s
