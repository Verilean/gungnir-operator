/-
  Gungnir Operator - Core Kubernetes Types
  Lean 4 translation of Anvil's kubernetes_api_objects/spec/common.rs,
  object_meta.rs, owner_reference.rs, and dynamic.rs

  These are the *specification* (verification) types used for formal proofs.
  They model K8s objects abstractly, following Anvil's spec/exec separation:
  - Spec types (this file): used in theorems and proof obligations
  - Exec types (future): runtime representations that refine these specs
-/

namespace Gungnir.K8s

-- Uid is modeled as Nat for easy comparison in proofs (mirrors Anvil's int-based Uid)
abbrev Uid := Nat

-- ResourceVersion is modeled as Nat for easy comparison in proofs
abbrev ResourceVersion := Nat

-- Value is an opaque string used for marshalled spec/status data
abbrev Value := String

-- UnmarshalError is a unit error (matches Anvil)
abbrev UnmarshalError := Unit

/-! ## Resource Kind -/

/-- Kind enumerates all K8s resource types the operator manages.
    Follows Anvil's `Kind` enum from common.rs. -/
inductive Kind where
  | ConfigMapKind
  | CustomResourceKind (name : String)
  | DaemonSetKind
  | PersistentVolumeClaimKind
  | PodKind
  | RoleKind
  | RoleBindingKind
  | StatefulSetKind
  | ServiceKind
  | ServiceAccountKind
  | SecretKind
  | PodDisruptionBudgetKind
  deriving Repr, BEq, DecidableEq

/-! ## Object Reference -/

/-- ObjectRef uniquely identifies a namespaced K8s resource.
    Corresponds to Anvil's `ObjectRef` struct. -/
structure ObjectRef where
  kind : Kind
  name : String
  «namespace» : String
  deriving Repr, BEq, DecidableEq

/-! ## Owner Reference -/

/-- OwnerReferenceView models a K8s owner reference for garbage collection.
    Corresponds to Anvil's `OwnerReferenceView`.
    Note: `kind` uses the `Kind` enum (not a raw string) for type-safe verification,
    matching Anvil's design. The `apiVersion` field is a string since K8s API versions
    are not enumerated in the spec types. -/
structure OwnerReferenceView where
  apiVersion : String := ""
  blockOwnerDeletion : Option Bool := none
  controller : Option Bool := none
  kind : Kind
  name : String
  uid : Uid
  deriving Repr, BEq

/-- Convert an owner reference to the object reference it points to. -/
def OwnerReferenceView.toObjectRef (oref : OwnerReferenceView) (ns : String) : ObjectRef :=
  { kind := oref.kind, name := oref.name, «namespace» := ns }

/-- Check if an owner reference is a controller reference. -/
def OwnerReferenceView.isController (oref : OwnerReferenceView) : Bool :=
  match oref.controller with
  | some true => true
  | _ => false

/-! ## Object Metadata -/

/-- ObjectMetaView is the specification type for K8s ObjectMeta.
    Corresponds to Anvil's `ObjectMetaView`. -/
structure ObjectMetaView where
  name : Option String := none
  generateName : Option String := none
  «namespace» : Option String := none
  resourceVersion : Option ResourceVersion := none
  uid : Option Uid := none
  labels : Option (List (String × String)) := none
  annotations : Option (List (String × String)) := none
  ownerReferences : Option (List OwnerReferenceView) := none
  finalizers : Option (List String) := none
  deletionTimestamp : Option String := none
  deriving Repr

namespace ObjectMetaView

def default : ObjectMetaView := {}

def withName (meta : ObjectMetaView) (n : String) : ObjectMetaView :=
  { meta with name := some n }

def withNamespace (meta : ObjectMetaView) (ns : String) : ObjectMetaView :=
  { meta with «namespace» := some ns }

def withLabels (meta : ObjectMetaView) (ls : List (String × String)) : ObjectMetaView :=
  { meta with labels := some ls }

def addLabel (meta : ObjectMetaView) (key value : String) : ObjectMetaView :=
  let oldLabels := meta.labels.getD []
  { meta with labels := some ((key, value) :: oldLabels.filter (·.1 != key)) }

def withAnnotations (meta : ObjectMetaView) (as_ : List (String × String)) : ObjectMetaView :=
  { meta with annotations := some as_ }

def withResourceVersion (meta : ObjectMetaView) (rv : ResourceVersion) : ObjectMetaView :=
  { meta with resourceVersion := some rv }

def withoutResourceVersion (meta : ObjectMetaView) : ObjectMetaView :=
  { meta with resourceVersion := none }

def withOwnerReferences (meta : ObjectMetaView) (refs : List OwnerReferenceView) : ObjectMetaView :=
  { meta with ownerReferences := some refs }

def withFinalizers (meta : ObjectMetaView) (fs : List String) : ObjectMetaView :=
  { meta with finalizers := some fs }

def withoutFinalizers (meta : ObjectMetaView) : ObjectMetaView :=
  { meta with finalizers := none }

def withDeletionTimestamp (meta : ObjectMetaView) (ts : String) : ObjectMetaView :=
  { meta with deletionTimestamp := some ts }

/-- Check if the owner references contain a specific reference. -/
def ownerReferencesContains (meta : ObjectMetaView) (oref : OwnerReferenceView) : Bool :=
  match meta.ownerReferences with
  | some refs => refs.any (· == oref)
  | none => false

/-- Check if the owner references contain exactly one specific reference. -/
def ownerReferencesOnlyContains (meta : ObjectMetaView) (oref : OwnerReferenceView) : Bool :=
  match meta.ownerReferences with
  | some [ref] => ref == oref
  | _ => false

/-- Well-formedness check for namespaced resources. -/
def wellFormedForNamespaced (meta : ObjectMetaView) : Prop :=
  meta.name.isSome ∧ meta.«namespace».isSome ∧ meta.resourceVersion.isSome ∧ meta.uid.isSome

end ObjectMetaView

/-! ## Dynamic Object -/

/-- DynamicObjectView is the type-erased representation of any K8s resource.
    Corresponds to Anvil's `DynamicObjectView`.
    All typed resources marshal to/from this representation. -/
structure DynamicObjectView where
  kind : Kind
  metadata : ObjectMetaView
  spec : Value
  status : Value
  deriving Repr

namespace DynamicObjectView

def objectRef (obj : DynamicObjectView) : ObjectRef :=
  { kind := obj.kind
  , name := obj.metadata.name.getD ""
  , «namespace» := obj.metadata.«namespace».getD "" }

def withMetadata (obj : DynamicObjectView) (meta : ObjectMetaView) : DynamicObjectView :=
  { obj with metadata := meta }

def withName (obj : DynamicObjectView) (n : String) : DynamicObjectView :=
  { obj with metadata := obj.metadata.withName n }

def withNamespace (obj : DynamicObjectView) (ns : String) : DynamicObjectView :=
  { obj with metadata := obj.metadata.withNamespace ns }

def withResourceVersion (obj : DynamicObjectView) (rv : ResourceVersion) : DynamicObjectView :=
  { obj with metadata := obj.metadata.withResourceVersion rv }

def withUid (obj : DynamicObjectView) (u : Uid) : DynamicObjectView :=
  { obj with metadata := { obj.metadata with uid := some u } }

end DynamicObjectView

/-! ## Stored State -/

/-- StoredState represents the entire cluster state as a map from ObjectRef to DynamicObjectView.
    Corresponds to Anvil's `StoredState`. -/
abbrev StoredState := List (ObjectRef × DynamicObjectView)

end Gungnir.K8s
