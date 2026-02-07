/-
  Gungnir Operator - Kubernetes API Request/Response Types
  Lean 4 translation of Anvil's spec/api_method.rs and reconciler/spec/io.rs

  Models the K8s API as a set of request/response pairs:
  - Get, List, Create, Delete, Update, UpdateStatus
  - GetThenUpdate, GetThenDelete (compound operations with owner ref checks)

  These types are used by the reconciler state machine. Each reconcile step
  produces at most one APIRequest and consumes one APIResponse.
-/
import Gungnir.K8s.Types
import Gungnir.K8s.Resources

namespace Gungnir.K8s

/-! ## API Requests -/

/-- GetRequest fetches an object by its (kind, name, namespace) key.
    Corresponds to Anvil's `GetRequest`. -/
structure GetRequest where
  key : ObjectRef
  deriving Repr, BEq

/-- ListRequest lists all objects of a given kind in a namespace.
    Corresponds to Anvil's `ListRequest`. -/
structure ListRequest where
  kind : Kind
  «namespace» : String
  deriving Repr, BEq

/-- CreateRequest creates a new K8s object.
    Corresponds to Anvil's `CreateRequest`. -/
structure CreateRequest where
  «namespace» : String
  obj : DynamicObjectView
  deriving Repr

namespace CreateRequest

def key (req : CreateRequest) : ObjectRef :=
  { kind := req.obj.kind
  , name := req.obj.metadata.name.getD ""
  , «namespace» := req.«namespace» }

end CreateRequest

/-- DeleteRequest deletes an object by its key.
    Corresponds to Anvil's `DeleteRequest`. -/
structure DeleteRequest where
  key : ObjectRef
  deriving Repr, BEq

/-- UpdateRequest replaces an existing object with a new version.
    Corresponds to Anvil's `UpdateRequest`. -/
structure UpdateRequest where
  «namespace» : String
  name : String
  obj : DynamicObjectView
  deriving Repr

namespace UpdateRequest

def key (req : UpdateRequest) : ObjectRef :=
  { kind := req.obj.kind
  , name := req.name
  , «namespace» := req.«namespace» }

end UpdateRequest

/-- UpdateStatusRequest replaces only the status subresource.
    Corresponds to Anvil's `UpdateStatusRequest`. -/
structure UpdateStatusRequest where
  «namespace» : String
  name : String
  obj : DynamicObjectView
  deriving Repr

namespace UpdateStatusRequest

def key (req : UpdateStatusRequest) : ObjectRef :=
  { kind := req.obj.kind
  , name := req.name
  , «namespace» := req.«namespace» }

end UpdateStatusRequest

/-- GetThenDeleteRequest deletes an object only if it is owned by the given owner ref.
    This avoids race conditions caused by version conflicts.
    Corresponds to Anvil's `GetThenDeleteRequest`. -/
structure GetThenDeleteRequest where
  key : ObjectRef
  ownerRef : OwnerReferenceView
  deriving Repr

namespace GetThenDeleteRequest

def wellFormed (req : GetThenDeleteRequest) : Prop :=
  req.ownerRef.controller = some true

end GetThenDeleteRequest

/-- GetThenUpdateRequest updates an object only if it is owned by the given owner ref.
    Corresponds to Anvil's `GetThenUpdateRequest`. -/
structure GetThenUpdateRequest where
  «namespace» : String
  name : String
  ownerRef : OwnerReferenceView
  obj : DynamicObjectView
  deriving Repr

namespace GetThenUpdateRequest

def key (req : GetThenUpdateRequest) : ObjectRef :=
  { kind := req.obj.kind
  , name := req.name
  , «namespace» := req.«namespace» }

def wellFormed (req : GetThenUpdateRequest) : Prop :=
  req.ownerRef.controller = some true

end GetThenUpdateRequest

/-- APIRequest represents all possible K8s API requests.
    Corresponds to Anvil's `APIRequest` enum. -/
inductive APIRequest where
  | GetRequest (req : GetRequest)
  | ListRequest (req : ListRequest)
  | CreateRequest (req : CreateRequest)
  | DeleteRequest (req : DeleteRequest)
  | UpdateRequest (req : UpdateRequest)
  | UpdateStatusRequest (req : UpdateStatusRequest)
  | GetThenDeleteRequest (req : GetThenDeleteRequest)
  | GetThenUpdateRequest (req : GetThenUpdateRequest)
  deriving Repr

/-! ## API Responses -/

/-- GetResponse returns the fetched object or an error.
    Corresponds to Anvil's `GetResponse`. -/
structure GetResponse where
  res : Except APIError DynamicObjectView
  deriving Repr

/-- ListResponse returns a list of objects or an error.
    Corresponds to Anvil's `ListResponse`. -/
structure ListResponse where
  res : Except APIError (List DynamicObjectView)
  deriving Repr

/-- CreateResponse returns the created object or an error.
    Corresponds to Anvil's `CreateResponse`. -/
structure CreateResponse where
  res : Except APIError DynamicObjectView
  deriving Repr

/-- DeleteResponse returns success or an error (no object body).
    Corresponds to Anvil's `DeleteResponse`. -/
structure DeleteResponse where
  res : Except APIError Unit
  deriving Repr

/-- UpdateResponse returns the updated object or an error.
    Corresponds to Anvil's `UpdateResponse`. -/
structure UpdateResponse where
  res : Except APIError DynamicObjectView
  deriving Repr

/-- UpdateStatusResponse returns the object after status update or an error.
    Corresponds to Anvil's `UpdateStatusResponse`. -/
structure UpdateStatusResponse where
  res : Except APIError DynamicObjectView
  deriving Repr

/-- GetThenUpdateResponse returns the updated object or an error.
    Corresponds to Anvil's `GetThenUpdateResponse`. -/
structure GetThenUpdateResponse where
  res : Except APIError DynamicObjectView
  deriving Repr

/-- GetThenDeleteResponse returns success or an error.
    Corresponds to Anvil's `GetThenDeleteResponse`. -/
structure GetThenDeleteResponse where
  res : Except APIError Unit
  deriving Repr

/-- APIResponse represents all possible K8s API responses.
    Corresponds to Anvil's `APIResponse` enum. -/
inductive APIResponse where
  | GetResponse (resp : GetResponse)
  | ListResponse (resp : ListResponse)
  | CreateResponse (resp : CreateResponse)
  | DeleteResponse (resp : DeleteResponse)
  | UpdateResponse (resp : UpdateResponse)
  | UpdateStatusResponse (resp : UpdateStatusResponse)
  | GetThenDeleteResponse (resp : GetThenDeleteResponse)
  | GetThenUpdateResponse (resp : GetThenUpdateResponse)
  deriving Repr

/-! ## Request/Response Views for Reconciler IO -/

/-- External request type for non-K8s API calls (e.g., Valkey commands).
    Corresponds to Anvil's `VoidEReqView` (placeholder for controllers with no external API). -/
structure VoidExternalRequest deriving Repr, BEq

/-- External response type for non-K8s API calls. -/
structure VoidExternalResponse deriving Repr, BEq

/-- RequestView wraps either a K8s API request or an external request.
    Corresponds to Anvil's `RequestView<T>`. -/
inductive RequestView (ExternalReq : Type) where
  | KRequest (req : APIRequest)
  | ExternalRequest (req : ExternalReq)
  deriving Repr

/-- ResponseView wraps either a K8s API response or an external response.
    Corresponds to Anvil's `ResponseView<T>`. -/
inductive ResponseView (ExternalResp : Type) where
  | KResponse (resp : APIResponse)
  | ExternalResponse (resp : ExternalResp)
  deriving Repr

/-- Default request type (no external API). -/
abbrev DefaultReq := Option (RequestView VoidExternalRequest)

/-- Default response type (no external API). -/
abbrev DefaultResp := Option (ResponseView VoidExternalResponse)

/-! ## Response Extraction Helpers -/

/-- Check if a response is a successful K8s Get response. -/
def isSomeKGetResp (resp : DefaultResp) : Bool :=
  match resp with
  | some (.KResponse (.GetResponse _)) => true
  | _ => false

/-- Check if a response is a successful K8s Create response. -/
def isSomeKCreateResp (resp : DefaultResp) : Bool :=
  match resp with
  | some (.KResponse (.CreateResponse _)) => true
  | _ => false

/-- Check if a response is a successful K8s Update response. -/
def isSomeKUpdateResp (resp : DefaultResp) : Bool :=
  match resp with
  | some (.KResponse (.UpdateResponse _)) => true
  | _ => false

/-- Check if a response is a successful K8s List response. -/
def isSomeKListResp (resp : DefaultResp) : Bool :=
  match resp with
  | some (.KResponse (.ListResponse _)) => true
  | _ => false

/-- Check if a response is a K8s Delete response. -/
def isSomeKDeleteResp (resp : DefaultResp) : Bool :=
  match resp with
  | some (.KResponse (.DeleteResponse _)) => true
  | _ => false

/-- Check if a response is a K8s UpdateStatus response. -/
def isSomeKUpdateStatusResp (resp : DefaultResp) : Bool :=
  match resp with
  | some (.KResponse (.UpdateStatusResponse _)) => true
  | _ => false

/-- Extract the result from a K8s Get response. -/
def extractKGetResp (resp : DefaultResp) : Option (Except APIError DynamicObjectView) :=
  match resp with
  | some (.KResponse (.GetResponse r)) => some r.res
  | _ => none

/-- Extract the result from a K8s Create response. -/
def extractKCreateResp (resp : DefaultResp) : Option (Except APIError DynamicObjectView) :=
  match resp with
  | some (.KResponse (.CreateResponse r)) => some r.res
  | _ => none

/-- Extract the result from a K8s Update response. -/
def extractKUpdateResp (resp : DefaultResp) : Option (Except APIError DynamicObjectView) :=
  match resp with
  | some (.KResponse (.UpdateResponse r)) => some r.res
  | _ => none

/-- Extract the result from a K8s List response. -/
def extractKListResp (resp : DefaultResp) : Option (Except APIError (List DynamicObjectView)) :=
  match resp with
  | some (.KResponse (.ListResponse r)) => some r.res
  | _ => none

/-- Extract the result from a K8s Delete response. -/
def extractKDeleteResp (resp : DefaultResp) : Option (Except APIError Unit) :=
  match resp with
  | some (.KResponse (.DeleteResponse r)) => some r.res
  | _ => none

/-- Extract the result from a K8s UpdateStatus response. -/
def extractKUpdateStatusResp (resp : DefaultResp) : Option (Except APIError DynamicObjectView) :=
  match resp with
  | some (.KResponse (.UpdateStatusResponse r)) => some r.res
  | _ => none

end Gungnir.K8s
