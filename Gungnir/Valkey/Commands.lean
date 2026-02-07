/-
  Gungnir Operator - Valkey Command Wrappers

  Type-safe wrappers for the Valkey commands used by the operator:
  - PING: Health check
  - INFO (replication section): Topology discovery
  - ROLE: Master/replica role detection
  - REPLICAOF: Replication reconfiguration (promotion + demotion)
  - BGSAVE / LASTSAVE: Backup triggers
  - SET / GET: Basic data operations (testing/diagnostics)

  Each command returns a typed result, not a raw RESPValue.
  Error handling converts RESP3 errors to ValkeyError.

  Reference: features.md [F1], [F2], [F5], [F8], [F10]
-/

import Gungnir.Valkey.RESP3
import Gungnir.Valkey.Connection

namespace Gungnir.Valkey

/-! ## Command Error Type -/

/-- Errors that can occur when executing a Valkey command. -/
inductive ValkeyError where
  | ConnectionError (err : ConnectionError)
  | ServerError (msg : String)
  | UnexpectedResponse (msg : String)
  | ParseError (msg : String)
  deriving Repr

instance : ToString ValkeyError where
  toString e := match e with
    | .ConnectionError err => s!"Connection: {err}"
    | .ServerError msg => s!"Server error: {msg}"
    | .UnexpectedResponse msg => s!"Unexpected response: {msg}"
    | .ParseError msg => s!"Parse error: {msg}"

/-- Helper: convert a connection-level result to a command-level result. -/
def liftConnectionResult (r : Except ConnectionError RESPValue)
    : Except ValkeyError RESPValue :=
  match r with
  | Except.ok v =>
    match v with
    | RESPValue.Error msg => Except.error (ValkeyError.ServerError msg)
    | _ => Except.ok v
  | Except.error e => Except.error (ValkeyError.ConnectionError e)

/-! ## PING Command -/

/-- Result of a PING command. -/
inductive PingResult where
  | Pong
  | Message (msg : String)
  deriving Repr, BEq

/-- Send PING command. Returns PingResult on success.
    Used for health monitoring (features.md [F5]). -/
def ping (conn : ValkeyConnection) : IO (Except ValkeyError PingResult) := do
  let resp ← sendCommand conn ["PING"]
  match liftConnectionResult resp with
  | Except.error e => pure (Except.error e)
  | Except.ok v =>
    match v with
    | RESPValue.SimpleString "PONG" => pure (Except.ok PingResult.Pong)
    | RESPValue.SimpleString s => pure (Except.ok (PingResult.Message s))
    | RESPValue.BulkString s => pure (Except.ok (PingResult.Message s))
    | _ => pure (Except.error (ValkeyError.UnexpectedResponse "expected PONG or string"))

/-! ## INFO Command -/

/-- Send INFO command for a specific section.
    Returns the raw info string for further parsing. -/
def info (conn : ValkeyConnection) («section» : String := "replication")
    : IO (Except ValkeyError String) := do
  let resp ← sendCommand conn ["INFO", «section»]
  match liftConnectionResult resp with
  | Except.error e => pure (Except.error e)
  | Except.ok v =>
    match v.asString with
    | some s => pure (Except.ok s)
    | none => pure (Except.error (ValkeyError.UnexpectedResponse "expected bulk string"))

/-! ## ROLE Command -/

/-- The detailed role response from the ROLE command.
    Named RoleResult to avoid clashing with Gungnir.K8s.ValkeyRole which
    is the simpler Master/Replica/Unknown enum used by the state machine. -/
inductive RoleResult where
  | Master (replicas : List (String × Nat × Nat))  -- (ip, port, offset)
  | Replica (masterHost : String) (masterPort : Nat) (replState : String) (dataReceived : Nat)
  deriving Repr

/-- Send ROLE command. Returns structured role information.
    Used for promotion verification (features.md [F8]). -/
def role (conn : ValkeyConnection) : IO (Except ValkeyError RoleResult) := do
  let resp ← sendCommand conn ["ROLE"]
  match liftConnectionResult resp with
  | Except.error e => pure (Except.error e)
  | Except.ok v =>
    match v with
    | RESPValue.Array elems =>
      match elems with
      | RESPValue.BulkString "master" :: _rest =>
        -- Master: ["master", <offset>, [[ip, port, offset], ...]]
        pure (Except.ok (RoleResult.Master []))
      | RESPValue.BulkString "slave" :: RESPValue.BulkString masterHost
          :: RESPValue.Integer masterPort :: RESPValue.BulkString replState
          :: RESPValue.Integer dataReceived :: _ =>
        pure (Except.ok (RoleResult.Replica masterHost masterPort.toNat replState dataReceived.toNat))
      | _ => pure (Except.error (ValkeyError.UnexpectedResponse "malformed ROLE response"))
    | _ => pure (Except.error (ValkeyError.UnexpectedResponse "expected array from ROLE"))

/-! ## REPLICAOF Command -/

/-- Result of a REPLICAOF command. -/
inductive ReplicaOfResult where
  | Ok
  deriving Repr, BEq

/-- Send REPLICAOF command to make a node a replica of the given master.
    Used during failover reconfiguration (features.md [F8]). -/
def replicaOf (conn : ValkeyConnection) (host : String) (port : Nat)
    : IO (Except ValkeyError ReplicaOfResult) := do
  let resp ← sendCommand conn ["REPLICAOF", host, toString port]
  match liftConnectionResult resp with
  | Except.error e => pure (Except.error e)
  | Except.ok v =>
    match v with
    | RESPValue.SimpleString "OK" => pure (Except.ok ReplicaOfResult.Ok)
    | _ => pure (Except.error (ValkeyError.UnexpectedResponse "expected OK from REPLICAOF"))

/-- Send REPLICAOF NO ONE to promote a replica to master.
    This is the key command for failover promotion (features.md [F8]). -/
def replicaOfNoOne (conn : ValkeyConnection)
    : IO (Except ValkeyError ReplicaOfResult) := do
  let resp ← sendCommand conn ["REPLICAOF", "NO", "ONE"]
  match liftConnectionResult resp with
  | Except.error e => pure (Except.error e)
  | Except.ok v =>
    match v with
    | RESPValue.SimpleString "OK" => pure (Except.ok ReplicaOfResult.Ok)
    | _ => pure (Except.error (ValkeyError.UnexpectedResponse "expected OK from REPLICAOF NO ONE"))

/-! ## BGSAVE / LASTSAVE Commands -/

/-- Send BGSAVE command to trigger a background RDB save.
    Used for backup operations (features.md [F10]). -/
def bgSave (conn : ValkeyConnection) : IO (Except ValkeyError String) := do
  let resp ← sendCommand conn ["BGSAVE"]
  match liftConnectionResult resp with
  | Except.error e => pure (Except.error e)
  | Except.ok v =>
    match v with
    | RESPValue.SimpleString s => pure (Except.ok s)
    | _ => pure (Except.error (ValkeyError.UnexpectedResponse "expected string from BGSAVE"))

/-- Send LASTSAVE command to get the timestamp of the last successful save.
    Used to verify backup completion (features.md [F10]). -/
def lastSave (conn : ValkeyConnection) : IO (Except ValkeyError Nat) := do
  let resp ← sendCommand conn ["LASTSAVE"]
  match liftConnectionResult resp with
  | Except.error e => pure (Except.error e)
  | Except.ok v =>
    match v with
    | RESPValue.Integer n => pure (Except.ok n.toNat)
    | _ => pure (Except.error (ValkeyError.UnexpectedResponse "expected integer from LASTSAVE"))

/-! ## SET / GET Commands -/

/-- Options for the SET command. -/
structure SetOptions where
  /-- Expire time in seconds -/
  ex : Option Nat := none
  /-- Expire time in milliseconds -/
  px : Option Nat := none
  /-- Only set if key does not exist -/
  nx : Bool := false
  /-- Only set if key already exists -/
  xx : Bool := false
  deriving Repr, BEq

/-- Send SET command with optional expiration and condition.
    Returns true on success, false if NX/XX condition was not met. -/
def set (conn : ValkeyConnection) (key value : String)
    (opts : SetOptions := {}) : IO (Except ValkeyError Bool) := do
  let mut args := ["SET", key, value]
  if let some ex := opts.ex then
    args := args ++ ["EX", toString ex]
  if let some px := opts.px then
    args := args ++ ["PX", toString px]
  if opts.nx then args := args ++ ["NX"]
  if opts.xx then args := args ++ ["XX"]
  let resp ← sendCommand conn args
  match liftConnectionResult resp with
  | Except.error e => pure (Except.error e)
  | Except.ok v =>
    match v with
    | RESPValue.SimpleString "OK" => pure (Except.ok true)
    | RESPValue.Null => pure (Except.ok false)  -- NX/XX condition not met
    | _ => pure (Except.error (ValkeyError.UnexpectedResponse "expected OK or null from SET"))

/-- Send GET command. Returns the value or none if key does not exist. -/
def get (conn : ValkeyConnection) (key : String)
    : IO (Except ValkeyError (Option String)) := do
  let resp ← sendCommand conn ["GET", key]
  match liftConnectionResult resp with
  | Except.error e => pure (Except.error e)
  | Except.ok v =>
    match v with
    | RESPValue.BulkString s => pure (Except.ok (some s))
    | RESPValue.Null => pure (Except.ok none)
    | _ => pure (Except.error (ValkeyError.UnexpectedResponse "expected string or null from GET"))

end Gungnir.Valkey
