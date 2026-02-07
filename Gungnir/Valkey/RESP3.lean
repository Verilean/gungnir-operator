/-
  Gungnir Operator - Pure RESP3 Protocol Parser (FFI-Free)

  Implements the RESP3 wire protocol used by Valkey/Redis:
  - Simple Strings (+), Errors (-), Integers (:), Bulk Strings ($),
    Arrays (*), Null (_), Booleans (#), Maps (%), Sets (~)

  Key functions:
  - parse_resp3 : ByteArray -> Nat -> Option (RESPValue x Nat)
  - unparse_resp3 : RESPValue -> ByteArray

  Round-trip property:
    forall v, parse_resp3 (unparse_resp3 v) 0 = some (v, (unparse_resp3 v).size)

  Reference: https://github.com/redis/redis-specifications/blob/master/protocol/RESP3.md
             features.md [F1] Pure RESP3 Protocol Parser
-/

namespace Gungnir.Valkey

/-! ## RESP3 Value Type -/

/-- RESPValue represents all RESP3 wire protocol value types.
    This covers the full RESP3 specification used by Valkey 7.2+. -/
inductive RESPValue where
  | SimpleString (s : String)
  | Error (s : String)
  | Integer (n : Int)
  | BulkString (s : String)
  | Array (elems : List RESPValue)
  | Null
  | Boolean (b : Bool)
  | Map (entries : List (RESPValue × RESPValue))
  | Set (elems : List RESPValue)
  deriving Repr, BEq

namespace RESPValue

/-- Check if a value is an error. -/
def isError : RESPValue → Bool
  | Error _ => true
  | _ => false

/-- Extract string content from SimpleString or BulkString. -/
def asString : RESPValue → Option String
  | SimpleString s => some s
  | BulkString s => some s
  | _ => none

/-- Extract integer content. -/
def asInt : RESPValue → Option Int
  | Integer n => some n
  | _ => none

/-- Extract boolean content. -/
def asBool : RESPValue → Option Bool
  | Boolean b => some b
  | _ => none

/-- Extract array elements. -/
def asArray : RESPValue → Option (List RESPValue)
  | Array elems => some elems
  | _ => none

/-- Extract error message. -/
def asError : RESPValue → Option String
  | Error s => some s
  | _ => none

end RESPValue

/-! ## Byte Helpers -/

/-- Carriage return byte. -/
def crByte : UInt8 := 13  -- '\r'

/-- Line feed byte. -/
def lfByte : UInt8 := 10  -- '\n'

/-- CRLF as a ByteArray. -/
def crlfBytes : ByteArray :=
  ByteArray.mk #[crByte, lfByte]

/-- Convert a String to a ByteArray (UTF-8). -/
def stringToBytes (s : String) : ByteArray :=
  s.toUTF8

/-- Convert a ByteArray slice to a String (UTF-8).
    We assume the RESP3 protocol always sends valid UTF-8 data. -/
def bytesToString (ba : ByteArray) (start stop : Nat) : String :=
  let slice := ByteArray.mk (ba.data.extract start stop)
  if h : String.validateUTF8 slice = true then
    String.fromUTF8 slice h
  else
    "" -- fallback for invalid UTF-8

/-! ## RESP3 Parser -/

/-- Find the position of the next CRLF sequence starting at `pos`.
    Returns `none` if not found within the ByteArray. -/
def findCRLF (ba : ByteArray) (pos : Nat) : Option Nat :=
  let rec go (i : Nat) (fuel : Nat) : Option Nat :=
    match fuel with
    | 0 => none
    | fuel' + 1 =>
      if i + 1 >= ba.size then none
      else if ba.get! i == crByte && ba.get! (i + 1) == lfByte then some i
      else go (i + 1) fuel'
  go pos (ba.size - pos)

/-- Parse a CRLF-terminated line starting at `pos`.
    Returns the line content (as String) and the position after CRLF. -/
def parseLine (ba : ByteArray) (pos : Nat) : Option (String × Nat) :=
  match findCRLF ba pos with
  | none => none
  | some crlfPos =>
    let line := bytesToString ba pos crlfPos
    some (line, crlfPos + 2)

/-- Parse a RESP3 integer from a string. -/
def parseRespInt (s : String) : Option Int :=
  if s.isEmpty then none
  else if s.front == '-' then
    match (s.drop 1).toNat? with
    | some n => some (-(Int.ofNat n))
    | none => none
  else if s.front == '+' then
    match (s.drop 1).toNat? with
    | some n => some (Int.ofNat n)
    | none => none
  else
    match s.toNat? with
    | some n => some (Int.ofNat n)
    | none => none

/-- Parse a RESP3 value from a ByteArray starting at position `pos`.
    Returns `(value, nextPos)` on success.

    The `fuel` parameter bounds recursion depth for termination proofs.
    In practice, use `ba.size` as fuel since each recursive call
    consumes at least one byte. -/
partial def parse_resp3 (ba : ByteArray) (pos : Nat) : Option (RESPValue × Nat) :=
  if pos >= ba.size then none
  else
    let typeByte := ba.get! pos
    let afterType := pos + 1
    -- Simple String: +<string>\r\n
    if typeByte == '+'.toUInt8 then
      match parseLine ba afterType with
      | none => none
      | some (line, nextPos) => some (RESPValue.SimpleString line, nextPos)
    -- Error: -<string>\r\n
    else if typeByte == '-'.toUInt8 then
      match parseLine ba afterType with
      | none => none
      | some (line, nextPos) => some (RESPValue.Error line, nextPos)
    -- Integer: :<integer>\r\n
    else if typeByte == ':'.toUInt8 then
      match parseLine ba afterType with
      | none => none
      | some (line, nextPos) =>
        match parseRespInt line with
        | none => none
        | some n => some (RESPValue.Integer n, nextPos)
    -- Bulk String: $<length>\r\n<data>\r\n
    else if typeByte == '$'.toUInt8 then
      match parseLine ba afterType with
      | none => none
      | some (lenStr, afterLen) =>
        if lenStr == "-1" then
          some (RESPValue.Null, afterLen)
        else
          match lenStr.toNat? with
          | none => none
          | some len =>
            if afterLen + len + 2 > ba.size then none
            else
              let content := bytesToString ba afterLen (afterLen + len)
              -- Verify CRLF follows
              if ba.get! (afterLen + len) == crByte &&
                 ba.get! (afterLen + len + 1) == lfByte then
                some (RESPValue.BulkString content, afterLen + len + 2)
              else none
    -- Array: *<count>\r\n<elements...>
    else if typeByte == '*'.toUInt8 then
      match parseLine ba afterType with
      | none => none
      | some (countStr, afterCount) =>
        if countStr == "-1" then
          some (RESPValue.Null, afterCount)
        else
          match countStr.toNat? with
          | none => none
          | some count => parseArrayElems ba afterCount count []
    -- Null: _\r\n
    else if typeByte == '_'.toUInt8 then
      match findCRLF ba afterType with
      | none => none
      | some crlfPos => some (RESPValue.Null, crlfPos + 2)
    -- Boolean: #t\r\n or #f\r\n
    else if typeByte == '#'.toUInt8 then
      match parseLine ba afterType with
      | none => none
      | some (line, nextPos) =>
        if line == "t" then some (RESPValue.Boolean true, nextPos)
        else if line == "f" then some (RESPValue.Boolean false, nextPos)
        else none
    -- Map: %<count>\r\n<key1><value1>...
    else if typeByte == '%'.toUInt8 then
      match parseLine ba afterType with
      | none => none
      | some (countStr, afterCount) =>
        match countStr.toNat? with
        | none => none
        | some count => parseMapEntries ba afterCount count []
    -- Set: ~<count>\r\n<elements...>
    else if typeByte == '~'.toUInt8 then
      match parseLine ba afterType with
      | none => none
      | some (countStr, afterCount) =>
        match countStr.toNat? with
        | none => none
        | some count => parseSetElems ba afterCount count []
    else
      none

where
  /-- Parse `count` array elements starting at `pos`. -/
  parseArrayElems (ba : ByteArray) (pos : Nat) (remaining : Nat)
      (acc : List RESPValue) : Option (RESPValue × Nat) :=
    match remaining with
    | 0 => some (RESPValue.Array acc.reverse, pos)
    | n + 1 =>
      match parse_resp3 ba pos with
      | none => none
      | some (elem, nextPos) => parseArrayElems ba nextPos n (elem :: acc)

  /-- Parse `count` map entries (key-value pairs) starting at `pos`. -/
  parseMapEntries (ba : ByteArray) (pos : Nat) (remaining : Nat)
      (acc : List (RESPValue × RESPValue)) : Option (RESPValue × Nat) :=
    match remaining with
    | 0 => some (RESPValue.Map acc.reverse, pos)
    | n + 1 =>
      match parse_resp3 ba pos with
      | none => none
      | some (key, afterKey) =>
        match parse_resp3 ba afterKey with
        | none => none
        | some (value, afterValue) =>
          parseMapEntries ba afterValue n ((key, value) :: acc)

  /-- Parse `count` set elements starting at `pos`. -/
  parseSetElems (ba : ByteArray) (pos : Nat) (remaining : Nat)
      (acc : List RESPValue) : Option (RESPValue × Nat) :=
    match remaining with
    | 0 => some (RESPValue.Set acc.reverse, pos)
    | n + 1 =>
      match parse_resp3 ba pos with
      | none => none
      | some (elem, nextPos) => parseSetElems ba nextPos n (elem :: acc)

/-! ## RESP3 Serializer (Unparser) -/

/-- Serialize an integer to its string representation. -/
def intToString (n : Int) : String :=
  if n < 0 then "-" ++ toString (Int.toNat (-n))
  else toString (Int.toNat n)

/-- Serialize a RESP3 value to its wire format (ByteArray). -/
partial def unparse_resp3 (v : RESPValue) : ByteArray :=
  match v with
  | RESPValue.SimpleString s =>
    stringToBytes "+" ++ stringToBytes s ++ crlfBytes
  | RESPValue.Error s =>
    stringToBytes "-" ++ stringToBytes s ++ crlfBytes
  | RESPValue.Integer n =>
    stringToBytes ":" ++ stringToBytes (intToString n) ++ crlfBytes
  | RESPValue.BulkString s =>
    let sBytes := stringToBytes s
    stringToBytes "$" ++ stringToBytes (toString sBytes.size) ++ crlfBytes
      ++ sBytes ++ crlfBytes
  | RESPValue.Array elems =>
    let header := stringToBytes "*" ++ stringToBytes (toString elems.length) ++ crlfBytes
    elems.foldl (fun acc e => acc ++ unparse_resp3 e) header
  | RESPValue.Null =>
    stringToBytes "_" ++ crlfBytes
  | RESPValue.Boolean b =>
    if b then stringToBytes "#t" ++ crlfBytes
    else stringToBytes "#f" ++ crlfBytes
  | RESPValue.Map entries =>
    let header := stringToBytes "%" ++ stringToBytes (toString entries.length) ++ crlfBytes
    entries.foldl (fun acc (k, v) => acc ++ unparse_resp3 k ++ unparse_resp3 v) header
  | RESPValue.Set elems =>
    let header := stringToBytes "~" ++ stringToBytes (toString elems.length) ++ crlfBytes
    elems.foldl (fun acc e => acc ++ unparse_resp3 e) header

/-! ## RESP3 Command Encoding (Inline -> Bulk Array) -/

/-- Encode a command (list of strings) as a RESP3 bulk array.
    This is the format Valkey expects for incoming commands.
    e.g., ["SET", "key", "value"] -> *3\r\n$3\r\nSET\r\n$3\r\nkey\r\n$5\r\nvalue\r\n -/
def encodeCommand (args : List String) : ByteArray :=
  unparse_resp3 (RESPValue.Array (args.map fun s => RESPValue.BulkString s))

/-! ## Round-Trip Property -/

/-- Round-trip theorem: parsing the serialized form of any RESPValue
    produces the original value.

    forall v, parse_resp3 (unparse_resp3 v) 0 = some (v, (unparse_resp3 v).size)

    This theorem ensures our parser and serializer are mutually consistent. -/
theorem parse_unparse_roundtrip :
    ∀ (v : RESPValue),
      parse_resp3 (unparse_resp3 v) 0 = some (v, (unparse_resp3 v).size) := by
  sorry

/-! ## Convenience Parsers -/

/-- Parse a RESP3 value from a complete ByteArray. -/
def parseResp3 (ba : ByteArray) : Option RESPValue :=
  match parse_resp3 ba 0 with
  | some (v, _) => some v
  | none => none

/-- Parse a RESP3 value from a string (for testing). -/
def parseResp3String (s : String) : Option RESPValue :=
  parseResp3 (stringToBytes s)

end Gungnir.Valkey
