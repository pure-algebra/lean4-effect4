module

public import Effect4.Data.Ascii
public import Init.Data.Nat.ToString
meta import Effect4.Data.Ascii

/-!
# Data.NatJson — the tool profile's JSON tree: numbers are naturals

Owner: the JSON tree the tool's profile reads and prints (`Tool.CodecProfile`), the steps of a
path into it, the place a reader refuses at, and its compact text.

- **`NatJson`** is JSON whose numbers are naturals. The raw tree `Effect4.Json`
  (`Data/Json.lean`) holds a number as a binary64 datum; this tree holds the natural itself, so
  the OCaml route lowers it with no binary64 arithmetic. A JSON number that the tree does not
  hold as a natural (a negative number, a fraction, an exponent, or a natural past the host's
  integers) is a `numeral` with the text it was written in, and every reader refuses it at its
  place. `safeBound` is the largest natural the profile reads.
- **`JsonStep`** is one step into a value: an object's entry by its key, or an array's element
  by its index. `NatJson.at?` follows a path of steps. A key reaches the object's first entry
  with that name, as every reader of an entry does.
- **`JsonSite`** is where a reader refuses: a value at a path, a field missing from the object
  at a path, or a place in the shape. A refusal pairs a site with a reason (`Data/Located.lean`);
  the reasons are the reader's own (`Store.JsonReason`).
- **`NatJson.render`** is the compact text, as bytes: no white space, `"` and `\` escaped, the
  control bytes 8, 9, 10, 12 and 13 by their letters, every other byte below 32 as `\u00xx`, and
  every other byte as it is, so UTF-8 passes through. A string is read through its UTF-8 bytes
  (`Ascii.bytesOf`), never by its characters, which would reach `Classical.choice`.

Nothing here reads a shape. The reader and the printer under a shape document are
`Store/Domain/ShapeJson.lean`.
-/

@[expose] public section

set_option autoImplicit false

namespace Effect4

/-- **The profile's JSON tree**: JSON whose numbers are naturals. An object's entries are an
ordered list, so a repeated key stays visible until a reader refuses it. -/
inductive NatJson where
  /-- The JSON `null` literal. -/
  | null
  /-- A JSON boolean. -/
  | bool (value : Bool)
  /-- A JSON number that is a natural. -/
  | nat (value : Nat)
  /-- A JSON number the tree does not hold as a natural, by its text: a negative number, a
  fraction, an exponent, or a natural past the host's integers. A binary64 datum that spells no
  natural carries no text. -/
  | numeral (text : String)
  /-- A JSON string. -/
  | str (value : String)
  /-- A JSON array, in order. -/
  | arr (elements : List NatJson)
  /-- A JSON object: its entries in order, a repeated key kept. -/
  | obj (entries : List (String × NatJson))
deriving Inhabited

/-- **One step into a JSON value**: an object's entry by its key, or an array's element by its
index. -/
inductive JsonStep where
  | key (name : String)
  | index (n : Nat)
deriving DecidableEq

/-- **Where a JSON reader refuses**: the value at a path; a field missing from the object at a
path, which is present; or a place in the shape, when the shape itself is refused. -/
inductive JsonSite where
  | value (path : List JsonStep)
  | missing (parent : List JsonStep) (field : String)
  | schema (path : List JsonStep)
deriving DecidableEq

/-- Whether two steps are one: the same key, or the same index. -/
def JsonStep.same : JsonStep → JsonStep → Bool
  | .key a, .key b => decide (a = b)
  | .index m, .index n => decide (m = n)
  | _, _ => false

/-- The rest of a path after a prefix, where the path starts with it. -/
def JsonStep.stripPrefix? : List JsonStep → List JsonStep → Option (List JsonStep)
  | [], path => some path
  | b :: base, s :: path => if JsonStep.same b s then stripPrefix? base path else none
  | _ :: _, [] => none

/-- **A site relative to a base path**: the site with the base removed from the front of its
path, where its path starts with the base; any other site as it is. A shell that writes the
agent's part at the base reports a refusal in that part by it. -/
def JsonSite.relative (base : List JsonStep) : JsonSite → JsonSite
  | .value path =>
    match JsonStep.stripPrefix? base path with
    | some rest => .value rest
    | none => .value path
  | .missing parent field =>
    match JsonStep.stripPrefix? base parent with
    | some rest => .missing rest field
    | none => .missing parent field
  | .schema path => .schema path

/-- **The safe integer bound**, `2^53 - 1`: the largest natural every JSON client reads exactly
(I-JSON's safe integer bound, RFC 7493 §2.2), JavaScript's `Number.MAX_SAFE_INTEGER`. It is the one
spelling of the number. The rc.112 profile's bound is `some safeBound` (`Program.rc112`; a
profile's bound has one owner, `ProfileData.natBound`). The tool's JSON reads naturals up to it
(`Store.ShapeJson`), and the schema's natural and integer wires write inside it
(`Schema.Codec`). -/
def safeBound : Nat := 9007199254740991

namespace NatJson

/-- The entry of an object with a name: the first. -/
def entryOf (name : String) : List (String × NatJson) → Option NatJson
  | [] => none
  | (n, t) :: rest => if n = name then some t else entryOf name rest

/-- **The value at a path**, if the path reaches one: a key reaches an object's first entry with
that name, an index an array's element. -/
def at? (t : NatJson) : List JsonStep → Option NatJson
  | [] => some t
  | .key k :: rest =>
    match t with
    | .obj entries => (entryOf k entries).bind fun t' => at? t' rest
    | _ => none
  | .index i :: rest =>
    match t with
    | .arr elements => elements[i]?.bind fun t' => at? t' rest
    | _ => none

/-! ## The compact text, as bytes -/

/-- The UTF-8 bytes of a string, as numbers: the lowered route has no `UInt8` arithmetic. -/
def codes (s : String) : List Nat := (Data.Ascii.bytesOf s).map (·.toNat)

/-- Whether a numeral's text is a natural's: digits only, at least one. -/
def allDigits (text : String) : Bool :=
  let cs := codes text
  !cs.isEmpty && cs.all fun c => 48 ≤ c && c ≤ 57

/-- A hexadecimal digit, lowercase. -/
def hexDigit (d : Nat) : Nat := if d < 10 then 48 + d else 87 + d

/-- One byte of a string's content as the text writes it. -/
def escapeByte (c : Nat) : List Nat :=
  if c = 34 then [92, 34]
  else if c = 92 then [92, 92]
  else if c = 10 then [92, 110]
  else if c = 13 then [92, 114]
  else if c = 9 then [92, 116]
  else if c = 8 then [92, 98]
  else if c = 12 then [92, 102]
  else if c < 32 then [92, 117, 48, 48, hexDigit (c / 16), hexDigit (c % 16)]
  else [c]

/-- A string's content bytes, escaped, before the rest of the text. -/
def escapeTo : List Nat → List Nat → List Nat
  | [], rest => rest
  | c :: cs, rest => escapeByte c ++ escapeTo cs rest

/-- A string quoted, before the rest of the text. -/
def quotedTo (s : String) (rest : List Nat) : List Nat := 34 :: escapeTo (codes s) (34 :: rest)

mutual
/-- **The compact text of a value**, before the rest of the text. -/
def renderTo : NatJson → List Nat → List Nat
  | .null, rest => 110 :: 117 :: 108 :: 108 :: rest
  | .bool b, rest => (if b then [116, 114, 117, 101] else [102, 97, 108, 115, 101]) ++ rest
  | .nat n, rest => codes (Nat.repr n) ++ rest
  | .numeral text, rest => codes text ++ rest
  | .str s, rest => quotedTo s rest
  | .arr [], rest => 91 :: 93 :: rest
  | .arr (t :: ts), rest => 91 :: renderTo t (renderItems ts (93 :: rest))
  | .obj [], rest => 123 :: 125 :: rest
  | .obj ((k, t) :: entries), rest =>
    123 :: quotedTo k (58 :: renderTo t (renderEntries entries (125 :: rest)))

/-- The elements after the first, each after a comma. -/
def renderItems : List NatJson → List Nat → List Nat
  | [], rest => rest
  | t :: ts, rest => 44 :: renderTo t (renderItems ts rest)

/-- The entries after the first, each after a comma. -/
def renderEntries : List (String × NatJson) → List Nat → List Nat
  | [], rest => rest
  | (k, t) :: entries, rest => 44 :: quotedTo k (58 :: renderTo t (renderEntries entries rest))
end

/-- **The compact text of a value**, as its bytes. -/
def render (t : NatJson) : List Nat := renderTo t []

-- Finite evaluations of the text: the six forms, the escapes, and UTF-8 passed through.
#guard render (.obj [("a", .arr [.nat 1, .null, .bool true]), ("b", .str "x")]) =
  codes "{\"a\":[1,null,true],\"b\":\"x\"}"
#guard render (.arr []) = codes "[]" && render (.obj []) = codes "{}"
#guard render (.str "q\"b\\n\n\t\x01\x7f") = codes "\"q\\\"b\\\\n\\n\\t\\u0001\x7f\""
#guard render (.str "é") = [34, 0xC3, 0xA9, 34]
#guard render (.numeral "-1.5e3") = codes "-1.5e3"
#guard allDigits "123" && !allDigits "" && !allDigits "-1" && !allDigits "1.5"
#guard (NatJson.obj [("k", .arr [.nat 1, .nat 2])]).at? [.key "k", .index 1] matches some (.nat 2)
#guard (NatJson.obj [("k", .nat 1), ("k", .nat 2)]).at? [.key "k"] matches some (.nat 1)
#guard (NatJson.arr [.nat 1]).at? [.index 1] matches none

end NatJson

end Effect4
