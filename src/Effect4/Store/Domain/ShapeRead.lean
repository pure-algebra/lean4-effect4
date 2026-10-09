module

public import Effect4.Store.Domain.Canonical
meta import Effect4.Data.Json
meta import Effect4.Store.Carrier.Digest
meta import Effect4.Store.Carrier.Val

/-!
# Store.ShapeRead — reading a canonical carrier back from its JSON print

`ShapeDoc.print` (`Store/Domain/Shape.lean`) writes a value tree as JSON, the names from the shape
and the structure from the value. This module reads that JSON back, under the same shape. It is
the schema form an agent can write: a program, a type or a row as JSON, instead of canonical
bytes.

**The reader accepts only the canonical print.** Each case checks that the JSON is what the
printer writes for the value it reads: a number is the binary64 of a natural, hex is lowercase
and exact, a field list is the shape's in order, a case name names the case its tag prints. So
whatever reads is that value's print, with no fragment condition (`readIn_exact`,
`Laws/Store/ShapeRead.lean`).

**The round trip has a fragment.** JSON numbers are binary64, so a natural above 2^53 prints
inexactly. An option is invisible in JSON (`some a` prints as `a`), so an option of a shape that
prints `null` is ambiguous. On values with neither, reading the print gives the value back.

**A budget bounds the steps.** The shape alone says how many option layers to unwrap, and a
cyclic definition could unwrap forever. So each step, a JSON node, a list or field cell, or an
option layer, takes one from a budget, and the readers are structural on it. The exactness law
holds at every budget.
-/

@[expose] public section

set_option autoImplicit false

namespace Effect4.Store

open Effect4 (Json Float64)

/-- The natural a positive binary64 integer datum stands for, by its exponent and significand; a
candidate only, which `natOfBinary64` checks. -/
def natCandidate (bits : UInt64) : Nat :=
  let b := bits.toNat
  let e := b / 2 ^ 52
  let sig := b % 2 ^ 52 + 2 ^ 52
  if b = 0 then 0
  else if 1023 + 52 ≤ e then sig * 2 ^ (e - (1023 + 52)) else sig / 2 ^ ((1023 + 52) - e)

/-- **The natural a binary64 datum spells**, where the datum is a non-negative finite binary64
(a pattern below `binary64Infinity`) and is the binary64 of that natural (`binary64OfNat`). Its
domain is the naturals binary64 holds exactly: below 2^1024, with at most 53 significant bits,
every natural up to 2^53 among them (the MCP face's profile is the naturals up to 2^53). A
negative or non-finite datum, a fraction and an inexact spelling read as none, so the natural
read is the number a binary64 host reads (`natOfBinary64_finite`). -/
def natOfBinary64 (bits : UInt64) : Option Nat :=
  if bits.toNat < Effect4.Arch.binary64Infinity ∧
      Effect4.Arch.binary64OfNat (natCandidate bits) = bits then
    some (natCandidate bits)
  else none

/-- **Bytes from their hex spelling**, where the spelling is the canonical one (`hexString`). The
spelling is read through its UTF-8 bytes, since a hex digit is one ASCII byte: a traversal of the
`String` as characters would reach `Classical.choice` through Lean's UTF-8 decoding. -/
def canonicalHex? (h : String) : Option Bytes :=
  (bytesOfHexCodes (h.toUTF8.toList.map (·.toNat))).bind fun d =>
    if hexString d = h then some d else none

/-- **The wire tag of a case name**, where the tag's case is that name: the first case with the
name, checked against `caseAt`, which the printer reads. -/
def tagOfName (name : String) (cases : List (String × Nat × List (String × Shape))) :
    Option (Nat × List (String × Shape)) :=
  (cases.find? fun c => decide (c.1 = name)).bind fun (_, tag, _) =>
    match caseAt tag cases with
    | some (name', fields) => if name' = name then some (tag, fields) else none
    | none => none

mutual
/-- **Read a value tree under a shape** from its JSON print; none where the JSON is not the
canonical print of a value fitting the shape's head. `budget` bounds the steps: each JSON node,
each list or field cell, and each option layer takes one. -/
def readIn (defs : List (String × Shape)) : Nat → Shape → Json → Option Val
  | 0, _, _ => none
  | n + 1, s, j =>
    match headShape defs s, j with
    | .unit, .null => some .unit
    | .option _, .null => some .none
    | .option item, j' => (readIn defs n item j').map .some
    | .bool, .bool b => some (.bool b)
    | .nat, .number x => (natOfBinary64 x.bits).map .nat
    | .string, .str t => some (.str t)
    | .bytes, .str h => (canonicalHex? h).map .bytes
    | .digest, .str h => (canonicalHex? h).map .bytes
    | .list item, .arr js => (readList defs n item js).map .list
    | .pair f g, .arr [a, b] =>
      (readIn defs n f a).bind fun x => (readIn defs n g b).map fun y => .pair x y
    | .struct _ fields, .obj entries => (readFields defs n fields entries).map (.ctor 0)
    | .sum _ cases, .str name =>
      if allNullary cases then
        (tagOfName name cases).bind fun (tag, fields) =>
          if fields.isEmpty then some (.ctor tag []) else none
      else none
    | .sum _ cases, .obj (("_tag", .str name) :: entries) =>
      if allNullary cases then none
      else (tagOfName name cases).bind fun (tag, fields) =>
        (readFields defs n fields entries).map (.ctor tag)
    | .ref k, .str h => (canonicalHex? h).map (.ref k.byte)
    | .anyRef, .obj [("kind", .str kn), ("address", .str h)] =>
      (Kind.ofName? kn).bind fun k =>
        if kindJson k.byte = .str kn then (canonicalHex? h).map (.ref k.byte) else none
    | _, _ => none

/-- Read the elements of a list, each under the item shape. -/
def readList (defs : List (String × Shape)) : Nat → Shape → List Json → Option (List Val)
  | 0, _, _ => none
  | _ + 1, _, [] => some []
  | n + 1, item, j :: js => (readIn defs n item j).bind fun x => (readList defs n item js).map (x :: ·)

/-- Read the fields of a struct or a case: the shape's names, in its order, and no other. -/
def readFields (defs : List (String × Shape)) :
    Nat → List (String × Shape) → List (String × Json) → Option (List Val)
  | 0, _, _ => none
  | _ + 1, [], [] => some []
  | n + 1, (k, s) :: fields, (k', j) :: entries =>
    if k' = k then
      (readIn defs n s j).bind fun x => (readFields defs n fields entries).map (x :: ·)
    else none
  | _ + 1, _, _ => none
end

mutual
/-- The nodes of a JSON value: the normaliser's budget. -/
def jsonNodes : Json → Nat
  | .arr js => 1 + listNodes js
  | .obj entries => 1 + entryNodes entries
  | _ => 1

/-- The nodes of a list of JSON values. -/
def listNodes : List Json → Nat
  | [] => 0
  | j :: js => jsonNodes j + listNodes js

/-- The nodes of an object's entries. -/
def entryNodes : List (String × Json) → Nat
  | [] => 0
  | (_, j) :: entries => jsonNodes j + entryNodes entries
end

/-- The entry of an object with a name: the first. -/
def entryOf (name : String) : List (String × Json) → Option Json
  | [] => none
  | (n, j) :: rest => if n = name then some j else entryOf name rest

mutual
/-- **Put each object's entries in its shape's field order**, under a shape: JSON objects are
unordered, and the canonical print orders a structure's fields, and a case's after its `_tag`, by
declaration. The named normaliser of the JSON form: an agent's JSON reads once ordered
(`Canonical.ofJsonAnyOrder`). An object that lacks a field, or holds another, is left as it is,
and reads as none. `fuel` bounds the nodes visited; past it the JSON is left as it is. -/
def orderIn (defs : List (String × Shape)) : Nat → Shape → Json → Json
  | 0, _, j => j
  | fuel + 1, s, j =>
    match headShape defs s, j with
    | .option _, .null => .null
    | .option item, j' => orderIn defs fuel item j'
    | .list item, .arr js => .arr (orderList defs fuel item js)
    | .pair f g, .arr [a, b] => .arr [orderIn defs fuel f a, orderIn defs fuel g b]
    | .struct _ fields, .obj entries =>
      match orderFields defs fuel fields entries with
      | some ordered => if ordered.length = entries.length then .obj ordered else .obj entries
      | none => .obj entries
    | .sum _ cases, .obj entries =>
      match entryOf "_tag" entries with
      | some (.str name) =>
        match tagOfName name cases with
        | some (_, fields) =>
          match orderFields defs fuel fields entries with
          | some ordered =>
            if ordered.length + 1 = entries.length then .obj (("_tag", .str name) :: ordered)
            else .obj entries
          | none => .obj entries
        | none => .obj entries
      | _ => .obj entries
    | _, j' => j'

/-- Order the elements of a list, each under the item shape. -/
def orderList (defs : List (String × Shape)) : Nat → Shape → List Json → List Json
  | 0, _, js => js
  | _ + 1, _, [] => []
  | fuel + 1, item, j :: js => orderIn defs fuel item j :: orderList defs fuel item js

/-- The shape's fields, each looked up by name among the entries and ordered under its shape;
none where an entry is missing. -/
def orderFields (defs : List (String × Shape)) :
    Nat → List (String × Shape) → List (String × Json) → Option (List (String × Json))
  | _, [], _ => some []
  | 0, _ :: _, _ => none
  | fuel + 1, (n, s) :: fields, entries =>
    match entryOf n entries with
    | some j => (orderFields defs fuel fields entries).map ((n, orderIn defs fuel s j) :: ·)
    | none => none
end

/-- The budget the readers below give a JSON value: eight steps a node, and 64 more. -/
def readBudget (j : Json) : Nat := 8 * jsonNodes j + 64

/-- **Read a value tree under a shape document** from its JSON print. -/
def ShapeDoc.read (doc : ShapeDoc) (j : Json) : Option Val :=
  readIn doc.defs (readBudget j) doc.root j

/-- **Read a canonical carrier from its JSON print** (`Canonical.print`). -/
def Canonical.ofJson {α : Type} [Canonical α] (j : Json) : Option α :=
  ((Canonical.shape α).read j).bind Canonical.ofVal

/-- **Order a document's JSON**: `orderIn` under its root. -/
def ShapeDoc.order (doc : ShapeDoc) (j : Json) : Json :=
  orderIn doc.defs (readBudget j) doc.root j

/-- **Read a canonical carrier from JSON whose objects may be in any order**: the JSON ordered
by the carrier's shape (`ShapeDoc.order`), then read. -/
def Canonical.ofJsonAnyOrder {α : Type} [Canonical α] (j : Json) : Option α :=
  Canonical.ofJson ((Canonical.shape α).order j)

end Effect4.Store
