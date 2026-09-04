import Effect4.Store.Canonical
import Effect4.Codegen.Schema

/-!
# Arch.JsonCanonical

Owner: the canonical bytes of a JSON value, and through them of a persisted
Schema representation and document — so a schema is a store entry with an
address like any other value.

A `Json` value is encoded structurally with the store's framing; a
`Representation` or a `Document` is encoded through its *persisted* JSON form,
the same form the generated module hands to `SchemaRepresentation.fromJson`
(`Effect4/Target/TypeScript/Schema.lean`): `representation`/`documentExpr`
spell it as target syntax and `reifyJson?` reads that syntax back as `Json`.
One persisted form, addressed once. `reifyJson?` covers exactly the syntax
those spellers emit, so the `Option` is always `some` in practice; the encoder
is total by encoding the `Option`.
-/

namespace Effect4.Arch

open Effect4.Store

/-! The tags of the JSON frames, above the store's own. -/
namespace JsonTag
def null : UInt8 := 16
def bool : UInt8 := 17
def number : UInt8 := 18
def str : UInt8 := 19
def arr : UInt8 := 20
def obj : UInt8 := 21
def entry : UInt8 := 22
end JsonTag

mutual
  /-- The canonical bytes of a JSON value: a number is its binary64 bits, a
  string its UTF-8 bytes, an object its entries in order with duplicates kept. -/
  def jsonBytes : Json → Bytes
    | .null => framed JsonTag.null []
    | .bool b => framed JsonTag.bool [if b then 1 else 0]
    | .number v => framed JsonTag.number (be64 v.bits.toNat)
    | .str s => framed JsonTag.str s.toUTF8.data.toList
    | .arr xs => framed JsonTag.arr (jsonListBytes xs)
    | .obj es => framed JsonTag.obj (jsonEntriesBytes es)
  termination_by structural v => v

  def jsonListBytes : List Json → Bytes
    | [] => []
    | x :: xs => jsonBytes x ++ jsonListBytes xs
  termination_by structural l => l

  def jsonEntriesBytes : List (String × Json) → Bytes
    | [] => []
    | (k, v) :: es => framed JsonTag.entry k.toUTF8.data.toList ++ jsonBytes v ++ jsonEntriesBytes es
  termination_by structural l => l
end

instance : Canonical Json := ⟨jsonBytes⟩

/-- The index of the highest set bit, with the number as its own fuel. -/
def highestBit (n : Nat) : Nat :=
  go n n 0
where
  go : Nat → Nat → Nat → Nat
    | 0, _, acc => acc
    | fuel + 1, m, acc => if m < 2 then acc else go fuel (m / 2) (acc + 1)

/-- The binary64 bit pattern of a natural, exact below 2^53 and truncated
toward zero above it: sign 0, biased exponent `1023 + e` where `e` is the
highest bit, and the 52 bits after it as the significand. Built from the
number's bits alone, so it reaches no `Float` primitive and no axiom. -/
def binary64OfNat (n : Nat) : UInt64 :=
  if n = 0 then 0
  else
    let e := highestBit n
    let significand := if e ≤ 52 then (n <<< (52 - e)) - (1 <<< 52) else (n >>> (e - 52)) - (1 <<< 52)
    UInt64.ofNat (((1023 + e) <<< 52) + significand)

/-- A JSON number from a natural: the binary64 the host would parse. -/
def Json.ofNat (n : Nat) : Json := .number ⟨binary64OfNat n⟩

/-- The persisted JSON form of a representation. -/
def Representation.toJson? (value : Representation) : Option Json :=
  Codegen.Schema.reifyJson? (Codegen.Schema.representation value)

/-- The persisted JSON form of a document. -/
def Document.toJson? (document : Document) : Option Json :=
  Codegen.Schema.reifyJson? (Codegen.Schema.documentExpr document)

/-- A representation is addressed by its persisted form. -/
instance : Canonical Representation := ⟨fun value => encode (Representation.toJson? value)⟩

/-- A document is addressed by its persisted form. -/
instance : Canonical Document := ⟨fun document => encode (Document.toJson? document)⟩

end Effect4.Arch
