import Effect4
import Effect4.Laws

/-! Seat TREE, data probe (2026-10-01): the Schema plane at `bc77e97f`.

1. Axioms of a sample of the plane's laws: the `Ty ↔ Representation` bridge, the JSON codec,
   the concrete images, the representation's admission, documents, the generated fold, the
   annotation keys, and the value judgment the codec should agree with.
2. Five finite facts, each a `#guard` (a finite check, not a theorem):
   the bridge's read is not exact at `number`; a struct has no program type; the JSON codec
   has no object layout; `int` has a schema but no value; a Shape structure has no type.
Scratch, not in the tree. -/

open Effect4 Effect4.Program Effect4.Schema

#print axioms Effect4.Schema.Bridge.ofSchema_schema
#print axioms Effect4.Program.CTy.ofSchema_schema
#print axioms Effect4.Schema.decode_of_encode
#print axioms Effect4.Schema.decode_encode
#print axioms Effect4.Schema.hasTy_decode
#print axioms Effect4.Schema.encode_injective
#print axioms Effect4.Schema.encode_sub
#print axioms Effect4.Schema.ProgramImage.decode_of_encode
#print axioms Effect4.Schema.ProgramImage.decode_exact
#print axioms Effect4.Representation.fieldAdmissible_iff
#print axioms Effect4.Document.toMulti_injective
#print axioms Effect4.hom_eq_cata_representation
#print axioms Effect4.AnnotationKey.Lawful.encode_injective
#print axioms Effect4.EffectfulFieldSpec.annotationKey_lawful
#print axioms Effect4.Program.Typed.fits_sub
#print axioms Effect4.Program.Typed.fits_hasTy

namespace DataProbe.SchemaFacts

/-- `integer ≥ 5`: the minimum is a check payload `ofSchema` never reads (`checkId`,
`Bridge.lean:62-65`). -/
def atLeastFive : Representation :=
  .number none [Bridge.isIntCheck,
    Check.named "effect/schema/isGreaterThanOrEqualTo" (.obj [("minimum", Arch.Json.ofNat 5)])]

-- Fact 1: the read answers `nat`, and `nat`'s schema is not that node: a widening at `number`.
#guard Bridge.ofSchema atLeastFive = some .nat
#guard Bridge.schema .nat ≠ atLeastFive

-- Fact 2: a struct (rc.112 `Schema.Struct`) has no program type.
#guard Bridge.ofSchema (Schema.struct [Schema.property "id" (Bridge.schema .nat)]) = none
#guard Bridge.ofSchema (Schema.tagged "User" [Schema.property "id" (Bridge.schema .nat)]) = none

-- Fact 3: the codec's layout has no object; a pair is an array, an object at a pair refuses.
#guard Ty.encode (.prod .nat .string) (.list [.nat 7, .str "a"]) =
  some (.arr [Arch.Json.ofNat 7, .str "a"])
#guard Ty.decode (.prod .nat .string) (.obj [("id", Arch.Json.ofNat 7), ("name", .str "a")]) = none
#guard Ty.decode (.prod .nat .string) (.arr [Arch.Json.ofNat 7, .str "a"]) =
  some (.list [.nat 7, .str "a"])

-- Fact 4: `int` prints, has a schema and reads back, and no value crosses at it.
#guard Bridge.ofSchema (Bridge.schema .int) = some .int
#guard Ty.encode .int (.nat 3) = none
#guard Ty.decode .int (Arch.Json.ofNat 3) = none

-- Fact 5: the store's structure shape renders to a struct the bridge does not read.
#guard Bridge.ofSchema (Effect4.Store.render (.struct "P" [("x", .nat)])) = none

-- Fact 6: the codec's read is order-free in object fields and its write is not, so it is exact
-- only modulo a field-order normaliser (none is named in the tree).
#guard Ty.decode (.option .nat) (.obj [("value", Arch.Json.ofNat 1), ("_tag", .str "Some")]) =
  some (.some (.nat 1))
#guard Ty.encode (.option .nat) (.some (.nat 1)) =
  some (.obj [("_tag", .str "Some"), ("value", Arch.Json.ofNat 1)])

end DataProbe.SchemaFacts
