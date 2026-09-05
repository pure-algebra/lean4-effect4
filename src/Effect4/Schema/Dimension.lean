import Effect4.Schema.Annotations

/-!
# Schema.Dimension — the `effect4/codegen` annotation key

`docs/SCHEMA-ANNOTATIONS.md` gives the host side a `withCodegen` combinator whose payload is
a codegen dimension: what a schema should become in generated code, over and above what its
representation says. This module is the Lean side of that key, typed and lawful like the
rc.112 standard keys of `src/Effect4/Surface/Annotate.lean`, and read by the emitters:

* `typeName` is the name generated code binds the schema to when it is not an entity;
* `brand`, when present, is the nominal narrowing: `Schema.String.pipe(Schema.brand("UserId"))`
  in TypeScript (`Schema.ts:5242`), `type user_id = private string` in OCaml. A brand adds no
  runtime check, so the JSON Schema and the persisted representation are unchanged by it,
  which is exactly what rc.112 says of `brand`.

The host record also carries `version`. It is deliberately not a field here: a `Nat` has no
kernel-reducible lawful encoding into `Json` in this tree (`src/Effect4/Surface/Annotate.lean`'s
header records the same decision for `SurfaceMark`), and codegen reads nothing off it. A bag
whose payload carries other fields does not decode, by exactness; the row that reconciles
the two records is `binary64OfNat`'s inverse and its theorem, owed.

`Lawful` is bought the way `markKey` buys it: `decode` re-encodes what it parsed and answers
only when the bytes agree, so exactness is `rfl`-shaped and the forward law is one case split.
-/

namespace Effect4.Schema

/-- What a schema should become in generated code. -/
structure CodegenDimension where
  /-- The name generated code binds the schema to. -/
  typeName : String
  /-- The nominal brand, when the schema is branded. -/
  brand : Option String := none
deriving DecidableEq, Repr, Inhabited

namespace CodegenDimension

/-- The payload: `typeName` always, `brand` when present, in that order. -/
def encode (dimension : CodegenDimension) : Json :=
  .obj
    ([("typeName", .str dimension.typeName)] ++
      (match dimension.brand with
       | some brand => [("brand", .str brand)]
       | none => []))

/-- A left inverse of `encode`. -/
def parse? : Json → Option CodegenDimension
  | .obj [("typeName", .str typeName)] => some ⟨typeName, none⟩
  | .obj [("typeName", .str typeName), ("brand", .str brand)] => some ⟨typeName, some brand⟩
  | _ => none

/-- `parse?` recovers every dimension it is handed the encoding of. -/
theorem parse?_encode (dimension : CodegenDimension) : parse? dimension.encode = some dimension := by
  cases dimension with
  | mk typeName brand => cases brand <;> rfl

end CodegenDimension

/-- The `effect4/codegen` key. -/
def codegenKey : AnnotationKey CodegenDimension where
  name := "effect4/codegen"
  encode := CodegenDimension.encode
  decode := fun raw =>
    match CodegenDimension.parse? raw with
    | some dimension => if CodegenDimension.encode dimension = raw then some dimension else none
    | none => none

/-- The key is an exact typed view of its payload. -/
theorem codegenKey_lawful : codegenKey.Lawful := by
  constructor
  · intro value
    show (match CodegenDimension.parse? value.encode with
      | some dimension =>
        if CodegenDimension.encode dimension = value.encode then some dimension else none
      | none => none) = some value
    rw [CodegenDimension.parse?_encode value]
    simp
  · intro raw value decoded
    show CodegenDimension.encode value = raw
    revert decoded
    show (match CodegenDimension.parse? raw with
      | some dimension =>
        if CodegenDimension.encode dimension = raw then some dimension else none
      | none => none) = some value → CodegenDimension.encode value = raw
    cases parsed : CodegenDimension.parse? raw with
    | none => simp
    | some dimension =>
      show (if CodegenDimension.encode dimension = raw then some dimension else none) =
          some value → CodegenDimension.encode value = raw
      split
      · next guard => intro answer; rw [← Option.some.inj answer]; exact guard
      · intro answer; exact absurd answer (by simp)

/-! ## Anti-vacuity -/

#guard codegenKey.decode (codegenKey.encode ⟨"UserId", some "UserId"⟩) == some ⟨"UserId", some "UserId"⟩
#guard codegenKey.decode (codegenKey.encode ⟨"Note", none⟩) == some ⟨"Note", none⟩
#guard codegenKey.decode (.obj [("typeName", .str "X"), ("version", .number ⟨0⟩)]) == none
#guard codegenKey.decode (.obj [("brand", .str "X"), ("typeName", .str "X")]) == none

end Effect4.Schema
