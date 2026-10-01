import ProbeU.FacesTable
import Effect4.Schema.Bridge
import Effect4.Codegen.Types
import Effect4.Program.Native
import Effect4.Program.Packages
import TypeScript.Render

/-!
# Probe U, question 3, family (c): the spelling folds are one table and three generic folds

`Ty.renderRaw`, `Bridge.schema` and `Ty.key` — three hand traversals of twenty arms each
(`#exhaustive_gate`: `alts 22`, `alts 20`, `alts 20`, no catch-all) — are each the fold of one
column of `ProbeU.tyFaces`. Each agreement is the generated uniqueness theorem
`hom_eq_cata_ty` with every homomorphism field definitional: the table is the hand arms' data,
nothing else. A constructor appended to `Ty` adds one field to `TyTable` (generated), so
`tyFaces` stops compiling until its row is written, and the three folds need no edit.

Then two findings the single table makes visible, tested on the tree's own types:
`Ty.render` is the TypeRef face printed (`Render.type ∘ ofTy`) on every vector the TypeRef
face spells, except where `renderRaw` does not escape a literal (`RED`).
-/

set_option autoImplicit false

open Effect4 Effect4.Program ProbeU

namespace ProbeU.Spelling

/-- **`Ty.renderRaw` is the TypeScript column's fold** (proved). -/
theorem renderRaw_eq_table (t : Ty) : Ty.renderRaw t = cata_ty (tsAlg tyFaces) t :=
  hom_eq_cata_ty (alg := tsAlg tyFaces)
    { f_ty := Ty.renderRaw
      h_ty_never := rfl, h_ty_unit := rfl, h_ty_nat := rfl, h_ty_int := rfl
      h_ty_string := rfl, h_ty_bool := rfl, h_ty_handle := fun _ => rfl
      h_ty_option := fun _ => rfl, h_ty_list := fun _ => rfl
      h_ty_prod := fun _ _ => rfl, h_ty_except := fun _ _ => rfl
      h_ty_exitOf := fun _ _ => rfl, h_ty_causeOf := fun _ => rfl
      h_ty_fiberOf := fun _ _ => rfl, h_ty_union := fun _ _ => rfl
      h_ty_lit := fun _ => rfl, h_ty_refOf := fun _ => rfl
      h_ty_deferredOf := fun _ _ => rfl
      h_ty_var := fun i => by rcases i with _ | _ | n <;> rfl
      h_ty_unknown := rfl } t

/-- **`Bridge.schema` is the Schema column's fold** (proved). -/
theorem schema_eq_table (t : Ty) : Schema.Bridge.schema t = cata_ty (schemaAlg tyFaces) t :=
  hom_eq_cata_ty (alg := schemaAlg tyFaces)
    { f_ty := Schema.Bridge.schema
      h_ty_never := rfl, h_ty_unit := rfl, h_ty_nat := rfl, h_ty_int := rfl
      h_ty_string := rfl, h_ty_bool := rfl, h_ty_handle := fun _ => rfl
      h_ty_option := fun _ => rfl, h_ty_list := fun _ => rfl
      h_ty_prod := fun _ _ => rfl, h_ty_except := fun _ _ => rfl
      h_ty_exitOf := fun _ _ => rfl, h_ty_causeOf := fun _ => rfl
      h_ty_fiberOf := fun _ _ => rfl, h_ty_union := fun _ _ => rfl
      h_ty_lit := fun _ => rfl, h_ty_refOf := fun _ => rfl
      h_ty_deferredOf := fun _ _ => rfl, h_ty_var := fun _ => rfl
      h_ty_unknown := rfl } t

/-- **`Ty.key` is the code column's fold** (proved): the code is the wire tag, the payload its
bytes, every child but the last length-prefixed. -/
theorem key_eq_table (t : Ty) : Ty.key t = cata_ty (keyAlg tyFaces) t :=
  hom_eq_cata_ty (alg := keyAlg tyFaces)
    { f_ty := Ty.key
      h_ty_never := rfl, h_ty_unit := rfl, h_ty_nat := rfl, h_ty_int := rfl
      h_ty_string := rfl, h_ty_bool := rfl, h_ty_handle := fun _ => rfl
      h_ty_option := fun _ => rfl, h_ty_list := fun _ => rfl
      h_ty_prod := fun _ _ => rfl, h_ty_except := fun _ _ => rfl
      h_ty_exitOf := fun _ _ => rfl, h_ty_causeOf := fun _ => rfl
      h_ty_fiberOf := fun _ _ => rfl, h_ty_union := fun _ _ => rfl
      h_ty_lit := fun _ => rfl, h_ty_refOf := fun _ => rfl
      h_ty_deferredOf := fun _ _ => rfl, h_ty_var := fun _ => rfl
      h_ty_unknown := rfl } t

/-! ## The tree's own types, tested -/

/-- One type per constructor (the same set as `src/OCaml5/Eff/Metadata.lean:52-60`), the rows'
columns of every native operation and package, and the two edge spellings. -/
def vectors : List Ty :=
  [.never, .unknown, .unit, .nat, .int, .string, .bool, .handle "Host.Resource",
   .option (.list .nat), .list (.option .string), .prod .string .nat, .except .string (.list .nat),
   .exitOf .nat .string, .causeOf .string, .fiberOf .unit .nat, .union .nat (.union .never .string),
   .lit "tag", .refOf .nat, .deferredOf .nat .string, .var 0, .var 1, .var 7] ++
  (NativeOp.all.flatMap fun op => [(NativeOp.row op).request, (NativeOp.row op).answer,
    (NativeOp.row op).error]) ++
  (Packages.all.flatMap fun p => p.rows.flatMap fun r => [r.request, r.answer, r.error])

#guard vectors.length ≥ 22
#guard vectors.all fun t => Ty.renderRaw t == cata_ty (tsAlg tyFaces) t
#guard vectors.all fun t => Ty.key t == cata_ty (keyAlg tyFaces) t

/-- The TypeRef face printed agrees with the text face on every vector it spells. -/
def printedAgrees (t : Ty) : Bool :=
  match Codegen.Types.ofTy t with
  | some tr => TypeScript.Render.type TypeScript.house0 tr == Ty.render t
  | none => true

#guard vectors.all printedAgrees
#guard (vectors.filter fun t => (Codegen.Types.ofTy t).isSome).length ≥ 20

/-- RED (a defect of the hand text face, tested): a literal holding a quote. `Ty.renderRaw`
writes the value between quotes without escaping it, so the printed text is not a TypeScript
literal type; the TypeRef face escapes it (`Render.quoted`). One table with one escaping rule
would not have two answers. -/
def quoted : Ty := .lit "a\"b"

#guard Ty.renderRaw quoted == "\"a\"b\""
#guard (Codegen.Types.ofTy quoted).map (TypeScript.Render.type TypeScript.house0) == some "\"a\\\"b\""
#guard !printedAgrees quoted

/-! The generated table's module rows name each rc.112 module once (tested): the TypeScript head
is `M.M`, the Schema declaration `effect/schema/M`, with the same argument order. -/

def moduleRows : List (TyCtor × String × List Nat) :=
  [(.option, "Option", [0]), (.except, "Result", [1, 0]), (.exitOf, "Exit", [0, 1]),
   (.causeOf, "Cause", [0]), (.fiberOf, "Fiber", [0, 1]), (.refOf, "Ref", [0]),
   (.deferredOf, "Deferred", [0, 1])]

#guard moduleRows.all fun (c, m, perm) =>
  (tyFaces.get c).ts == moduleTs (m ++ "." ++ m) perm &&
    (match (tyFaces.get c).schema with
     | .decl id p _ => id == "effect/schema/" ++ m && p == perm
     | _ => false)

end ProbeU.Spelling

#print axioms ProbeU.Spelling.renderRaw_eq_table
#print axioms ProbeU.Spelling.schema_eq_table
#print axioms ProbeU.Spelling.key_eq_table
