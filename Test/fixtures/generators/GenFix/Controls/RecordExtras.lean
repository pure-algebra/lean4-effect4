import GenFix.Record.TyExtras

/-!
# GenFix.Controls.RecordExtras — the nested extras on lists of labelled children (a generator fixture)

Finite controls beside the laws `tools/Effect4Gen/Fold.lean --extras` generates for the record
family (`GenFix.Record.TyExtras`, from `GenFix.Record.Ty`'s `record (fields : List (String × Ty))`):
records of 0, 1, 2, 3 and 7 labelled fields, one of them a record itself, so a fixed-arity
default cannot hide. They complement the universally quantified laws (`tyBuild_view`,
`cata_ofLayer_view`, `eq_cata_ofLayer`, `cata_fusion_ty`, `cata_ofLayer_inv`, `cata_prod_ty`,
`foldMap_head_eq_cata`, `foldMap_eq_cata`); they do not replace them.

The red control: `spellTwo`, a layer that reads at most two fields of a record (probe U's
fixed-arity default, `U/note.md` §3.5), agrees with the full fold at 0, 1 and 2 fields and
differs at 3 and 7, so the length controls see what a fixed-arity reading drops.

Read by `scripts/test-generators.py`; not a battery module (`Test/fixtures/` is outside the
module-closure gate).
-/

set_option autoImplicit false

namespace GenFix.Controls.RecordExtras

open GenFix.Record

/-- A spelling layer: a record prints every field as `label: child`, in written order; any other
node its tag's name and its arguments. -/
def spell : TyCtor → List (TyArgF String) → String
  | c, args => c.name ++ "(" ++ String.intercalate ", " (args.map fun
      | .child r => r
      | .str v => "\"" ++ v ++ "\""
      | .nat v => toString v
      | .list_prod_string_ty v =>
        "{" ++ String.intercalate "; " (v.map fun (n, r) => n ++ ": " ++ r) ++ "}") ++ ")"

/-- The red control: the same layer reading at most two fields of a record. -/
def spellTwo : TyCtor → List (TyArgF String) → String
  | c, args => spell c (args.map fun
      | .list_prod_string_ty v => .list_prod_string_ty (v.take 2)
      | a => a)

/-- How many labels the node's own shape holds (its record's field names, children erased). -/
def labels : TyCtor → List (TyArgF Unit) → Nat
  | _, shape => (shape.map fun
      | .list_prod_string_ty v => v.length
      | _ => 0).sum

/-- The node count, as a layer: one, then every child at every position. -/
def size : TyCtor → List (TyArgF Nat) → Nat
  | _, args => 1 + (args.flatMap TyArgF.kids).sum

/-! ## Lengths 0, 1, 2, 3 and 7 -/

/-- The record of the first `n` of seven labelled fields (the seventh a record itself). -/
def rec (n : Nat) : Ty :=
  .record ([("a", .nat), ("b", .string), ("c", .list .bool), ("d", .unit), ("e", .lit "x"),
    ("f", .option .int), ("g", .record [("h", .never)])].take n)

-- the view rebuilds the node, and reads every labelled child, at every length
#guard (List.range 8).all fun n => tyBuild (tyCtor (rec n)) (tyArgs (rec n)) == rec n
#guard [0, 1, 2, 3, 7].map (fun n => (tyKids (rec n)).length) = [0, 1, 2, 3, 7]
#guard tyKids (rec 3) = [.nat, .string, .list .bool]
#guard (tyShape (rec 3)).map (fun
    | .list_prod_string_ty v => v.map Prod.fst
    | _ => []) = [["a", "b", "c"]]

-- the layer fold reads every field with its label, in written order
#guard cata_ty (TyAlgebra.ofLayer spell) (rec 0) = "record({})"
#guard cata_ty (TyAlgebra.ofLayer spell) (rec 1) = "record({a: nat()})"
#guard cata_ty (TyAlgebra.ofLayer spell) (rec 2) = "record({a: nat(); b: string()})"
#guard cata_ty (TyAlgebra.ofLayer spell) (rec 3) =
  "record({a: nat(); b: string(); c: list(bool())})"
#guard cata_ty (TyAlgebra.ofLayer spell) (rec 7) =
  "record({a: nat(); b: string(); c: list(bool()); d: unit(); e: lit(\"x\"); f: option(int()); g: record({h: never()})})"

-- red: a two-field reading agrees up to two fields and differs at three and seven
#guard [0, 1, 2].all fun n =>
  cata_ty (TyAlgebra.ofLayer spellTwo) (rec n) == cata_ty (TyAlgebra.ofLayer spell) (rec n)
#guard [3, 7].all fun n =>
  cata_ty (TyAlgebra.ofLayer spellTwo) (rec n) != cata_ty (TyAlgebra.ofLayer spell) (rec n)

-- the head fold reads the labels through the shape; the paired fold rebuilds the node
#guard [0, 1, 2, 3, 7].map (fun n => cata_ty (TyAlgebra.headAlg 0 (· + ·) labels) (rec n)) =
  [0, 1, 2, 3, 8]
#guard [0, 1, 2, 3, 7].all fun n =>
  cata_ty (TyAlgebra.headAlg 0 (· + ·) labels) (rec n) ==
    foldMap_ty 0 (· + ·) (rec n) (fun s => labels (tyCtor s) (tyShape s))
#guard [0, 1, 2, 3, 7].all fun n =>
  cata_ty (TyAlgebra.paraAlg 0 (· + ·) fun _ => 1) (rec n) == (rec n, foldMap_ty 0 (· + ·) (rec n) fun _ => 1)
#guard [0, 1, 2, 3, 7].map (fun n => cata_ty (TyAlgebra.ofLayer size) (rec n)) = [1, 2, 3, 5, 11]

/-! ## The laws used at the record position (instances of the generated statements) -/

/-- Every node counts at least itself: the layer invariant through the field list. -/
theorem size_pos (t : Ty) : 0 < cata_ty (TyAlgebra.ofLayer size) t :=
  cata_ofLayer_inv size (0 < ·) (fun _ _ _ => Nat.lt_of_lt_of_le Nat.zero_lt_one (Nat.le_add_right 1 _)) t

/-- The spelling and the count side by side, at seven fields, by the banana split. -/
theorem spell_size_rec7 :
    cata_ty (TyAlgebra.prod (TyAlgebra.ofLayer spell) (TyAlgebra.ofLayer size)) (rec 7) =
      (cata_ty (TyAlgebra.ofLayer spell) (rec 7), cata_ty (TyAlgebra.ofLayer size) (rec 7)) :=
  cata_prod_ty _ _ (rec 7)

#print axioms size_pos
#print axioms spell_size_rec7

end GenFix.Controls.RecordExtras
