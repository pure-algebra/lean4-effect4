module

public import Effect4.Program.Fold

/-!
# Program.TyNormal — a certificate that a type is its own normal form, by one fold

`Ty.normalize` at a product or a union goes through the union rows, whose order is decided by
subtyping (`Ty.sub`), a well-founded definition. So `t.normalize = t` does not reduce by
evaluation at a product, and `decide` cannot close it there. The certificate (`Ty.certNormal`) is
a fold of the generated `Ty` signature, so it reduces on every concrete type. Its soundness is
`Ty.normalize_of_certNormal` (`src/Effect4/Laws/Program/TyNormal.lean`): a certified type is its
own normal form.

The fold answers two Booleans at each type: whether it certifies the type, and whether the type is
a factor (no union at its head). It certifies:

- every leaf, and every constructor whose normal form is the constructor at its children's
  normal forms, when the children are certified;
- a product of two certified factors;
- a record whose names are strictly ascending by their bytes, when every field's type is
  certified.

It never certifies a union, a tuple or a reference with arguments: their normal forms reorder or
rewrite their children. A type it refuses may still be normal. Its consumer is the step
language's typing check (`src/Effect4/Step.lean`; decisions row 330, slice L2).
-/

@[expose] public section

namespace Effect4.Program

instance {β : Type} (l : List (String × β)) : Decidable (Field.Ascending Field.bytesKey l) :=
  inferInstanceAs (Decidable (l.Pairwise _))

/-- The certificate algebra: at each type, whether it is certified, and whether it is a factor. -/
def certNormalAlg : TyAlgebra (fun _ => Bool × Bool) where
  ty_never := (true, true)
  ty_unit := (true, true)
  ty_nat := (true, true)
  ty_int := (true, true)
  ty_string := (true, true)
  ty_bool := (true, true)
  ty_handle _ := (true, true)
  ty_option t := (t.1, true)
  ty_list t := (t.1, true)
  ty_prod a b := (a.1 && b.1 && a.2 && b.2, true)
  ty_except a b := (a.1 && b.1, true)
  ty_exitOf a b := (a.1 && b.1, true)
  ty_causeOf t := (t.1, true)
  ty_fiberOf a b := (a.1 && b.1, true)
  ty_union _ _ := (false, false)
  ty_lit _ := (true, true)
  ty_refOf t := (t.1, true)
  ty_deferredOf a b := (a.1 && b.1, true)
  ty_var _ := (true, true)
  ty_unknown := (true, true)
  ty_record fs := (decide (Field.Ascending Field.bytesKey fs) && fs.all (fun f => f.2.2.1), true)
  ty_map k v := (k.1 && v.1, true)
  ty_tuple _ := (false, true)
  ty_app _ _ := (false, true)
  ty_null := (true, true)
  ty_undefined := (true, true)
  ty_number := (true, true)
  ty_bytes := (true, true)

/-- **The certificate**: the type is its own normal form, by its shape. -/
def Ty.certNormal (t : Ty) : Bool := (cata_ty certNormalAlg t).1

end Effect4.Program
