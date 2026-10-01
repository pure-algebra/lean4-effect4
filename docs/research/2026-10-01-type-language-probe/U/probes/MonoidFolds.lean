import ProbeU.Classes
import Effect4.Laws.Program.Template
import Effect4.Laws.Program.TypeAlgebra
import Effect4.Laws.Program.Typed.Membership
import Effect4.Program.Admission
import Effect4.Schema.Codec

/-!
# Probe U, question 3, family (b): the collection and predicate folds are columns of one table

Eight traversals of `Ty` — four structural hand definitions (`Ty.varsOf`, `Ty.closed`,
`Ty.templateAdmissible`, `Codec.isSupported`), one structural hand definition with a
`fold_of` connector (`findInt`) and three hand-written `TyAlgebra` literals (`handleFreeAlg`,
`valueVarsAlg`, `internalHandleScan`) — are four generic folds read at a column of
`ProbeU.tyClasses`:

| today | generic fold | column / hit |
| --- | --- | --- |
| `Ty.varsOf` | `paramsAlg` (the `(List Nat, ++, [])` head fold) | `param` |
| `Ty.closed` | `allHeads` (the `(Bool, &&, true)` head fold) | `!param` |
| `Codec.isSupported` | `allHeads` | `codec` |
| `handleFree` | `allHeads` | `handleFree` |
| `valueVarsAlg` | `varsUnder` | `valueFormer` |
| `(closed, templateAdmissible)` | `varsUnder` | `positional` |
| `findInt` | `firstAlg` (the first node of a class, at its binder-name path) | `int` |
| `internalHandleScan` | `firstAlg` | an internal handle target, a fiber, cell or promise |

Each agreement is the generated uniqueness theorem with definitional fields. `findInt`'s path
segments ("inner", "left", "right", "error", "value") turn out to be exactly the constructors'
binder names, so the located search reads them off the declaration (`TyCtor.binders`).
-/

set_option autoImplicit false

open Effect4 Effect4.Program ProbeU

namespace ProbeU.Monoid

/-- **`Ty.varsOf` is the parameter column's list fold** (proved). -/
theorem varsOf_eq (t : Ty) : Ty.varsOf t = cata_ty paramsAlg t :=
  hom_eq_cata_ty (alg := paramsAlg)
    { f_ty := Ty.varsOf
      h_ty_never := rfl, h_ty_unit := rfl, h_ty_nat := rfl, h_ty_int := rfl
      h_ty_string := rfl, h_ty_bool := rfl, h_ty_handle := fun _ => rfl
      h_ty_option := fun _ => rfl, h_ty_list := fun _ => rfl
      h_ty_prod := fun _ _ => rfl, h_ty_except := fun _ _ => rfl
      h_ty_exitOf := fun _ _ => rfl, h_ty_causeOf := fun _ => rfl
      h_ty_fiberOf := fun _ _ => rfl, h_ty_union := fun _ _ => rfl
      h_ty_lit := fun _ => rfl, h_ty_refOf := fun _ => rfl
      h_ty_deferredOf := fun _ _ => rfl, h_ty_var := fun _ => rfl
      h_ty_unknown := rfl } t

/-- And so `Ty.varsOf` is `foldMap_ty` at a hook that reads the layer (proved). -/
theorem varsOf_eq_foldMap (t : Ty) :
    Ty.varsOf t = foldMap_ty [] (· ++ ·) t (fun s =>
      bif (tyClasses.get (tyCtor s)).param then
        (match tyLeaf s with | .nat i => [i] | _ => []) else []) := by
  rw [varsOf_eq]
  exact (foldMap_head_eq_cata [] (· ++ ·) _ t).symm

/-- **`Ty.closed` is the `(Bool, &&)` fold of the column `!param`** (proved). -/
theorem closed_eq (t : Ty) : Ty.closed t = cata_ty (allHeads fun r => !r.param) t :=
  hom_eq_cata_ty (alg := allHeads fun r => !r.param)
    { f_ty := Ty.closed
      h_ty_never := rfl, h_ty_unit := rfl, h_ty_nat := rfl, h_ty_int := rfl
      h_ty_string := rfl, h_ty_bool := rfl, h_ty_handle := fun _ => rfl
      h_ty_option := fun _ => rfl, h_ty_list := fun _ => rfl
      h_ty_prod := fun _ _ => rfl, h_ty_except := fun _ _ => rfl
      h_ty_exitOf := fun _ _ => rfl, h_ty_causeOf := fun _ => rfl
      h_ty_fiberOf := fun _ _ => rfl, h_ty_union := fun _ _ => rfl
      h_ty_lit := fun _ => rfl, h_ty_refOf := fun _ => rfl
      h_ty_deferredOf := fun _ _ => rfl, h_ty_var := fun _ => rfl
      h_ty_unknown := rfl } t

/-- **`Codec.isSupported` is the `(Bool, &&)` fold of the column `codec`** (proved). -/
theorem isSupported_eq (t : Ty) : Schema.Codec.isSupported t = cata_ty (allHeads (·.codec)) t :=
  hom_eq_cata_ty (alg := allHeads (·.codec))
    { f_ty := Schema.Codec.isSupported
      h_ty_never := rfl, h_ty_unit := rfl, h_ty_nat := rfl, h_ty_int := rfl
      h_ty_string := rfl, h_ty_bool := rfl, h_ty_handle := fun _ => rfl
      h_ty_option := fun _ => rfl, h_ty_list := fun _ => rfl
      h_ty_prod := fun _ _ => rfl, h_ty_except := fun _ _ => rfl
      h_ty_exitOf := fun _ _ => rfl, h_ty_causeOf := fun _ => rfl
      h_ty_fiberOf := fun _ _ => rfl, h_ty_union := fun _ _ => rfl
      h_ty_lit := fun _ => rfl, h_ty_refOf := fun _ => rfl
      h_ty_deferredOf := fun _ _ => rfl, h_ty_var := fun _ => rfl
      h_ty_unknown := rfl } t

/-- **`handleFreeAlg` is the column `handleFree` read by the generic fold, as an algebra**
(proved by `rfl`: the hand algebra literal is the table's row, field by field). -/
theorem handleFreeAlg_eq : Typed.handleFreeAlg = allHeads (·.handleFree) := rfl

theorem handleFree_eq (t : Ty) : Typed.handleFree t = cata_ty (allHeads (·.handleFree)) t := by
  rw [Typed.handleFree, handleFreeAlg_eq]

/-- **`valueVarsAlg` is `varsUnder` at the column `valueFormer`** (proved by `rfl`). -/
theorem valueVarsAlg_eq : Ty.valueVarsAlg = varsUnder (·.valueFormer) := rfl

/-- **`(Ty.closed, Ty.templateAdmissible)` is `varsUnder` at the column `positional`** (proved):
the hand pair is one generic fold at another column. -/
theorem templateAdmissible_eq (t : Ty) :
    (Ty.closed t, Ty.templateAdmissible t) = cata_ty (varsUnder (·.positional)) t :=
  hom_eq_cata_ty (alg := varsUnder (·.positional))
    { f_ty := fun s => (Ty.closed s, Ty.templateAdmissible s)
      h_ty_never := rfl, h_ty_unit := rfl, h_ty_nat := rfl, h_ty_int := rfl
      h_ty_string := rfl, h_ty_bool := rfl, h_ty_handle := fun _ => rfl
      h_ty_option := fun _ => rfl, h_ty_list := fun _ => rfl
      h_ty_prod := fun _ _ => rfl, h_ty_except := fun _ _ => rfl
      h_ty_exitOf := fun _ _ => rfl, h_ty_causeOf := fun _ => rfl
      h_ty_fiberOf := fun _ _ => rfl, h_ty_union := fun _ _ => rfl
      h_ty_lit := fun _ => rfl, h_ty_refOf := fun _ => rfl
      h_ty_deferredOf := fun _ _ => rfl, h_ty_var := fun _ => rfl
      h_ty_unknown := rfl } t

/-- The hit of `findInt`: the `int` node. -/
def intHit (c : TyCtor) (_ : TyLeaf) : Bool := decide (c = .int)

/-- **`findInt` is the located search for `int`, children at their binder names** (proved). -/
theorem findInt_eq (pos : Path) (t : Ty) : findInt pos t = cata_ty (firstAlg intHit) t pos := by
  rw [findInt.eq_cata]
  exact congrFun (hom_eq_cata_ty (alg := firstAlg intHit)
    { f_ty := cata_ty findInt.alg
      h_ty_never := rfl, h_ty_unit := rfl, h_ty_nat := rfl, h_ty_int := rfl
      h_ty_string := rfl, h_ty_bool := rfl, h_ty_handle := fun _ => rfl
      h_ty_option := fun _ => rfl, h_ty_list := fun _ => rfl
      h_ty_prod := fun _ _ => rfl, h_ty_except := fun _ _ => rfl
      h_ty_exitOf := fun _ _ => rfl, h_ty_causeOf := fun _ => rfl
      h_ty_fiberOf := fun _ _ => rfl, h_ty_union := fun _ _ => rfl
      h_ty_lit := fun _ => rfl, h_ty_refOf := fun _ => rfl
      h_ty_deferredOf := fun _ _ => rfl, h_ty_var := fun _ => rfl
      h_ty_unknown := rfl } t) pos

/-- The hit of the internal-handle scan: an internal handle spelling, or a fiber, cell or
promise node (a classifier: its positive arms listed, an explicit negative last). -/
def internalHit : TyCtor → TyLeaf → Bool
  | .handle, .str target => internalHandleTargets.contains target
  | .fiberOf, _ | .refOf, _ | .deferredOf, _ => true
  | _, _ => false

/-- **`internalHandleScan` is the located search at `internalHit`** (proved by `rfl`). -/
theorem internalHandleScan_eq : internalHandleScan = firstAlg internalHit := rfl

theorem findInternalHandle_eq (pos : Path) (t : Ty) :
    findInternalHandle pos t = cata_ty (firstAlg internalHit) t pos := by
  rw [findInternalHandle, internalHandleScan_eq]

/-! The tree's own types, tested (the theorems above are the agreement; these pin a few values). -/

#guard Ty.varsOf (.prod (.var 0) (.option (.var 3))) == [0, 3]
#guard cata_ty paramsAlg (.prod (.var 0) (.option (.var 3))) == [0, 3]
#guard cata_ty (firstAlg intHit) (.except .string (.list .int)) ["program"] ==
  some ["program", "value", "inner"]

end ProbeU.Monoid

#print axioms ProbeU.Monoid.varsOf_eq
#print axioms ProbeU.Monoid.varsOf_eq_foldMap
#print axioms ProbeU.Monoid.closed_eq
#print axioms ProbeU.Monoid.isSupported_eq
#print axioms ProbeU.Monoid.handleFreeAlg_eq
#print axioms ProbeU.Monoid.handleFree_eq
#print axioms ProbeU.Monoid.valueVarsAlg_eq
#print axioms ProbeU.Monoid.templateAdmissible_eq
#print axioms ProbeU.Monoid.findInt_eq
#print axioms ProbeU.Monoid.internalHandleScan_eq
#print axioms ProbeU.Monoid.findInternalHandle_eq
