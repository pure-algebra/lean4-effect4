import ProbeU.Reflect
import Conform.Effect4.LcnfSemantics

/-!
# Probe U, question 4: `tyValue` is the generic reflection (proved); `valueTy?`, its inverse, is
a `partial` if-chain by name that the same view would read back generically
-/

set_option autoImplicit false

open Lean Effect4.Program ProbeU

namespace ProbeU.ReflectionsSemantics

/-- The LCNF interpreter's values: `.ctor ``Ty.<name> fields`. -/
def valueR : Reflection Conform.Lcnf.Value where
  app c args := .ctor (Name.str `Effect4.Program.Ty c.name) (args.map (·.2)).toArray
  str := .str
  nat := .nat

theorem tyValue_eq (t : Ty) : Conform.Effect4.LcnfSemantics.tyValue t = cata_ty (reflectAlg valueR) t :=
  hom_eq_cata_ty (alg := reflectAlg valueR)
    { f_ty := Conform.Effect4.LcnfSemantics.tyValue
      h_ty_never := rfl, h_ty_unit := rfl, h_ty_nat := rfl, h_ty_int := rfl
      h_ty_string := rfl, h_ty_bool := rfl, h_ty_handle := fun _ => rfl
      h_ty_option := fun _ => rfl, h_ty_list := fun _ => rfl
      h_ty_prod := fun _ _ => rfl, h_ty_except := fun _ _ => rfl
      h_ty_exitOf := fun _ _ => rfl, h_ty_causeOf := fun _ => rfl
      h_ty_fiberOf := fun _ _ => rfl, h_ty_union := fun _ _ => rfl
      h_ty_lit := fun _ => rfl, h_ty_refOf := fun _ => rfl
      h_ty_deferredOf := fun _ _ => rfl, h_ty_var := fun _ => rfl
      h_ty_unknown := rfl } t

end ProbeU.ReflectionsSemantics

#print axioms ProbeU.ReflectionsSemantics.tyValue_eq
#print axioms Conform.Effect4.LcnfSemantics.tyValue
