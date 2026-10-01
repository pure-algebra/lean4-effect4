import ProbeU.Reflect
import Tools.ProfileJson
import OCaml5.Eff.Goldens
import OCaml5.Eff.Emit

/-!
# Probe U, question 4: three of the six reflections are the generic one (proved)

`tyJson`, `tyV` and `tyO` are `cata_ty (reflectAlg r)` at a three-field `Reflection`: the
generated uniqueness theorem with every field definitional. The other three are in
`ReflectionsLcnfMl.lean` and `ReflectionsLcnfSemantics.lean` (their modules each declare a
`main`, so they cannot share one file).
-/

set_option autoImplicit false

open Lean Effect4.Program ProbeU

namespace ProbeU.Reflections

/-- Tagged JSON: `{"_tag": name, binder: argument, …}`. -/
def jsonR : Reflection Json where
  app c args := Tools.ProfileJson.tagged c.name args
  str := .str
  nat := fun n => .num n

theorem tyJson_eq (t : Ty) : Tools.ProfileJson.tyJson t = cata_ty (reflectAlg jsonR) t :=
  hom_eq_cata_ty (alg := reflectAlg jsonR)
    { f_ty := Tools.ProfileJson.tyJson
      h_ty_never := rfl, h_ty_unit := rfl, h_ty_nat := rfl, h_ty_int := rfl
      h_ty_string := rfl, h_ty_bool := rfl, h_ty_handle := fun _ => rfl
      h_ty_option := fun _ => rfl, h_ty_list := fun _ => rfl
      h_ty_prod := fun _ _ => rfl, h_ty_except := fun _ _ => rfl
      h_ty_exitOf := fun _ _ => rfl, h_ty_causeOf := fun _ => rfl
      h_ty_fiberOf := fun _ _ => rfl, h_ty_union := fun _ _ => rfl
      h_ty_lit := fun _ => rfl, h_ty_refOf := fun _ => rfl
      h_ty_deferredOf := fun _ _ => rfl, h_ty_var := fun _ => rfl
      h_ty_unknown := rfl } t

/-- The golden value tree: `.ctor ``Ty.<name> args`. -/
def goldenR : Reflection OCaml5.Eff.V where
  app c args := .ctor (Name.str `Effect4.Program.Ty c.name) (args.map (·.2))
  str := .str
  nat := .nat

theorem tyV_eq (t : Ty) : OCaml5.Eff.tyV t = cata_ty (reflectAlg goldenR) t :=
  hom_eq_cata_ty (alg := reflectAlg goldenR)
    { f_ty := OCaml5.Eff.tyV
      h_ty_never := rfl, h_ty_unit := rfl, h_ty_nat := rfl, h_ty_int := rfl
      h_ty_string := rfl, h_ty_bool := rfl, h_ty_handle := fun _ => rfl
      h_ty_option := fun _ => rfl, h_ty_list := fun _ => rfl
      h_ty_prod := fun _ _ => rfl, h_ty_except := fun _ _ => rfl
      h_ty_exitOf := fun _ _ => rfl, h_ty_causeOf := fun _ => rfl
      h_ty_fiberOf := fun _ _ => rfl, h_ty_union := fun _ _ => rfl
      h_ty_lit := fun _ => rfl, h_ty_refOf := fun _ => rfl
      h_ty_deferredOf := fun _ _ => rfl, h_ty_var := fun _ => rfl
      h_ty_unknown := rfl } t

/-- OCaml syntax for `Eff_types.ty`, strings through `ostr` (escaped). -/
def effTypesR : Reflection String := oSyntax (OCaml5.Eff.octor "ty") OCaml5.Eff.ostr

theorem tyO_eq (t : Ty) : OCaml5.Eff.tyO t = cata_ty (reflectAlg effTypesR) t :=
  hom_eq_cata_ty (alg := reflectAlg effTypesR)
    { f_ty := OCaml5.Eff.tyO
      h_ty_never := rfl, h_ty_unit := rfl, h_ty_nat := rfl, h_ty_int := rfl
      h_ty_string := rfl, h_ty_bool := rfl, h_ty_handle := fun _ => rfl
      h_ty_option := fun _ => rfl, h_ty_list := fun _ => rfl
      h_ty_prod := fun _ _ => rfl, h_ty_except := fun _ _ => rfl
      h_ty_exitOf := fun _ _ => rfl, h_ty_causeOf := fun _ => rfl
      h_ty_fiberOf := fun _ _ => rfl, h_ty_union := fun _ _ => rfl
      h_ty_lit := fun _ => rfl, h_ty_refOf := fun _ => rfl
      h_ty_deferredOf := fun _ _ => rfl, h_ty_var := fun _ => rfl
      h_ty_unknown := rfl } t

end ProbeU.Reflections

#print axioms ProbeU.Reflections.tyJson_eq
#print axioms ProbeU.Reflections.tyV_eq
#print axioms ProbeU.Reflections.tyO_eq

/-! The two theorems above that print `Classical.choice` inherit it from the definitions they
are about (a mirror that builds a `Json` object or escapes through `String.toList`), not from
the proof: the definitions' own receipts, for the record. -/
#print axioms Tools.ProfileJson.tyJson
#print axioms Tools.ProfileJson.tagged
#print axioms OCaml5.Eff.tyO
#print axioms OCaml5.Eff.ostr
#print axioms OCaml5.Eff.tyV
#print axioms ProbeU.reflectAlg
