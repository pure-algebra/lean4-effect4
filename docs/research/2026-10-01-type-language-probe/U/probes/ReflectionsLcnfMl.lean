import ProbeU.Reflect
import Conform.Effect4.LcnfMl

/-!
# Probe U, question 4: `tyT` is the generic reflection (proved); `tyOcaml` agrees on the
vectors (tested) except where it does not escape a string (RED)

`tyOcaml` writes a handle target or a literal between quotes with no escaping (`LcnfMl.lean:277`,
`:286`), where `tyO` escapes through `ostr`: two OCaml-syntax reflections of one type, one of
them not a lexical OCaml string for a target holding `"` or `\`. The rung's vectors hold no such
string (their handles are `Ref.Ref<number>` and `Scope.Scope`), so the lane never meets it.
-/

set_option autoImplicit false

open Lean Effect4.Program ProbeU

namespace ProbeU.ReflectionsMl

/-- The target evaluator's values: `.ctorV (ctorName Ty name) args`. -/
def targetR : Reflection Conform.Lcnf.Target.TValue where
  app c args := .ctorV (Conform.Effect4.LcnfMl.tyCtor c.name) (args.map (·.2)).toArray
  str := .str
  nat := fun n => .int n

theorem tyT_eq (t : Ty) : Conform.Effect4.LcnfMl.tyT t = cata_ty (reflectAlg targetR) t :=
  hom_eq_cata_ty (alg := reflectAlg targetR)
    { f_ty := Conform.Effect4.LcnfMl.tyT
      h_ty_never := rfl, h_ty_unit := rfl, h_ty_nat := rfl, h_ty_int := rfl
      h_ty_string := rfl, h_ty_bool := rfl, h_ty_handle := fun _ => rfl
      h_ty_option := fun _ => rfl, h_ty_list := fun _ => rfl
      h_ty_prod := fun _ _ => rfl, h_ty_except := fun _ _ => rfl
      h_ty_exitOf := fun _ _ => rfl, h_ty_causeOf := fun _ => rfl
      h_ty_fiberOf := fun _ _ => rfl, h_ty_union := fun _ _ => rfl
      h_ty_lit := fun _ => rfl, h_ty_refOf := fun _ => rfl
      h_ty_deferredOf := fun _ _ => rfl, h_ty_var := fun _ => rfl
      h_ty_unknown := rfl } t

/-- OCaml syntax for the LCNF-cut types, the way `tyOcaml` spells it, with the strings escaped
as `ostr` escapes them would make it `tyO`'s shape; written here with `tyOcaml`'s own string rule
(quotes, no escaping) to compare. -/
def ocamlR : Reflection String where
  app c args :=
    match args with
    | [] => Conform.Effect4.LcnfMl.tyCtor c.name
    | [(_, a)] => Conform.Effect4.LcnfMl.tyCtor c.name ++ " (" ++ a ++ ")"
    | [(_, a), (_, b)] => Conform.Effect4.LcnfMl.tyCtor c.name ++ " (" ++ a ++ ", " ++ b ++ ")"
    | _ => ""
  str := fun s => "\"" ++ s ++ "\""
  nat := fun n => toString n

#guard Conform.Effect4.LcnfMl.vectors.all fun t =>
  Conform.Effect4.LcnfMl.tyOcaml t == cata_ty (reflectAlg ocamlR) t
#guard (Conform.Effect4.LcnfMl.vectors ++ [Ty.lit "tag", Ty.var 3, Ty.refOf Ty.nat, Ty.deferredOf Ty.nat Ty.unknown]).all fun t =>
  Conform.Effect4.LcnfMl.tyOcaml t == cata_ty (reflectAlg ocamlR) t

-- RED (a defect of the hand mirror, tested): a handle target with a quote is written into the
-- OCaml source unescaped.
#guard Conform.Effect4.LcnfMl.tyOcaml (.handle "a\"b") ==
  Conform.Effect4.LcnfMl.tyCtor "handle" ++ " (\"a\"b\")"

end ProbeU.ReflectionsMl

#print axioms ProbeU.ReflectionsMl.tyT_eq
#print axioms Conform.Effect4.LcnfMl.tyT
