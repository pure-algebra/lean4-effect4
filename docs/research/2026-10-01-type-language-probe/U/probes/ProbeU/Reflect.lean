import ProbeU.Generic

/-!
# Probe U — the generic reflection of `Ty` (family (c')): the signature alone

Six Lean functions outside the `Effect4` roots spell a `Ty` value in another carrier, each with
twenty hand arms: `tyJson` (tagged JSON, `tools/Tools/ProfileJson.lean:21`), `tyV` (the golden
value tree, `src/OCaml5/Eff/Goldens.lean:89`), `tyO` (OCaml syntax for `Eff_types.ty`,
`src/OCaml5/Eff/Emit.lean:366`), `tyT` and `tyOcaml` (the target evaluator's values and OCaml
syntax for the LCNF-cut types, `tools/Conform/Effect4/LcnfMl.lean:164`, `:270`) and `tyValue`
(the LCNF interpreter's values, `tools/Conform/Effect4/LcnfSemantics.lean:40`). None carries a
per-constructor decision: each is "the constructor's name applied to its arguments" in its
carrier, with the arguments named by the declaration's own binders. So each is one
`Reflection` record — how the carrier spells an application, a string and a number — and one
generic fold that reads the names, binders and payload sorts off the emitted view. A
constructor appended to `Ty` is reflected in every carrier with no edit.
-/

set_option autoImplicit false

namespace ProbeU

open Effect4.Program

/-- How a carrier spells a constructor application (its tag and its arguments named by their
binders, in declaration order), a string payload and a number payload. -/
structure Reflection (X : Type) where
  app : TyCtor → List (String × X) → X
  str : String → X
  nat : Nat → X

/-- The payload as arguments. -/
def Reflection.leaf {X : Type} (r : Reflection X) : TyLeaf → List X
  | .none => []
  | .str s => [r.str s]
  | .nat n => [r.nat n]

/-- **The reflection fold**: one definition for every carrier. -/
def reflectAlg {X : Type} (r : Reflection X) : TyAlgebra (fun _ => X) :=
  TyAlgebra.ofLayer fun c l kids => r.app c (c.binders.zip (r.leaf l ++ kids))

/-- An OCaml constructor-syntax carrier, one template per arity (the forms `tyO` writes). -/
def oSyntax (head : String → String) (str : String → String) : Reflection String where
  app c args :=
    match args with
    | [] => head c.name
    | [(_, a)] => s!"({head c.name} {a})"
    | [(_, a), (_, b)] => s!"({head c.name} ({a}, {b}))"
    | _ => ""
  str := str
  nat := fun n => toString n

end ProbeU
