import Effect4.Laws.Program.ValueModel
import Effect4.Program.Derived
import Effect4.Store.Image.Containers
import Effect4.Program.Typing
import Conform.Model.Container

/-!
# Conform.Effect4.Models — the four models the brief asks for, composed and proved

**What it is.** The Effect4 configuration of `Conform.Model.Container`: the `Store.Image`
library as a `Combinators` record, the element models the environment supplies, and the four
composed models with their two laws — `ofVal_toVal` and `ofVal_exact` — *obtained from the
element laws*, never restated.

| model | composition | how the laws arrive |
| --- | --- | --- |
| `Option (Option Nat)` | `Image.option (Image.option Image.nat)` | `Image.option`'s own fields, twice |
| `List (Option Ty)` | `Image.list (Image.option tyImage)` | `Image.list`'s fields over `Image.option`'s |
| `GenTy` | `(Image.ctor3 (option tyImage) tyImage requirementImage 0).equiv` | `ctor3`'s fields through `equiv`'s |
| `EffTy` | `(Image.ctor3 tyImage tyImage requirementImage 0).equiv` | the same |

The foundation now provides `Canonical Ty`, `Canonical Requirement`, and `Canonical EffTy`.
These models reuse those exact images; metadata decoding does not normalize raw types.

**The nested-option distinction, through the composition.** `canonical_nested_distinct` (the
wave-1 follow-up control) says the canonical encoding separates `none` from `some none`.
`optOptNat_toVal_eq_canonical` says the *composed model* writes exactly the canonical bytes,
and `canonical_nested_distinct_via_model` derives the control from the model's own
injectivity — so the model and the wire agree by a theorem rather than by two separate facts.

**Depends on.** `Effect4.Program.Derived` (the derived `Canonical` instances),
`Effect4.Program.Typing` (`GenTy`, `EffTy`), `Conform.Model.Container`.
-/

set_option autoImplicit false

namespace Conform.Effect4.Models

-- `_root_.` throughout: this file's own namespace is `Conform.Effect4`, so a bare `Effect4`
-- would resolve to it.
open _root_.Effect4 _root_.Effect4.Store _root_.Effect4.Program

/-- `Effect4.Machine.Env.Requirement`, spelled once: the namespace also holds a `Val` and
`open`ing it would make `Val` ambiguous with the store's. -/
abbrev Requirement := _root_.Effect4.Machine.Env.Requirement

/-! ## The element library, as a `Combinators` record

Nothing new is declared: the three fields are the existing higher-order combinators of
`src/Effect4/Store/Image.lean`, and `sumOf` uses the disjoint constructor image. Missing element models remain explicit obligations. -/

def imageCombinators : Conform.Model.Combinators Image where
  optionOf := fun I => Image.option I
  listOf := fun I => Image.list I
  pairOf := fun I J => Image.pair I J
  sumOf := some (fun I J => Image.sum I J)

/-- Program-value composition carries normalization and allocation-indexed membership.
There is deliberately no generic sum membership rule until the program language supplies one. -/
def valueCombinators : Conform.Model.Combinators ValueModel where
  optionOf := ValueModel.option
  listOf := ValueModel.list
  pairOf := ValueModel.pair
  sumOf := none

def imageLibrary : Conform.Model.Library :=
  { name := "Store.Image"
    combinators := ["element", "optionOf", "listOf", "pairOf", "sumOf"]
    laws := ["ofVal_toVal", "ofVal_exact"] }

/-! ## Foundation metadata images

The generated canonical writer is the single owner of constructor tags and fields.
These aliases keep existing report and membership consumers on that writer.
-/

abbrev tyToVal : Ty → Val := Canonical.toVal

def tyImage : Image Ty := Canonical.image Ty

theorem tyImage_ofVal_toVal (t : Ty) : tyImage.ofVal (tyImage.toVal t) = some t :=
  tyImage.ofVal_toVal t

theorem tyImage_ofVal_exact {v : Val} {t : Ty} (h : tyImage.ofVal v = some t) :
    v = tyImage.toVal t :=
  tyImage.ofVal_exact h

/-- Exact canonical rows: decoding refuses duplicates and nonascending keys. -/
def requirementImage : Image Requirement := Canonical.image Requirement

theorem requirementImage_ofVal_toVal (r : Requirement) :
    requirementImage.ofVal (requirementImage.toVal r) = some r :=
  requirementImage.ofVal_toVal r

theorem requirementImage_ofVal_exact {v : Val} {r : Requirement}
    (h : requirementImage.ofVal v = some r) : v = requirementImage.toVal r :=
  requirementImage.ofVal_exact h

/-! ## The four composed models -/

/-- `Option (Option Nat)` — the brief's minimal nesting. -/
def optOptNat : Image (Option (Option Nat)) := Image.option (Image.option Image.nat)

/-- `List (Option Ty)`. -/
def listOptTy : Image (List (Option Ty)) := Image.list (Image.option tyImage)

/-- `Option (Option Ty)` — the nesting `GenTy.joinAnswer` returns. -/
def optOptTy : Image (Option (Option Ty)) := Image.option (Image.option tyImage)

/-- `GenTy`: the wire's shape for a structure, `ctor 0 [fields in declaration order]`. -/
def genTyImage : Image GenTy :=
  (Image.ctor3 (Image.option tyImage) tyImage requirementImage 0).equiv
    (fun p => ⟨p.1, p.2.1, p.2.2⟩)
    (fun g => (g.answer, g.error, g.requires))
    (fun _ => rfl) (fun _ => rfl)

/-- `EffTy`, the same shape with a `Ty` answer. -/
def effTyImage : Image EffTy := Canonical.image EffTy

/-! ### The two laws, obtained from the elements

Each is the composed `Image`'s own field: the combinator carried the element's proof through,
which is exactly the claim that no law was restated. -/

theorem optOptNat_ofVal_toVal (v : Option (Option Nat)) : optOptNat.ofVal (optOptNat.toVal v) = some v :=
  optOptNat.ofVal_toVal v
theorem optOptNat_ofVal_exact {w : Val} {v : Option (Option Nat)} (h : optOptNat.ofVal w = some v) :
    w = optOptNat.toVal v := optOptNat.ofVal_exact h

theorem listOptTy_ofVal_toVal (v : List (Option Ty)) : listOptTy.ofVal (listOptTy.toVal v) = some v :=
  listOptTy.ofVal_toVal v
theorem listOptTy_ofVal_exact {w : Val} {v : List (Option Ty)} (h : listOptTy.ofVal w = some v) :
    w = listOptTy.toVal v := listOptTy.ofVal_exact h

theorem genTy_ofVal_toVal (g : GenTy) : genTyImage.ofVal (genTyImage.toVal g) = some g :=
  genTyImage.ofVal_toVal g
theorem genTy_ofVal_exact {w : Val} {g : GenTy} (h : genTyImage.ofVal w = some g) :
    w = genTyImage.toVal g := genTyImage.ofVal_exact h

theorem effTy_ofVal_toVal (e : EffTy) : effTyImage.ofVal (effTyImage.toVal e) = some e :=
  effTyImage.ofVal_toVal e
theorem effTy_ofVal_exact {w : Val} {e : EffTy} (h : effTyImage.ofVal w = some e) :
    w = effTyImage.toVal e := effTyImage.ofVal_exact h

/-! ### The nested-option distinction, and the wire

`Wave1Review.canonical_nested_distinct` (`docs/research/wave1-followup-probes/LeanControls.lean:29`)
is the fact that the canonical encoding separates the two values. Here it is *derived* from the
composed model: the model writes the canonical bytes (`optOptNat_toVal_eq_canonical`), the model
is injective because its two combinators are (`Image.toVal_injective`), so the canonical writer
separates them too. Model and wire agree by a theorem. -/

theorem optOptNat_toVal_eq_canonical (v : Option (Option Nat)) :
    optOptNat.toVal v = Canonical.toVal v := by
  match v with
  | none => rfl
  | some none => rfl
  | some (some _) => rfl

theorem optOptNat_nested_distinct :
    optOptNat.toVal none ≠ optOptNat.toVal (some none) := by
  intro h
  have hv := optOptNat.toVal_injective h
  exact nomatch hv

theorem canonical_nested_distinct_via_model :
    Canonical.toVal (none : Option (Option Nat)) ≠ Canonical.toVal (some none : Option (Option Nat)) := by
  rw [← optOptNat_toVal_eq_canonical, ← optOptNat_toVal_eq_canonical]
  exact optOptNat_nested_distinct

/-- The same distinction at the nesting `GenTy.joinAnswer` actually returns. `Ty` has no
`Canonical` instance, so this one cannot be stated against the wire's own writer at all: the
model *is* the wire's writer here. -/
theorem optOptTy_nested_distinct : optOptTy.toVal none ≠ optOptTy.toVal (some none) := by
  intro h
  have hv := optOptTy.toVal_injective h
  exact nomatch hv

/-- And the reason it matters: the value the collision destroys is a real answer of
`GenTy.joinAnswer`, not a hypothetical one. -/
theorem joinAnswer_none_none : GenTy.joinAnswer none none = some none := rfl

/-! ### Handle-freedom, carried through the same combinators -/

theorem tyToVal_handles (t : Ty) : (tyToVal t).handles = [] := by
  induction t with
  | never | unit | nat | int | string | bool => rfl
  | handle t => rfl
  | lit s => rfl
  | option i ih | list i ih | causeOf i ih =>
    show (Val.ctor _ [tyToVal i]).handles = []
    rw [Val.handles, Val.handlesList_cons, ih, Val.handlesList_nil]
    rfl
  | prod a b iha ihb | except a b iha ihb | exitOf a b iha ihb | fiberOf a b iha ihb
  | union a b iha ihb =>
    show (Val.ctor _ [tyToVal a, tyToVal b]).handles = []
    rw [Val.handles, Val.handlesList_cons, Val.handlesList_cons, iha, ihb, Val.handlesList_nil]
    rfl

theorem tyImage_handleFree : Image.HandleFree tyImage := tyToVal_handles

theorem optOptNat_handleFree : Image.HandleFree optOptNat :=
  Image.option_handleFree _ (Image.option_handleFree _ Image.nat_handleFree)

theorem listOptTy_handleFree : Image.HandleFree listOptTy :=
  Image.list_handleFree _ (Image.option_handleFree _ tyImage_handleFree)

/-! ## The plan, as data, and what it resolves to

The environment names the element models this file supplies; a plan that needs anything else
answers an obligation instead of a model. -/

def elementEnv : Conform.Model.Env :=
  { models :=
      [ (``Nat, ["ofVal_toVal", "ofVal_exact"])
      , (`Effect4.Program.Ty, ["ofVal_toVal", "ofVal_exact"])
      , (`Effect4.Machine.Env.Requirement, ["ofVal_toVal", "ofVal_exact"]) ] }

/-- The four plans, in the order the table at the head of this file lists them. -/
def plans : List (String × Conform.Model.Plan) :=
  [ ("Option (Option Nat)", .optionOf (.optionOf (.element ``Nat)))
  , ("List (Option Ty)", .listOf (.optionOf (.element `Effect4.Program.Ty)))
  , ("Option (Option Ty)", .optionOf (.optionOf (.element `Effect4.Program.Ty)))
  , ("GenTy.answer × error × requires",
      .pairOf (.optionOf (.element `Effect4.Program.Ty))
        (.pairOf (.element `Effect4.Program.Ty) (.element `Effect4.Machine.Env.Requirement))) ]

/-- Sum composition uses the two independently proved constructor images. -/
def sumPlan : Conform.Model.Plan := .sumOf (.element ``Nat) (.element `Effect4.Program.Ty)

/-- `build` on the plan really does produce the model, at the type the plan describes. -/
def builtOptOptNat :
    Option (Image ((Conform.Model.Plan.optionOf (.optionOf (.element ``Nat))).carrier
      (fun _ => Nat))) :=
  Conform.Model.build imageCombinators (fun _ => Nat) (fun _ => some Image.nat)
    (.optionOf (.optionOf (.element ``Nat)))

/-- And a plan whose element the environment lacks produces `none`, not a wrong model. -/
theorem build_missing_element :
    Conform.Model.build imageCombinators (fun _ => Nat) (fun _ => none)
      (.optionOf (.element ``Nat)) = none := rfl

/-! ## Guards: the composed bytes are the wire's bytes -/

open Canonical in
#guard optOptNat.toVal none = Canonical.toVal (none : Option (Option Nat))
open Canonical in
#guard optOptNat.toVal (some none) = Canonical.toVal (some none : Option (Option Nat))
#guard tyImage.toVal (.option .nat) = Val.ctor 7 [Val.ctor 2 []]
#guard tyImage.ofVal (Val.ctor 7 [Val.ctor 2 []]) = some (Ty.option .nat)
#guard tyImage.ofVal (Val.ctor 7 [Val.ctor 2 [], Val.ctor 2 []]) = none
#guard genTyImage.toVal ⟨none, .never, _root_.Effect4.Machine.Env.Requirement.empty⟩
  = Val.ctor 0 [Val.none, Val.ctor 0 [], Val.list []]
#guard (Conform.Model.resolve imageLibrary elementEnv ["Effect4"] sumPlan).2.size = 0
#guard (Conform.Model.resolve imageLibrary elementEnv ["Effect4"]
  (.optionOf (.optionOf (.element ``Nat)))).2.size = 0
#guard (Conform.Model.resolve imageLibrary elementEnv ["Effect4"]
  (.optionOf (.element `Effect4.Program.Eff))).2.size = 1

/-! ## Receipts -/

#print axioms tyImage
#print axioms tyImage_ofVal_toVal
#print axioms tyImage_ofVal_exact
#print axioms tyImage_handleFree
#print axioms requirementImage
#print axioms requirementImage_ofVal_toVal
#print axioms requirementImage_ofVal_exact
#print axioms optOptNat_ofVal_toVal
#print axioms optOptNat_ofVal_exact
#print axioms listOptTy_ofVal_toVal
#print axioms listOptTy_ofVal_exact
#print axioms genTy_ofVal_toVal
#print axioms genTy_ofVal_exact
#print axioms effTy_ofVal_toVal
#print axioms effTy_ofVal_exact
#print axioms optOptNat_toVal_eq_canonical
#print axioms optOptNat_nested_distinct
#print axioms canonical_nested_distinct_via_model
#print axioms optOptTy_nested_distinct
#print axioms joinAnswer_none_none
#print axioms optOptNat_handleFree
#print axioms listOptTy_handleFree
#print axioms build_missing_element

end Conform.Effect4.Models
