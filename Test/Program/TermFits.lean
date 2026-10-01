import Effect4.Laws.Program.Typed.Admission

/-!
# Term soundness for membership (TY-07) and the coarse heap reading (TY-08)

`evalTerm_fits` (`Laws/Program/Typed/Admission.lean`) is the membership twin of the coarse
`evalTerm_hasTy`: a term that types in a typed environment and evaluates there evaluates to a
value of its type. Positive controls on the two places the coarse law could not reach:

* `pair_fits`: the TY-01 child's `pair(x, undefined)` with `x : nat | string` (the raw product
  the checker certifies) evaluates to a value fitting the raw product;
* `fst_union_fits`: `fst` over a union of products answers at the join of the projections,
  which only the checker's join closure covers (`projectProduct_fits`).

Red control (proved): the template widening needs its parameters under value formers. At
`refOf (var 0)`, widening the binding from `nat` to `nat | string` loses the cell
(`widens_needs_valueVars`), which is why `Ty.valueVars` is a premise of
`fits_instantiate_widens` and every `poly` atom template satisfies it (`decide`, in `atomFits`).
-/

set_option autoImplicit false

namespace Test.Program.TermFits

open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Typed
open Effect4.Machine.Env (Requirement)

/-- `nat | string` as the checker builds it. -/
abbrev u : Ty := Ty.normalize (.union .nat .string)

/-- The raw product the TY-01 child is certified at. -/
abbrev T : Ty := .prod u .unit

/-- `pair(x, undefined)` over `x`. -/
def pairTerm : Term := .app "pair" (.cons (.var 0) (.cons (.lit .unit) .nil))

theorem pairTerm_ty : termTy (nativeSignature []) [u] pairTerm = some T := by decide +kernel

theorem pairTerm_eval : evalTerm [Val.nat 1] pairTerm = some (Val.list [Val.nat 1, Val.unit]) := rfl

theorem env_u (w : Typed.World) : EnvTyped w [u] [Val.nat 1] := by
  refine ⟨rfl, fun i ty v hty hv => ?_⟩
  cases i with
  | zero =>
    cases Option.some.inj hty
    cases Option.some.inj hv
    exact (fits_normalize w (.union .nat .string) (Val.nat 1)).mpr (Or.inl trivial)
  | succ i => cases hty

/-- **Positive control (proved).** The pair fits the raw product, at every world. -/
theorem pair_fits (w : Typed.World) : Typed.Fits w (Val.list [Val.nat 1, Val.unit]) T :=
  evalTerm_fits_native [] (env_u w) pairTerm_ty pairTerm_eval

/-- A union of two products. -/
abbrev P : Ty := .union (.prod .nat .unit) (.prod .string .unit)

/-- `fst(p)`. -/
def fstTerm : Term := .app "fst" (.cons (.var 0) .nil)

theorem fstTerm_ty : termTy (nativeSignature []) [P] fstTerm = some (Ty.join .nat .string) := by
  decide +kernel

theorem fstTerm_eval :
    evalTerm [Val.list [Val.str "a", Val.unit]] fstTerm = some (Val.str "a") := rfl

theorem env_P (w : Typed.World) : EnvTyped w [P] [Val.list [Val.str "a", Val.unit]] := by
  refine ⟨rfl, fun i ty v hty hv => ?_⟩
  cases i with
  | zero =>
    cases Option.some.inj hty
    cases Option.some.inj hv
    exact Or.inr ⟨trivial, trivial⟩
  | succ i => cases hty

/-- **Positive control (proved).** `fst` over a union of products answers at the join. -/
theorem fst_union_fits (w : Typed.World) : Typed.Fits w (Val.str "a") (Ty.join .nat .string) :=
  evalTerm_fits_native [] (env_P w) fstTerm_ty fstTerm_eval

/-! ## Red control: the widening needs `valueVars` -/

/-- A world declaring cell 0 at `nat`. -/
def wCell : Typed.World := { initialWorld (EffTy.pure .unit) with Ρ := fun _ => some .nat }

theorem union_not_subN_nat : Ty.subN (.union .nat .string) .nat = false := by decide +kernel

/-- **Red control (proved).** At an invariant position a widening of the bindings loses
membership: the cell fits `refOf (instantiate [(0, nat)] (var 0))` and not
`refOf (instantiate [(0, nat | string)] (var 0))`, though `nat ≤ nat | string`. -/
theorem widens_needs_valueVars :
    ¬ ∀ (σ σ' : Ty.Subst) (w : Typed.World) (t : Ty) (v : Val), Ty.WidensSub σ σ' →
        Typed.Fits w v (Ty.instantiate σ t) → Typed.Fits w v (Ty.instantiate σ' t) := by
  intro h
  have hw : Ty.WidensSub [(0, .nat)] [(0, .union .nat .string)] := by
    intro j x hj
    cases j with
    | zero =>
      cases Option.some.inj hj
      exact ⟨_, rfl, by decide +kernel⟩
    | succ j => cases hj
  have hfit : Typed.Fits wCell (Val.cell ⟨0⟩) (Ty.instantiate [(0, .nat)] (.refOf (.var 0))) :=
    ⟨.nat, rfl, Ty.subN_refl _, Ty.subN_refl _⟩
  have hbad := h _ _ wCell (.refOf (.var 0)) _ hw hfit
  obtain ⟨t', hΡ, _, hback⟩ := hbad
  cases Option.some.inj hΡ
  change Ty.subN (.union .nat .string) .nat = true at hback
  rw [union_not_subN_nat] at hback
  exact Bool.noConfusion hback

-- tested: every polymorphic atom template has its parameters under value formers, and the
-- invariant template of the red control does not
#guard Ty.valueVars (.var 0) && Ty.valueVars (.option (.var 0)) && Ty.valueVars (.list (.var 0))
#guard !Ty.valueVars (.refOf (.var 0))

#print axioms pairTerm_ty
#print axioms env_u
#print axioms pair_fits
#print axioms fstTerm_ty
#print axioms env_P
#print axioms fst_union_fits
#print axioms union_not_subN_nat
#print axioms widens_needs_valueVars

/-! The step's own theorems. -/
#print axioms Effect4.Program.Ty.WidensSub.refl
#print axioms Effect4.Program.Ty.WidensSub.trans
#print axioms Effect4.Program.Ty.infer_widensSub
#print axioms Effect4.Program.Ty.matchTemplate_widensSub
#print axioms Effect4.Program.Ty.matchTemplateArgs_widensSub
#print axioms Effect4.Program.Ty.instantiate_of_noVars
#print axioms Effect4.Program.Typed.fits_unit_inv
#print axioms Effect4.Program.Typed.fits_nat_inv
#print axioms Effect4.Program.Typed.fits_bool_inv
#print axioms Effect4.Program.Typed.fits_string_inv
#print axioms Effect4.Program.Typed.fits_option_inv
#print axioms Effect4.Program.Typed.fits_nat_irrel
#print axioms Effect4.Program.Typed.FitsAll.get?
#print axioms Effect4.Program.Typed.FitsAll.nil_inv
#print axioms Effect4.Program.Typed.FitsAll.singleton_inv
#print axioms Effect4.Program.Typed.FitsAll.pair_inv
#print axioms Effect4.Program.Typed.FitsAll.triple_inv
#print axioms Effect4.Program.Typed.FitsAll.sub
#print axioms Effect4.Program.Typed.FitsAll.all_sub
#print axioms Effect4.Program.Typed.fitsAll_of_pointwise
#print axioms Effect4.Program.Typed.fits_instantiate_widens
#print axioms Effect4.Program.Typed.FitsAll.instantiate
#print axioms Effect4.Program.Typed.atomFits_of_mono
#print axioms Effect4.Program.Typed.atomFits_of_variadic
#print axioms Effect4.Program.Typed.atomFits_of_custom
#print axioms Effect4.Program.Typed.atomFits_of_poly
#print axioms Effect4.Program.Typed.atomFits_of_alts
#print axioms Effect4.Program.Typed.atomFits_of_shape
#print axioms Effect4.Program.Typed.projectProduct_fits
#print axioms Effect4.Program.Typed.queryTag_bool
#print axioms Effect4.Program.Typed.fits_queryReasons
#print axioms Effect4.Program.Typed.fits_firstErrorValue
#print axioms Effect4.Program.Typed.queryError_fits
#print axioms Effect4.Program.Typed.atomFits
#print axioms Effect4.Program.Typed.fits_lit
#print axioms Effect4.Program.Typed.evalTerm_fitsAll
#print axioms Effect4.Program.Typed.evalTerms_fitsAll
#print axioms Effect4.Program.Typed.evalTerm_fits
#print axioms Effect4.Program.Typed.evalTerm_fits_native
#print axioms Effect4.Program.Typed.heapTable_of_fits
#print axioms Effect4.Program.Typed.completionOk_of_fitsExit

end Test.Program.TermFits
