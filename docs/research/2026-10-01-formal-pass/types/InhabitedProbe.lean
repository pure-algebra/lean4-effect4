import Effect4.Laws.Program.Typed.Membership
import Effect4.Laws.Program.TypeAlgebra
import Effect4.Program.Fold

/-!
# Seat TYPES, formal pass (2026-10-01): DI-67's inhabitance check as a fold, against `Fits`

Research probe, outside every root; nothing imports it. Row 127 (ruled 2026-10-01) repairs
DI-67 with "a decidable `inhabited : Ty → Bool` agreeing with `Fits`, checked at admission".
This probe writes that check over the tree's own `Ty` as a `TyAlgebra` (so it is a fold by the
census rule) and checks the agreement theorem's shape against the tree's own `Typed.Fits` and
`Val.hasTy` (DI-67's frozen statement reads `Val.hasTy`).

* §1 (proved) soundness, both judgments: a type with a member at some world (or under some
  allocation table) is `inhabited`. Contrapositive: refusing `inhabited t = false` never refuses
  a type with a member. Structural recursion on `Ty`; no premise.
* §2 (proved) completeness on the handle-free fragment, with a world-independent witness:
  `inhabited t = true → ∃ v, ∀ w, Fits w v t`. The handle constructors are inhabited at every
  argument in some world (`fiberOf never never` included); one world for several handle
  positions at once (amalgamation by fresh keys) is the owed part.
* §3 (proved) closure under the raw order: `sub a b → inhabited a → inhabited b`
  (`fun_induction Ty.sub`, as `fits_sub`).
* §4 (proved, RED CONTROLS kept) DI-67's gap: `prod never nat` and `except never never` are
  canonical, not `never`, and have no member at any world; the proposed admission predicate
  refuses them. `list int` is inhabited, so the `int` scan stays a separate, syntactic refusal.
-/

set_option autoImplicit false

namespace Research.TypesSeat.Inhabit

open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Typed
open Effect4.Machine.Env (Requirement)

/-! ## The check, as a fold -/

/-- One carrier field per `Ty` constructor. A handle is inhabited in some world (an internal
kind declared there, an external allocation, a context); `option`, `list`, `exitOf` and
`causeOf` by `none`, `[]`, a failure with no typed reason and the empty cause. -/
def inhabitedAlg : TyAlgebra (fun _ => Bool) where
  ty_never := false
  ty_unit := true
  ty_nat := true
  ty_int := false
  ty_string := true
  ty_bool := true
  ty_handle _ := true
  ty_option _ := true
  ty_list _ := true
  ty_prod a b := a && b
  ty_except e a := e || a
  ty_exitOf _ _ := true
  ty_causeOf _ := true
  ty_fiberOf _ _ := true
  ty_union l r := l || r
  ty_lit _ := true
  ty_refOf _ := true
  ty_deferredOf _ _ := true
  ty_var _ := false
  ty_unknown := true

def inhabited (t : Ty) : Bool := cata_ty inhabitedAlg t

/-- No handle, fiber, cell or deferred anywhere: the data fragment, world-free. -/
def handleFreeAlg : TyAlgebra (fun _ => Bool) where
  ty_never := true
  ty_unit := true
  ty_nat := true
  ty_int := true
  ty_string := true
  ty_bool := true
  ty_handle _ := false
  ty_option a := a
  ty_list a := a
  ty_prod a b := a && b
  ty_except e a := e && a
  ty_exitOf a e := a && e
  ty_causeOf e := e
  ty_fiberOf _ _ := false
  ty_union l r := l && r
  ty_lit _ := true
  ty_refOf _ := false
  ty_deferredOf _ _ := false
  ty_var _ := true
  ty_unknown := true

def handleFree (t : Ty) : Bool := cata_ty handleFreeAlg t

/-! ## §1 Soundness: a member makes the check true (both judgments) -/

theorem inhabited_of_fits (w : Typed.World) : ∀ (t : Ty) (v : Val), Fits w v t → inhabited t = true := by
  intro t
  induction t with
  | never => intro v h; exact h.elim
  | int => intro v h; exact h.elim
  | var _ => intro v h; exact h.elim
  | unit | nat | string | bool | handle | option | list | exitOf | causeOf | fiberOf | lit
  | refOf | deferredOf | unknown => intro _ _; rfl
  | prod a b iha ihb =>
    intro v h
    simp only [Typed.Fits] at h
    split at h
    · show (inhabited a && inhabited b) = true
      rw [iha _ h.1, ihb _ h.2]
      rfl
    · exact h.elim
  | except e a ihe iha =>
    intro v h
    simp only [Typed.Fits] at h
    split at h
    · show (inhabited e || inhabited a) = true
      rw [ihe _ h]
      rfl
    · show (inhabited e || inhabited a) = true
      rw [iha _ h, Bool.or_true]
    · exact h.elim
  | union l r ihl ihr =>
    intro v h
    show (inhabited l || inhabited r) = true
    rcases h with h | h
    · rw [ihl v h]
      rfl
    · rw [ihr v h, Bool.or_true]

/-- DI-67's frozen statement reads `Val.hasTy` under some allocation table. -/
theorem inhabited_of_hasTy :
    ∀ (t : Ty) (v : Val) (alloc : List String), Val.hasTy v t alloc = true → inhabited t = true := by
  intro t
  induction t with
  | never => intro v alloc h; exact Bool.noConfusion h
  | int => intro v alloc h; exact Bool.noConfusion h
  | var _ => intro v alloc h; exact Bool.noConfusion h
  | unit | nat | string | bool | handle | option | list | exitOf | causeOf | fiberOf | lit
  | refOf | deferredOf | unknown => intro _ _ _; rfl
  | prod a b iha ihb =>
    intro v alloc h
    simp only [Val.hasTy] at h
    split at h
    · obtain ⟨h1, h2⟩ := Bool.and_eq_true_iff.mp h
      show (inhabited a && inhabited b) = true
      rw [iha _ _ h1, ihb _ _ h2]
      rfl
    · exact Bool.noConfusion h
  | except e a ihe iha =>
    intro v alloc h
    simp only [Val.hasTy] at h
    split at h
    · show (inhabited e || inhabited a) = true
      rw [ihe _ _ h]
      rfl
    · show (inhabited e || inhabited a) = true
      rw [iha _ _ h, Bool.or_true]
    · exact Bool.noConfusion h
  | union l r ihl ihr =>
    intro v alloc h
    simp only [Val.hasTy] at h
    show (inhabited l || inhabited r) = true
    rcases Bool.or_eq_true_iff.mp h with h | h
    · rw [ihl _ _ h]
      rfl
    · rw [ihr _ _ h, Bool.or_true]

/-! ## §2 Completeness: world-free witnesses on the handle-free fragment -/

theorem fits_of_inhabited_handleFree :
    ∀ t : Ty, handleFree t = true → inhabited t = true → ∃ v : Val, ∀ w : Typed.World, Fits w v t := by
  intro t
  induction t with
  | never => intro _ hi; exact absurd hi (by decide)
  | int => intro _ hi; exact absurd hi (by decide)
  | var _ => intro _ hi; exact Bool.noConfusion hi
  | handle _ => intro hf _; exact Bool.noConfusion hf
  | fiberOf _ _ _ _ => intro hf _; exact Bool.noConfusion hf
  | refOf _ _ => intro hf _; exact Bool.noConfusion hf
  | deferredOf _ _ _ _ => intro hf _; exact Bool.noConfusion hf
  | unit => intro _ _; exact ⟨.unit, fun _ => trivial⟩
  | nat => intro _ _; exact ⟨.nat 0, fun _ => trivial⟩
  | string => intro _ _; exact ⟨.str "", fun _ => trivial⟩
  | bool => intro _ _; exact ⟨.bool true, fun _ => trivial⟩
  | lit s => intro _ _; exact ⟨.str s, fun _ => rfl⟩
  | option _ _ => intro _ _; exact ⟨.none, fun _ => trivial⟩
  | unknown => intro _ _; exact ⟨.unit, fun _ => live_of_keys_nil rfl⟩
  | list a _ =>
    intro _ _
    refine ⟨.list [], fun w => ?_⟩
    intro x hx
    nomatch hx
  | exitOf a e _ _ =>
    intro _ _
    exact ⟨Val.exitErr ⟨[]⟩, fun w =>
      (fitsExit_failure_iff w ⟨a, e, Requirement.empty⟩ ⟨[]⟩).mpr (fun _ hr => nomatch hr)⟩
  | causeOf e _ =>
    intro _ _
    refine ⟨Val.exitErr ⟨[]⟩, fun w => ?_⟩
    have hc : Val.cause? (Val.exitErr ⟨[]⟩) = some ⟨[]⟩ := causeImage.ofVal_toVal ⟨[]⟩
    simp only [Typed.Fits, hc]
    intro _ hr
    nomatch hr
  | prod a b iha ihb =>
    intro hf hi
    have hf' : (handleFree a && handleFree b) = true := hf
    have hi' : (inhabited a && inhabited b) = true := hi
    obtain ⟨hfa, hfb⟩ := Bool.and_eq_true_iff.mp hf'
    obtain ⟨hia, hib⟩ := Bool.and_eq_true_iff.mp hi'
    obtain ⟨va, hva⟩ := iha hfa hia
    obtain ⟨vb, hvb⟩ := ihb hfb hib
    exact ⟨.list [va, vb], fun w => fits_pair (hva w) (hvb w)⟩
  | except e a ihe iha =>
    intro hf hi
    have hf' : (handleFree e && handleFree a) = true := hf
    have hi' : (inhabited e || inhabited a) = true := hi
    obtain ⟨hfe, hfa⟩ := Bool.and_eq_true_iff.mp hf'
    rcases Bool.or_eq_true_iff.mp hi' with hie | hia
    · obtain ⟨ve, hve⟩ := ihe hfe hie
      exact ⟨.ctor 0 [ve], fun w => hve w⟩
    · obtain ⟨va, hva⟩ := iha hfa hia
      exact ⟨.ctor 1 [va], fun w => hva w⟩
  | union l r ihl ihr =>
    intro hf hi
    have hf' : (handleFree l && handleFree r) = true := hf
    have hi' : (inhabited l || inhabited r) = true := hi
    obtain ⟨hfl, hfr⟩ := Bool.and_eq_true_iff.mp hf'
    rcases Bool.or_eq_true_iff.mp hi' with hil | hir
    · obtain ⟨v, hv⟩ := ihl hfl hil
      exact ⟨v, fun w => Or.inl (hv w)⟩
    · obtain ⟨v, hv⟩ := ihr hfr hir
      exact ⟨v, fun w => Or.inr (hv w)⟩

/-- The agreement on the handle-free fragment, both directions. -/
theorem inhabited_iff_handleFree (t : Ty) (hf : handleFree t = true) :
    inhabited t = true ↔ ∃ (w : Typed.World) (v : Val), Fits w v t := by
  constructor
  · intro hi
    obtain ⟨v, hv⟩ := fits_of_inhabited_handleFree t hf hi
    exact ⟨initialWorld (EffTy.pure .unit), v, hv _⟩
  · rintro ⟨w, v, h⟩
    exact inhabited_of_fits w t v h

/-- The handle constructors are inhabited at every argument, in some world: a fiber declared at
the columns (even `never`, `never`: a fiber that never completes), a cell, a deferred. -/
theorem fiber_inhabited (a e : Ty) :
    Fits (initialWorld ⟨a, e, Requirement.empty⟩) (Val.fiber Api.root) (.fiberOf a e) :=
  ⟨⟨a, e, Requirement.empty⟩, rfl, Ty.sub_refl _, Ty.sub_refl _⟩

theorem cell_inhabited (t : Ty) :
    Fits { initialWorld (EffTy.pure .unit) with Ρ := fun _ => some t } (Val.cell ⟨0⟩) (.refOf t) :=
  ⟨t, rfl, Ty.sub_refl _, Ty.sub_refl _⟩

theorem promise_inhabited (a e : Ty) :
    Fits { initialWorld (EffTy.pure .unit) with «Π» := fun _ => some (a, e) } (Val.promise ⟨0⟩)
      (.deferredOf a e) :=
  ⟨a, e, rfl, ⟨Ty.sub_refl _, Ty.sub_refl _⟩, ⟨Ty.sub_refl _, Ty.sub_refl _⟩⟩

/-! ## §3 Closure under the raw order -/

theorem inhabited_sub {a b : Ty} (hsub : Ty.sub a b = true) : inhabited a = true → inhabited b = true := by
  fun_induction Ty.sub a b
  case case1 => exact id
  case case2 => intro h; exact absurd h (by decide)
  case case3 a1 a2 b _ iha ihb =>
    obtain ⟨h1, h2⟩ := Bool.and_eq_true_iff.mp hsub
    intro h
    have h' : (inhabited a1 || inhabited a2) = true := h
    rcases Bool.or_eq_true_iff.mp h' with h | h
    · exact iha h1 h
    · exact ihb h2 h
  case case4 a b1 b2 _ _ _ iha ihb =>
    intro h
    show (inhabited b1 || inhabited b2) = true
    rcases Bool.or_eq_true_iff.mp hsub with hx | hx
    · rw [iha hx h]
      rfl
    · rw [ihb hx h, Bool.or_true]
  case case5 => intro _; rfl
  case case6 => intro _; rfl
  case case7 => intro _; rfl
  case case8 => intro _; rfl
  case case9 a1 a2 b1 b2 _ iha ihb =>
    obtain ⟨h1, h2⟩ := Bool.and_eq_true_iff.mp hsub
    intro h
    have h' : (inhabited a1 && inhabited a2) = true := h
    obtain ⟨i1, i2⟩ := Bool.and_eq_true_iff.mp h'
    show (inhabited b1 && inhabited b2) = true
    rw [iha h1 i1, ihb h2 i2]
    rfl
  case case10 e1 a1 e2 a2 _ ihe iha =>
    obtain ⟨h1, h2⟩ := Bool.and_eq_true_iff.mp hsub
    intro h
    have h' : (inhabited e1 || inhabited a1) = true := h
    show (inhabited e2 || inhabited a2) = true
    rcases Bool.or_eq_true_iff.mp h' with h | h
    · rw [ihe h1 h]
      rfl
    · rw [iha h2 h, Bool.or_true]
  case case11 => intro _; rfl
  case case12 => intro _; rfl
  case case13 => intro _; rfl
  case case14 => intro _; rfl
  case case15 => intro _; rfl
  case case16 => exact Bool.noConfusion hsub

/-! ## §4 DI-67's gap on the tree (red controls) and the admission predicate -/

/-- Row 127's proposed column check: canonical `never`, or inhabited. -/
def admitColumn (t : Ty) : Bool := t.normalize == .never || inhabited t

theorem prod_never_nat_canonical : (Ty.prod .never .nat).normalize = .prod .never .nat :=
  (Ty.Normal.prod .never .nat rfl rfl).fixed

theorem except_never_never_canonical : (Ty.except .never .never).normalize = .except .never .never :=
  (Ty.Normal.except .never .never).fixed

/-- **Red control.** Canonical, not `never`, and no member at any world. -/
theorem prod_never_nat_empty (w : Typed.World) (v : Val) : ¬ Fits w v (.prod .never .nat) :=
  fun h => absurd (inhabited_of_fits w _ v h) (by decide)

theorem except_never_never_empty (w : Typed.World) (v : Val) : ¬ Fits w v (.except .never .never) :=
  fun h => absurd (inhabited_of_fits w _ v h) (by decide)

/-- And none under any allocation table, in DI-67's own words. -/
theorem prod_never_nat_no_hasTy (v : Val) (alloc : List String) :
    Val.hasTy v (.prod .never .nat) alloc = false := by
  cases h : Val.hasTy v (.prod .never .nat) alloc with
  | false => rfl
  | true => exact absurd (inhabited_of_hasTy _ v alloc h) (by decide)

theorem admit_refuses_prod_never_nat : admitColumn (.prod .never .nat) = false := by
  unfold admitColumn
  rw [prod_never_nat_canonical]
  rfl

theorem admit_refuses_except_never_never : admitColumn (.except .never .never) = false := by
  unfold admitColumn
  rw [except_never_never_canonical]
  rfl

-- tested: the designed bottom and the always-inhabited formers stay admitted
#guard admitColumn .never
#guard admitColumn (.union .never .never)
#guard admitColumn (.list .never)
#guard admitColumn (.option .never)
#guard admitColumn (.fiberOf .never .never)
#guard admitColumn (.exitOf .never .never)
#guard admitColumn (.except .never .nat)
#guard !admitColumn (.prod .nat (.except .never .never))
-- tested: `int` is refused by inhabitance only where it empties the type; the `int` scan
-- (`findInt`, `Program/Admission.lean:31-41`) refuses `list int` syntactically, inhabitance
-- does not: two refusals, not one
#guard !admitColumn .int
#guard admitColumn (.list .int)
#guard (findInt [] (.list .int)).isSome

end Research.TypesSeat.Inhabit

#print axioms Research.TypesSeat.Inhabit.inhabited_of_fits
#print axioms Research.TypesSeat.Inhabit.inhabited_of_hasTy
#print axioms Research.TypesSeat.Inhabit.fits_of_inhabited_handleFree
#print axioms Research.TypesSeat.Inhabit.inhabited_iff_handleFree
#print axioms Research.TypesSeat.Inhabit.fiber_inhabited
#print axioms Research.TypesSeat.Inhabit.cell_inhabited
#print axioms Research.TypesSeat.Inhabit.promise_inhabited
#print axioms Research.TypesSeat.Inhabit.inhabited_sub
#print axioms Research.TypesSeat.Inhabit.prod_never_nat_canonical
#print axioms Research.TypesSeat.Inhabit.except_never_never_canonical
#print axioms Research.TypesSeat.Inhabit.prod_never_nat_empty
#print axioms Research.TypesSeat.Inhabit.except_never_never_empty
#print axioms Research.TypesSeat.Inhabit.prod_never_nat_no_hasTy
#print axioms Research.TypesSeat.Inhabit.admit_refuses_prod_never_nat
#print axioms Research.TypesSeat.Inhabit.admit_refuses_except_never_never
