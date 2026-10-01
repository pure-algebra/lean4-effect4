import Effect4
import Effect4.Laws

/-!
Verifier of seat ORGANIZATION (2026-10-01), probe for ORG-11 (the seat left it untested).

The meaning layer's exit judgment `Effect4.Program.Denote.ExitOk answer error s ex`
(`Laws/Program/MeaningSound.lean:322`) asks a success to pass `Val.hasTy` at the DEFAULT, empty
external allocation list and to be `validIn` the store `s`; a failure's cause to pass
`causeAdmits` at `Val.hasTy`. The typed state's `Typed.FitsExit w ty ex`
(`Laws/Program/Typed/Membership.lean:150`) is `Fits` at the reified exit, at a world.

1. `exitOk_of_fitsExit` (proved): the connector holds under two premises, the world allocates
   no external handle and a successful value is valid in the store.
2. Red control A (proved): the validity premise cannot be dropped. A scope handle naming no scope
   fits `Ty.handle Ty.scopeTarget` at the initial world (`HandleFits`'s scope arm checks only the
   spelling), while `Denote.ExitOk` refuses it at the empty store (`validIn` asks for the entry).
   Note: with both `Effect4.Machine` and `Effect4.Program.Typed` open, a bare `World` is
   ambiguous (`Typed.World` against `Machine.World`): the collision ORG-12 names, met here.
3. Red control B (proved): the allocation premise cannot be dropped. At a world whose store
   allocates one external handle spelled "Foo", the handle fits `Ty.handle "Foo"`, while the
   meaning layer's shape check at the empty list refuses it.
-/

set_option autoImplicit false

open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Typed

theorem exitOk_of_fitsExit (w : Typed.World) (ty : EffTy) (s : Stores) (ex : ExitV)
    (halloc : w.state.externals.allocated = [])
    (hvalid : ∀ v, ex = .success v → v.validIn s = true)
    (h : FitsExit w ty ex) : Denote.ExitOk ty.answer ty.error s ex := by
  cases ex with
  | success v =>
    have hf : Fits w v ty.answer := (fitsExit_success_iff w ty v).mp h
    have hs := fits_hasTy w ty.answer v hf
    rw [halloc] at hs
    exact ⟨hs, hvalid v rfl⟩
  | failure c =>
    have hc : FitsCause w ty.error c := (fitsExit_failure_iff w ty c).mp h
    exact causeFits_admits (fun x hx => by
      have hs := fits_hasTy w ty.error x hx
      rw [halloc] at hs
      exact hs) c hc

#print axioms exitOk_of_fitsExit

/-- The root's declared type in the red controls: answers a scope handle. -/
def scopeRoot : EffTy := ⟨.handle Ty.scopeTarget, .never, Env.Requirement.empty⟩

/-- Red control A: a dangling scope handle fits, and the meaning layer refuses it. -/
theorem redA_scope :
    (initialWorld scopeRoot).state.externals.allocated = [] ∧
    FitsExit (initialWorld scopeRoot) scopeRoot (.success (Value.scope 7)) ∧
    ¬ Denote.ExitOk scopeRoot.answer scopeRoot.error Stores.empty (.success (Value.scope 7)) := by
  refine ⟨rfl, ?_, ?_⟩
  · exact (fitsExit_success_iff _ _ _).mpr rfl
  · intro h
    have hv : Val.validIn Stores.empty (Value.scope 7) = false := by decide
    have h2 : Val.validIn Stores.empty (Value.scope 7) = true := h.2
    rw [hv] at h2
    exact Bool.false_ne_true h2

#print axioms redA_scope

/-- A world whose store allocates one external handle spelled "Foo". -/
def fooWorld : Typed.World :=
  { initialWorld scopeRoot with
    state := { Stores.empty with externals := { ExternalStore.empty with allocated := ["Foo"] } } }

/-- Red control B: an allocated external handle fits; the meaning layer's shape check (at the
default empty allocation list) refuses it. -/
theorem redB_external :
    Fits fooWorld (Value.external 0) (.handle "Foo") ∧
    Val.hasTy (Value.external 0) (.handle "Foo") = false := by
  refine ⟨?_, by decide⟩
  exact ⟨by decide, rfl⟩

#print axioms redB_external
