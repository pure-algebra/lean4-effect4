import Effect4.Laws.Program.Typed.Membership
import Effect4.Laws.Program.MeaningSound

/-!
# Typed.ExitConnector — the typed state's exit judgment reaches the meaning layer's

Two judgments say that an exit has its program's type. The typed state's `FitsExit w ty ex`
(`Typed/Membership.lean`) reads the reified exit with `Fits` at a world, as every typed position
does. The meaning layer's `Denote.ExitHasTy answer error s ex` (`MeaningSound.lean`), which
`meaning_typed` and the run theorems conclude, reads a success with the executable shape check
`Val.hasTy` at its default, empty allocation list and asks it to be valid in the store `s`, and
a failure's cause with `causeAdmits`. `exitHasTy_of_fitsExit` takes the first to the second
under two premises, and each is necessary (the red controls are `Test/Program/ExitConnector.lean`):

* **The world allocates no external handle** (`w.state.externals.allocated = []`). `Fits` admits
  an external handle the world allocated at its spelled type, while `Val.hasTy` at the empty
  allocation list refuses every external handle, even where the handle is valid in the store
  (`allocation_needed`).
* **A successful value is valid in the store** (`v.validIn s = true`). `Fits` checks a scope
  handle by its spelling only (`HandleFits`), so a handle naming no scope fits
  `.handle Ty.scopeTarget` at the initial world, while the meaning layer asks the store for the
  scope's entry (`validity_needed`).

The typed state supplies neither premise today: `TypedState` carries no scope-handle validity
(organization verifier, `docs/research/2026-10-01-formal-pass/organization/verify.md` ORG-11 and
§3 M4), and the allocation premise holds on host-free runs only. The meaning-level judgment was
called `ExitOk` until 2026-10-01; it was renamed `ExitHasTy` (landing plan O5) so that `ExitOk`
names one judgment, the typed state's `FitsExit ∧ NoShapeDefect` (`Typed/Admission.lean`). The
proof is the organization verifier's (`verify-ExitOkConnector.lean`), at the renamed judgment.
-/

set_option autoImplicit false

namespace Effect4.Program.Typed

open Effect4 Effect4.Machine Effect4.Program

/-- `FitsExit` gives the meaning layer's exit judgment when the world allocates no external
handle and a successful value is valid in the store; each premise is necessary
(`Test/Program/ExitConnector.lean`: `allocation_needed`, `validity_needed`). -/
theorem exitHasTy_of_fitsExit (w : Typed.World) (ty : EffTy) (s : Stores) (ex : ExitV)
    (halloc : w.state.externals.allocated = [])
    (hvalid : ∀ v, ex = .success v → v.validIn s = true)
    (h : FitsExit w ty ex) : Denote.ExitHasTy ty.answer ty.error s ex := by
  cases ex with
  | success v =>
    have hf : Fits w v ty.answer := (fitsExit_success_iff w ty v).mp h
    have hs := fits_hasTy w ty.answer v hf
    rw [halloc] at hs
    exact ⟨hs, hvalid v rfl⟩
  | failure c =>
    have hc : FitsCause w ty.error c := fitsExit_failure_cause h
    exact causeFits_admits (fun x hx => by
      have hs := fits_hasTy w ty.error x hx
      rw [halloc] at hs
      exact hs) c hc

end Effect4.Program.Typed
