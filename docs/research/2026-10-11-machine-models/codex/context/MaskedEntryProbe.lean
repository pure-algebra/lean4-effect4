import ReleaseAmbientBoundary
import Effect4.Laws.Program.Typed.MaskEntry
import Effect4.Laws.Program.EvaluateR
set_option autoImplicit false
namespace Test.MaskedEntryProbe
open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Typed Effect4.Program.Sched Effect4.Program.Denote

/-!
Concept: residual-program-typing, R4 and R9; helper of the closed M5 source claim.
The same ProgramArrow accepts an entry mask index without changing its stored program.
This probe tests only the actual restoring setter and actual saved onExit entries.
It does not claim a complete source, frame or machine typing instance.
-/

-- The probe uses the shared carrier, not a copied program or entry judgment.
abbrev EntryInput := AmbientEntryInput
abbrev EntryAt := AmbientEntryAt
abbrev Entry := ambientEntryBound
abbrev ProgramAt := AmbientProgAt

-- Forgetting protection changes only the physical assertion, never available services.
example {available : Env.Requirement} {frame : RSaved}
    (_protected : EntryAt (available, false) frame) : EntryAt (available, true) frame := ambientEntry_forget _protected

-- False onExit protection follows from the actual pop, for success and failure.
example (interp : RInterp) (exit : ExitV) (next : ExitV → RProgram) (frame : RSaved) :
    (popR interp exit [.resume (.onExit false) next] frame).1.interruptible = false := by
  cases exit <;> rfl

-- True onExit preserves the actual prior flag; its name alone supplies no protection.
example (interp : RInterp) (next : ExitV → RProgram) (frame : RSaved) :
    (popR interp (.success .unit) [.resume (.onExit true) next] frame).1.interruptible =
      frame.interruptible := by rfl

example (interp : RInterp) (next : ExitV → RProgram) (frame : RSaved)
    (ordinary : frame.interruptible = true) :
    ¬ EntryAt (Env.Requirement.empty, false)
      (popR interp (.success .unit) [.resume (.onExit true) next] frame).1 := by
  intro protectedEntry
  have disabled := protectedEntry rfl
  change frame.interruptible = false at disabled
  rw [ordinary] at disabled
  exact Bool.noConfusion disabled

-- Restoration covers both exits at protected entry, even when the captured map lacks prior keys.
example (root : ProgramSource) (world : Typed.World) (available : Env.Requirement)
    (previous : Ctx) (services : ServicesFit world previous.services) :
    ProgramAt root world (available, false)
      (EffTy.pure .unit, previous.services.keysRow, previous.services.keysRow)
      (fiberValR (.setContext previous) rfl) := ambient_setContext_protected root world available previous services

-- The ordinary-entry bound is a real obligation, not a restoration rule.
example : ¬ Entry (ReleaseAmbientBoundary.previous.services.keysRow, true)
    (EffTy.pure .unit, ReleaseAmbientBoundary.captured.services.keysRow,
      ReleaseAmbientBoundary.captured.services.keysRow) := by
  intro allowed
  rcases allowed with impossible | included
  · exact Bool.noConfusion impossible
  · have satisfied := (Provision.satisfies_iff_subset_keysRow _ _).mpr included
    have absent : (ReleaseAmbientBoundary.previous.services.get? ReleaseAmbientBoundary.key).isSome = false := by
      kernel_rfl
    have present : ReleaseAmbientBoundary.key ∈ ReleaseAmbientBoundary.captured.services.keysRow := by decide
    have required := satisfied ReleaseAmbientBoundary.key present
    rw [absent] at required
    exact Bool.noConfusion required
end Test.MaskedEntryProbe
