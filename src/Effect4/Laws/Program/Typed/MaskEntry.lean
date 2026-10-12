import Effect4.Laws.Program.Typed.Context

/-!
Concept: residual-program-typing, R4 and R9; helper of the closed M5 source claim.
The captured release body (`Body.release`) at the ambient judgment. An interruption can reach a
program at any entry, under a mask too: the loop top and `getCont` deliver a deferred interrupt
whatever the mask (rc.112 `internal/effect.ts:639-642` and `:684-686`; equal text in 4.0.1
`:632-635` and `:679-681`). So the judgment holds every program's failure row within its entry
row at either mask (`AmbientProg`'s entry), and restoring code promises on failure only the keys
both contexts hold (`rowMeet`).
This module establishes no whole-machine preservation or outside-runtime observation.
-/
set_option autoImplicit false
namespace Effect4.Program.Typed
open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Sched Effect4.Program.Denote

/-- A program at a constant row is at every smaller constant row: its exits promise less.
Consumer: the captured release body, at the keys both possible contexts hold. -/
theorem ambientProg_shrink (root : ProgramSource) {world : Typed.World}
    {available : Env.Requirement} {type : EffTy} {row smaller : Env.Requirement} {code : RProgram}
    (sub : Row.Subset smaller row) (typed : AmbientProg root world available (type, row, row) code) :
    AmbientProg root world available (type, smaller, smaller) code :=
  ProgramArrow.outputMap typed
    (fun _ _ exit payload => ⟨payload.1,
      Row.subset_trans (show Row.Subset (ambientInput (type, smaller, smaller) exit)
        (ambientInput (type, row, row) exit) by cases exit <;> exact sub) payload.2⟩)
    (fun _ entry => ⟨Row.subset_trans sub entry.1, Row.subset_refl _⟩)

/-- **The captured release body**: the body at its own row, then the previous context restored on
every exit. It returns at the keys both the restored context and the captured one hold
(`rowMeet`): an interruption at its entry returns before the restore is installed.
Consumer: the release arm of `bodyTyped_ambient` (`Typed/Body.lean`). -/
theorem ambient_release_body (root : ProgramSource) {world : Typed.World}
    (available : Env.Requirement) (point : Point) (previous : Ctx)
    (services : ServicesFit world previous.services) (type : EffTy)
    (typed : AmbientProg root world available (type, available, available)
      (denoteAt root.program point)) :
    AmbientProg root world available
      (type, rowMeet previous.services.keysRow available, rowMeet previous.services.keysRow available)
      (bodyR (interpR root.program) (.release point previous)) := by
  change AmbientProg root world available
    (type, rowMeet previous.services.keysRow available, rowMeet previous.services.keysRow available)
    (onExitR (denoteAt root.program point) fun _ => fiberValR (.setContext previous) rfl)
  exact ambient_onExit_restore root previous services (rowMeet_left _ _)
    (ambientProg_shrink root (rowMeet_right _ _) typed)

end Effect4.Program.Typed
