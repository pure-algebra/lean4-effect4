import Effect4.Laws.Program.Typed.Context

/-!
Concept: residual-program-typing, R4; dependency of typed-state-reachable.
Control: the shared entry premise now rejects unsupported failure capabilities.
The old successful completion remains accepted with its actual failure-row bound.
This states no execution history or source admission claim.
-/
set_option autoImplicit false
namespace Test.TypedContextEntryAfter
open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Typed Effect4.Program.Sched

example (root : ProgramSource) (world : Typed.World) (available missing : Env.Requirement)
    (absent : ¬ Row.Subset missing available) :
    ¬ AmbientProg root world available (EffTy.pure .unit, available, missing)
      (.pure (.success Val.unit)) :=
  fun typed => by
    have bounded := ProgramArrow.entry typed
    exact absent bounded

example (root : ProgramSource) (world : Typed.World) (available : Env.Requirement) :
    AmbientProg root world available (EffTy.pure .unit, available, available)
      (.pure (.success Val.unit)) :=
  .pure ⟨strongExit_success _ _ _ trivial, Row.subset_refl available⟩ (Row.subset_refl available)

-- A raw setter that removes the guaranteed failure services cannot keep that guarantee.
example (root : ProgramSource) (world : Typed.World) (entry : Env.Requirement) (supplied : Ctx)
    (absent : ¬ Row.Subset entry supplied.services.keysRow) :
    ¬ AmbientProg root world entry (EffTy.pure .unit, supplied.services.keysRow, entry)
      (fiberValR (.setContext supplied) rfl) := by
  intro typed
  cases typed with
  | fiber _ _ _ _ cert _ next =>
    have returned := next world (leHost_refl world) Val.unit (show ambientFiberPost world entry
      (.setContext supplied) cert Val.unit from rfl)
    have bounded := ProgramArrow.entry returned
    exact absent bounded

end Test.TypedContextEntryAfter
