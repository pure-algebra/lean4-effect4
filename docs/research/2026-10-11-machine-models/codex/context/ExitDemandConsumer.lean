import Effect4.Laws.Program.Typed.Context

/-!
Concept: residual-program-typing, R4; dependency of typed-state-reachable.
Control: a successful setter's enlarged completion row is absent before that setter.
The available rows are lower bounds on actual service presence.
This control does not claim that failures restore the entry context.
-/
set_option autoImplicit false
namespace Test.TypedContextExitDemand
open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Typed Effect4.Program.Sched

-- A program certificate describes successful provision, not already-present entry services.
example (root : ProgramSource) (world : Typed.World) (entry : Env.Requirement) (supplied : Ctx)
    (services : ServicesFit world supplied.services) :
    AmbientProg root world entry (EffTy.pure .unit, supplied.services.keysRow, entry)
      (fiberValR (.setContext supplied) rfl) :=
  ambient_setContext_typed root world entry supplied services

-- A failure delivered before the setter cannot use that enlarged completion demand.
example (world : Typed.World) (entry : Env.Requirement) (supplied : Ctx) (cause : CauseV)
    (absent : ¬ Row.Subset supplied.services.keysRow entry) :
    ¬ AmbientExit world entry (EffTy.pure .unit, supplied.services.keysRow, supplied.services.keysRow) (.failure cause) :=
  fun typed => absent typed.2

-- The approved failure row uses the capabilities guaranteed at this actual cut.
example (world : Typed.World) (entry : Env.Requirement) (supplied : Ctx) (cause : CauseV)
    (payload : ExitOk world (EffTy.pure .unit) (.failure cause)) :
    AmbientExit world entry (EffTy.pure .unit, supplied.services.keysRow, entry) (.failure cause) :=
  ⟨payload, Row.subset_refl entry⟩

-- The actual setter retains the old context before its operation, and installs the supplied
-- context only in its actual result. No proof index changes either runtime equation.
example (root : NativeEff) (table : RowTable) (machine : NativeMachine)
    (fiber : RunFiber EffName EffThunk Val Err Defect FiberId Ann Ctx)
    (yielding : Bool) (supplied : Ctx) :
    (FiberAction.setContext (interpOf root table) machine fiber yielding supplied).fiber.context = supplied :=
  rfl

-- This is the actual loop-top failure branch, before an internal setter can run.
-- It retains whichever context this execution phase already has.
example (fiber : RunFiber EffName EffThunk Val Err Defect FiberId Ann Ctx)
    (pending : fiber.frame.deferredInterrupt = true) :
    (runloopTop fiber).frame.current = .failure fiber.frame.pendingCause ∧
      (runloopTop fiber).context = fiber.context := by
  unfold runloopTop
  split
  · exact ⟨rfl, rfl⟩
  · rename_i absent
    exact False.elim (absent pending)

end Test.TypedContextExitDemand
