import Effect4.Program.Compile

/-!
Concept: residual-program-typing, R4; dependency of typed-state-reachable.
Control: a successful setter's enlarged completion row is absent before that setter.
The available rows are lower bounds on actual service presence.
This control does not claim that failures restore the entry context.
-/
set_option autoImplicit false
namespace Test.TypedContextExitDemand
open Effect4 Effect4.Machine Effect4.Program

-- This concrete required service is absent at the empty entry row.
#guard ¬ Row.Subset (Env.Requirement.single Env.scopeKey) Env.Requirement.empty

-- The actual setter retains the old context before its operation, and installs the supplied
-- context only in its actual result. No proof index changes either runtime equation.
example (root : NativeEff) (table : RowTable) (machine : RunMachine EffName EffThunk Val Err Defect FiberId Ann Ctx Stores)
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
