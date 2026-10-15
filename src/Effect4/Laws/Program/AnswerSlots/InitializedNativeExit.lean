import Effect4.Laws.Program.AnswerSlots.InitializedFrame
import Effect4.Laws.Machine.AnswerFlowNativeExit

/-!
Concept: store-typing R4 and scope-lifetime-finalization R11.
Question: actual terminal primitive evaluation retains the initialized writer-safe frame graph.
Reach: native finishFrame, actual retained exit code and ordered saved suffixes.
Limit: nonterminal action, park and command closure remain separate producers.
Consumer: the initialized native primitive producer and crew log-history invariant.
-/
set_option autoImplicit false
set_option maxHeartbeats 8000000
namespace Effect4.Program.AnswerSlots.Initialized
open Effect4 Effect4.Machine Effect4.Program

/-- Actual frame completion retains a writer-safe frame even before the finish command settles. -/
theorem finish_exit (spec : Spec) (completed : List (FiberId × ExitV)) (world : World)
    (input output : Kind) (machine : NativeMachine)
    (fiber : RunFiber EffName EffThunk Val Err Defect FiberId Ann Ctx) (yielding : Bool)
    (exit : ExitV) (_current : fiber.frame.current = Prim.ofExit exit)
    (owned : CodeAt spec world input fiber.frame.current)
    (_saved : Effect4.Contracts.Path (Edge spec completed world) input output fiber.frame.stack)
    (running : AnswerFlow.External.RunningStep (model spec completed) (Edge spec completed) world output
      (fiber.frame.step (interpAt spec.root completed spec.table).toPrimInterp).1) :
    let next := evaluatePrim.stepFrame (interpAt spec.root completed spec.table) machine fiber yielding
    ∃ result, AnswerFlow.FamilyResult (model spec completed) (Edge spec completed) world result
      next.fiber.frame.current next.fiber.frame.stack := by
  exact AnswerFlow.External.Native.finish_exit (model spec completed) (interpAt spec.root completed spec.table)
    (Edge spec completed) world input output machine fiber yielding owned running

/-- The current successful primitive supplies its actual answer class through the existing head law. -/
theorem success_value (spec : Spec) (fragment : SourceScope.Fragment spec.root)
    (completed : List (FiberId × ExitV)) (world : World) (input : Kind) (value : Val)
    (owned : CodeAt spec world input (.success value)) : ValueAt spec world input value := by
  have typed := head spec fragment completed world input (.success value) owned (by intro thunk wrong; cases wrong)
  cases typed with
  | success value good => exact good

/-- Actual native exit classes admit their own delivered failure and success. -/
theorem current_exit (spec : Spec) (fragment : SourceScope.Fragment spec.root)
    (completed : List (FiberId × ExitV)) (world : World) (input : Kind) (exit : ExitV)
    (owned : CodeAt spec world input (Prim.ofExit exit)) :
    AnswerFlow.ExitAt (model spec completed) world input exit := by
  cases exit with
  | success value => exact success_value spec fragment completed world input value owned
  | failure cause => exact code_phase spec world input _ owned

/-- A native terminal fallback consumes only actual absent finalizer programs. -/
theorem pure_exit_step (spec : Spec) (fragment : SourceScope.Fragment spec.root)
    (completed : List (FiberId × ExitV)) (world : World) (input output : Kind)
    (machine : NativeMachine) (fiber : RunFiber EffName EffThunk Val Err Defect FiberId Ann Ctx)
    (yielding : Bool) (exit : ExitV) (current : fiber.frame.current = Prim.ofExit exit)
    (owned : CodeAt spec world input fiber.frame.current)
    (saved : Effect4.Contracts.Path (Edge spec completed world) input output fiber.frame.stack)
    (pure : ∀ selected,
      (fiber.frame.getCont
        (match exit with | .success _ => .contA | .failure _ => .contE)
        (match exit with | .success _ => false | .failure _ => true)
        (match exit with | .success _ => none | .failure cause => some cause)).answer = .frame selected →
      AnswerFlow.programOf (model spec completed) world selected
        ((fiber.frame.getCont
          (match exit with | .success _ => .contA | .failure _ => .contE)
          (match exit with | .success _ => false | .failure _ => true)
          (match exit with | .success _ => none | .failure cause => some cause)).deliveredExit exit) = none) :
    let next := evaluatePrim.stepFrame (interpAt spec.root completed spec.table) machine fiber yielding
    ∃ result, AnswerFlow.FamilyResult (model spec completed) (Edge spec completed) world result
      next.fiber.frame.current next.fiber.frame.stack := by
  exact AnswerFlow.External.Native.pure_exit_step (model spec completed) (interpAt spec.root completed spec.table)
    (Edge spec completed) (family spec fragment completed) (mask_edge spec completed) world input output
    machine fiber yielding exit current owned saved
    (current_exit spec fragment completed world input exit (current ▸ owned))
    (fun _ _ => code_phase spec world input _ owned) (by cases exit <;> exact pure)

/-- The actual finalizer dispatcher either installs its certified wrapper or uses the checked pure return. -/
theorem finalizer_frame (spec : Spec) (fragment : SourceScope.Fragment spec.root)
    (completed : List (FiberId × ExitV)) (world : World) (input output : Kind)
    (machine : NativeMachine) (fiber : RunFiber EffName EffThunk Val Err Defect FiberId Ann Ctx)
    (yielding : Bool) (exit : ExitV) (current : fiber.frame.current = Prim.ofExit exit)
    (owned : CodeAt spec world input fiber.frame.current)
    (saved : Effect4.Contracts.Path (Edge spec completed world) input output fiber.frame.stack) :
    let next := evaluatePrim.finalizerOr (interpAt spec.root completed spec.table) machine fiber yielding exit
    ∃ result, AnswerFlow.FamilyResult (model spec completed) (Edge spec completed) world result
      next.fiber.frame.current next.fiber.frame.stack := by
  exact AnswerFlow.External.Native.finalizer_frame (model spec completed) (interpAt spec.root completed spec.table)
    (Edge spec completed) (family spec fragment completed) (mask_edge spec completed) world input output
    machine fiber yielding exit current owned saved
    (current_exit spec fragment completed world input exit (current ▸ owned))
    (fun _ _ => code_phase spec world input _ owned) (fun _ _ => rfl)

end Effect4.Program.AnswerSlots.Initialized
