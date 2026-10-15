import Effect4.Laws.Program.AnswerSlots.InitializedNativeParks
import Effect4.Laws.Program.PrimitiveProducer
import Effect4.Laws.Machine.AnswerFlowNativeIteration

/-!
Concept: store-typing R4 and reactive-scheduling R11.
Question: the actual loop top and scheduler yield retain initialized saved answer paths.
Reach: pending interruptions, charged operations and the evaluator's actual injected yield wrapper.
Limit: the native primitive and stored-row producers remain separate inputs to iteration assembly.
Consumer: the coupled crew command driver and its log-history endpoints.
-/
set_option autoImplicit false
namespace Effect4.Program.AnswerSlots.Initialized
open Effect4 Effect4.Machine Effect4.Program

/-- Native loop-top interruption preserves the same saved input and output classes. -/
theorem loop_top (spec : Spec) (completed : List (FiberId × ExitV)) (world : World)
    (input output : Kind) (fiber : SourceScope.SourceFiber)
    (owned : CodeAt spec world input fiber.frame.current)
    (saved : Effect4.Contracts.Path (Edge spec completed world) input output fiber.frame.stack) :
    AnswerFlow.FamilyResult (model spec completed) (Edge spec completed) world output
      (countOp (runloopTop fiber)).frame.current (countOp (runloopTop fiber)).frame.stack := by
  unfold countOp runloopTop
  split
  · exact ⟨input, .failure (code_phase spec world input _ owned), saved⟩
  · exact ⟨input, owned, saved⟩

/-- Scheduler injection retains the actual next primitive under its constant yield callback. -/
theorem injected_code (spec : Spec) (world : World) (input : Kind) (program : NCode)
    (owned : CodeAt spec world input program) :
    CodeAt spec world input (.onSuccessConst (.yieldNowWith 0) program) :=
  .yieldThen (code_phase spec world input program owned) owned

/-- An ordinary pure native step retains the actual returned frame, including drained exits. -/
theorem step_frame (spec : Spec) (fragment : SourceScope.Fragment spec.root)
    (completed : List (FiberId × ExitV)) (world : World) (input output : Kind)
    (machine : NativeMachine) (fiber : SourceScope.SourceFiber) (yielding : Bool)
    (owned : CodeAt spec world input fiber.frame.current)
    (saved : Effect4.Contracts.Path (Edge spec completed world) input output fiber.frame.stack)
    (noSuccess : ∀ value, fiber.frame.current ≠ .success value)
    (noFailure : ∀ cause, fiber.frame.current ≠ .failure cause)
    (noSync : ∀ thunk, fiber.frame.current ≠ .sync thunk) :
    let next := evaluatePrim.stepFrame (interpAt spec.root completed spec.table) machine fiber yielding
    ∃ result, AnswerFlow.FamilyResult (model spec completed) (Edge spec completed) world result
      next.fiber.frame.current next.fiber.frame.stack := by
  exact AnswerFlow.External.Native.step_frame (model spec completed)
    (interpAt spec.root completed spec.table) (Edge spec completed) world input output machine fiber yielding
    owned saved (head spec fragment completed world input fiber.frame.current owned noSync)
    noSuccess noFailure noSync
end Effect4.Program.AnswerSlots.Initialized
