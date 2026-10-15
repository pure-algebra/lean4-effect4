import Effect4.Laws.Program.AnswerSlots.InitializedNativeParks
import Effect4.Laws.Program.PrimitiveProducer

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
  have next := nonterminal_step spec fragment completed world input output fiber.frame owned saved noSuccess noFailure noSync
  unfold evaluatePrim.stepFrame
  cases actual : fiber.frame.step (interpAt spec.root completed spec.table).toPrimInterp with
  | mk step events =>
    rw [actual] at next
    cases step with
    | running frame => exact ⟨output, next⟩
    | finished exit =>
      have empty := Effect4.Machine.step_finished_stack
        (interpAt spec.root completed spec.table).toPrimInterp fiber.frame exit (congrArg Prod.fst actual)
      have same : (frameExitState fiber.frame).current = fiber.frame.current := by
        unfold frameExitState
        split <;> exact getCont_current fiber.frame _ _ none
      refine ⟨input, input, ?_, ?_⟩
      · change CodeAt spec world input (frameExitState fiber.frame).current
        rw [same]
        exact owned
      · change Effect4.Contracts.Path (Edge spec completed world) input input (frameExitState fiber.frame).stack
        rw [empty]
        exact .nil input
end Effect4.Program.AnswerSlots.Initialized
