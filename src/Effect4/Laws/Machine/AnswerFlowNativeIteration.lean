import Effect4.Laws.Machine.AnswerFlowNativeExit
import Effect4.Laws.Program.PrimitiveProducer

/-!
Concept: store-typing R4 and reactive-scheduling R11.
Consumer: initialized crew and Atomic native iteration producers.
The existing frame-step algebra supplies the pure transition.
The connector retains the native evaluator's actual returned frame when the saved suffix drains.
Primitive writes, action results, interruption authority and command closure remain local obligations.
-/
set_option autoImplicit false
namespace Effect4.Machine.AnswerFlow.External.Native
open Effect4 Effect4.Machine Effect4.Program
universe w
variable {World Kind : Type w}
variable (model : Model (ν := EffName) (σ := EffThunk) (β := Val) (ε := Err) (δ := Defect)
  (ι := FiberId) (α := Ann) World Kind)
variable (interp : RunInterp EffName EffThunk Val Err Defect FiberId Ann Ctx Stores)
variable (Edge : World → Kind → Kind → NCode → Prop)

/-- The actual ordinary native step consumes a supplied head and its actual saved answer path. -/
theorem step_frame (world : World) (input output : Kind)
    (machine : NativeMachine) (fiber : RunFiber EffName EffThunk Val Err Defect FiberId Ann Ctx) (yielding : Bool)
    (owned : model.code world input fiber.frame.current)
    (saved : Effect4.Contracts.Path (Edge world) input output fiber.frame.stack)
    (head : HeadAt model interp.toPrimInterp Edge world input fiber.frame.current)
    (noSuccess : ∀ value, fiber.frame.current ≠ .success value)
    (noFailure : ∀ cause, fiber.frame.current ≠ .failure cause)
    (noSync : ∀ thunk, fiber.frame.current ≠ .sync thunk) :
    let next := evaluatePrim.stepFrame interp machine fiber yielding
    ∃ result, FamilyResult model Edge world result next.fiber.frame.current next.fiber.frame.stack := by
  have next : FamilyStep model Edge world output (fiber.frame.step interp.toPrimInterp).1 := by
    apply frame_step model interp.toPrimInterp Edge world input output fiber.frame head saved
    · intro value provided actual good
      rcases actual with ⟨current, supplied⟩ | ⟨thunk, current, valueEq, supplied⟩
      · exact (noSuccess value current).elim
      · exact (noSync thunk current).elim
    · intro cause current good
      exact (noFailure cause current).elim
  unfold evaluatePrim.stepFrame
  cases actual : fiber.frame.step interp.toPrimInterp with
  | mk step events =>
    rw [actual] at next
    cases step with
    | running frame => exact ⟨output, next⟩
    | finished exit =>
      have empty := Effect4.Machine.step_finished_stack interp.toPrimInterp fiber.frame exit (congrArg Prod.fst actual)
      have same : (frameExitState fiber.frame).current = fiber.frame.current := by
        unfold frameExitState
        split <;> exact getCont_current fiber.frame _ _ none
      refine ⟨input, input, ?_, ?_⟩
      · change model.code world input (frameExitState fiber.frame).current
        rw [same]
        exact owned
      · change Effect4.Contracts.Path (Edge world) input input (frameExitState fiber.frame).stack
        rw [empty]
        exact .nil input
end Effect4.Machine.AnswerFlow.External.Native
