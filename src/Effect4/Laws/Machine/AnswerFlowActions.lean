import Effect4.Laws.Machine.AnswerFlowHooks
import Effect4.Machine.Fibers

/-!
Concepts: store-typing R4 and scope-lifetime-finalization R11.
Question: Workers log history needs actual native mask, context and fork answer producers.
Reach: returned frames of the existing fiber-action evaluator, at a supplied world.
The application supplies each actual returned value's class and each child body's code class.
Limit: these laws supply no source, allocation, fork provenance, or command history.
Consumer: the Workers source-head and live-current-frame invariant.
-/
set_option autoImplicit false
namespace Effect4.Machine.AnswerFlow
universe u v w
open Effect4
variable {ν σ : Type u} {β : Type v} {ε δ ι α χ : Type u} {St : Type (max u v)}
variable [DecidableEq ε] [DecidableEq δ] [DecidableEq ι] [DecidableEq α]
variable {World Kind : Type w}
variable (model : Model (ν := ν) (σ := σ) (β := β) (ε := ε) (δ := δ) (ι := ι) (α := α) World Kind)
variable (interp : RunInterp ν σ β ε δ ι α χ St)

/-- An actual mask action retains the body and stack classes, or consumes its pending entry cause. -/
theorem withFiber_mask (world : World) (input output : Kind)
    (machine : RunMachine ν σ β ε δ ι α χ St) (fiber : RunFiber ν σ β ε δ ι α χ)
    (yielding flag : Bool) (body : Prim ν σ β ε δ ι α)
    (first : model.code world input body)
    (stack : StackAt model interp.toPrimInterp world input output fiber.frame.stack)
    (pending : flag = true → fiber.frame.interruptible = false →
      ∀ cause ∈ fiber.frame.interruptedCause, model.cause world input cause) :
    FrameAt model interp.toPrimInterp world output
      (evaluatePrim.withFiber interp machine fiber yielding (.setInterruptible body flag)).fiber.frame := by
  cases flag with
  | false =>
    simp only [evaluatePrim.withFiber, FrameFiber.uninterruptible]
    split
    · exact ⟨input, first, .cons (saved_mask model interp.toPrimInterp world input true) stack⟩
    · exact ⟨input, first, stack⟩
  | true =>
    simp only [evaluatePrim.withFiber, FrameFiber.interruptibleRegion]
    split
    · exact ⟨input, first, stack⟩
    · rename_i disabled
      have masked : fiber.frame.interruptible = false := Bool.eq_false_iff.mpr disabled
      cases cause : fiber.frame.interruptedCause with
      | none =>
        simp only [FrameFiber.setFiberInterruptible, cause]
        exact ⟨input, first, .cons (saved_mask model interp.toPrimInterp world input false) stack⟩
      | some reason =>
        simp only [FrameFiber.setFiberInterruptible, cause]
        exact ⟨input, model.failure world input reason (pending rfl masked reason cause),
          .cons (saved_mask model interp.toPrimInterp world input false) stack⟩

/-- Context installation answers with the actual interpreter's unit value and keeps its saved suffix. -/
theorem withFiber_setContext (world : World) (input output : Kind)
    (machine : RunMachine ν σ β ε δ ι α χ St) (fiber : RunFiber ν σ β ε δ ι α χ)
    (yielding : Bool) (context : χ)
    (good : model.value world input interp.voidValue)
    (stack : StackAt model interp.toPrimInterp world input output fiber.frame.stack) :
    FrameAt model interp.toPrimInterp world output
      (evaluatePrim.withFiber interp machine fiber yielding (.setContext context)).fiber.frame :=
  ⟨input, model.success world input interp.voidValue good, stack⟩

/-- Context reading answers with the actual current context value at the existing input class. -/
theorem withFiber_getContext (world : World) (input output : Kind)
    (machine : RunMachine ν σ β ε δ ι α χ St) (fiber : RunFiber ν σ β ε δ ι α χ)
    (yielding : Bool)
    (good : model.value world input (interp.contextValue fiber.context))
    (stack : StackAt model interp.toPrimInterp world input output fiber.frame.stack) :
    FrameAt model interp.toPrimInterp world output
      (evaluatePrim.withFiber interp machine fiber yielding .getContext).fiber.frame :=
  ⟨input, model.success world input _ good, stack⟩

/-- Forking answers its parent with the actual newly allocated fiber handle and keeps its saved suffix. -/
theorem withFiber_fork_parent (world : World) (input output : Kind)
    (machine : RunMachine ν σ β ε δ ι α χ St) (fiber : RunFiber ν σ β ε δ ι α χ)
    (yielding : Bool) (program : Prim ν σ β ε δ ι α)
    (options : Supervision.ForkOptions) (site : List Nat)
    (good : model.value world input (interp.fiberValue ⟨machine.nextId⟩))
    (stack : StackAt model interp.toPrimInterp world input output fiber.frame.stack) :
    FrameAt model interp.toPrimInterp world output
      (evaluatePrim.withFiber interp machine fiber yielding (.fork program options site)).fiber.frame := by
  cases options with
  | mk daemon immediate mode =>
    cases daemon <;> cases immediate
    all_goals exact ⟨input, model.success world input _ good, stack⟩

/-- The actual fork retains old typed rows and initializes the new child at its supplied body class.
The world and output class may depend on each row's existing fiber identity. -/
theorem withFiber_fork_rows (world : FiberId → World) (output : FiberId → Kind)
    (machine : RunMachine ν σ β ε δ ι α χ St) (fiber : RunFiber ν σ β ε δ ι α χ)
    (yielding : Bool) (program : Prim ν σ β ε δ ι α)
    (options : Supervision.ForkOptions) (site : List Nat)
    (old : ∀ row ∈ machine.fibers,
      FrameAt model interp.toPrimInterp (world row.id) (output row.id) row.frame)
    (new : model.code (world ⟨machine.nextId⟩) (output ⟨machine.nextId⟩) program) :
    ∀ row ∈ (evaluatePrim.withFiber interp machine fiber yielding (.fork program options site)).machine.fibers,
      FrameAt model interp.toPrimInterp (world row.id) (output row.id) row.frame := by
  cases options with
  | mk daemon immediate mode =>
    cases daemon <;> cases immediate
    all_goals intro row member
    all_goals dsimp only [evaluatePrim.withFiber, spawn, start, RunMachine.emit, RunMachine.arm] at member
    all_goals
      rcases List.mem_append.mp member with prior | created
      · exact old row prior
      · rw [List.mem_singleton.mp created]
        exact ⟨output ⟨machine.nextId⟩, new, .nil _ _⟩

end Effect4.Machine.AnswerFlow
