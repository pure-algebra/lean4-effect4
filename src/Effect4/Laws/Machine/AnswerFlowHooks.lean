import Effect4.Laws.Machine.AnswerFlowFrames

/-!
Concepts: store-typing R4 and scope-lifetime-finalization R11.
Question: actual mask hooks serve Workers log history and Timeout cleanup ordering.
Reach: the existing ensure operation and state-indexed ordered saved frames.
Hook replacement requires the actual pending cause's incoming class.
Limit: this module supplies no cause admissibility, command history, or progress.
Consumers: typed continuation pop and native finalizer installation after its mask hook.
-/
set_option autoImplicit false
namespace Effect4.Machine.AnswerFlow
universe u v w
open Effect4
variable {ν σ : Type u} {β : Type v} {ε δ ι α : Type u}
variable [DecidableEq ε] [DecidableEq δ] [DecidableEq ι] [DecidableEq α]
variable {World Kind : Type w}
variable (model : Model (ν := ν) (σ := σ) (β := β) (ε := ε) (δ := δ) (ι := ι) (α := α) World Kind)
variable (interp : PrimInterp ν σ β ε δ ι α)

/-- A restoring mask's saved answer classes agree; its hook has a separate cause obligation. -/
theorem saved_mask (world : World) (kind : Kind) (flag : Bool) :
    SavedAt model interp world kind kind (.setInterruptible flag) := by
  refine .mk world kind kind _ ?_ ?_ ?_ ?_ ?_ ?_
  · intro _ _ _ good _; exact good
  · intro _ _ _ good _; exact good
  · intro _ _ _ _ _ _ _ _ _ impossible; cases impossible
  · intro _ _ _ _ _ _ _ _ _ impossible; cases impossible
  · intro _ _ _ _ _ impossible; cases impossible
  · intro _ _ _ _ _ _ arm; cases arm

/-- Every actual hook retains the ordered suffix, inserting only an identity mask frame. -/
theorem ensure_stack (world : World) (input output : Kind)
    (code : Prim ν σ β ε δ ι α) (fiber : FrameFiber ν σ β ε δ ι α)
    (stack : StackAt model interp world input output fiber.stack) :
    StackAt model interp world input output (code.ensure fiber).1.stack := by
  rcases FrameFiber.ensure_stack_cases code fiber with kept | ⟨pushed, _, _⟩
  · rw [kept]; exact stack
  · rw [pushed]; exact .cons (saved_mask model interp world input true) stack

/-- A hook's substituted failure consumes its actual stored interruption cause.
A mask frame's saved contract transports that cause to the class expected by its older suffix. -/
theorem ensure_replacement (world : World) (input middle output : Kind)
    (code next : Prim ν σ β ε δ ι α) (fiber : FrameFiber ν σ β ε δ ι α)
    (callback : SavedAt model interp world input middle code)
    (pending : ∀ cause ∈ fiber.interruptedCause, model.cause world input cause)
    (stack : StackAt model interp world middle output fiber.stack)
    (installed : (code.ensure fiber).2 = some next) :
    FrameAt model interp world output {(code.ensure fiber).1 with current := next} := by
  have suffix := ensure_stack model interp world middle output code fiber stack
  cases code with
  | setInterruptible flag =>
    cases found : fiber.interruptedCause with
    | none => simp only [Prim.ensure, found] at installed; cases installed
    | some cause =>
      cases flag with
      | false => simp only [Prim.ensure, found] at installed; cases installed
      | true =>
        simp only [Prim.ensure, found] at installed
        change some (.failure cause) = some next at installed
        cases installed
        have good := pending cause found
        cases callback with
        | mk _ _ _ _ _ skip _ _ _ =>
          exact ⟨middle, model.failure world middle cause
            (skip world (model.future_refl world) cause good rfl), suffix⟩
  | onExit body name flag =>
    simp only [Prim.ensure] at installed
    split at installed <;> cases installed
  | asyncFinalizer name =>
    simp only [Prim.ensure] at installed
    split at installed <;> cases installed
  | _ => cases installed

/-- Native finalizer installation retains the actual mask hook's saved suffix.
The installed program still consumes exactly the captured exit supplied to its callback. -/
theorem install_finalizer_after_ensure (world : World) (input middle output : Kind)
    (fiber : FrameFiber ν σ β ε δ ι α) (body : Prim ν σ β ε δ ι α)
    (name : ν) (flag : Bool) (exit : Exit β ε δ ι α) (next : Prim ν σ β ε δ ι α)
    (good : ExitAt model world input exit)
    (callback : SavedAt model interp world input middle (.onExit body name flag))
    (installed : model.finalizer world name exit = some next)
    (stack : StackAt model interp world middle output fiber.stack) :
    FrameAt model interp world output {((Prim.onExit body name flag).ensure fiber).1 with current := next} :=
  install_finalizer model interp world input middle output _ body name flag exit next good callback installed
    (ensure_stack model interp world middle output (.onExit body name flag) fiber stack)

omit [DecidableEq ε] [DecidableEq δ] [DecidableEq ι] [DecidableEq α] in
/-- An actual protected finalizer hook cannot be discarded by the interrupted-handler branch. -/
theorem ensure_protected_not_interrupted (body : Prim ν σ β ε δ ι α) (name : ν)
    (fiber : FrameFiber ν σ β ε δ ι α) :
    ((Prim.onExit body name false).ensure fiber).1.interrupted = false := by
  cases fiber with
  | mk current stack flag pending deferred => cases flag <;> rfl

end Effect4.Machine.AnswerFlow
