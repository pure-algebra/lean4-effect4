import Effect4.Laws.Machine.AnswerFlow

/-!
Concepts: store-typing R4 and scope-lifetime-finalization R11.
Question: compose actual saved callbacks for Workers logs and Timeout cleanup and retry.
Reach: existing state-indexed answer classes, saved frames and permitted future states.
Failure delivery requires that interruption neither defers nor skips the selected handler.
Limit: these readers supply no source, state transition or whole-history producer.
Consumers: Workers allocation continuations and Timeout completed-form callbacks.
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

/-- Actual saved lists compose at their shared intermediate answer class. -/
theorem stack_append {world : World} {input middle output : Kind}
    {first rest : List (Prim ν σ β ε δ ι α)}
    (front : StackAt model interp world input middle first)
    (suffix : StackAt model interp world middle output rest) :
    StackAt model interp world input output (first ++ rest) := by
  exact path_stack model interp (Effect4.Contracts.Path.append
    (stack_path model interp front) (stack_path model interp suffix))

/-- A callback's actual pushed frames join the older saved suffix. -/
theorem result_attach {world : World} {middle output : Kind}
    {next : Prim ν σ β ε δ ι α} {pushed : List (Prim ν σ β ε δ ι α)}
    (fiber : FrameFiber ν σ β ε δ ι α)
    (result : ResultAt model interp world middle next pushed)
    (suffix : StackAt model interp world middle output fiber.stack) :
    FrameAt model interp world output {fiber with current := next, stack := pushed ++ fiber.stack} := by
  cases result with
  | mk _ input _ _ _ current saved =>
    exact ⟨input, current, stack_append model interp saved suffix⟩

/-- A failure callback consumes the state and cause after its body fails. -/
theorem saved_failure (world : World) (input output : Kind)
    (body : Prim ν σ β ε δ ι α) (name : ν)
    (skip : ∀ nextWorld, model.future world nextWorld → ∀ value,
      model.value nextWorld input value → model.value nextWorld output value)
    (callback : ∀ nextWorld, model.future world nextWorld → ∀ cause,
      model.cause nextWorld input cause → model.code nextWorld output (interp.contE name cause))
    (discard : ∀ nextWorld, model.future world nextWorld →
      ∀ (fiber : FrameFiber ν σ β ε δ ι α) cause delivered,
      model.cause nextWorld input cause → fiber.interrupted = true →
      FrameFiber.skippedCause .contE (.onFailure body name) fiber (some cause) = some delivered →
      model.cause nextWorld output delivered) :
    SavedAt model interp world input output (.onFailure body name) := by
  refine .mk world input output _ ?_ ?_ ?_ ?_ ?_ ?_
  · intro nextWorld future value good absent
    exact skip nextWorld future value good
  · intro nextWorld future cause good absent
    cases absent
  · intro nextWorld future value provided next pushed good supplied noProgram arm
    cases arm
  · intro nextWorld future cause provided next pushed good supplied noProgram arm
    change some (interp.contE name cause, []) = some (next, pushed) at arm
    cases arm
    exact .mk nextWorld output output _ [] (callback nextWorld future cause good) (.nil nextWorld output)
  · intro nextWorld future exit next good program
    cases program
  · intro nextWorld future fiber cause delivered good _ interrupted skipped
    exact discard nextWorld future fiber cause delivered good interrupted skipped

/-- Pushing an actual failure frame retains its body and the older suffix. -/
theorem push_failure (world : World) (input middle output : Kind)
    (fiber : FrameFiber ν σ β ε δ ι α) (body : Prim ν σ β ε δ ι α) (name : ν)
    (current : fiber.current = .onFailure body name)
    (first : model.code world input body)
    (callback : SavedAt model interp world input middle (.onFailure body name))
    (stack : StackAt model interp world middle output fiber.stack) :
    ∃ next events, fiber.step interp = (.running next, events) ∧ FrameAt model interp world output next := by
  simp only [FrameFiber.step, current]
  exact ⟨_, _, rfl, input, first, .cons callback stack⟩

/-- The selected failure callback answers only when interruption does not skip it. -/
theorem resume_failure (world : World) (input middle output : Kind)
    (fiber : FrameFiber ν σ β ε δ ι α) (body : Prim ν σ β ε δ ι α) (name : ν)
    (cause : Cause ε δ ι α) (provided : Option (Exit β ε δ ι α))
    (noDeferred : fiber.deferredInterrupt = false)
    (noSkip : fiber.interrupted = false)
    (good : model.cause world input cause)
    (supplied : ∀ exit ∈ provided, ExitAt model world input exit)
    (callback : SavedAt model interp world input middle (.onFailure body name))
    (stack : StackAt model interp world middle output fiber.stack) :
    ({fiber with stack := .onFailure body name :: fiber.stack}).resumeCause interp cause provided =
      (.running {fiber with current := interp.contE name cause}, [.popped (.onFailure body name)]) ∧
    FrameAt model interp world output {fiber with current := interp.contE name cause} := by
  have code : model.code world middle (interp.contE name cause) := by
    cases callback with
    | mk _ _ _ _ _ _ _ answer _ =>
      have result := answer world (model.future_refl world) cause provided
        (interp.contE name cause) [] good supplied rfl rfl
      cases result with
      | mk _ _ _ _ _ current saved => cases saved; exact current
  constructor
  · cases fiber with
    | mk current frames interruptible interrupted deferred =>
      change deferred = false at noDeferred
      subst deferred
      cases interruptible <;> cases interrupted
      · rfl
      · rfl
      · rfl
      · cases noSkip
  · exact ⟨middle, code, stack⟩

/-- A constant continuation needs its code only when the incoming answer admits that future state.
This does not assert unrestricted transport of transient current code. -/
theorem saved_constant (world : World) (input output : Kind)
    (body next : Prim ν σ β ε δ ι α)
    (callback : ∀ nextWorld, model.future world nextWorld → ∀ value,
      model.value nextWorld input value → model.code nextWorld output next)
    (skipCause : ∀ nextWorld, model.future world nextWorld → ∀ cause,
      model.cause nextWorld input cause → model.cause nextWorld output cause) :
    SavedAt model interp world input output (.onSuccessConst body next) := by
  refine .mk world input output _ ?_ ?_ ?_ ?_ ?_ ?_
  · intro nextWorld future value good absent
    cases absent
  · intro nextWorld future cause good absent
    exact skipCause nextWorld future cause good
  · intro nextWorld future value provided code pushed good supplied noProgram arm
    change some (next, []) = some (code, pushed) at arm
    cases arm
    exact .mk nextWorld output output _ [] (callback nextWorld future value good) (.nil nextWorld output)
  · intro nextWorld future cause provided code pushed good supplied noProgram arm
    cases arm
  · intro nextWorld future exit code good program
    cases program
  · intro _ _ _ _ _ _ arm
    cases arm

/-- Pushing the actual constant frame preserves the ordered saved answer classes. -/
theorem push_constant (world : World) (input middle output : Kind)
    (fiber : FrameFiber ν σ β ε δ ι α) (body next : Prim ν σ β ε δ ι α)
    (current : fiber.current = .onSuccessConst body next)
    (first : model.code world input body)
    (callback : SavedAt model interp world input middle (.onSuccessConst body next))
    (stack : StackAt model interp world middle output fiber.stack) :
    ∃ later events, fiber.step interp = (.running later, events) ∧ FrameAt model interp world output later := by
  simp only [FrameFiber.step, current]
  exact ⟨_, _, rfl, input, first, .cons callback stack⟩

/-- The existing constant-pop equation installs the code justified by its incoming answer. -/
theorem resume_constant (world : World) (input middle output : Kind)
    (fiber : FrameFiber ν σ β ε δ ι α) (body next : Prim ν σ β ε δ ι α)
    (value : β) (provided : Option (Exit β ε δ ι α))
    (noDeferred : fiber.deferredInterrupt = false)
    (good : model.value world input value)
    (supplied : ∀ exit ∈ provided, ExitAt model world input exit)
    (callback : SavedAt model interp world input middle (.onSuccessConst body next))
    (stack : StackAt model interp world middle output fiber.stack) :
    ({fiber with stack := .onSuccessConst body next :: fiber.stack}).resumeValue interp value provided =
      (.running {fiber with current := next}, [.popped (.onSuccessConst body next)]) ∧
    FrameAt model interp world output {fiber with current := next} := by
  refine ⟨FrameFiber.resumeValue_onSuccessConst interp fiber body next value provided noDeferred, ?_⟩
  cases callback with
  | mk _ _ _ _ _ _ answer _ _ =>
    have result := answer world (model.future_refl world) value provided next [] good supplied rfl rfl
    exact result_attach model interp fiber result stack

/-- Native finalizer installation consumes the same captured exit and the actual model program.
The caller supplies the stack after its mask hook, including any restoring frame. -/
theorem install_finalizer (world : World) (input middle output : Kind)
    (fiber : FrameFiber ν σ β ε δ ι α) (body : Prim ν σ β ε δ ι α)
    (name : ν) (flag : Bool) (exit : Exit β ε δ ι α) (next : Prim ν σ β ε δ ι α)
    (good : ExitAt model world input exit)
    (callback : SavedAt model interp world input middle (.onExit body name flag))
    (installed : model.finalizer world name exit = some next)
    (stack : StackAt model interp world middle output fiber.stack) :
    FrameAt model interp world output {fiber with current := next} := by
  cases callback with
  | mk _ _ _ _ _ _ _ _ program =>
    exact ⟨middle, program world (model.future_refl world) exit next good installed, stack⟩

end Effect4.Machine.AnswerFlow
