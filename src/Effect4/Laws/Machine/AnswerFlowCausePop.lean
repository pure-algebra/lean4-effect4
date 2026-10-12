import Effect4.Laws.Machine.AnswerFlowPop

/-!
Concepts: store-typing R4 and scope-lifetime-finalization R11.
Question: actual failure selection serves Workers log history and Timeout cleanup.
Reach: the existing fused failure pop, including actual interrupted handler discards.
The saved contract supplies each discarded handler's exact sanitized-cause transport.
Limit: source and command histories must still produce the input cause and saved contracts.
Consumer: actual native failure callback and finalizer selection.
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

/-- The fused failure pop discards a restoring mask's replacement and retains its carried cause.
Consumer: the structural induction proceeds through the original saved list. -/
theorem drain_cause (code : Prim ν σ β ε δ ι α) (fiber : FrameFiber ν σ β ε δ ι α)
    (cause : Cause ε δ ι α) (empty : fiber.stack = []) :
    (FrameFiber.passPushed .contE true (code.ensure fiber).1 (some cause)).answer = .empty ∧
    (FrameFiber.passPushed .contE true (code.ensure fiber).1 (some cause)).carriedCause = some cause :=
  External.drain_cause code fiber cause empty

/-- Passing an interrupted saved frame uses its exact discard or missing-arm clause. -/
theorem saved_discard_cause (world : World) (input middle : Kind)
    (code : Prim ν σ β ε δ ι α) (fiber : FrameFiber ν σ β ε δ ι α)
    (cause : Cause ε δ ι α)
    (saved : SavedAt model interp world input middle code)
    (good : model.cause world input cause)
    (interrupted : (code.ensure fiber).1.interrupted = true) :
    ∃ delivered, FrameFiber.skippedCause .contE code (code.ensure fiber).1 (some cause) = some delivered ∧
      model.cause world middle delivered :=
  External.saved_discard_cause model interp (SavedAt model interp) (saved_family model interp)
    world input middle code fiber cause saved good interrupted

/-- The selected failure callback retains the cause actually carried past earlier discarded handlers. -/
theorem popFrom_cause_selected (world : World) (input output : Kind)
    (frames : List (Prim ν σ β ε δ ι α)) (fiber : FrameFiber ν σ β ε δ ι α)
    (cause : Cause ε δ ι α) (selected : Prim ν σ β ε δ ι α)
    (empty : fiber.stack = [])
    (good : model.cause world input cause)
    (stack : StackAt model interp world input output frames)
    (found : (FrameFiber.popFrom .contE true frames fiber (some cause)).answer = .frame selected) :
    ∃ incoming middle delivered,
      (FrameFiber.popFrom .contE true frames fiber (some cause)).carriedCause = some delivered ∧
      model.cause world incoming delivered ∧ SavedAt model interp world incoming middle selected ∧
      StackAt model interp world middle output
        (FrameFiber.popFrom .contE true frames fiber (some cause)).fiber.stack := by
  obtain ⟨incoming, middle, delivered, carried, good, callback, suffix⟩ :=
    External.popFrom_cause_selected model interp (SavedAt model interp) (saved_family model interp)
      (fun world kind => saved_mask model interp world kind true) world input output frames fiber cause selected
      empty good (stack_path model interp stack) found
  exact ⟨incoming, middle, delivered, carried, good, callback, path_stack model interp suffix⟩

/-- Actual getCont selects a failure callback at the class of its delivered cause. -/
theorem getCont_cause_selected (world : World) (input output : Kind)
    (fiber : FrameFiber ν σ β ε δ ι α) (cause : Cause ε δ ι α)
    (selected : Prim ν σ β ε δ ι α)
    (good : model.cause world input cause)
    (stack : StackAt model interp world input output fiber.stack)
    (found : (fiber.getCont .contE true (some cause)).answer = .frame selected) :
    ∃ incoming middle delivered,
      (fiber.getCont .contE true (some cause)).carriedCause = some delivered ∧
      model.cause world incoming delivered ∧ SavedAt model interp world incoming middle selected ∧
      StackAt model interp world middle output (fiber.getCont .contE true (some cause)).fiber.stack := by
  simp only [FrameFiber.getCont, Bool.not_true, Bool.and_false, Bool.false_eq_true, ↓reduceIte] at found ⊢
  exact popFrom_cause_selected model interp world input output fiber.stack _ cause selected rfl good stack found

/-- The actual selected failure arm consumes the carried cause and retains its older suffix. -/
theorem resumeCause_selected (world : World) (input output : Kind)
    (fiber : FrameFiber ν σ β ε δ ι α) (cause : Cause ε δ ι α)
    (selected next : Prim ν σ β ε δ ι α) (pushed : List (Prim ν σ β ε δ ι α))
    (good : model.cause world input cause)
    (stack : StackAt model interp world input output fiber.stack)
    (found : (fiber.getCont .contE true (some cause)).answer = .frame selected)
    (pure : programOf model world selected
      ((fiber.getCont .contE true (some cause)).deliveredExit (.failure cause)) = none)
    (evaluated : selected.armE interp
      ((fiber.getCont .contE true (some cause)).carriedCause.getD cause) none = some (next, pushed)) :
    ∃ events, fiber.resumeCause interp cause none =
      (.running {(fiber.getCont .contE true (some cause)).fiber with
        current := next
        stack := pushed ++ (fiber.getCont .contE true (some cause)).fiber.stack}, events) ∧
      FrameAt model interp world output {(fiber.getCont .contE true (some cause)).fiber with
        current := next
        stack := pushed ++ (fiber.getCont .contE true (some cause)).fiber.stack} := by
  obtain ⟨events, equation, head, code, path⟩ :=
    External.resumeCause_selected model interp (SavedAt model interp) (saved_family model interp)
      (fun world kind => saved_mask model interp world kind true) world input output fiber cause selected next pushed
      good (stack_path model interp stack) found pure evaluated
  exact ⟨events, equation, head, code, path_stack model interp path⟩

/-- Native failure finalization consumes the selected frame's actual delivered exit. -/
theorem getCont_cause_finalizer (world : World) (input output : Kind)
    (fiber : FrameFiber ν σ β ε δ ι α) (cause : Cause ε δ ι α)
    (body next : Prim ν σ β ε δ ι α) (name : ν) (flag : Bool)
    (good : model.cause world input cause)
    (stack : StackAt model interp world input output fiber.stack)
    (found : (fiber.getCont .contE true (some cause)).answer = .frame (.onExit body name flag))
    (installed : model.finalizer world name
      ((fiber.getCont .contE true (some cause)).deliveredExit (.failure cause)) = some next) :
    FrameAt model interp world output {(fiber.getCont .contE true (some cause)).fiber with current := next} := by
  obtain ⟨input, code, path⟩ := External.getCont_cause_finalizer model interp (SavedAt model interp)
    (saved_family model interp) (fun world kind => saved_mask model interp world kind true)
    world input output fiber cause (.onExit body name flag) next good (stack_path model interp stack) found installed
  exact ⟨input, code, path_stack model interp path⟩

end Effect4.Machine.AnswerFlow
