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
    (FrameFiber.passPushed .contE true (code.ensure fiber).1 (some cause)).carriedCause = some cause := by
  rcases FrameFiber.ensure_stack_cases code fiber with kept | ⟨pushed, _, _⟩
  · simp only [FrameFiber.passPushed, kept.trans empty]
    exact ⟨True.intro, True.intro⟩
  · have shape : (code.ensure fiber).1.stack = [.setInterruptible true] := by rw [pushed, empty]
    simp only [FrameFiber.passPushed, shape]
    cases pending : (code.ensure fiber).1.interruptedCause with
    | none => simp only [Prim.ensure]; exact ⟨rfl, rfl⟩
    | some interrupted => simp only [Prim.ensure]; exact ⟨rfl, rfl⟩

/-- Passing an interrupted saved frame uses its exact discard or missing-arm clause. -/
theorem saved_discard_cause (world : World) (input middle : Kind)
    (code : Prim ν σ β ε δ ι α) (fiber : FrameFiber ν σ β ε δ ι α)
    (cause : Cause ε δ ι α)
    (saved : SavedAt model interp world input middle code)
    (good : model.cause world input cause)
    (interrupted : (code.ensure fiber).1.interrupted = true) :
    ∃ delivered, FrameFiber.skippedCause .contE code (code.ensure fiber).1 (some cause) = some delivered ∧
      model.cause world middle delivered := by
  cases arm : code.hasArm .contE with
  | false =>
    have unchanged : FrameFiber.skippedCause .contE code (code.ensure fiber).1 (some cause) = some cause := by
      simp only [FrameFiber.skippedCause, arm, Bool.and_false, Bool.false_eq_true, ↓reduceIte]
    cases saved with
    | mk _ _ _ _ _ skip _ _ _ _ =>
      exact ⟨cause, unchanged, skip world (model.future_refl world) cause good arm⟩
  | true =>
    have produced : ∃ delivered,
        FrameFiber.skippedCause .contE code (code.ensure fiber).1 (some cause) = some delivered := by
      cases pending : (code.ensure fiber).1.interruptedCause with
      | none => exact ⟨cause, by simp only [FrameFiber.skippedCause, arm, pending]; rfl⟩
      | some other => exact ⟨Cause.sanitize cause other, by simp only [FrameFiber.skippedCause, arm, pending]; rfl⟩
    rcases produced with ⟨delivered, equation⟩
    cases saved with
    | mk _ _ _ _ _ _ _ _ _ discard =>
      exact ⟨delivered, equation,
        discard world (model.future_refl world) fiber cause delivered good arm interrupted equation⟩

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
  have family : PopTrace.Family .contE true (SavedAt model interp world)
      (fun fiber => fiber.stack = [])
      (fun input output carried pop => ∀ cause, carried = some cause → model.cause world input cause →
        pop.answer = .frame selected → ∃ incoming middle delivered,
          pop.carriedCause = some delivered ∧ model.cause world incoming delivered ∧
          SavedAt model interp world incoming middle selected ∧ StackAt model interp world middle output pop.fiber.stack) := by
    constructor
    · intro kind fiber before scratch cause incoming good found
      cases found
    · intro input middle output head tail fiber before answer callback path empty chosen kept cause incoming good found
      have shape := Prim.answerOf_frame_eq head selected .contE _
        (chosen.trans (congrArg some found))
      rw [shape.1]
      have scratch : StackAt model interp world middle middle fiber.stack := by
        rw [empty]; exact .nil world middle
      exact ⟨input, middle, cause, incoming, good, callback,
        stack_append model interp (ensure_stack model interp world middle middle head fiber scratch)
          (path_stack model interp path)⟩
    · intro input middle head fiber after callback empty
      rw [FrameFiber.passPushed_fiber_cause]; exact drain_empty .contE true head fiber empty
    · intro input middle output head tail fiber before after tailPop callback path empty passed drained next cause incoming good found
      have advanced : ∃ delivered, after = some delivered ∧ model.cause world middle delivered := by
        rcases passed with ⟨chosen, unchanged⟩ | ⟨answer, _, skipped, changed⟩
        · have missing := PopTrace.answer_missing head .contE _ chosen
          cases callback with
          | mk _ _ _ _ _ skip _ _ _ _ =>
            exact ⟨cause, unchanged.trans incoming,
              skip world (model.future_refl world) cause good missing⟩
        · rcases saved_discard_cause model interp world input middle head fiber cause callback good
            (by simpa only [Bool.true_and] using skipped) with ⟨delivered, equation, nextGood⟩
          exact ⟨delivered, changed.trans (by rw [incoming]; exact equation), nextGood⟩
      rcases advanced with ⟨delivered, changed, nextGood⟩
      have causeKept := (drain_cause head fiber delivered empty).2
      simp only [FrameFiber.passOn, FrameFiber.joinPushed, drained] at found ⊢
      exact next delivered (by rw [changed]; exact causeKept) nextGood found
    · intro input middle output head tail fiber before after tailPop callback path empty passed answered cause incoming good found
      have produced : ∃ delivered, after = some delivered := by
        rcases passed with ⟨_, unchanged⟩ | ⟨answer, _, skipped, changed⟩
        · exact ⟨cause, unchanged.trans incoming⟩
        · rcases saved_discard_cause model interp world input middle head fiber cause callback good
            (by simpa only [Bool.true_and] using skipped) with ⟨delivered, equation, _⟩
          exact ⟨delivered, changed.trans (by rw [incoming]; exact equation)⟩
      rcases produced with ⟨delivered, changed⟩
      rw [changed, (drain_cause head fiber delivered empty).1] at answered
      exact False.elim (answered rfl)
  exact family.popFrom input output frames fiber (some cause) (stack_path model interp stack) empty cause rfl good found

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
  rcases getCont_cause_selected model interp world input output fiber cause selected good stack found with
    ⟨incoming, middle, delivered, carried, incomingGood, callback, suffix⟩
  refine ⟨_, FrameFiber.resumeCause_frame interp fiber cause none selected next pushed found evaluated, ?_⟩
  simp only [carried, Option.getD_some] at evaluated
  simp only [FramePop.deliveredExit, carried, Option.getD_some] at pure
  cases callback with
  | mk _ _ _ _ _ _ _ answer _ _ =>
    exact result_attach model interp _ (answer world (model.future_refl world) delivered none next pushed
      incomingGood (by intro exit member; cases member) pure evaluated) suffix

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
  rcases getCont_cause_selected model interp world input output fiber cause (.onExit body name flag)
    good stack found with ⟨incoming, middle, delivered, carried, incomingGood, callback, suffix⟩
  simp only [FramePop.deliveredExit, carried, Option.getD_some] at installed
  exact install_finalizer model interp world incoming middle output _ body name flag (.failure delivered) next
    incomingGood callback installed suffix

end Effect4.Machine.AnswerFlow
