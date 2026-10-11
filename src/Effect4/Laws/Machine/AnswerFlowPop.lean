import Effect4.Laws.Machine.AnswerFlowHooks

/-!
Concepts: store-typing R4 and scope-lifetime-finalization R11.
Question: selected native callbacks serve Workers log history and Timeout cleanup.
Reach: actual value getCont over the existing ordered saved stack, at one world.
The selected callback retains its incoming value class and its older suffix.
Limit: pending causes and supplied exits need separate admissibility premises.
Consumers: native finalizer interception and actual value callback invocation.
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

/-- Draining the actual hook's scratch stack leaves it empty.
Consumer: the structural induction over the original saved list. -/
theorem drain_empty (demand : Arm) (skip : Bool) (code : Prim ν σ β ε δ ι α) (fiber : FrameFiber ν σ β ε δ ι α)
    (empty : fiber.stack = []) :
    (FrameFiber.passPushed demand skip (code.ensure fiber).1).fiber.stack = [] := by
  rcases FrameFiber.ensure_stack_cases code fiber with kept | ⟨pushed, _, _⟩
  · rw [FrameFiber.passPushed_nil _ _ _ (kept.trans empty)]
    exact kept.trans empty
  · rw [FrameFiber.passPushed_fiber _ _ _ (.setInterruptible true) [] (by rw [pushed, empty])]
    exact Prim.ensure_setInterruptible_stack true _

/-- A pushed mask can replace an answer, but cannot select a value callback.
Consumer: value selection comes from the original ordered saved list. -/
theorem drain_not_frame (demand : Arm) (skip : Bool)
    (missing : (Prim.setInterruptible true : Prim ν σ β ε δ ι α).hasArm demand = false)
    (code selected : Prim ν σ β ε δ ι α)
    (fiber : FrameFiber ν σ β ε δ ι α) (empty : fiber.stack = []) :
    (FrameFiber.passPushed demand skip (code.ensure fiber).1).answer ≠ .frame selected := by
  rcases FrameFiber.ensure_stack_cases code fiber with kept | ⟨pushed, _, _⟩
  · rw [FrameFiber.passPushed_nil _ _ _ (kept.trans empty)]
    intro impossible; cases impossible
  · have shape : (code.ensure fiber).1.stack = [.setInterruptible true] := by rw [pushed, empty]
    rw [FrameFiber.passPushed_answer _ _ _ (.setInterruptible true) [] shape]
    intro selectedAnswer
    cases found : Prim.answerOf (.setInterruptible true) demand
        ((Prim.setInterruptible true).ensure {(code.ensure fiber).1 with stack := []}).2 with
    | none => rw [found] at selectedAnswer; cases selectedAnswer
    | some answer =>
      rw [found] at selectedAnswer
      dsimp only at selectedAnswer
      split at selectedAnswer
      · cases selectedAnswer
      have arm := Prim.answerOf_frame_eq (.setInterruptible true) selected demand _
        (found.trans (congrArg some selectedAnswer))
      rw [missing] at arm
      cases arm.2

/-- The actual value pop carries its incoming value into the selected saved callback.
It retains the suffix after that callback's actual mask hook. -/
theorem popFrom_value_selected (world : World) (input output : Kind)
    (frames : List (Prim ν σ β ε δ ι α)) (fiber : FrameFiber ν σ β ε δ ι α)
    (value : β) (selected : Prim ν σ β ε δ ι α)
    (empty : fiber.stack = [])
    (good : model.value world input value)
    (stack : StackAt model interp world input output frames)
    (found : (FrameFiber.popFrom .contA false frames fiber).answer = .frame selected) :
    ∃ incoming middle, model.value world incoming value ∧
      SavedAt model interp world incoming middle selected ∧
      StackAt model interp world middle output (FrameFiber.popFrom .contA false frames fiber).fiber.stack := by
  induction frames generalizing input fiber with
  | nil => cases found
  | cons head tail ih =>
    cases stack with
    | @cons _ _ middle _ _ _ callback suffix =>
      cases chosen : Prim.answerOf head .contA (head.ensure fiber).2 with
      | none =>
        have missing : head.hasArm .contA = false := by
          unfold Prim.answerOf at chosen
          split at chosen
          · cases chosen
          · split at chosen
            · cases chosen
            · rename_i absent
              exact Bool.eq_false_iff.mpr absent
        have nextGood : model.value world middle value := by
          cases callback with
          | mk _ _ _ _ skip _ _ _ _ => exact skip world (model.future_refl world) value good missing
        rw [FrameFiber.popFrom_continue_answer _ _ _ _ _ (Or.inl chosen)] at found
        rw [FrameFiber.popFrom_continue_fiber _ _ _ _ _ (Or.inl chosen)]
        rcases FrameFiber.continueFrom_cases .contA false head tail fiber with continued | drained
        · rw [continued] at found ⊢
          exact ih _ _ (drain_empty .contA false head fiber empty) nextGood suffix found
        · rw [drained] at found
          exact False.elim (drain_not_frame .contA false rfl head selected fiber empty found)
      | some answer =>
        rw [FrameFiber.popFrom_answer_answer _ _ _ _ _ answer chosen rfl] at found
        have shape := Prim.answerOf_frame_eq head selected .contA _
          (chosen.trans (congrArg some found))
        rw [shape.1]
        rw [FrameFiber.popFrom_answer_fiber _ _ _ _ _ answer chosen rfl]
        have scratch : StackAt model interp world middle middle fiber.stack := by
          rw [empty]; exact .nil world middle
        exact ⟨input, middle, good, callback,
          stack_append model interp (ensure_stack model interp world middle middle head fiber scratch) suffix⟩

/-- Actual getCont retains the selected callback and its ordered suffix.
Deferred and replacement answers cannot inhabit this selected-frame branch. -/
theorem getCont_value_selected (world : World) (input output : Kind)
    (fiber : FrameFiber ν σ β ε δ ι α) (value : β) (selected : Prim ν σ β ε δ ι α)
    (good : model.value world input value)
    (stack : StackAt model interp world input output fiber.stack)
    (found : (fiber.getCont .contA false).answer = .frame selected) :
    ∃ incoming middle, model.value world incoming value ∧
      SavedAt model interp world incoming middle selected ∧
      StackAt model interp world middle output (fiber.getCont .contA false).fiber.stack := by
  unfold FrameFiber.getCont at found ⊢
  split
  · rename_i deferred
    rw [if_pos deferred] at found
    cases found
  · rename_i normal
    rw [if_neg normal] at found
    exact popFrom_value_selected model interp world input output fiber.stack _ value selected rfl good stack found

/-- The actual selected value arm installs its typed result above the older suffix.
The optional supplied exit must describe the same successful answer. -/
theorem resumeValue_selected (world : World) (input output : Kind)
    (fiber : FrameFiber ν σ β ε δ ι α) (value : β)
    (selected next : Prim ν σ β ε δ ι α) (pushed : List (Prim ν σ β ε δ ι α))
    (provided : Option (Exit β ε δ ι α))
    (same : provided = none ∨ provided = some (.success value))
    (good : model.value world input value)
    (stack : StackAt model interp world input output fiber.stack)
    (found : (fiber.getCont .contA false).answer = .frame selected)
    (pure : programOf model world selected (.success value) = none)
    (evaluated : selected.armA interp value provided = some (next, pushed)) :
    ∃ events, fiber.resumeValue interp value provided =
      (.running {(fiber.getCont .contA false).fiber with
        current := next
        stack := pushed ++ (fiber.getCont .contA false).fiber.stack}, events) ∧
      FrameAt model interp world output {(fiber.getCont .contA false).fiber with
        current := next
        stack := pushed ++ (fiber.getCont .contA false).fiber.stack} := by
  rcases getCont_value_selected model interp world input output fiber value selected good stack found with
    ⟨incoming, middle, incomingGood, callback, suffix⟩
  refine ⟨_, FrameFiber.resumeValue_frame interp fiber value provided selected next pushed found evaluated, ?_⟩
  have supplied : ∀ exit ∈ provided, ExitAt model world incoming exit := by
    rcases same with absent | present
    · rw [absent]; intro exit member; cases member
    · rw [present]; intro exit member
      cases Option.some.inj member
      exact incomingGood
  have original : provided.getD (.success value) = .success value := by
    rcases same with absent | present
    · rw [absent]; rfl
    · rw [present]; rfl
  cases callback with
  | mk _ _ _ _ _ _ answer _ _ =>
    exact result_attach model interp _ (answer world (model.future_refl world) value provided next pushed
      incomingGood supplied (by rw [original]; exact pure) evaluated) suffix

/-- Native value finalization consumes the selected saved frame's actual program clause.
The pop has already run its mask hooks and retained the older typed suffix. -/
theorem getCont_value_finalizer (world : World) (input output : Kind)
    (fiber : FrameFiber ν σ β ε δ ι α) (value : β)
    (body next : Prim ν σ β ε δ ι α) (name : ν) (flag : Bool)
    (good : model.value world input value)
    (stack : StackAt model interp world input output fiber.stack)
    (found : (fiber.getCont .contA false).answer = .frame (.onExit body name flag))
    (installed : model.finalizer world name (.success value) = some next) :
    FrameAt model interp world output {(fiber.getCont .contA false).fiber with current := next} := by
  rcases getCont_value_selected model interp world input output fiber value (.onExit body name flag)
    good stack found with ⟨incoming, middle, incomingGood, callback, suffix⟩
  exact install_finalizer model interp world incoming middle output _ body name flag (.success value) next
    incomingGood callback installed suffix

end Effect4.Machine.AnswerFlow
