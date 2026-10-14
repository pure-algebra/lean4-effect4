import Effect4.Laws.Machine.AnswerFlowHooks
import Effect4.Laws.Machine.AnswerFlowFamilyPop

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
  obtain ⟨incoming, middle, good, callback, suffix⟩ :=
    External.popFrom_value_selected model interp (SavedAt model interp) (saved_family model interp)
      (fun world kind => saved_mask model interp world kind true) world input output frames fiber value selected
      empty good (stack_path model interp stack) found
  exact ⟨incoming, middle, good, callback, path_stack model interp suffix⟩

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
  have supplied (incoming : Kind) (incomingGood : model.value world incoming value) :
      ∀ exit ∈ provided, ExitAt model world incoming exit := by
    rcases same with absent | present
    · rw [absent]; intro exit member; cases member
    · rw [present]; intro exit member; cases Option.some.inj member; exact incomingGood
  have original : provided.getD (.success value) = .success value := by
    rcases same with absent | present
    · rw [absent]; rfl
    · rw [present]; rfl
  obtain ⟨events, equation, head, code, path⟩ :=
    External.resumeValue_selected model interp (SavedAt model interp) (saved_family model interp)
      (fun world kind => saved_mask model interp world kind true) world input output fiber value selected next pushed
      provided good (stack_path model interp stack) found supplied (by rw [original]; exact pure) evaluated
  exact ⟨events, equation, head, code, path_stack model interp path⟩

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
  obtain ⟨input, code, path⟩ := External.getCont_value_finalizer model interp (SavedAt model interp)
    (saved_family model interp) (fun world kind => saved_mask model interp world kind true)
    world input output fiber value (.onExit body name flag) next good (stack_path model interp stack) found installed
  exact ⟨input, code, path_stack model interp path⟩

end Effect4.Machine.AnswerFlow
