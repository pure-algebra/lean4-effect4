import Effect4.Laws.Machine.PopTraceFamily

/-!
Concept: scope-lifetime-finalization R11.
Question: actual continuation selection either retains the authored protected finalizer or masks the returned frame.
Consumers: the actual pending-fiber runtime permissions for Timeout and Atomic numeric histories.
Reach: the existing fused pop at either value or cause demand, with the actual authored finalizer on its stack.
Limit: this result supplies no source occurrence or command execution permission.
-/
set_option autoImplicit false
namespace Effect4.Machine.ProtectedFinalizer
open Effect4 Effect4.Machine
universe u v
variable {ν σ : Type u} {β : Type v} {ε δ ι α : Type u}

/-- The protected finalizer hook returns an uninterruptible frame at either incoming flag. -/
theorem ensure_masked (fiber : FrameFiber ν σ β ε δ ι α) (body : Prim ν σ β ε δ ι α) (name : ν) :
    ((Prim.onExit body name false).ensure fiber).1.interruptible = false := by
  cases flag : fiber.interruptible <;>
    simp only [Prim.ensure, flag, Bool.not_false, Bool.false_and, Bool.true_and,
      Bool.false_eq_true, ↓reduceIte]

/-- An edge reads the existing stack suffix before and after one existing saved frame. -/
def Edge (input output : List (Prim ν σ β ε δ ι α)) (frame : (Prim ν σ β ε δ ι α)) : Prop := input = frame :: output

/-- The existing path reads the original frames and its retained suffix. -/
theorem path_shape (input output frames : List (Prim ν σ β ε δ ι α)) (path : Effect4.Contracts.Path Edge input output frames) :
    input = frames ++ output := by
  induction path with
  | nil kind => rfl
  | cons head tail ih => rw [head, ih]; rfl

/-- The original saved list supplies this path without any program-code traversal. -/
theorem path_self (frames : List (Prim ν σ β ε δ ι α)) : Effect4.Contracts.Path Edge frames [] frames := by
  induction frames with
  | nil => exact .nil []
  | cons frame rest ih => exact .cons rfl ih

variable [DecidableEq ε] [DecidableEq δ] [DecidableEq ι] [DecidableEq α]

/-- The authored protected callback cannot be discarded by either actual exit demand. -/
theorem not_passed (body : (Prim ν σ β ε δ ι α)) (name : ν) (demand : Effect4.Arm) (skip : Bool)
    (exitDemand : demand = .contA ∨ demand = .contE) (fiber : FrameFiber ν σ β ε δ ι α)
    (before after : Option (Cause ε δ ι α)) : ¬ PopTrace.Passes demand skip (.onExit body name false) fiber before after := by
  have answer : (Prim.onExit body name false).answerOf demand ((Prim.onExit body name false).ensure fiber).2 =
      some (.frame (.onExit body name false)) := by
    rw [Prim.ensure_onExit_no_replacement]
    rcases exitDemand with same | same <;> cases same <;> rfl
  have quiet : ((Prim.onExit body name false).ensure fiber).1.interrupted = false := by
    unfold FrameFiber.interrupted
    rw [ensure_masked]
    rfl
  intro passed
  rcases passed with ⟨absent, carried⟩ | ⟨selected, chosen, skipped, carried⟩
  · rw [answer] at absent
    cases absent
  · rw [quiet, Bool.and_false] at skipped
    cases skipped

/-- The existing pop family retains the actual protected finalizer while its returned frame stays interruptible. -/
theorem pop_family (body : (Prim ν σ β ε δ ι α)) (name : ν) (demand : Effect4.Arm) (skip : Bool)
    (exitDemand : demand = .contA ∨ demand = .contE) :
    PopTrace.Family demand skip Edge (fun _ => True)
      (fun input output _ pop => output = [] → (.onExit body name false) ∈ input →
        pop.fiber.interruptible = false ∨ (.onExit body name false) ∈ pop.fiber.stack) := by
  constructor
  · intro kind fiber cause scratch last member
    rw [last] at member
    cases member
  · intro input middle output frame rest fiber cause answer edge path scratch chosen kept last member
    have suffix := path_shape middle output rest path
    rw [last, List.append_nil] at suffix
    rw [edge, suffix] at member
    rcases List.mem_cons.mp member with same | present
    · cases same
      exact Or.inl (ensure_masked fiber body name)
    · exact Or.inr (List.mem_append_right _ present)
  · intros; trivial
  · intro input middle output frame rest fiber before after tail edge path scratch passed drained ih last member
    have suffix := path_shape middle output rest path
    rw [last, List.append_nil] at suffix
    rw [edge, suffix] at member
    rcases List.mem_cons.mp member with same | present
    · cases same
      exact False.elim (not_passed body name demand skip exitDemand fiber before after passed)
    · have next := ih last (suffix.symm ▸ present)
      simpa only [FrameFiber.passOn, FrameFiber.joinPushed, drained] using next
  · intro input middle output frame rest fiber before after tail edge path scratch passed answered last member
    have suffix := path_shape middle output rest path
    rw [last, List.append_nil] at suffix
    rw [edge, suffix] at member
    rcases List.mem_cons.mp member with same | present
    · cases same
      exact False.elim (not_passed body name demand skip exitDemand fiber before after passed)
    · cases actual : (FrameFiber.passPushed demand skip (frame.ensure fiber).1 after).answer with
      | empty => exact False.elim (answered actual)
      | deferred cause =>
        simp only [FrameFiber.passOn, FrameFiber.joinPushed, actual]
        exact Or.inr (List.mem_append_right _ present)
      | replacement next =>
        simp only [FrameFiber.passOn, FrameFiber.joinPushed, actual]
        exact Or.inr (List.mem_append_right _ present)
      | frame selected =>
        simp only [FrameFiber.passOn, FrameFiber.joinPushed, actual]
        exact Or.inr (List.mem_append_right _ present)

/-- Actual fused selection cannot lose the protected finalizer and return an unmasked frame together. -/
theorem pop (body : (Prim ν σ β ε δ ι α)) (name : ν) (demand : Effect4.Arm) (skip : Bool)
    (exitDemand : demand = .contA ∨ demand = .contE) (frames : List (Prim ν σ β ε δ ι α))
    (fiber : FrameFiber ν σ β ε δ ι α) (cause : Option (Cause ε δ ι α))
    (present : (.onExit body name false) ∈ frames) :
    (FrameFiber.popFrom demand skip frames fiber cause).fiber.interruptible = false ∨
      (.onExit body name false) ∈ (FrameFiber.popFrom demand skip frames fiber cause).fiber.stack :=
  (pop_family body name demand skip exitDemand).popFrom frames [] frames fiber cause (path_self frames) trivial rfl present

/-- The deferred branch retains the same authored callback; every other branch uses the existing pop producer. -/
theorem getCont (body : (Prim ν σ β ε δ ι α)) (name : ν) (demand : Effect4.Arm) (skip : Bool)
    (exitDemand : demand = .contA ∨ demand = .contE) (fiber : FrameFiber ν σ β ε δ ι α)
    (cause : Option (Cause ε δ ι α)) (present : (.onExit body name false) ∈ fiber.stack) :
    (fiber.getCont demand skip cause).fiber.interruptible = false ∨
      (.onExit body name false) ∈ (fiber.getCont demand skip cause).fiber.stack := by
  unfold FrameFiber.getCont
  split
  · exact Or.inr present
  · exact pop body name demand skip exitDemand fiber.stack _ cause present

end Effect4.Machine.ProtectedFinalizer
