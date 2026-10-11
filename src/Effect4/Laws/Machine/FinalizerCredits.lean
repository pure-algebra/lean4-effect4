import Effect4.Laws.Machine.FrameWeights
import Effect4.Laws.Auto.Semantics

/-!
# Finalizer credits in the continuation stack

Concept: scope-lifetime-finalization, R11, at most one start per registration.
The consumer is `Atomic.cleans_once` through its finalizer trace accounting.
The stack gives one credit to each selected `onExit` frame.
A pop transfers that credit to its answering frame or discards it.
The helpers serve the planned whole-run finalizer debit, not control linearity or log writer provenance.
The statement covers every frame stack, mask, deferred interrupt and carried cause.
It establishes no finalization progress or host agreement.
-/

set_option autoImplicit false

namespace Effect4.Machine.FinalizerCredits

universe u v
variable {ν σ : Type u} {β : Type v} {ε δ ι α : Type u}

/-- Only an already pushed finalizer frame owns a registration credit. -/
def selected (choose : ν → Bool) : Prim ν σ β ε δ ι α → Bool
  | .onExit _ name _ => choose name
  | _ => false

/-- The registration credits held by a stack. Old bodies inside frames own none. -/
def stack (choose : ν → Bool) (frames : List (Prim ν σ β ε δ ι α)) : Nat :=
  frames.countP (selected choose)

/-- An answering finalizer frame owns the credit removed from the stack. -/
def answer (choose : ν → Bool) : ContAnswer ν σ β ε δ ι α → Nat
  | .frame frame => (if selected choose frame then 1 else 0)
  | _ => 0

/-- A pop splits credits between its answering frame and remaining stack. -/
def pop (choose : ν → Bool) (result : FramePop ν σ β ε δ ι α) : Nat :=
  answer choose result.answer + stack choose result.fiber.stack

/-- Mask restoration adds no finalizer frame. -/
theorem ensure_stack (choose : ν → Bool) (frame : Prim ν σ β ε δ ι α)
    (fiber : FrameFiber ν σ β ε δ ι α) :
    stack choose (frame.ensure fiber).1.stack = stack choose fiber.stack := by
  rcases FrameFiber.ensure_stack_cases frame fiber with same | ⟨push, _, _⟩
  · rw [same]
  · rw [push]
    rfl

/-- The arm selector transfers at most its frame's registration credit. -/
theorem answerOf_le (choose : ν → Bool) (frame : Prim ν σ β ε δ ι α)
    (demand : Arm) (replacement : Option (Prim ν σ β ε δ ι α))
    (result : ContAnswer ν σ β ε δ ι α)
    (found : frame.answerOf demand replacement = some result) :
    answer choose result ≤ (if selected choose frame then 1 else 0) := by
  unfold Prim.answerOf at found
  split at found
  · cases found
    exact Nat.zero_le _
  · split at found
    · cases found
      exact Nat.le_refl _
    · cases found

/-- The existing count is the shared saved-frame sum. -/
theorem stack_eq_sum (choose : ν → Bool) (frames : List (Prim ν σ β ε δ ι α)) :
    stack choose frames = (frames.map fun frame => if selected choose frame then 1 else 0).sum := by
  induction frames with
  | nil => rfl
  | cons frame rest ih =>
    simp only [stack, List.countP_cons, List.map_cons, List.sum_cons] at ih ⊢
    omega

variable [DecidableEq ε] [DecidableEq δ] [DecidableEq ι] [DecidableEq α]

/-- Finalizer registration credit is an instance of the shared pop model.
Current code owns no credit until its finalizer frame has been pushed. -/
def weightModel (choose : ν → Bool) : FrameWeights.Model ν σ β ε δ ι α where
  current := fun _ => 0
  saved := fun frame => if selected choose frame then 1 else 0
  ensure_stack frame fiber := by
    rw [← stack_eq_sum, ← stack_eq_sum, ensure_stack]
    exact Nat.le_refl _
  ensure_replacement _ _ _ _ := rfl

/-- The shared selected answer has exactly the existing credit. -/
theorem weightModel_answer (choose : ν → Bool) (result : ContAnswer ν σ β ε δ ι α) :
    FrameWeights.answer (weightModel choose) result = answer choose result := by
  cases result <;> rfl

/-- The shared saved weight has exactly the existing stack count. -/
theorem weightModel_stack (choose : ν → Bool) (frames : List (Prim ν σ β ε δ ι α)) :
    (frames.map (weightModel choose).saved).sum = stack choose frames :=
  (stack_eq_sum choose frames).symm

/-- The live hook's extra pop cannot duplicate a finalizer registration. -/
theorem passPushed_le (choose : ν → Bool) (demand : Arm) (skip : Bool)
    (fiber : FrameFiber ν σ β ε δ ι α) :
    pop choose (FrameFiber.passPushed demand skip fiber) ≤ stack choose fiber.stack := by
  have shared := FrameWeights.passPushed_le (weightModel choose) demand skip fiber none
  simpa only [weightModel_stack, weightModel_answer, pop, Nat.add_comm] using shared

/-- Joining a hook pop to the remaining traversal retains one combined credit bound. -/
theorem joinPushed_le (choose : ν → Bool) (demand : Arm) (skip : Bool)
    (fiber : FrameFiber ν σ β ε δ ι α) (rest : List (Prim ν σ β ε δ ι α))
    (tail : FramePop ν σ β ε δ ι α)
    (bound : pop choose tail ≤ stack choose rest + stack choose fiber.stack) :
    pop choose (FrameFiber.joinPushed demand skip fiber rest tail) ≤
      stack choose rest + stack choose fiber.stack := by
  have pushed := passPushed_le choose demand skip fiber
  unfold FrameFiber.joinPushed
  split
  · exact bound
  · simp only [pop, stack, List.countP_append] at pushed ⊢
    omega

/-- Every popped finalizer credit is transferred once or discarded. -/
theorem popFrom_le (choose : ν → Bool) (demand : Arm) (skip : Bool) :
    ∀ (frames : List (Prim ν σ β ε δ ι α)) (fiber : FrameFiber ν σ β ε δ ι α),
      pop choose (FrameFiber.popFrom demand skip frames fiber) ≤
        stack choose frames + stack choose fiber.stack := by
  intro frames fiber
  have shared := FrameWeights.popFrom_le (weightModel choose) demand skip frames fiber none
  simpa only [weightModel_stack, weightModel_answer, pop, Nat.add_comm] using shared

/-- The actual continuation lookup retains the debit at every interrupt boundary. -/
@[semantics "scope-lifetime-finalization" (requirement := R11)]
theorem getCont_le (choose : ν → Bool) (fiber : FrameFiber ν σ β ε δ ι α)
    (demand : Arm) (skip : Bool) (cause : Option (Cause ε δ ι α) := none) :
    pop choose (fiber.getCont demand skip cause) ≤ stack choose fiber.stack := by
  have shared := FrameWeights.getCont_le (weightModel choose) fiber demand skip cause
  simpa only [weightModel_stack, weightModel_answer, pop, Nat.add_comm] using shared

end Effect4.Machine.FinalizerCredits
