import Effect4.Machine.Frames
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

variable [DecidableEq ε] [DecidableEq δ] [DecidableEq ι] [DecidableEq α]

/-- The live hook's extra pop cannot duplicate a finalizer registration. -/
theorem passPushed_le (choose : ν → Bool) (demand : Arm) (skip : Bool)
    (fiber : FrameFiber ν σ β ε δ ι α) :
    pop choose (FrameFiber.passPushed demand skip fiber) ≤ stack choose fiber.stack := by
  unfold FrameFiber.passPushed
  split
  · simp only [pop, answer, Nat.zero_add, Nat.le_refl]
  · next frame rest frames =>
    have same := ensure_stack choose frame { fiber with stack := rest }
    dsimp only at same
    simp only [pop, same]
    rw [frames]
    simp only [stack, List.countP_cons]
    split
    · next result found =>
      have bound := answerOf_le choose frame demand _ result found
      split
      · simp only [answer, Nat.zero_add]
        omega
      · omega
    · simp only [answer, Nat.zero_add]
      omega

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
        stack choose frames + stack choose fiber.stack
  | [], fiber => by
    exact Nat.le_refl _
  | frame :: rest, fiber => by
    have ensured := ensure_stack choose frame fiber
    have pushed := passPushed_le choose demand skip (frame.ensure fiber).1
    have remaining :
        stack choose (FrameFiber.passPushed demand skip (frame.ensure fiber).1).fiber.stack ≤
          stack choose fiber.stack := by
      unfold pop at pushed
      omega
    have recur := popFrom_le choose demand skip rest
      (FrameFiber.passPushed demand skip (frame.ensure fiber).1).fiber
    have bound : pop choose (FrameFiber.popFrom demand skip rest
        (FrameFiber.passPushed demand skip (frame.ensure fiber).1).fiber) ≤
        stack choose rest + stack choose (frame.ensure fiber).1.stack := by
      omega
    have joined := joinPushed_le choose demand skip (frame.ensure fiber).1 rest _ bound
    simp only [FrameFiber.popFrom, FrameFiber.skippedCause_none,
      FrameFiber.passPushed_carriedCause_none]
    split
    · next result found =>
      have answered := answerOf_le choose frame demand _ result found
      split
      · simp only [FrameFiber.passOn, pop] at joined ⊢
        simp only [stack, List.countP_cons] at joined ensured ⊢
        omega
      · simp only [pop, stack, List.countP_append, List.countP_cons] at ensured ⊢
        omega
    · simp only [FrameFiber.passOn, pop] at joined ⊢
      simp only [stack, List.countP_cons] at joined ensured ⊢
      omega

/-- The actual continuation lookup retains the debit at every interrupt boundary. -/
@[semantics "scope-lifetime-finalization" (requirement := R11)]
theorem getCont_le (choose : ν → Bool) (fiber : FrameFiber ν σ β ε δ ι α)
    (demand : Arm) (skip : Bool) (cause : Option (Cause ε δ ι α) := none) :
    pop choose (fiber.getCont demand skip cause) ≤ stack choose fiber.stack := by
  simp only [pop, FrameFiber.getCont_answer_cause, FrameFiber.getCont_fiber_cause]
  change pop choose (fiber.getCont demand skip) ≤ _
  unfold FrameFiber.getCont
  split
  · simp only [pop, answer, Nat.zero_add, Nat.le_refl]
  · have bound := popFrom_le choose demand skip fiber.stack
      { fiber with stack := [], deferredInterrupt := false }
    simpa only [stack, List.countP_nil, Nat.add_zero] using bound

end Effect4.Machine.FinalizerCredits
