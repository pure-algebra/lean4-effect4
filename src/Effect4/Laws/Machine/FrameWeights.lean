import Effect4.Machine.Frames
import Effect4.Laws.Auto.RuleSets

/-!
Concept: scope-lifetime-finalization, R11.
Consumers: existing source-opportunity frame transport and Atomic.Cleanup.log_debits.
The scalar model reads existing primitive code and ordered saved frames.
Hook premises describe actual ensure operations; no source grammar or machine state is duplicated.
This law accounts for an actual pop, not progress or finalizer issuance.
-/
set_option autoImplicit false
namespace Effect4.Machine.FrameWeights
open Effect4
universe u v
variable {ν σ ε δ ι α : Type u} {β : Type v}
variable [DecidableEq ε] [DecidableEq δ] [DecidableEq ι] [DecidableEq α]

/-- The current and saved scalar projections retain actual hook behavior. -/
structure Model (ν σ : Type u) (β : Type v) (ε δ ι α : Type u)
    [DecidableEq ε] [DecidableEq δ] [DecidableEq ι] [DecidableEq α] where
  current : Prim ν σ β ε δ ι α → Nat
  saved : Prim ν σ β ε δ ι α → Nat
  ensure_stack : ∀ (code : Prim ν σ β ε δ ι α) (fiber : FrameFiber ν σ β ε δ ι α),
    ((code.ensure fiber).1.stack.map saved).sum ≤ (fiber.stack.map saved).sum
  ensure_replacement : ∀ (code : Prim ν σ β ε δ ι α) (fiber : FrameFiber ν σ β ε δ ι α) next,
    (code.ensure fiber).2 = some next → current next = 0

variable (model : Model ν σ β ε δ ι α)

/-- The selected answering frame retains its saved reservation. -/
def answer : ContAnswer ν σ β ε δ ι α → Nat
  | .frame code => model.saved code
  | .replacement code => model.current code
  | _ => 0

/-- Answer selection retains the saved frame's bound or a zero-opportunity hook replacement.
Consumer: actual continuation pop debit. -/
theorem answerOf_le (code : Prim ν σ β ε δ ι α) (demand : Effect4.Arm)
    (replacement : Option (Prim ν σ β ε δ ι α)) (result : ContAnswer ν σ β ε δ ι α)
    (hook : ∀ next ∈ replacement, model.current next = 0)
    (found : Prim.answerOf code demand replacement = some result) :
    answer model result ≤ model.saved code := by
  unfold Prim.answerOf at found
  repeat' split at found
  all_goals aesop (add norm simp [answer, Option.mem_def])

/-- Draining one pushed administrative hook retains the remaining saved reservations.
Consumer: fused continuation pop accounting. -/
theorem passPushed_le (demand : Effect4.Arm) (skip : Bool)
    (fiber : FrameFiber ν σ β ε δ ι α) (cause : Option (Cause ε δ ι α)) :
    ((FrameFiber.passPushed demand skip fiber cause).fiber.stack.map model.saved).sum +
      answer model (FrameFiber.passPushed demand skip fiber cause).answer ≤
      (fiber.stack.map model.saved).sum := by
  unfold FrameFiber.passPushed
  cases stored : fiber.stack with
  | nil => simp only [stored, answer, List.map_nil, List.sum_nil, Nat.add_zero, Nat.le_refl]
  | cons head tail =>
    have kept := model.ensure_stack head {fiber with stack := tail}
    change ((head.ensure {fiber with stack := tail}).1.stack.map model.saved).sum ≤
      (tail.map model.saved).sum at kept
    have hook : ∀ next ∈ (head.ensure {fiber with stack := tail}).2, model.current next = 0 := by
      intro next member
      exact model.ensure_replacement head _ next (Option.mem_def.mp member)
    have selected (result : ContAnswer ν σ β ε δ ι α)
        (found : Prim.answerOf head demand (head.ensure {fiber with stack := tail}).2 = some result) :=
      answerOf_le model head demand _ result hook found
    dsimp only
    split
    · split
      · simp only [answer, Nat.add_zero, List.map_cons, List.sum_cons]
        omega
      · have bound := selected _ (by assumption)
        simp only [List.map_cons, List.sum_cons]
        omega
    · simp only [answer, Nat.add_zero, List.map_cons, List.sum_cons]
      omega

/-- The actual fused pop retains the answering reservation and every unconsumed frame.
Consumer: native success, cause and finalizer pop debit. -/
theorem popFrom_le (demand : Effect4.Arm) (skip : Bool)
    (frames : List (Prim ν σ β ε δ ι α)) (fiber : FrameFiber ν σ β ε δ ι α)
    (cause : Option (Cause ε δ ι α)) :
    ((FrameFiber.popFrom demand skip frames fiber cause).fiber.stack.map model.saved).sum +
      answer model (FrameFiber.popFrom demand skip frames fiber cause).answer ≤
      (frames.map model.saved).sum + (fiber.stack.map model.saved).sum := by
  induction frames generalizing fiber cause with
  | nil => simp only [FrameFiber.popFrom, answer, List.map_nil, List.sum_nil, Nat.add_zero, Nat.zero_add, Nat.le_refl]
  | cons head tail ih =>
    have kept := model.ensure_stack head fiber
    have hook : ∀ next ∈ (head.ensure fiber).2, model.current next = 0 := by
      intro next member
      exact model.ensure_replacement head fiber next (Option.mem_def.mp member)
    have selected (result : ContAnswer ν σ β ε δ ι α)
        (found : Prim.answerOf head demand (head.ensure fiber).2 = some result) :=
      answerOf_le model head demand _ result hook found
    have pushed := passPushed_le model demand skip (head.ensure fiber).1 none
    have recursive := ih (FrameFiber.passPushed demand skip (head.ensure fiber).1 none).fiber none
    unfold FrameFiber.popFrom
    dsimp only
    split
    · split
      · simp only [FrameFiber.passOn, FrameFiber.joinPushed]
        split
        all_goals simp only [List.map_append, List.sum_append, List.map_cons, List.sum_cons,
          FrameFiber.passPushed_fiber_cause, FrameFiber.passPushed_answer_cause,
          FrameFiber.popFrom_fiber_cause, FrameFiber.popFrom_answer_cause]
        all_goals omega
      · have selected := selected _ (by assumption)
        simp only [List.map_append, List.sum_append, List.map_cons, List.sum_cons]
        omega
    · simp only [FrameFiber.passOn, FrameFiber.joinPushed]
      split
      all_goals simp only [List.map_append, List.sum_append, List.map_cons, List.sum_cons,
        FrameFiber.passPushed_fiber_cause, FrameFiber.passPushed_answer_cause,
        FrameFiber.popFrom_fiber_cause, FrameFiber.popFrom_answer_cause]
      all_goals omega

/-- Actual getCont retains the sum of its answering reservation and remaining saved frames.
Consumer: native finalizer and frame resume accounting. -/
theorem getCont_le
    (fiber : FrameFiber ν σ β ε δ ι α)
    (demand : Effect4.Arm) (skip : Bool) (cause : Option (Cause ε δ ι α)) :
    ((fiber.getCont demand skip cause).fiber.stack.map model.saved).sum +
      answer model (fiber.getCont demand skip cause).answer ≤
      (fiber.stack.map model.saved).sum := by
  unfold FrameFiber.getCont
  split
  · simp only [answer, Nat.add_zero, Nat.le_refl]
  · simpa only [List.map_nil, List.sum_nil, Nat.add_zero] using
      popFrom_le model demand skip fiber.stack {fiber with stack := [], deferredInterrupt := false} cause


end Effect4.Machine.FrameWeights
