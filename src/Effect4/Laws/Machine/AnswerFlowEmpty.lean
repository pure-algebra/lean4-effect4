import Effect4.Laws.Machine.AnswerFlowResume
import Effect4.Laws.Machine.MaskRuns

/-!
Concept: scope-lifetime-finalization R11 and store-typing R4.
Consumer: actual terminal exits in Atomic's `shop_stages` and Timeout's numeric history.
The existing pop trace transports permissions to its empty answer.
This gives exit permission, rather than only permission for a running frame.
-/
set_option autoImplicit false
namespace Effect4.Machine.PopTrace
open Effect4 Effect4.Contracts
universe u v w
variable {ν σ : Type u} {β : Type v} {ε δ ι α : Type u} {Kind : Type w}
variable [DecidableEq ε] [DecidableEq δ] [DecidableEq ι] [DecidableEq α]

/-- Actual passed frames transport a permission to the empty answer of the same pop trace. -/
theorem empty_transport (Edge : Kind → Kind → Prim ν σ β ε δ ι α → Prop)
    (Scratch : FrameFiber ν σ β ε δ ι α → Prop)
    (Input : Kind → Option (Cause ε δ ι α) → Prop) (demand : Arm) (skip : Bool)
    (drain : ∀ input middle head fiber after, Edge input middle head → Scratch fiber →
      Scratch (FrameFiber.passPushed demand skip (head.ensure fiber).1 after).fiber)
    (advance : ∀ input middle head fiber before after, Edge input middle head → Scratch fiber →
      Passes demand skip head fiber before after → Input input before →
      Input middle (FrameFiber.passPushed demand skip (head.ensure fiber).1 after).carriedCause)
    (input output : Kind) (frames : List (Prim ν σ β ε δ ι α))
    (fiber : FrameFiber ν σ β ε δ ι α) (carried : Option (Cause ε δ ι α))
    (path : Path Edge input output frames) (scratch : Scratch fiber) (good : Input input carried)
    (found : (FrameFiber.popFrom demand skip frames fiber carried).answer = .empty) :
    Input output (FrameFiber.popFrom demand skip frames fiber carried).carriedCause := by
  have family : Family demand skip Edge Scratch
      (fun input output carried pop => Input input carried → pop.answer = .empty → Input output pop.carriedCause) := by
    constructor
    · intro kind fiber cause held good found
      exact good
    · intro input middle output head rest fiber cause answer callback path scratch chosen kept good found
      exact (FrameFiber.answerOf_ne_empty head demand _ answer chosen found).elim
    · exact drain
    · intro input middle output head rest fiber before after tail callback path scratch passed drained next good found
      simp only [FrameFiber.passOn, FrameFiber.joinPushed, drained] at found ⊢
      exact next (advance input middle head fiber before after callback scratch passed good) found
    · intro input middle output head rest fiber before after tail callback path scratch passed answered good found
      unfold FrameFiber.passOn FrameFiber.joinPushed at found
      split at found
      · rename_i drained
        exact (answered drained).elim
      · exact (answered found).elim
  exact family.popFrom input output frames fiber carried path scratch good found
end Effect4.Machine.PopTrace

namespace Effect4.Machine.AnswerFlow.Contextual
open Effect4 Effect4.Contracts
universe u v w
variable {ν σ : Type u} {β : Type v} {ε δ ι α : Type u} {World Kind : Type w}
variable [DecidableEq ε] [DecidableEq δ] [DecidableEq ι] [DecidableEq α]
variable (model : Model (ν := ν) (σ := σ) (β := β) (ε := ε) (δ := δ) (ι := ι) (α := α) World Kind)
variable (interp : PrimInterp ν σ β ε δ ι α)
variable (Edge : World → Kind → Kind → Prim ν σ β ε δ ι α → Prop)
variable (Allowed : World → Option (Cause ε δ ι α) → Prop)
variable (family : ContextualSavedFamily model interp Edge Allowed)

include interp family in
/-- An actual empty value pop reaches the outer value permission through its passed frames. -/
theorem getCont_value_empty (world : World) (input output : Kind)
    (fiber : FrameFiber ν σ β ε δ ι α) (value : β) (good : model.value world input value)
    (path : Path (Edge world) input output fiber.stack)
    (found : (fiber.getCont .contA false).answer = .empty) : model.value world output value := by
  unfold FrameFiber.getCont at found
  split at found
  · cases found
  · apply PopTrace.empty_transport (Edge world) (fun scratch => scratch.stack = [])
      (fun kind _ => model.value world kind value) .contA false ?_ ?_
      input output fiber.stack {fiber with stack := [], deferredInterrupt := false} none path rfl good found
    · intro input middle head scratch after callback empty
      rw [FrameFiber.passPushed_fiber_cause]
      exact PopTrace.drain_empty .contA false head scratch empty
    · intro input middle head scratch before after callback empty passed good
      have missing : head.hasArm .contA = false := by
        rcases passed with ⟨absent, unchanged⟩ | ⟨answer, selected, skipped, changed⟩
        · exact PopTrace.answer_missing head .contA _ absent
        · cases skipped
      exact family.skip world input middle head callback world (model.future_refl world) value good missing

include interp family in
/-- An actual empty failure pop retains its delivered cause at the outer failure permission. -/
theorem getCont_cause_empty (world : World) (input output : Kind)
    (fiber : FrameFiber ν σ β ε δ ι α) (cause : Cause ε δ ι α)
    (good : model.cause world input cause) (path : Path (Edge world) input output fiber.stack)
    (absorbs : AbsorbsInterrupt model world fiber.interruptedCause)
    (admitted : Allowed world fiber.interruptedCause)
    (found : (fiber.getCont .contE true (some cause)).answer = .empty) :
    ∃ delivered, (fiber.getCont .contE true (some cause)).carriedCause = some delivered ∧
      model.cause world output delivered := by
  unfold FrameFiber.getCont at found ⊢
  simp only [Bool.not_true, Bool.and_false, Bool.false_eq_true, if_false] at found ⊢
  apply PopTrace.empty_transport (Edge world)
    (fun scratch => scratch.stack = [] ∧ scratch.interruptedCause = fiber.interruptedCause)
    (fun kind carried => ∃ delivered, carried = some delivered ∧ model.cause world kind delivered)
    .contE true ?_ ?_ input output fiber.stack {fiber with stack := [], deferredInterrupt := false}
    (some cause) path ⟨rfl, rfl⟩ ⟨cause, rfl, good⟩ found
  · intro input middle head scratch after callback empty
    rw [FrameFiber.passPushed_fiber_cause]
    exact ⟨PopTrace.drain_empty .contE true head scratch empty.1,
      (External.passPushed_recorded .contE true (head.ensure scratch).1 none).trans
        ((ensure_recorded head scratch).trans empty.2)⟩
  · intro input middle head scratch before after callback empty passed good
    obtain ⟨current, incoming, good⟩ := good
    have recorded : AbsorbsInterrupt model world (head.ensure scratch).1.interruptedCause := by
      rw [ensure_recorded head scratch, empty.2]
      exact absorbs
    have admissible : Allowed world (head.ensure scratch).1.interruptedCause := by
      rw [ensure_recorded head scratch, empty.2]
      exact admitted
    have advanced : ∃ delivered, after = some delivered ∧ model.cause world middle delivered := by
      rcases passed with ⟨chosen, unchanged⟩ | ⟨answer, selected, skipped, changed⟩
      · have missing := PopTrace.answer_missing head .contE _ chosen
        exact ⟨current, unchanged.trans incoming,
          family.skipCause world input middle head callback world (model.future_refl world) current good missing⟩
      · obtain ⟨delivered, equation, nextGood⟩ := Hooked.saved_discard_cause
          (admitted := admissible) model interp Edge Allowed family world input middle head scratch current
          callback good (by simpa only [Bool.true_and] using skipped) recorded
        exact ⟨delivered, changed.trans (by rw [incoming]; exact equation), nextGood⟩
    obtain ⟨delivered, changed, nextGood⟩ := advanced
    rcases (Hooked.drain_cause head scratch delivered empty.1).2 with kept | ⟨interrupted, pending, combined⟩
    · exact ⟨delivered, by rw [changed]; exact kept, nextGood⟩
    · exact ⟨Cause.combine delivered interrupted, by rw [changed]; exact combined,
        absorbs interrupted (empty.2.symm.trans pending) middle delivered nextGood⟩
include interp family in
/-- Actual completed value returns carry their outer exit permission. -/
theorem resume_value_finished (world : World) (input output : Kind)
    (fiber : FrameFiber ν σ β ε δ ι α) (value : β) (good : model.value world input value)
    (path : Path (Edge world) input output fiber.stack) (exit : Exit β ε δ ι α)
    (finished : (fiber.resumeValue interp value (some (.success value))).1 = .finished exit) :
    ExitAt model world output exit := by
  have empty := FrameFiber.resumeValue_finished interp fiber value (some (.success value)) exit finished
  have permitted := getCont_value_empty model interp Edge Allowed family world input output fiber value good path empty
  rw [FrameFiber.resumeValue_empty interp fiber value (some (.success value)) empty] at finished
  cases finished
  exact permitted

include interp family in
/-- Actual completed failure returns retain the delivered failure permission after handler discards. -/
theorem resume_cause_finished (world : World) (input output : Kind)
    (fiber : FrameFiber ν σ β ε δ ι α) (cause : Cause ε δ ι α) (good : model.cause world input cause)
    (path : Path (Edge world) input output fiber.stack)
    (absorbs : AbsorbsInterrupt model world fiber.interruptedCause)
    (admitted : Allowed world fiber.interruptedCause) (exit : Exit β ε δ ι α)
    (finished : (fiber.resumeCause interp cause (some (.failure cause))).1 = .finished exit) :
    ExitAt model world output exit := by
  have empty := FrameFiber.resumeCause_finished interp fiber cause (some (.failure cause)) exit finished
  rw [← FrameFiber.getCont_answer_cause fiber .contE true (some cause)] at empty
  obtain ⟨delivered, carried, permitted⟩ := getCont_cause_empty model interp Edge Allowed family world input output fiber cause good path absorbs admitted empty
  rw [FrameFiber.resumeCause_empty interp fiber cause (some (.failure cause)) empty] at finished
  simp only [Option.getD_some, FramePop.deliveredExit, carried] at finished
  cases finished
  exact permitted

end Effect4.Machine.AnswerFlow.Contextual
