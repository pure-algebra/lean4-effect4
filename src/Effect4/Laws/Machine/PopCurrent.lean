import Effect4.Laws.Machine.PopTrace

/-!
Concept: scope-lifetime-finalization R11 and reactive-scheduling R2.
Question: actual continuation pops retain current code for frame debit.
Consumers: WriterWeights.getCont_frame_le and SourceScope.getCont_frame_at.
The shared pop trace supplies the recursive structure.
These field equalities establish no callback closure or history invariant.
-/
set_option autoImplicit false
namespace Effect4.Machine.PopTrace
open Effect4
universe u v
variable {ν σ : Type u} {β : Type v} {ε δ ι α : Type u}
variable [DecidableEq ε] [DecidableEq δ] [DecidableEq ι] [DecidableEq α]

omit [DecidableEq ε] [DecidableEq δ] [DecidableEq ι] [DecidableEq α] in
/-- Frame hooks retain current code while changing the interrupt state and saved stack. -/
theorem ensure_current (frame : Prim ν σ β ε δ ι α) (fiber : FrameFiber ν σ β ε δ ι α) :
    (frame.ensure fiber).1.current = fiber.current := by
  fun_cases Prim.ensure frame fiber
  all_goals rfl

/-- The one pushed hook retains current code. -/
theorem pushed_current (demand : Arm) (skip : Bool) (fiber : FrameFiber ν σ β ε δ ι α)
    (cause : Option (Cause ε δ ι α)) :
    (FrameFiber.passPushed demand skip fiber cause).fiber.current = fiber.current := by
  unfold FrameFiber.passPushed
  cases fiber.stack with
  | nil => rfl
  | cons frame rest => exact ensure_current frame _

/-- Current code is a projection of the existing actual pop trace. -/
theorem Trace.current {demand : Arm} {skip : Bool} {frames : List (Prim ν σ β ε δ ι α)}
    {fiber : FrameFiber ν σ β ε δ ι α} {cause : Option (Cause ε δ ι α)}
    {parts : List (Prim ν σ β ε δ ι α × List (Prim ν σ β ε δ ι α))}
    {suffix : List (Prim ν σ β ε δ ι α)} {result : FramePop ν σ β ε δ ι α}
    (trace : Trace demand skip frames fiber cause parts suffix result) :
    result.fiber.current = fiber.current := by
  induction trace with
  | nil => rfl
  | selected frame rest fiber cause answer chosen kept => exact ensure_current frame fiber
  | continued frame rest fiber before after parts suffix tail passed empty next ih =>
    simp only [FrameFiber.passOn, FrameFiber.joinPushed, empty, ih, pushed_current, ensure_current]
  | hooked frame rest fiber before after tail passed answered =>
    simp only [FrameFiber.passOn, FrameFiber.joinPushed]
    exact (pushed_current demand skip _ after).trans (ensure_current frame fiber)

/-- The actual fused pop retains current code by its shared trace. -/
theorem pop_current (demand : Arm) (skip : Bool) (frames : List (Prim ν σ β ε δ ι α))
    (fiber : FrameFiber ν σ β ε δ ι α) (cause : Option (Cause ε δ ι α)) :
    (FrameFiber.popFrom demand skip frames fiber cause).fiber.current = fiber.current := by
  obtain ⟨parts, suffix, trace⟩ := popFrom_spec demand skip frames fiber cause
  exact trace.current

/-- Deferred delivery and ordinary continuation selection both retain current code. -/
theorem getCont_current (fiber : FrameFiber ν σ β ε δ ι α) (demand : Arm) (skip : Bool)
    (cause : Option (Cause ε δ ι α)) : (fiber.getCont demand skip cause).fiber.current = fiber.current := by
  obtain deferred | ordinary := getCont_spec fiber demand skip cause
  · rw [deferred.2]
  · obtain ⟨_, parts, suffix, trace, _⟩ := ordinary
    exact trace.current

end Effect4.Machine.PopTrace
