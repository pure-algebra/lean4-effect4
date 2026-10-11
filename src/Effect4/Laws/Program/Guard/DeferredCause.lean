import Effect4.Laws.Program.Guard.Interruption

/-! Local deferred-cause consistency for the native evaluator and one iteration.
The input implication is the only premise; no machine or queue invariant is used.
Proof graph: frame cause preservation + step_preserves_uninterrupted
→ frame consistency → primitive evaluation → native evaluation → iteration.
-/

set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 800000

namespace Effect4.Program.Guard.DeferredCause
open Effect4 Effect4.Machine Effect4.Program
open Effect4.Program.Guard.Interruption (frame_step_interruptedCause)

abbrev NFrame := FrameFiber EffName EffThunk Val Err Defect FiberId Ann
abbrev NFiber := RunFiber EffName EffThunk Val Err Defect FiberId Ann Ctx
abbrev NInterp := RunInterp EffName EffThunk Val Err Defect FiberId Ann Ctx Stores

def DeferredCause (frame : NFrame) : Prop :=
  frame.deferredInterrupt = true → frame.interruptedCause.isSome = true

theorem getCont_deferred_false (self : NFrame) (demand : Effect4.Arm) (skip : Bool) :
    (self.getCont demand skip).fiber.deferredInterrupt = false := by
  unfold FrameFiber.getCont
  split
  · rfl
  · exact FrameFiber.popFrom_deferredInterrupt _ _ _ _

theorem getCont_deferredCause (self : NFrame) (demand : Effect4.Arm) (skip : Bool) :
    DeferredCause (self.getCont demand skip).fiber := by
  intro hd
  rw [getCont_deferred_false] at hd
  cases hd

theorem getCont_deferredCause_carried (self : NFrame) (demand : Effect4.Arm)
    (skip : Bool) (cause : Option CauseV) : DeferredCause (self.getCont demand skip cause).fiber := by
  rw [FrameFiber.getCont_fiber_cause]
  exact getCont_deferredCause _ _ _

theorem frame_step_deferredCause (interp : PrimInterp EffName EffThunk Val Err Defect FiberId Ann)
    (self next : NFrame) (hf : DeferredCause self)
    (h : (self.step interp).fst = FrameStep.running next) : DeferredCause next := by
  cases hc : self.interruptedCause with
  | none =>
    have hd : self.deferredInterrupt = false := by
      cases he : self.deferredInterrupt with
      | false => rfl
      | true => simpa [hc] using hf he
    have hn := FrameFiber.step_preserves_uninterrupted interp self next hc hd h
    intro hnDeferred
    rw [hn.2] at hnDeferred
    cases hnDeferred
  | some cause =>
    intro _
    rw [frame_step_interruptedCause interp self next h, hc]
    rfl

theorem frameExitState_deferredCause (self : NFrame) :
    DeferredCause (frameExitState self) := by
  unfold frameExitState
  split <;> exact getCont_deferredCause _ _ _

theorem move_deferredCause {f g : NFrame} (m : Moves.FrameMove f g)
    (kept : DeferredCause f) : DeferredCause g := by
  cases m with
  | answer => exact kept
  | push => exact kept
  | step interp _ _ _ h =>
    exact frame_step_deferredCause interp _ _ kept (congrArg Prod.fst h)
  | finish => exact frameExitState_deferredCause _
  | pop => exact getCont_deferredCause_carried _ _ _ _
  | mask =>
    unfold FrameFiber.uninterruptible
    split
    · exact kept
    · exact kept
  | unmask =>
    unfold FrameFiber.interruptibleRegion FrameFiber.setFiberInterruptible
    split
    · exact kept
    · exact kept
  | pendingFailure =>
    intro deferred
    cases deferred

/-- A word of frame moves retains the deferred-cause implication.
This serves the existing guard consistency claim at every evaluator level. -/
theorem moves_deferredCause {f g : NFrame} (word : Moves.Moves f g)
    (held : DeferredCause f) : DeferredCause g :=
  word.keeps DeferredCause (fun _ _ changed kept => move_deferredCause changed kept) held

theorem stepFrame_deferredCause (interp : NInterp) (m : NativeMachine)
    (f : NFiber) (yielding : Bool) (hf : DeferredCause f.frame) :
    DeferredCause (evaluatePrim.stepFrame interp m f yielding).fiber.frame :=
  moves_deferredCause (Moves.stepFrame_moves interp m f yielding) hf

theorem finalizerOr_deferredCause (interp : NInterp) (m : NativeMachine)
    (f : NFiber) (yielding : Bool) (exit : ExitV) (hf : DeferredCause f.frame) :
    DeferredCause (evaluatePrim.finalizerOr interp m f yielding exit).fiber.frame :=
  moves_deferredCause (Moves.finalizerOr_moves interp m f yielding exit) hf

theorem withFiber_deferredCause (interp : NInterp) (m : NativeMachine)
    (f : NFiber) (yielding : Bool) (action : NAction) (hf : DeferredCause f.frame) :
    DeferredCause (evaluatePrim.withFiber interp m f yielding action).fiber.frame :=
  moves_deferredCause (Moves.withFiber_moves interp m f yielding action) hf

theorem evaluatePrim_deferredCause (interp : NInterp) (m : NativeMachine)
    (f : NFiber) (yielding : Bool) (hf : DeferredCause f.frame) :
    DeferredCause (evaluatePrim interp m f yielding).fiber.frame :=
  moves_deferredCause (Moves.evaluatePrim_moves interp m f yielding) hf

theorem exitScoped_deferredCause (p : NativeEff) (m : NativeMachine)
    (f : NFiber) (yielding : Bool) (exit : ExitV) (hf : DeferredCause f.frame) :
    DeferredCause (exitScoped p m f yielding exit).fiber.frame :=
  moves_deferredCause (Moves.exitScoped_moves p m f yielding exit) hf

/-- Native evaluation retains the deferred-cause implication for its returned
fiber, for every root, table, machine, fiber, and yielding latch. -/
theorem evaluateNative_deferredCause (p : NativeEff) (table : RowTable)
    (m : NativeMachine) (f : NFiber) (yielding : Bool)
    (hf : f.frame.deferredInterrupt = true → f.frame.interruptedCause.isSome = true) :
    (evaluateNative p m f yielding table).fiber.frame.deferredInterrupt = true →
      (evaluateNative p m f yielding table).fiber.frame.interruptedCause.isSome = true :=
  moves_deferredCause (Moves.evaluateNative_moves p table m f yielding) hf

theorem runloopTop_deferredCause (f : NFiber) (hf : DeferredCause f.frame) :
    DeferredCause (runloopTop f).frame := by
  unfold runloopTop
  split
  · intro h; cases h
  · exact hf

theorem injectYield_deferredCause (m : NativeMachine) (f : NFiber) (yielding : Bool)
    (it : Iter EffName EffThunk Val Err Defect FiberId Ann Ctx Stores)
    (hf : DeferredCause f.frame) (h : injectYield m f yielding = some it) :
    DeferredCause it.fiber.frame := by
  unfold injectYield at h
  split at h
  · injection h with h'; subst h'; exact hf
  · cases h

/-- One native iteration retains the same implication. The evaluator instance
is pinned explicitly; this is a returned-fiber law, not a machine invariant. -/
theorem iteration_deferredCause (p : NativeEff) (table : RowTable)
    (m : NativeMachine) (f : NFiber) (yielding : Bool)
    (hf : f.frame.deferredInterrupt = true → f.frame.interruptedCause.isSome = true) :
    letI := evaluatorFor p table
    (iteration (interpOf p table) m f yielding).fiber.frame.deferredInterrupt = true →
      (iteration (interpOf p table) m f yielding).fiber.frame.interruptedCause.isSome = true :=
  moves_deferredCause (Moves.iteration_moves p table (interpOf p table) m f yielding) hf

end Effect4.Program.Guard.DeferredCause
