import Effect4.Api

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

abbrev NFrame := FrameFiber EffName EffThunk Val Err Defect FiberId Ann
abbrev NFiber := RunFiber EffName EffThunk Val Err Defect FiberId Ann Ctx
abbrev NInterp := RunInterp EffName EffThunk Val Err Defect FiberId Ann Ctx Stores

def DeferredCause (frame : NFrame) : Prop :=
  frame.deferredInterrupt = true → frame.interruptedCause.isSome = true

theorem getCont_interruptedCause (self : NFrame) (demand : Effect4.Arm) (skip : Bool) :
    (self.getCont demand skip).fiber.interruptedCause = self.interruptedCause := by
  unfold FrameFiber.getCont
  split
  · rfl
  · exact FrameFiber.popFrom_interruptedCause _ _ _ _

theorem resumeValue_interruptedCause (interp : PrimInterp EffName EffThunk Val Err Defect FiberId Ann)
    (self next : NFrame) (value : Val) (provided : Option ExitV)
    (h : (self.resumeValue interp value provided).fst = FrameStep.running next) :
    next.interruptedCause = self.interruptedCause := by
  have hc := getCont_interruptedCause self Effect4.Arm.contA false
  unfold FrameFiber.resumeValue at h
  split at h
  · exact absurd h (by simp)
  · injection h with h'; subst h'; exact hc
  · injection h with h'; subst h'; exact hc
  · split at h
    · injection h with h'; subst h'; exact hc
    · exact absurd h (by simp)

theorem resumeCause_interruptedCause (interp : PrimInterp EffName EffThunk Val Err Defect FiberId Ann)
    (self next : NFrame) (cause : Cause Err Defect FiberId Ann) (provided : Option ExitV)
    (h : (self.resumeCause interp cause provided).fst = FrameStep.running next) :
    next.interruptedCause = self.interruptedCause := by
  have hc := getCont_interruptedCause self Effect4.Arm.contE true
  unfold FrameFiber.resumeCause at h
  split at h
  · exact absurd h (by simp)
  · injection h with h'; subst h'; exact hc
  · injection h with h'; subst h'; exact hc
  · split at h
    · injection h with h'; subst h'; exact hc
    · exact absurd h (by simp)

theorem frame_step_interruptedCause (interp : PrimInterp EffName EffThunk Val Err Defect FiberId Ann)
    (self next : NFrame) (h : (self.step interp).fst = FrameStep.running next) :
    next.interruptedCause = self.interruptedCause := by
  unfold FrameFiber.step at h
  split at h
  all_goals first
    | exact resumeValue_interruptedCause interp self next _ _ h
    | exact resumeCause_interruptedCause interp self next _ _ h
    | (injection h with h'; subst h'; rfl)
    | (split at h <;> (injection h with h'; subst h'; rfl))

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

theorem stepFrame_deferredCause (interp : NInterp) (m : NativeMachine)
    (f : NFiber) (yielding : Bool) (hf : DeferredCause f.frame) :
    DeferredCause (evaluatePrim.stepFrame interp m f yielding).fiber.frame := by
  unfold evaluatePrim.stepFrame
  cases hs : f.frame.step interp.toPrimInterp with
  | mk step events =>
    cases step with
    | running next =>
      exact frame_step_deferredCause interp.toPrimInterp f.frame next hf (congrArg Prod.fst hs)
    | finished exit => exact frameExitState_deferredCause f.frame

theorem finalizerOr_deferredCause (interp : NInterp) (m : NativeMachine)
    (f : NFiber) (yielding : Bool) (exit : ExitV) (hf : DeferredCause f.frame) :
    DeferredCause (evaluatePrim.finalizerOr interp m f yielding exit).fiber.frame := by
  cases exit <;> unfold evaluatePrim.finalizerOr <;> dsimp only
  all_goals
    split
    · split
      · exact getCont_deferredCause _ _ _
      · exact stepFrame_deferredCause _ _ _ _ hf
    · exact stepFrame_deferredCause _ _ _ _ hf

theorem withFiber_deferredCause (interp : NInterp) (m : NativeMachine)
    (f : NFiber) (yielding : Bool) (action : NAction) (hf : DeferredCause f.frame) :
    DeferredCause (evaluatePrim.withFiber interp m f yielding action).fiber.frame := by
  cases action <;>
    simp only [evaluatePrim.withFiber,
      evaluatePrim.interruptAs, spawn, start, countdownPark, beginRace,
      RunFiber.park, FrameFiber.uninterruptible, FrameFiber.interruptibleRegion,
      FrameFiber.setFiberInterruptible]
  all_goals repeat' first | exact hf | split
  all_goals simp_all [DeferredCause]

theorem evaluatePrim_deferredCause (interp : NInterp) (m : NativeMachine)
    (f : NFiber) (yielding : Bool) (hf : DeferredCause f.frame) :
    DeferredCause (evaluatePrim interp m f yielding).fiber.frame := by
  simp only [evaluatePrim, registerRace, countdownPark, RunFiber.park]
  repeat' first
    | exact stepFrame_deferredCause _ _ _ _ hf
    | exact finalizerOr_deferredCause _ _ _ _ _ hf
    | exact withFiber_deferredCause _ _ _ _ _ hf
    | exact hf
    | split
  all_goals simp_all [DeferredCause]
  all_goals repeat' first | assumption | split

theorem exitScoped_deferredCause (p : NativeEff) (m : NativeMachine)
    (f : NFiber) (yielding : Bool) (exit : ExitV) (hf : DeferredCause f.frame) :
    DeferredCause (exitScoped p m f yielding exit).fiber.frame := by
  cases exit <;> simp only [exitScoped]
  all_goals repeat' first
    | exact evaluatePrim_deferredCause _ _ _ _ hf
    | exact getCont_deferredCause _ _ _
    | exact hf
    | split

/-- Native evaluation retains the deferred-cause implication for its returned
fiber, for every root, table, machine, fiber, and yielding latch. -/
theorem evaluateNative_deferredCause (p : NativeEff) (table : RowTable)
    (m : NativeMachine) (f : NFiber) (yielding : Bool)
    (hf : f.frame.deferredInterrupt = true → f.frame.interruptedCause.isSome = true) :
    (evaluateNative p m f yielding table).fiber.frame.deferredInterrupt = true →
      (evaluateNative p m f yielding table).fiber.frame.interruptedCause.isSome = true := by
  change DeferredCause (evaluateNative p m f yielding table).fiber.frame
  simp only [evaluateNative]
  repeat' first
    | exact evaluatePrim_deferredCause _ _ _ _ hf
    | exact exitScoped_deferredCause _ _ _ _ _ hf
    | exact hf
    | split

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
      (iteration (interpOf p table) m f yielding).fiber.frame.interruptedCause.isSome = true := by
  letI := evaluatorFor p table
  have ht : DeferredCause (countOp (runloopTop f)).frame := runloopTop_deferredCause f hf
  cases hi : injectYield m (countOp (runloopTop f)) yielding with
  | none =>
    simpa only [iteration, hi] using
      evaluateNative_deferredCause p table m (countOp (runloopTop f)) yielding ht
  | some it =>
    simpa only [iteration, hi] using
      evaluateNative_deferredCause p table it.machine it.fiber it.yielding
        (injectYield_deferredCause m _ yielding it ht hi)


end Effect4.Program.Guard.DeferredCause
