import Effect4.Api

set_option autoImplicit false
namespace Effect4.Program.Guard.Interruption
open Effect4 Effect4.Machine Effect4.Program
abbrev NFrame := FrameFiber EffName EffThunk Val Err Defect FiberId Ann

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


abbrev NFiber := RunFiber EffName EffThunk Val Err Defect FiberId Ann Ctx
abbrev NInterp := RunInterp EffName EffThunk Val Err Defect FiberId Ann Ctx Stores

theorem frameExitState_interruptedCause (self : NFrame) :
    (frameExitState self).interruptedCause = self.interruptedCause := by
  unfold frameExitState
  split <;> exact getCont_interruptedCause _ _ _

theorem stepFrame_interruptedCause (interp : NInterp) (m : NativeMachine)
    (f : NFiber) (yielding : Bool) :
    (evaluatePrim.stepFrame interp m f yielding).fiber.frame.interruptedCause =
      f.frame.interruptedCause := by
  unfold evaluatePrim.stepFrame
  cases hs : f.frame.step interp.toPrimInterp with
  | mk step events =>
    cases step with
    | running next =>
      exact frame_step_interruptedCause interp.toPrimInterp f.frame next
        (congrArg Prod.fst hs)
    | finished exit =>
      exact frameExitState_interruptedCause f.frame

theorem finalizerOr_interruptedCause (interp : NInterp) (m : NativeMachine)
    (f : NFiber) (yielding : Bool) (exit : ExitV) :
    (evaluatePrim.finalizerOr interp m f yielding exit).fiber.frame.interruptedCause =
      f.frame.interruptedCause := by
  cases exit <;> unfold evaluatePrim.finalizerOr <;> dsimp only
  all_goals
    split
    · split
      · exact getCont_interruptedCause _ _ _
      · exact stepFrame_interruptedCause _ _ _ _
    · exact stepFrame_interruptedCause _ _ _ _


theorem withFiber_interruptedCause (interp : NInterp) (m : NativeMachine)
    (f : NFiber) (yielding : Bool) (action : NAction) :
    (evaluatePrim.withFiber interp m f yielding action).fiber.frame.interruptedCause =
      f.frame.interruptedCause := by
  cases action <;>
    simp only [evaluatePrim.withFiber,
      evaluatePrim.interruptAs, spawn, start, countdownPark, beginRace,
      RunFiber.park, FrameFiber.uninterruptible, FrameFiber.interruptibleRegion,
      FrameFiber.setFiberInterruptible]
  all_goals repeat' first | rfl | split
  all_goals simp_all


theorem evaluatePrim_interruptedCause (interp : NInterp) (m : NativeMachine)
    (f : NFiber) (yielding : Bool) :
    (evaluatePrim interp m f yielding).fiber.frame.interruptedCause =
      f.frame.interruptedCause := by
  simp only [evaluatePrim, registerRace, countdownPark, RunFiber.park]
  repeat' first
    | exact stepFrame_interruptedCause _ _ _ _
    | exact finalizerOr_interruptedCause _ _ _ _ _
    | exact withFiber_interruptedCause _ _ _ _ _
    | rfl
    | split
  all_goals simp_all
  all_goals repeat' first | rfl | split


theorem exitScoped_interruptedCause (p : NativeEff) (m : NativeMachine)
    (f : NFiber) (yielding : Bool) (exit : ExitV) :
    (exitScoped p m f yielding exit).fiber.frame.interruptedCause =
      f.frame.interruptedCause := by
  cases exit <;> simp only [exitScoped]
  all_goals repeat' first
    | exact evaluatePrim_interruptedCause _ _ _ _
    | exact getCont_interruptedCause _ _ _
    | rfl
    | split

theorem evaluateNative_interruptedCause (p : NativeEff) (table : RowTable)
    (m : NativeMachine) (f : NFiber) (yielding : Bool) :
    (evaluateNative p m f yielding table).fiber.frame.interruptedCause =
      f.frame.interruptedCause := by
  simp only [evaluateNative]
  repeat' first
    | exact evaluatePrim_interruptedCause _ _ _ _
    | exact exitScoped_interruptedCause _ _ _ _ _
    | rfl
    | split

theorem runloopTop_interruptedCause (f : NFiber) :
    (runloopTop f).frame.interruptedCause = f.frame.interruptedCause := by
  unfold runloopTop
  split <;> rfl

theorem injectYield_interruptedCause (m : NativeMachine) (f : NFiber) (yielding : Bool)
    (it : Iter EffName EffThunk Val Err Defect FiberId Ann Ctx Stores)
    (h : injectYield m f yielding = some it) :
    it.fiber.frame.interruptedCause = f.frame.interruptedCause := by
  unfold injectYield at h
  split at h
  · injection h with h'; subst h'; rfl
  · cases h

theorem iteration_interruptedCause (p : NativeEff) (table : RowTable)
    (m : NativeMachine) (f : NFiber) (yielding : Bool) :
    letI := evaluatorFor p table
    (iteration (interpOf p table) m f yielding).fiber.frame.interruptedCause =
      f.frame.interruptedCause := by
  letI := evaluatorFor p table
  cases hi : injectYield m (countOp (runloopTop f)) yielding with
  | none =>
    simpa only [iteration, hi] using
      (evaluateNative_interruptedCause p table m (countOp (runloopTop f)) yielding).trans
        (runloopTop_interruptedCause f)
  | some it =>
    simpa only [iteration, hi] using
      (evaluateNative_interruptedCause p table it.machine it.fiber it.yielding).trans
        ((injectYield_interruptedCause m _ yielding it hi).trans (runloopTop_interruptedCause f))

theorem stepFrame_id (interp : NInterp) (m : NativeMachine)
    (f : NFiber) (yielding : Bool) :
    (evaluatePrim.stepFrame interp m f yielding).fiber.id =
      f.id := by
  unfold evaluatePrim.stepFrame
  cases hs : f.frame.step interp.toPrimInterp with
  | mk step events => cases step <;> rfl

theorem finalizerOr_id (interp : NInterp) (m : NativeMachine)
    (f : NFiber) (yielding : Bool) (exit : ExitV) :
    (evaluatePrim.finalizerOr interp m f yielding exit).fiber.id =
      f.id := by
  cases exit <;> unfold evaluatePrim.finalizerOr <;> dsimp only
  all_goals
    split
    · split
      · rfl
      · exact stepFrame_id _ _ _ _
    · exact stepFrame_id _ _ _ _

theorem withFiber_id (interp : NInterp) (m : NativeMachine)
    (f : NFiber) (yielding : Bool) (action : NAction) :
    (evaluatePrim.withFiber interp m f yielding action).fiber.id =
      f.id := by
  cases action <;>
    simp only [evaluatePrim.withFiber,
      evaluatePrim.interruptAs, spawn, start, countdownPark, beginRace,
      RunFiber.park, FrameFiber.uninterruptible, FrameFiber.interruptibleRegion,
      FrameFiber.setFiberInterruptible]
  all_goals repeat' first | rfl | split
  all_goals simp_all

theorem evaluatePrim_id (interp : NInterp) (m : NativeMachine)
    (f : NFiber) (yielding : Bool) :
    (evaluatePrim interp m f yielding).fiber.id =
      f.id := by
  simp only [evaluatePrim, registerRace, countdownPark, RunFiber.park]
  repeat' first
    | exact stepFrame_id _ _ _ _
    | exact finalizerOr_id _ _ _ _ _
    | exact withFiber_id _ _ _ _ _
    | rfl
    | split
  all_goals simp_all
  all_goals repeat' first | rfl | split

theorem exitScoped_id (p : NativeEff) (m : NativeMachine)
    (f : NFiber) (yielding : Bool) (exit : ExitV) :
    (exitScoped p m f yielding exit).fiber.id =
      f.id := by
  cases exit <;> simp only [exitScoped]
  all_goals repeat' first
    | exact evaluatePrim_id _ _ _ _
    | rfl
    | rfl
    | split

theorem evaluateNative_id (p : NativeEff) (table : RowTable)
    (m : NativeMachine) (f : NFiber) (yielding : Bool) :
    (evaluateNative p m f yielding table).fiber.id =
      f.id := by
  simp only [evaluateNative]
  repeat' first
    | exact evaluatePrim_id _ _ _ _
    | exact exitScoped_id _ _ _ _ _
    | rfl
    | split

theorem runloopTop_id (f : NFiber) :
    (runloopTop f).id = f.id := by
  unfold runloopTop
  split <;> rfl

theorem injectYield_id (m : NativeMachine) (f : NFiber) (yielding : Bool)
    (it : Iter EffName EffThunk Val Err Defect FiberId Ann Ctx Stores)
    (h : injectYield m f yielding = some it) :
    it.fiber.id = f.id := by
  unfold injectYield at h
  split at h
  · injection h with h'; subst h'; rfl
  · cases h

theorem iteration_id (p : NativeEff) (table : RowTable)
    (m : NativeMachine) (f : NFiber) (yielding : Bool) :
    letI := evaluatorFor p table
    (iteration (interpOf p table) m f yielding).fiber.id =
      f.id := by
  letI := evaluatorFor p table
  cases hi : injectYield m (countOp (runloopTop f)) yielding with
  | none =>
    simpa only [iteration, hi] using
      (evaluateNative_id p table m (countOp (runloopTop f)) yielding).trans
        (runloopTop_id f)
  | some it =>
    simpa only [iteration, hi] using
      (evaluateNative_id p table it.machine it.fiber it.yielding).trans
        ((injectYield_id m _ yielding it hi).trans (runloopTop_id f))

theorem stepFrame_exit (interp : NInterp) (m : NativeMachine)
    (f : NFiber) (yielding : Bool) :
    (evaluatePrim.stepFrame interp m f yielding).fiber.exit =
      f.exit := by
  unfold evaluatePrim.stepFrame
  cases hs : f.frame.step interp.toPrimInterp with
  | mk step events => cases step <;> rfl

theorem finalizerOr_exit (interp : NInterp) (m : NativeMachine)
    (f : NFiber) (yielding : Bool) (exit : ExitV) :
    (evaluatePrim.finalizerOr interp m f yielding exit).fiber.exit =
      f.exit := by
  cases exit <;> unfold evaluatePrim.finalizerOr <;> dsimp only
  all_goals
    split
    · split
      · rfl
      · exact stepFrame_exit _ _ _ _
    · exact stepFrame_exit _ _ _ _

theorem withFiber_exit (interp : NInterp) (m : NativeMachine)
    (f : NFiber) (yielding : Bool) (action : NAction) :
    (evaluatePrim.withFiber interp m f yielding action).fiber.exit =
      f.exit := by
  cases action <;>
    simp only [evaluatePrim.withFiber,
      evaluatePrim.interruptAs, spawn, start, countdownPark, beginRace,
      RunFiber.park, FrameFiber.uninterruptible, FrameFiber.interruptibleRegion,
      FrameFiber.setFiberInterruptible]
  all_goals repeat' first | rfl | split
  all_goals simp_all

theorem evaluatePrim_exit (interp : NInterp) (m : NativeMachine)
    (f : NFiber) (yielding : Bool) :
    (evaluatePrim interp m f yielding).fiber.exit =
      f.exit := by
  simp only [evaluatePrim, registerRace, countdownPark, RunFiber.park]
  repeat' first
    | exact stepFrame_exit _ _ _ _
    | exact finalizerOr_exit _ _ _ _ _
    | exact withFiber_exit _ _ _ _ _
    | rfl
    | split
  all_goals simp_all
  all_goals repeat' first | rfl | split

theorem exitScoped_exit (p : NativeEff) (m : NativeMachine)
    (f : NFiber) (yielding : Bool) (exit : ExitV) :
    (exitScoped p m f yielding exit).fiber.exit =
      f.exit := by
  cases exit <;> simp only [exitScoped]
  all_goals repeat' first
    | exact evaluatePrim_exit _ _ _ _
    | rfl
    | rfl
    | split

theorem evaluateNative_exit (p : NativeEff) (table : RowTable)
    (m : NativeMachine) (f : NFiber) (yielding : Bool) :
    (evaluateNative p m f yielding table).fiber.exit =
      f.exit := by
  simp only [evaluateNative]
  repeat' first
    | exact evaluatePrim_exit _ _ _ _
    | exact exitScoped_exit _ _ _ _ _
    | rfl
    | split

theorem runloopTop_exit (f : NFiber) :
    (runloopTop f).exit = f.exit := by
  unfold runloopTop
  split <;> rfl

theorem injectYield_exit (m : NativeMachine) (f : NFiber) (yielding : Bool)
    (it : Iter EffName EffThunk Val Err Defect FiberId Ann Ctx Stores)
    (h : injectYield m f yielding = some it) :
    it.fiber.exit = f.exit := by
  unfold injectYield at h
  split at h
  · injection h with h'; subst h'; rfl
  · cases h

theorem iteration_exit (p : NativeEff) (table : RowTable)
    (m : NativeMachine) (f : NFiber) (yielding : Bool) :
    letI := evaluatorFor p table
    (iteration (interpOf p table) m f yielding).fiber.exit =
      f.exit := by
  letI := evaluatorFor p table
  cases hi : injectYield m (countOp (runloopTop f)) yielding with
  | none =>
    simpa only [iteration, hi] using
      (evaluateNative_exit p table m (countOp (runloopTop f)) yielding).trans
        (runloopTop_exit f)
  | some it =>
    simpa only [iteration, hi] using
      (evaluateNative_exit p table it.machine it.fiber it.yielding).trans
        ((injectYield_exit m _ yielding it hi).trans (runloopTop_exit f))



/-- The owner-approved interruption observation; consistency is an internal invariant. -/
def Interrupted (f : NFiber) : Prop := f.interruptPending = true ∨ f.exit.isSome = true

def DeferredCause (f : NFiber) : Prop :=
  f.frame.deferredInterrupt = true → f.frame.interruptedCause.isSome = true

theorem interrupted_iff_recorded_or_exit (f : NFiber) (consistent : DeferredCause f) :
    Interrupted f ↔ f.frame.interruptedCause.isSome = true ∨ f.exit.isSome = true := by
  simp only [Interrupted, RunFiber.interruptPending, FiberCore.deferredInterrupt,
    FiberCore.interruptedCause, Bool.or_eq_true]
  constructor
  · intro h
    rcases h with (hd | hc) | he
    · exact Or.inl (consistent hd)
    · exact Or.inl hc
    · exact Or.inr he
  · intro h
    rcases h with hc | he
    · exact Or.inl (Or.inr hc)
    · exact Or.inr he

theorem interrupted_of_recorded_or_exit (f : NFiber)
    (h : f.frame.interruptedCause.isSome = true ∨ f.exit.isSome = true) : Interrupted f := by
  rcases h with hc | he
  · exact Or.inl (by simp [RunFiber.interruptPending, FiberCore.interruptedCause, hc])
  · exact Or.inr he

theorem evaluateNative_interrupted (p : NativeEff) (table : RowTable)
    (m : NativeMachine) (f : NFiber) (yielding : Bool)
    (consistent : DeferredCause f) (h : Interrupted f) :
    Interrupted (evaluateNative p m f yielding table).fiber := by
  apply interrupted_of_recorded_or_exit
  rw [evaluateNative_interruptedCause, evaluateNative_exit]
  exact (interrupted_iff_recorded_or_exit f consistent).mp h

theorem iteration_interrupted (p : NativeEff) (table : RowTable)
    (m : NativeMachine) (f : NFiber) (yielding : Bool)
    (consistent : DeferredCause f) (h : Interrupted f) :
    letI := evaluatorFor p table
    Interrupted (iteration (interpOf p table) m f yielding).fiber := by
  letI := evaluatorFor p table
  apply interrupted_of_recorded_or_exit
  rw [iteration_interruptedCause, iteration_exit]
  exact (interrupted_iff_recorded_or_exit f consistent).mp h

end Effect4.Program.Guard.Interruption
