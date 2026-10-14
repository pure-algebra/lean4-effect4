import Effect4.Laws.Program.Moves

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

theorem getCont_interruptedCause_carried (self : NFrame) (demand : Effect4.Arm)
    (skip : Bool) (cause : Option CauseV) :
    (self.getCont demand skip cause).fiber.interruptedCause = self.interruptedCause := by
  rw [FrameFiber.getCont_fiber_cause]
  exact getCont_interruptedCause _ _ _

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
  have hc := getCont_interruptedCause_carried self Effect4.Arm.contE true (some cause)
  unfold FrameFiber.resumeCause at h
  dsimp only at h
  split at h
  · cases h
  · injection h with h'; subst h'; exact hc
  · injection h with h'; subst h'; exact hc
  · split at h
    · injection h with h'; subst h'; exact hc
    · cases h

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

theorem move_interruptedCause {f g : NFrame} (m : Moves.FrameMove f g) :
    g.interruptedCause = f.interruptedCause := by
  cases m with
  | answer => rfl
  | push => rfl
  | step interp _ _ _ h =>
    exact frame_step_interruptedCause interp _ _ (congrArg Prod.fst h)
  | finish => exact frameExitState_interruptedCause _
  | pop => exact getCont_interruptedCause_carried _ _ _ _
  | mask =>
    unfold FrameFiber.uninterruptible
    split <;> rfl
  | unmask =>
    unfold FrameFiber.interruptibleRegion FrameFiber.setFiberInterruptible
    split <;> rfl
  | pendingFailure => rfl

/-- A word of frame moves retains the recorded cause.
This serves the existing guard interruption claim through each evaluator level. -/
theorem moves_interruptedCause {f g : NFrame} (word : Moves.Moves f g) :
    g.interruptedCause = f.interruptedCause :=
  word.keeps (fun next => next.interruptedCause = f.interruptedCause)
    (fun _ _ changed held => (move_interruptedCause changed).trans held) rfl

theorem stepFrame_interruptedCause (interp : NInterp) (m : NativeMachine)
    (f : NFiber) (yielding : Bool) :
    (evaluatePrim.stepFrame interp m f yielding).fiber.frame.interruptedCause =
      f.frame.interruptedCause :=
  moves_interruptedCause (Moves.stepFrame_moves interp m f yielding)

theorem finalizerOr_interruptedCause (interp : NInterp) (m : NativeMachine)
    (f : NFiber) (yielding : Bool) (exit : ExitV) :
    (evaluatePrim.finalizerOr interp m f yielding exit).fiber.frame.interruptedCause =
      f.frame.interruptedCause :=
  moves_interruptedCause (Moves.finalizerOr_moves interp m f yielding exit)

theorem withFiber_interruptedCause (interp : NInterp) (m : NativeMachine)
    (f : NFiber) (yielding : Bool) (action : NAction) :
    (evaluatePrim.withFiber interp m f yielding action).fiber.frame.interruptedCause =
      f.frame.interruptedCause :=
  moves_interruptedCause (Moves.withFiber_moves interp m f yielding action)

theorem evaluatePrim_interruptedCause (interp : NInterp) (m : NativeMachine)
    (f : NFiber) (yielding : Bool) :
    (evaluatePrim interp m f yielding).fiber.frame.interruptedCause =
      f.frame.interruptedCause :=
  moves_interruptedCause (Moves.evaluatePrim_moves interp m f yielding)

theorem exitScoped_interruptedCause (p : NativeEff) (m : NativeMachine)
    (f : NFiber) (yielding : Bool) (exit : ExitV) :
    (exitScoped p m f yielding exit).fiber.frame.interruptedCause =
      f.frame.interruptedCause :=
  moves_interruptedCause (Moves.exitScoped_moves p m f yielding exit)

@[semantics "reactive-scheduling"]
theorem evaluateNative_interruptedCause (p : NativeEff) (table : RowTable)
    (m : NativeMachine) (f : NFiber) (yielding : Bool) :
    (evaluateNative p m f yielding table).fiber.frame.interruptedCause =
      f.frame.interruptedCause :=
  moves_interruptedCause (Moves.evaluateNative_moves p table m f yielding)

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

@[semantics "reactive-scheduling"]
theorem iteration_interruptedCause (p : NativeEff) (table : RowTable)
    (m : NativeMachine) (f : NFiber) (yielding : Bool) :
    letI := evaluatorFor p table
    (iteration (interpOf p table) m f yielding).fiber.frame.interruptedCause =
      f.frame.interruptedCause :=
  moves_interruptedCause (Moves.iteration_moves p table (interpOf p table) m f yielding)

theorem stepFrame_id (interp : NInterp) (m : NativeMachine)
    (f : NFiber) (yielding : Bool) :
    (evaluatePrim.stepFrame interp m f yielding).fiber.id =
      f.id :=
  (Moves.stepFrame_footprint interp m f yielding).id

theorem finalizerOr_id (interp : NInterp) (m : NativeMachine)
    (f : NFiber) (yielding : Bool) (exit : ExitV) :
    (evaluatePrim.finalizerOr interp m f yielding exit).fiber.id =
      f.id :=
  (Moves.finalizerOr_footprint interp m f yielding exit).id

theorem withFiber_id (interp : NInterp) (m : NativeMachine)
    (f : NFiber) (yielding : Bool) (action : NAction) :
    (evaluatePrim.withFiber interp m f yielding action).fiber.id =
      f.id :=
  (Moves.withFiber_footprint interp m f yielding action).id

theorem evaluatePrim_id (interp : NInterp) (m : NativeMachine)
    (f : NFiber) (yielding : Bool) :
    (evaluatePrim interp m f yielding).fiber.id =
      f.id :=
  (Moves.evaluatePrim_footprint interp m f yielding).id

theorem exitScoped_id (p : NativeEff) (m : NativeMachine)
    (f : NFiber) (yielding : Bool) (exit : ExitV) :
    (exitScoped p m f yielding exit).fiber.id =
      f.id :=
  (Moves.exitScoped_footprint p m f yielding exit).id

theorem evaluateNative_id (p : NativeEff) (table : RowTable)
    (m : NativeMachine) (f : NFiber) (yielding : Bool) :
    (evaluateNative p m f yielding table).fiber.id =
      f.id :=
  (Moves.evaluateNative_footprint p table m f yielding).id

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
      f.id :=
  (Moves.iteration_footprint p table (interpOf p table) m f yielding).id

theorem stepFrame_exit (interp : NInterp) (m : NativeMachine)
    (f : NFiber) (yielding : Bool) :
    (evaluatePrim.stepFrame interp m f yielding).fiber.exit =
      f.exit :=
  (Moves.stepFrame_footprint interp m f yielding).exit

theorem finalizerOr_exit (interp : NInterp) (m : NativeMachine)
    (f : NFiber) (yielding : Bool) (exit : ExitV) :
    (evaluatePrim.finalizerOr interp m f yielding exit).fiber.exit =
      f.exit :=
  (Moves.finalizerOr_footprint interp m f yielding exit).exit

theorem withFiber_exit (interp : NInterp) (m : NativeMachine)
    (f : NFiber) (yielding : Bool) (action : NAction) :
    (evaluatePrim.withFiber interp m f yielding action).fiber.exit =
      f.exit :=
  (Moves.withFiber_footprint interp m f yielding action).exit

theorem evaluatePrim_exit (interp : NInterp) (m : NativeMachine)
    (f : NFiber) (yielding : Bool) :
    (evaluatePrim interp m f yielding).fiber.exit =
      f.exit :=
  (Moves.evaluatePrim_footprint interp m f yielding).exit

theorem exitScoped_exit (p : NativeEff) (m : NativeMachine)
    (f : NFiber) (yielding : Bool) (exit : ExitV) :
    (exitScoped p m f yielding exit).fiber.exit =
      f.exit :=
  (Moves.exitScoped_footprint p m f yielding exit).exit

theorem evaluateNative_exit (p : NativeEff) (table : RowTable)
    (m : NativeMachine) (f : NFiber) (yielding : Bool) :
    (evaluateNative p m f yielding table).fiber.exit =
      f.exit :=
  (Moves.evaluateNative_footprint p table m f yielding).exit

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
      f.exit :=
  (Moves.iteration_footprint p table (interpOf p table) m f yielding).exit

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
