import Effect4.Laws.Program.Guard.NativeState

set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 1200000
namespace Effect4.Program.Guard.NativeStateMotion
open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Guard
abbrev NInterp := RunInterp EffName EffThunk Val Err Defect FiberId Ann Ctx Stores

theorem modify_nextId (m : NativeMachine) (fiber : FiberId) (update : NFiber → NFiber) :
    (m.modify fiber update).nextId = m.nextId := by
  unfold RunMachine.modify
  split <;> rfl

theorem countdown_nextId (interp : NInterp) (m : NativeMachine) (f : NFiber)
    (targets : List FiberId) (resume : Resume EffName) (failFast : Bool) :
    (countdownPark interp m f targets resume failFast).1.nextId = m.nextId := by
  unfold countdownPark
  dsimp only
  split
  · rfl
  · exact modify_nextId _ _ _

theorem forkFinalizers_nextId (interp : NInterp) (m : NativeMachine) (f : NFiber)
    (codes : List NCode) : m.nextId ≤ (forkFinalizers interp m f codes).1.nextId := by
  induction codes generalizing m with
  | nil => exact Nat.le_refl _
  | cons code rest ih =>
    exact Nat.le_trans (Nat.le_succ _) (ih (spawn interp m f code ⟨true, true, .inherit⟩).1)

theorem linkScope_nextId (interp : NInterp) (m : NativeMachine) (mode : Supervision.ScopeMode)
    (scope : Nat) (target : FiberId) (who : Option FiberId) (extra : ReasonAnnotations Ann) :
    (linkScope interp m mode scope target who extra).1.nextId = m.nextId := by
  unfold linkScope
  repeat' first | rfl | dsimp only | split
  all_goals exact modify_nextId _ _ _

theorem stepFrame_nextId (interp : NInterp) (m : NativeMachine) (f : NFiber) (yielding : Bool) :
    (evaluatePrim.stepFrame interp m f yielding).machine.nextId = m.nextId := by
  unfold evaluatePrim.stepFrame evaluatePrim.finishFrame
  dsimp only
  split <;> rfl

theorem finalizerOr_nextId (interp : NInterp) (m : NativeMachine) (f : NFiber)
    (yielding : Bool) (exit : ExitV) :
    (evaluatePrim.finalizerOr interp m f yielding exit).machine.nextId = m.nextId := by
  unfold evaluatePrim.finalizerOr
  repeat' first | rfl | exact stepFrame_nextId _ _ _ _ | dsimp only | split

theorem withFiber_nextId (interp : NInterp) (m : NativeMachine) (f : NFiber)
    (yielding : Bool) (action : NAction) :
    m.nextId ≤ (evaluatePrim.withFiber interp m f yielding action).machine.nextId := by
  cases action <;> simp only [evaluatePrim.withFiber, evaluatePrim.interruptAs, spawn, start, beginRace]
  all_goals repeat' first
    | exact Nat.le_refl _
    | exact Nat.le_succ _
    | exact forkFinalizers_nextId _ _ _ _
    | solve | apply Nat.le_of_eq; exact (countdown_nextId _ _ _ _ _ _).symm
    | solve | apply Nat.le_of_eq; exact (linkScope_nextId _ _ _ _ _ _ _).symm
    | dsimp only
    | split
  all_goals try simp_all

theorem evaluatePrim_nextId (interp : NInterp) (m : NativeMachine) (f : NFiber) (yielding : Bool) :
    m.nextId ≤ (evaluatePrim interp m f yielding).machine.nextId := by
  simp only [evaluatePrim, registerRace]
  repeat' first
    | exact Nat.le_refl _
    | exact withFiber_nextId _ _ _ _ _
    | solve | apply Nat.le_of_eq; exact (stepFrame_nextId _ _ _ _).symm
    | solve | apply Nat.le_of_eq; exact (finalizerOr_nextId _ _ _ _ _).symm
    | solve | apply Nat.le_of_eq; exact (countdown_nextId _ _ _ _ _ _).symm
    | dsimp only
    | split

theorem exitScoped_nextId (p : NativeEff) (m : NativeMachine) (f : NFiber)
    (yielding : Bool) (exit : ExitV) :
    m.nextId ≤ (exitScoped p m f yielding exit).machine.nextId := by
  unfold exitScoped
  repeat' first | exact Nat.le_refl _ | exact evaluatePrim_nextId _ _ _ _ | dsimp only | split

theorem evaluateNative_nextId (p : NativeEff) (table : RowTable) (m : NativeMachine)
    (f : NFiber) (yielding : Bool) :
    m.nextId ≤ (evaluateNative p m f yielding table).machine.nextId := by
  unfold evaluateNative
  repeat' first
    | exact Nat.le_refl _
    | exact evaluatePrim_nextId _ _ _ _
    | exact exitScoped_nextId _ _ _ _ _
    | dsimp only
    | split

theorem iteration_nextId (p : NativeEff) (table : RowTable) (m : NativeMachine)
    (f : NFiber) (yielding : Bool) :
    letI := evaluatorFor p table
    m.nextId ≤ (iteration (interpOf p table) m f yielding).machine.nextId := by
  letI := evaluatorFor p table
  unfold iteration
  dsimp only
  cases hy : injectYield m (countOp (runloopTop f)) yielding with
  | none => exact evaluateNative_nextId _ _ _ _ _
  | some it =>
    unfold injectYield at hy
    split at hy
    · cases hy
      exact evaluateNative_nextId p table (m.emit _) _ _
    · cases hy

end Effect4.Program.Guard.NativeStateMotion
