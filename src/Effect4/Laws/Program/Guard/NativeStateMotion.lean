import Effect4.Laws.Program.Interference
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
  rw [(RunMachine.applyFiberEdits_shape _ _).1]
  change (countdownParkEdits interp m f targets resume failFast).1.nextId = m.nextId
  rw [Edits.countdown_word]
  unfold Edits.countdownWord
  cases walk : countdownWalk {m with nextToken := m.nextToken + 1} targets [] with
  | mk exits target => cases target <;> rfl

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
  dsimp only
  rw [(RunMachine.applyFiberEdits_shape _ _).1]
  change (linkScopeEdits interp m mode scope target who extra).1.nextId = m.nextId
  rw [Edits.link_plan_word]
  apply Edits.run_keeps (fun held : NativeMachine => held.nextId) _ ?_ m
  intro edit member held
  unfold Edits.linkWord at member
  repeat' split at member
  all_goals aesop (add norm simp [List.mem_cons, List.not_mem_nil, Edit.apply, RunMachine.halt, RunMachine.emit])

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
    m.nextId ≤ (evaluatePrim.withFiber interp m f yielding action).machine.nextId :=
  (Moves.withFiber_interferes interp m f yielding action).nextId

theorem evaluatePrim_nextId (interp : NInterp) (m : NativeMachine) (f : NFiber) (yielding : Bool) :
    m.nextId ≤ (evaluatePrim interp m f yielding).machine.nextId :=
  (Moves.evaluatePrim_interferes interp m f yielding).nextId

theorem exitScoped_nextId (p : NativeEff) (m : NativeMachine) (f : NFiber)
    (yielding : Bool) (exit : ExitV) :
    m.nextId ≤ (exitScoped p m f yielding exit).machine.nextId :=
  (Moves.exitScoped_interferes p m f yielding exit).nextId

theorem evaluateNative_nextId (p : NativeEff) (table : RowTable) (m : NativeMachine)
    (f : NFiber) (yielding : Bool) :
    m.nextId ≤ (evaluateNative p m f yielding table).machine.nextId :=
  (Moves.evaluateNative_interferes p table m f yielding).nextId

theorem iteration_nextId (p : NativeEff) (table : RowTable) (m : NativeMachine)
    (f : NFiber) (yielding : Bool) :
    letI := evaluatorFor p table
    m.nextId ≤ (iteration (interpOf p table) m f yielding).machine.nextId :=
  (Moves.iteration_interferes p table (interpOf p table) m f yielding).nextId

end Effect4.Program.Guard.NativeStateMotion
