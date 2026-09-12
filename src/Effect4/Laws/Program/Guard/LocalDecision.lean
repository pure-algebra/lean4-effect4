import Effect4.Laws.Program.Guard.AnswerDecision

set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 800000
namespace Effect4.Program.Guard.LocalDecision
open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Guard
open Effect4.Program.Guard.RegistrationQueue Effect4.Program.Guard.AnswerDecision

theorem guardQueue_evaluate_drainDue (p : NativeEff) (table : RowTable)
    (m : NativeMachine) (target : FiberId) : GuardQueue p table m [.evaluate target, .drainDue] :=
  guardQueue_cons_evaluate p table target (guardQueue_drainDue p table m)

theorem guardState_evaluate (p : NativeEff) (table : RowTable)
    (driver : DriverContract p table) (fuel : Nat) (m : NativeMachine)
    (target : FiberId) (state : GuardState m) :
    GuardState (steppedBy p fuel table m (.evaluate target)) :=
  (driver.invariant fuel m [.evaluate target, .drainDue] state
    (guardQueue_evaluate_drainDue p table m target) ⟨True.intro, True.intro, True.intro⟩).1

theorem requestOrInterrupted_evaluate (p : NativeEff) (table : RowTable)
    (driver : DriverContract p table) (fuel : Nat) (m : NativeMachine)
    (target fiber : FiberId) (token : Nat) (request : NativeOp × Val)
    (state : GuardState m) (hr : requestOf m fiber token = some request) :
    requestOf (steppedBy p fuel table m (.evaluate target)) fiber token = some request ∨
      InterruptedAt (steppedBy p fuel table m (.evaluate target)) fiber :=
  driver.request fuel m [.evaluate target, .drainDue] fiber token request state
    (guardQueue_evaluate_drainDue p table m target) ⟨True.intro, True.intro, True.intro⟩ hr

theorem guardState_yieldVerdict (p : NativeEff) (table : RowTable)
    (fuel : Nat) (m : NativeMachine) (target : FiberId) (verdict : Bool)
    (state : GuardState m) : GuardState (steppedBy p fuel table m (.yieldVerdict target verdict)) := by
  apply guardState_modify_view state target (fun f => { f with yieldOverride := some verdict })
  · intro f hf
    have valid := guardState_fiber (f := f) state hf
    exact ⟨valid.below, valid.pending, valid.idle, valid.parkedBelow, valid.exited,
      valid.deferredCause, valid.codes, valid.tasks⟩
  · intro f; exact ⟨rfl, rfl, rfl⟩
  · intro f; rfl

theorem guardState_installMiddleware (p : NativeEff) (table : RowTable)
    (fuel : Nat) (m : NativeMachine) (state : GuardState m) :
    GuardState (steppedBy p fuel table m .installMiddleware) := by
  cases state
  constructor <;> assumption

theorem guardState_interrupted_emit (p : NativeEff) (table : RowTable)
    (m : NativeMachine) (f : NFiber) (who : Option FiberId) (extra : ReasonAnnotations Ann)
    (events : List (RunEvent EffName EffThunk Val Err Defect FiberId Ann Ctx))
    (state : GuardState m) (lookup : m.fiber? f.id = some f) :
    GuardState ((m.emit events).update (interruptRecord (interpOf p table) who extra f).1) := by
  exact guardState_emit (guardState_interruptRecord p table state lookup who extra) events

theorem requestOrInterrupted_interrupted_emit (p : NativeEff) (table : RowTable)
    (m : NativeMachine) (target : FiberId) (f : NFiber) (who : Option FiberId)
    (extra : ReasonAnnotations Ann) (events : List (RunEvent EffName EffThunk Val Err Defect FiberId Ann Ctx))
    (fiber : FiberId) (token : Nat) (request : NativeOp × Val)
    (lookup : m.fiber? target = some f) (hr : requestOf m fiber token = some request) :
    let after := (m.emit events).update (interruptRecord (interpOf p table) who extra f).1
    requestOf after fiber token = some request ∨ InterruptedAt after fiber := by
  have check := requestOrInterrupted_driveStep_interruptTarget p table m target who extra [] fiber token request hr
  simp only [driveStep, lookup] at check
  simpa only [requestOf, InterruptedAt, RunMachine.emit, RunMachine.update, RunMachine.fiber?] using check


def interruptBeforeLoop (p : NativeEff) (table : RowTable) (m : NativeMachine)
    (target : FiberId) (f : NFiber) (who : Option FiberId) (extra : ReasonAnnotations Ann) : NativeMachine :=
  let g := (interruptRecord (interpOf p table) who extra f).1
  let logged := m.emit [RunEvent.interruptRecorded who target]
  let logged := if g.frame.deferredInterrupt && g.running then
    logged.emit [RunEvent.interruptDeferred target] else logged
  logged.update g

theorem guardState_interruptBeforeLoop (p : NativeEff) (table : RowTable) (m : NativeMachine)
    (target : FiberId) (f : NFiber) (who : Option FiberId) (extra : ReasonAnnotations Ann)
    (state : GuardState m) (lookup : m.fiber? f.id = some f) :
    GuardState (interruptBeforeLoop p table m target f who extra) := by
  unfold interruptBeforeLoop
  dsimp only
  split
  · exact guardState_interrupted_emit p table (m.emit [RunEvent.interruptRecorded who target])
      f who extra [RunEvent.interruptDeferred target] (guardState_emit state _) lookup
  · exact guardState_interrupted_emit p table m f who extra [RunEvent.interruptRecorded who target] state lookup

theorem requestOrInterrupted_interruptBeforeLoop (p : NativeEff) (table : RowTable) (m : NativeMachine)
    (target : FiberId) (f : NFiber) (who : Option FiberId) (extra : ReasonAnnotations Ann)
    (fiber : FiberId) (token : Nat) (request : NativeOp × Val)
    (lookup : m.fiber? target = some f) (hr : requestOf m fiber token = some request) :
    requestOf (interruptBeforeLoop p table m target f who extra) fiber token = some request ∨
      InterruptedAt (interruptBeforeLoop p table m target f who extra) fiber := by
  unfold interruptBeforeLoop
  dsimp only
  split
  · exact requestOrInterrupted_interrupted_emit p table (m.emit [RunEvent.interruptRecorded who target])
      target f who extra [RunEvent.interruptDeferred target] fiber token request lookup hr
  · exact requestOrInterrupted_interrupted_emit p table m target f who extra
      [RunEvent.interruptRecorded who target] fiber token request lookup hr

theorem interruptFrom_eq (p : NativeEff) (table : RowTable) (fuel : Nat) (m : NativeMachine)
    (target : FiberId) (f : NFiber) (who : Option FiberId) (extra : ReasonAnnotations Ann)
    (lookup : m.fiber? target = some f) :
    letI := evaluatorFor p table
    steppedBy p fuel table m (.interruptFrom who extra target) =
      if (interruptRecord (interpOf p table) who extra f).2 then
        (driveState (interpOf p table) fuel (interruptBeforeLoop p table m target f who extra)
          [.evaluate target, .drainDue]).1
      else interruptBeforeLoop p table m target f who extra := by
  letI := evaluatorFor p table
  simp only [steppedBy, stepDecision, stepDecisionState, lookup, interruptBeforeLoop,
    stepDecisionState.loop, FiberCore.deferredInterrupt]
  split <;> rfl

theorem guardState_interruptFrom (p : NativeEff) (table : RowTable)
    (driver : DriverContract p table) (fuel : Nat) (m : NativeMachine)
    (who : Option FiberId) (extra : ReasonAnnotations Ann) (target : FiberId) (state : GuardState m) :
    GuardState (steppedBy p fuel table m (.interruptFrom who extra target)) := by
  letI := evaluatorFor p table
  cases lookup : m.fiber? target with
  | none => simpa only [steppedBy, stepDecision, stepDecisionState, lookup] using state
  | some f =>
    have saved : m.fiber? f.id = some f := by simpa only [fiber_id_of_lookup lookup] using lookup
    have before := guardState_interruptBeforeLoop p table m target f who extra state saved
    rw [interruptFrom_eq p table fuel m target f who extra lookup]
    split
    · exact (driver.invariant fuel _ _ before
        (guardQueue_evaluate_drainDue p table _ target) ⟨True.intro, True.intro, True.intro⟩).1
    · exact before

theorem requestOrInterrupted_interruptFrom (p : NativeEff) (table : RowTable)
    (driver : DriverContract p table) (fuel : Nat) (m : NativeMachine)
    (who : Option FiberId) (extra : ReasonAnnotations Ann) (target fiber : FiberId)
    (token : Nat) (request : NativeOp × Val) (state : GuardState m)
    (hr : requestOf m fiber token = some request) :
    requestOf (steppedBy p fuel table m (.interruptFrom who extra target)) fiber token = some request ∨
      InterruptedAt (steppedBy p fuel table m (.interruptFrom who extra target)) fiber := by
  letI := evaluatorFor p table
  cases lookup : m.fiber? target with
  | none => exact Or.inl (by simpa only [steppedBy, stepDecision, stepDecisionState, lookup] using hr)
  | some f =>
    have saved : m.fiber? f.id = some f := by simpa only [fiber_id_of_lookup lookup] using lookup
    have stateBefore := guardState_interruptBeforeLoop p table m target f who extra state saved
    have requestBefore := requestOrInterrupted_interruptBeforeLoop p table m target f who extra
      fiber token request lookup hr
    rw [interruptFrom_eq p table fuel m target f who extra lookup]
    split
    · rcases requestBefore with same | interrupted
      · exact driver.request fuel _ _ fiber token request stateBefore
          (guardQueue_evaluate_drainDue p table _ target) ⟨True.intro, True.intro, True.intro⟩ same
      · exact Or.inr (driver.interrupted fuel _ _ fiber stateBefore
          (guardQueue_evaluate_drainDue p table _ target) ⟨True.intro, True.intro, True.intro⟩ interrupted)
    · exact requestBefore

end Effect4.Program.Guard.LocalDecision
