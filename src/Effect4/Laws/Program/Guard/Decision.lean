import Effect4.Laws.Program.Guard.Driver
import Effect4.Laws.Program.Guard.OuterDriver
import Effect4.Laws.Program.Guard.AnswerDecision
import Effect4.Laws.Program.Guard.LocalDecision

set_option autoImplicit false
set_option maxRecDepth 4096
namespace Effect4.Program.Guard
open Effect4 Effect4.Machine Effect4.Program

theorem guardState_steppedBy (p : NativeEff) (table : RowTable) (fuel : Nat)
    (m : NativeMachine) (d : NativeDecision) (state : GuardState m) :
    GuardState (steppedBy p fuel table m d) := by
  letI := evaluatorFor p table
  cases d with
  | fire owner =>
      exact (Effect4.Program.Guard.OuterDriver.fireState_preserved p table (driverContract p table) fuel m owner state).state
  | flush =>
      exact (Effect4.Program.Guard.OuterDriver.flushAllState_preserved p table (driverContract p table) fuel fuel m state).state
  | evaluate target =>
      exact Effect4.Program.Guard.LocalDecision.guardState_evaluate p table (driverContract p table) fuel m target state
  | yieldVerdict target verdict =>
      exact Effect4.Program.Guard.LocalDecision.guardState_yieldVerdict p table fuel m target verdict state
  | answerAsync target offered answer =>
      exact Effect4.Program.Guard.AnswerDecision.guardState_answerAsync p table
        (driverContract p table) fuel m target offered answer state
  | interruptFrom who extra target =>
      exact Effect4.Program.Guard.LocalDecision.guardState_interruptFrom p table
        (driverContract p table) fuel m who extra target state
  | installMiddleware =>
      exact Effect4.Program.Guard.LocalDecision.guardState_installMiddleware p table fuel m state
  | advance millis =>
      exact (Effect4.Program.Guard.OuterDriver.advanceState_preserved p table
        (driverContract p table) fuel millis fuel m state).state

theorem requestOrInterrupted_steppedBy (p : NativeEff) (table : RowTable) (fuel : Nat)
    (m : NativeMachine) (d : NativeDecision) (fiber : FiberId) (token : Nat) (request : NativeOp × Val)
    (state : GuardState m) (hr : requestOf m fiber token = some request)
    (different : NotKeyAnswer fiber token d) :
    requestOf (steppedBy p fuel table m d) fiber token = some request ∨
        InterruptedAt (steppedBy p fuel table m d) fiber := by
  letI := evaluatorFor p table
  cases d with
  | fire owner =>
      exact (Effect4.Program.Guard.OuterDriver.fireState_preserved p table (driverContract p table) fuel m owner state).request fiber token request hr
  | flush =>
      exact (Effect4.Program.Guard.OuterDriver.flushAllState_preserved p table (driverContract p table) fuel fuel m state).request fiber token request hr
  | evaluate target =>
      exact Effect4.Program.Guard.LocalDecision.requestOrInterrupted_evaluate p table
        (driverContract p table) fuel m target fiber token request state hr
  | yieldVerdict target verdict =>
      exact Or.inl ((requestOf_yieldVerdict p fuel table m fiber target token verdict).trans hr)
  | answerAsync target offered answer =>
      exact Effect4.Program.Guard.AnswerDecision.requestOrInterrupted_answerAsync p table
        (driverContract p table) fuel m target fiber offered token answer request state hr
        ((notKeyAnswer_answer_iff fiber target token offered answer).mp different)
  | interruptFrom who extra target =>
      exact Effect4.Program.Guard.LocalDecision.requestOrInterrupted_interruptFrom p table
        (driverContract p table) fuel m who extra target fiber token request state hr
  | installMiddleware =>
      exact Or.inl hr
  | advance millis =>
      exact (Effect4.Program.Guard.OuterDriver.advanceState_preserved p table
        (driverContract p table) fuel millis fuel m state).request fiber token request hr

theorem guardState_executePrefix (p : NativeEff) (table : RowTable)
    (m : NativeMachine) (history : Prefix) (state : GuardState m) :
    GuardState (executePrefix p table m history) := by
  induction history generalizing m with
  | nil => exact state
  | cons entry history ih =>
    exact ih _ (guardState_steppedBy p table entry.1 m entry.2 state)

theorem guardState_reachable (p : NativeEff) (table : RowTable) (compileFuel : Nat)
    (choices : List Bool) (answers : List (Completion Val Err Defect FiberId Ann))
    (m : NativeMachine) (reachable : Reachable p table compileFuel choices answers m) : GuardState m := by
  obtain ⟨history, rfl⟩ := reachable
  exact guardState_executePrefix p table (Api.load p compileFuel choices answers) history
    (guardState_load p compileFuel choices answers)

theorem requestsOwned_reachable (p : NativeEff) (table : RowTable) (compileFuel : Nat)
    (choices : List Bool) (answers : List (Completion Val Err Defect FiberId Ann))
    (m : NativeMachine) (reachable : Reachable p table compileFuel choices answers m) : RequestsOwned m :=
  (guardState_reachable p table compileFuel choices answers m reachable).requestsOwned

end Effect4.Program.Guard
