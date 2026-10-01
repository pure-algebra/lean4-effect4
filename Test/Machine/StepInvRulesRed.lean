import Effect4.Laws.Program.Guard.ForkLedger
import Test.Api.TraceOrigin

namespace Test.Machine.StepInvRulesRed
open Effect4 Effect4.Machine Effect4.Program Effect4.Api.TraceFacts.Agreement

/--
error: Tactic `aesop` failed, made no progress
Initial goal:
  m : NativeMachine
  events : List (RunEvent EffName EffThunk Val Err Defect FiberId Ann Ctx)
  h : Ok m
  hf : NoFork events
  ⊢ Ok (RunMachine.emit m events)
-/
#guard_msgs (error) in
example (m : NativeMachine)
    (events : List (RunEvent EffName EffThunk Val Err Defect FiberId Ann Ctx))
    (h : Ok m) (hf : NoFork events) : Ok (m.emit events) := by
  aesop

#print axioms Effect4.Api.TraceFacts.Agreement.emit_with_bank
end Test.Machine.StepInvRulesRed

namespace Test.Machine.StepInvRulesRed
open Effect4 Effect4.Machine Effect4.Program

/--
error: Tactic `aesop` failed, made no progress
Initial goal:
  m : NativeMachine
  f : Guard.NFiber
  h : ForkLedger.Invariant.Ok m
  ⊢ ForkLedger.Invariant.Ok (RunMachine.update m f)
-/
#guard_msgs (error) in
example (m : NativeMachine) (f : Guard.NFiber)
    (h : Effect4.Machine.ForkLedger.Invariant.Ok m) :
    Effect4.Machine.ForkLedger.Invariant.Ok (m.update f) := by
  aesop

#print axioms Effect4.Machine.ForkLedger.Invariant.Native.update_with_bank
end Test.Machine.StepInvRulesRed
