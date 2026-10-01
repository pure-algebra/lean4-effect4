import Effect4.Laws.Api.TraceOrigin

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
