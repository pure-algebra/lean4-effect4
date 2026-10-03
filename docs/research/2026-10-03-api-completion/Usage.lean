import Effect4
import Effect4.Laws.Program.Author
import Effect4.Laws.Run
import Effect4.Laws.Program.MeaningEq
import Effect4.Laws.Program.ReasonsR

open Effect4

def editProgram (b : Api.Built) (path : List Nat)
    (replacement : Api.Program) :
    Option (Except Api.BuildRefusal Api.Built) := do
  let node ← (Program.Node.eff b.program).replaceAt path (.eff replacement)
  let candidate ← node.eff?
  pure (b.rebuild candidate)

#check Effect4.Program.Authoring.rebuild_spec
#check Effect4.Program.Authoring.rebuild_self
#check Effect4.Run.nextControl_spec
#check Effect4.Run.controlOnce_journal
#check Effect4.Run.play_controls_eq_replay
#check Effect4.Run.runClock_eq_run
#check Effect4.Program.Denote.StraightEq.run_agrees_at_bound

#print axioms Effect4.Program.Sched.hasRunnable_eq_ref
#print axioms Effect4.Program.Sched.reasons_eq_ref
