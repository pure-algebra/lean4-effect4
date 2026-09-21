import Effect4.Laws.Program.Simulation.Actions
import Effect4.Laws.Program.Simulation.Pending
import Effect4.Laws.Program.Intro.Weight
open Lean Elab Command Meta
/-- For each obligation, print its binder count against its theorem's. -/
def binderCount (n : Name) : MetaM Nat := do
  let ci ← getConstInfo n
  forallTelescope ci.type fun xs _ => pure xs.size
run_cmd liftTermElabM do
  let pairs : List (Name × Name) := [
    (`Effect4.Program.Sched.M1Origin.fork_rel, `Effect4.Program.Sched.fork_rel),
    (`Effect4.Program.Sched.M1Origin.forkIn_rel, `Effect4.Program.Sched.forkIn_rel),
    (`Effect4.Program.Sched.M1Origin.raceAll_rel, `Effect4.Program.Sched.raceAll_rel),
    (`Effect4.Program.Sched.M1Origin.actionAt_fork, `Effect4.Program.Sched.actionAt_fork),
    (`Effect4.Program.Sched.M1Origin.actionAt_forkIn, `Effect4.Program.Sched.actionAt_forkIn),
    (`Effect4.Program.Sched.M1Origin.actionAt_not_forkScoped, `Effect4.Program.Sched.actionAt_not_forkScoped),
    (`Effect4.Program.Sched.M1Origin.actionAt_raceAll, `Effect4.Program.Sched.actionAt_raceAll)]
  for (o, t) in pairs do
    let a ← binderCount o
    let b ← (do try binderCount t catch _ => pure 0)
    logInfo m!"{o}: obligation binders {a}, theorem binders {b}"
#check @Effect4.Program.Sched.M1Origin.fork_rel
#check @Effect4.Program.Sched.fork_rel
