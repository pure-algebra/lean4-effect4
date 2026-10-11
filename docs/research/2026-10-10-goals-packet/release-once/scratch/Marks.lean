import Test.Dogfood.Scenario.Workers
import Test.Dogfood.Scenario.QueueWorkers
import Test.Dogfood.Scenario.Atomic
import Test.Dogfood.Scenario.Timeout

/-! Scratch: the trace marks of registrations and finalizer starts on the scenarios' named runs.
A finite probe: it reads what the machine's trace records, run by run. -/

set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 0

open Effect4 Effect4.Machine Effect4.Program Test.Dogfood.Scenario

namespace Scratch.Marks

/-- The node path a pushed frame marks, for the frames that mark a registration or a start. -/
def markOf : NCode → Option (String × List Nat)
  | .onExit _ (.fin p) _ => some ("onExit-push", p.path)
  | .onSuccess _ (.afterScopeAdd _ (.foreign c)) => some ("register-push", c.path)
  | .onSuccess _ (.releaseUnder p _ _) => some ("release-start", p.path)
  | .onSuccess _ (.acquireCtx p) => some ("acquire-entry", p.path)
  | _ => none

/-- The marks of a machine's trace: fiber, kind, path. -/
def marks (m : Api.Machine) : List (Nat × String × List Nat) :=
  m.trace.filterMap fun
    | .frame f (.pushed fr) => (markOf fr).map fun (k, q) => (f.value, k, q)
    | .finalizerProgram f (.fin p) _ => some (f.value, "fin-start", p.path)
    | .frame f (.ranFinalizer (.fin p) _) => some (f.value, "fin-pure", p.path)
    | _ => none

/-- Each distinct mark with its count. -/
def tally (xs : List (Nat × String × List Nat)) : List ((Nat × String × List Nat) × Nat) :=
  xs.foldl (fun acc x =>
    if acc.any (·.1 == x) then acc.map (fun e => if e.1 == x then (e.1, e.2 + 1) else e)
    else acc ++ [(x, 1)]) []

/-- The run of a named run, with its marks tallied and the trace's length. -/
def report (run : NamedRun) : String :=
  let s := run.played
  s!"{run.name}: trace {s.machine.trace.length}, marks {tally (marks s.machine)}"

#eval (Workers.runsAndControls.1.take 18).map report
#eval (QueueWorkers.runsAndControls.1.filter (fun r => r.name == "closed" ||
  r.name == "cancelled-waiting-closed" || r.name == "twice" || r.name == "dropped")).map report
#eval Atomic.runsAndControls.1.map report
#eval Timeout.runsAndControls.1.map report

end Scratch.Marks
