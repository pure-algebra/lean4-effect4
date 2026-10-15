import Test.Dogfood.Scenario.QueueWorkers

/-!
Concept: translation-simulation R10, the boundary control of QueueWorkers `Assertions.jobs_step`.
Question: the original fed observation omits an admitted delayed reference read.
Reach: the actual crew with two jobs, its count reference and one six-move host session.
Limit: this finite control establishes no conservation theorem for a corrected observation.
Consumer: correction of the job observation or of its external-reply profile.
-/
set_option autoImplicit false
set_option maxRecDepth 1000000
set_option maxHeartbeats 16000000
namespace Test.Dogfood.Scenario.QueueWorkers.RefReplyControl
open Effect4 Effect4.Machine Effect4.Program
open Accounting

/-- The count cell initially contains zero, an admitted Nat reply for Jobs.take. -/
def moves : List Move := parked ++ [.receive feederCall (.ofRefGet ⟨4⟩), .apply feederCall, .flush]

/-- The actual built session plays the delayed reference-read completion. -/
def run : Option Run := (Test.Dogfood.P3WorkerQueue.built? (crew 2)).map fun b => Scenario.play (opened b) moves

/-- A conserving job ledger with no fed entries can show no held jobs. -/
theorem jobs_empty_fed (s : Run) (jobs : Assertions.RawJobs s) (empty : (observe s).fed = []) :
    (observe s).held = [] := by
  obtain ⟨ledger, shows, conserved⟩ := jobs
  have no_fed : ledger.fed = [] := List.map_eq_nil_iff.mp (shows.fed.symm.trans empty)
  have lengths := conserved.length_eq
  change ledger.fed.length = (ledger.heldJobs ++ ledger.custody ++ ledger.lost).length at lengths
  rw [no_fed, List.length_nil, List.length_append, List.length_append] at lengths
  have no_held : ledger.heldJobs = [] := List.eq_nil_of_length_eq_zero (by omega)
  rw [held_of_shows shows, no_held]
  rfl

/-- The actual admitted and funded run holds job zero while its original fed observation is empty. -/
theorem data : run.map (fun s => ((observe s).fed, (observe s).held, funded s)) =
    some ([], [.nat 0], true) := by
  kernel_rfl
/-- The actual delayed-reference session lies outside the terminal-reply profile. -/
theorem outside_profile : run.map terminalRepliesCheck = some false := by
  kernel_rfl

/-- A resumed delayed reference completion still contains unexecuted code in the trace. -/
def delayedResume : RunEvent EffName EffThunk Val Err Defect FiberId Ann Ctx → Bool
  | .resumedWith _ _ (.sync (.store (.op (.refGet cell)))) => decide (cell = ⟨4⟩)
  | _ => false

/-- The actual trace records the delayed read program before its synchronous value is known. -/
theorem resumed_delayed : run.map (fun s => s.machine.trace.any delayedResume) = some true := by
  kernel_rfl

/-- The admitted funded session refutes the original conserving-ledger assertion. -/
theorem refutes : ∃ s : Run, run = some s ∧ funded s = true ∧ ¬ Assertions.RawJobs s := by
  have measured := data
  cases selected : run with
  | none => rw [selected] at measured; cases measured
  | some s =>
    rw [selected] at measured
    have triple := Option.some.inj measured
    have no_fed := congrArg (fun value : List Val × List Val × Bool => value.1) triple
    have held := congrArg (fun value : List Val × List Val × Bool => value.2.1) triple
    have enough := congrArg (fun value : List Val × List Val × Bool => value.2.2) triple
    refine ⟨s, rfl, enough, ?_⟩
    intro jobs
    have impossible : [Val.nat 0] = [] := held.symm.trans (jobs_empty_fed s jobs no_fed)
    exact List.cons_ne_nil _ _ impossible
end Test.Dogfood.Scenario.QueueWorkers.RefReplyControl
