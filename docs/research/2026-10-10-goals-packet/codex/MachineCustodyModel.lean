import Test.Dogfood.Scenario.Workers
import Test.Dogfood.Scenario.Programs
import Effect4.Laws.Program.ReleaseCustody.Control
import ProofGraph.AxiomAudit

/-! Selected finite custody checks on the actual one-job crew.
These checks establish no whole-command preservation theorem. -/
set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 4000000
namespace MachineCustodyModel
open Effect4 Effect4.Machine Effect4.Program
open Effect4.Program.ReleaseCustody Effect4.Program.ReleaseCustody.Control
open Test.Dogfood.Scenario Test.Dogfood.Scenario.Workers
#eval show IO Unit from do
  match Api.Author.build (crew 1) with
  | .error _ => throw (IO.userError "crew refuses admission")
  | .ok b =>
    let parkedRun := Test.Dogfood.Scenario.play (Run.open b "workers" budget) parked
    let states := [("load", (Run.open b "workers" budget).machine), ("parked", parkedRun.machine)] ++
      ([1, 8, 24, 64, 1000].map fun fuel =>
        (s!"cancel-cut-{fuel}", Program.steppedBy b.program fuel b.table parkedRun.machine
          (.interruptFrom none .empty ⟨0⟩)))
    for (label, m) in states do
      for i in [1, 2] do
        let q := Test.Dogfood.Scenario.Programs.crewAcquire i
        let starts := m.trace.countP (ReleaseTrace.releaseAt q)
        let registered := m.trace.countP (ReleaseTrace.registeredAt q)
        IO.println s!"{label} worker{i}: starts={starts}, custody={machineCredits q m}, registrations={registered}"
        unless decide (starts + machineCredits q m ≤ registered) do throw (IO.userError s!"custody fails at {label}, worker {i}")
#axiom_audit Effect4.Laws.Machine.ControlWeights Effect4.Laws.Program.ReleaseCustody.Control
end MachineCustodyModel
