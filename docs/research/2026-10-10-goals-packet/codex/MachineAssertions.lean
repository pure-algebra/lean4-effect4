import Test.Dogfood.Scenario.Workers.Assertions
import Test.Dogfood.Scenario.Workers
import ProofGraph.AxiomAudit

open Effect4
namespace MachineAssertions

/-- The actual scenario observation consumes the concrete assertions, at universal total and budget. -/
theorem reader : Test.Dogfood.Scenario.Workers.ReleasesOnce := by
  intro total budget b moves hb
  have hh := Test.Dogfood.Scenario.history b "workers" budget "" moves
  have hs := Test.Dogfood.Scenario.Workers.Assertions.history
    total budget.compileFuel b hb _ hh
  exact Test.Dogfood.Scenario.Workers.Assertions.read b budget.compileFuel _ hs

#axiom_audit Test.Dogfood.Scenario.Workers.Program Test.Dogfood.Scenario.Workers.Assertions
#plan_status Test.Dogfood.Scenario.Workers.Assertions.history
end MachineAssertions
