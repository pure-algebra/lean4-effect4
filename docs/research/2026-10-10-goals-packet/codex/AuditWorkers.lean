import Test.Dogfood.Scenario.Workers
import ProofGraph.AxiomAudit

#axiom_audit Effect4.Laws.Program.ReleaseTrace Test.Dogfood.Scenario.Workers.Program
  Test.Dogfood.Scenario.Workers.Assertions Test.Dogfood.Scenario.Workers
#plan_status Test.Dogfood.Scenario.Workers.releases_once
