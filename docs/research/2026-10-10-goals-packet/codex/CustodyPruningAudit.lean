import Test.Dogfood.Scenario.Workers
import Test.Dogfood.Scenario.Atomic
import Test.Program.CommandDebit
import ProofGraph.AxiomAudit
import ProofGraph.Plan

#axiom_audit Effect4.Laws.Machine.ControlWeights Effect4.Laws.Program.ReleaseCustody.Control Effect4.Laws.Program.ReleaseCustody.Execution Test.Program.CommandDebit Test.Dogfood.Scenario.Workers.Assertions Test.Dogfood.Scenario.Atomic.Cleanup
#plan_status Test.Dogfood.Scenario.Atomic.cleans_once
#plan_status Test.Dogfood.Scenario.Workers.releases_once
