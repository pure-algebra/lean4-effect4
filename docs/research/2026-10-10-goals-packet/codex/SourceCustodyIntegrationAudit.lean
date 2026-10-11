import Test.Dogfood.Scenario.Workers
import ProofGraph.AxiomAudit
import ProofGraph.Plan

#axiom_audit Effect4.Laws.Program.SourceOpportunityCommands Effect4.Laws.Program.SourceOpportunityHistory Test.Dogfood.Scenario.SourceOpportunity Effect4.Laws.Program.ReleaseCustody.HistoryLift Effect4.Laws.Program.ReleaseCustody.Execution Test.Dogfood.Scenario.Workers.Assertions
#plan_status Test.Dogfood.Scenario.Workers.Assertions.registrations_step
#plan_status Test.Dogfood.Scenario.Workers.Assertions.releases_step
#plan_status Test.Dogfood.Scenario.Workers.releases_once
