import Test.Dogfood.Scenario.QueueWorkers
import ProofGraph.AxiomAudit
import ProofGraph.Plan

open Test.Dogfood.Scenario.QueueWorkers

-- Readers: each assertion assembly has the exact original universal clause proposition.
example : HeldWithinFed := held_within_fed
example : FedAccounted := fed_accounted
example : QueueSettled := queue_settled
example : ReleasesOnce := releases_once

#axiom_audit Effect4.Laws.Library.Queue.Conservation
  Test.Dogfood.Scenario.QueueWorkers.Model Test.Dogfood.Scenario.QueueWorkers.Ledger
  Test.Dogfood.Scenario.QueueWorkers.Assertions

#plan_status Test.Dogfood.Scenario.QueueWorkers.held_within_fed
#plan_status Test.Dogfood.Scenario.QueueWorkers.fed_accounted
#plan_status Test.Dogfood.Scenario.QueueWorkers.queue_settled
#plan_status Test.Dogfood.Scenario.QueueWorkers.releases_once
