import Test.Dogfood.Scenario.QueueWorkers.Assertions
import ProofGraph.AxiomAudit
import ProofGraph.Plan

open Test.Dogfood.Scenario.QueueWorkers

-- Readers: each assertion assembly has the exact original universal clause proposition.
example : HeldWithinFed := Assertions.held_within_fed
example : FedAccounted := Assertions.fed_accounted
example : QueueSettled := Assertions.queue_settled
example : ReleasesOnce := Assertions.releases_once

#axiom_audit Effect4.Laws.Library.Queue.Conservation
  Test.Dogfood.Scenario.QueueWorkers.Model Test.Dogfood.Scenario.QueueWorkers.Ledger
  Test.Dogfood.Scenario.QueueWorkers.Assertions

#plan_status Test.Dogfood.Scenario.QueueWorkers.Assertions.held_within_fed
#plan_status Test.Dogfood.Scenario.QueueWorkers.Assertions.fed_accounted
#plan_status Test.Dogfood.Scenario.QueueWorkers.Assertions.queue_settled
#plan_status Test.Dogfood.Scenario.QueueWorkers.Assertions.releases_once
