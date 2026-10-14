import Effect4.Laws.Program.DenoteCtl
import Effect4.Laws.Api.SessionMeaningBlocks
import Effect4.Laws.Run.CallTree
import Test.Dogfood.Scenario.Workers
import Test.Dogfood.Scenario.QueueWorkers
import Test.Dogfood.Scenario.Timeout
import Test.Dogfood.Scenario.Atomic
import Effect4.Laws.Program.FinalizerRun
import ProofGraph.Plan
import ProofGraph.AxiomAudit

#plan_status Test.Dogfood.Scenario.Workers.Assertions.logs_step
  Test.Dogfood.Scenario.QueueWorkers.Assertions.logs_history
  Test.Dogfood.Scenario.Timeout.cleanup_keeps
  Test.Dogfood.Scenario.Timeout.retries_declared
  Test.Dogfood.Scenario.QueueWorkers.Assertions.jobs_step
  Test.Dogfood.Scenario.QueueWorkers.Assertions.rest_step
  Test.Dogfood.Scenario.Atomic.Store.shop_stages
  Effect4.Program.FinalizerRun.once_placed_outside_census

#plan_status Test.Dogfood.Scenario.Workers.workers
  Test.Dogfood.Scenario.QueueWorkers.queueWorkers
  Test.Dogfood.Scenario.Timeout.timeout
  Test.Dogfood.Scenario.Atomic.atomic
  Effect4.Run.CallTree.bound_in_tree
  Effect4.Run.h9_blocks

#axiom_audit Effect4.Laws.Program.DenoteCtl Effect4.Laws.Program.BlockMeaning
  Effect4.Laws.Api.SessionMeaningBlocks Effect4.Laws.Run.CallTree
