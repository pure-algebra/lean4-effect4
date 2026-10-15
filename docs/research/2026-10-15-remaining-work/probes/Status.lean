import Test.Dogfood.Scenario.Timeout
import Test.Dogfood.Scenario.QueueWorkers
import Test.Dogfood.Scenario.Atomic
import Test.Dogfood.Scenario.Workers
import Effect4.Laws.Program.FinalizerRun
import ProofGraph.Plan

/-!
# Status of the six open goals at the integrated head

A measurement, not a proof: `#plan_status` reads each node's proof and reports its status and the
planned goals it rests on. The six goals of the remaining-work note and their scenario claims.
-/

#plan_status Test.Dogfood.Scenario.Timeout.cleanup_keeps Test.Dogfood.Scenario.Timeout.retries_declared Test.Dogfood.Scenario.QueueWorkers.Assertions.jobs_step Test.Dogfood.Scenario.QueueWorkers.Assertions.rest_step Test.Dogfood.Scenario.Atomic.Store.shop_stages Effect4.Program.FinalizerRun.once_placed_outside_census

#plan_status Test.Dogfood.Scenario.Timeout.timeout Test.Dogfood.Scenario.QueueWorkers.queueWorkers Test.Dogfood.Scenario.Atomic.atomic Test.Dogfood.Scenario.Workers.workers Effect4.Program.FinalizerRun.once_placed_pushes_once Test.Dogfood.Scenario.Workers.Assertions.logs_step Test.Dogfood.Scenario.QueueWorkers.Assertions.logs_history
