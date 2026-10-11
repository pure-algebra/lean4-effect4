import Test.Dogfood.Scenario.Atomic
import ProofGraph.AxiomAudit

#axiom_audit Effect4.Laws.Program.HeapSites Test.Dogfood.Scenario.Atomic.Model
  Test.Dogfood.Scenario.Atomic.Store Test.Dogfood.Scenario.Atomic
#plan_status Test.Dogfood.Scenario.Atomic.bounded Test.Dogfood.Scenario.Atomic.counted
  Test.Dogfood.Scenario.Atomic.committed Test.Dogfood.Scenario.Atomic.cleans_once
