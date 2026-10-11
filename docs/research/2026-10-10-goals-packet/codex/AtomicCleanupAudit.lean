import Test.Dogfood.Scenario.Atomic
import ProofGraph.AxiomAudit

#axiom_audit Effect4.Laws.Program.FinalizerRun Test.Dogfood.Scenario.Atomic.Cleanup Test.Dogfood.Scenario.Atomic
#plan_status Test.Dogfood.Scenario.Atomic.cleans_once
