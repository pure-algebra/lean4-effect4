import Test.Dogfood.Scenario.Atomic
import ProofGraph.AxiomAudit

#axiom_audit Effect4.Laws.Machine.FinalizerRun Effect4.Laws.Machine.FinalizerBookkeeping Effect4.Laws.Machine.FinalizerEvaluation Effect4.Laws.Program.FinalizerTransfer Effect4.Laws.Program.FinalizerCommands Effect4.Laws.Program.FinalizerRun Test.Dogfood.Scenario.Atomic.Cleanup Test.Dogfood.Scenario.Atomic
#plan_status Effect4.Program.FinalizerRun.funded_reachable
#plan_status Test.Dogfood.Scenario.Atomic.cleans_once
