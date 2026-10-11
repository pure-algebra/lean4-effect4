import Test.Dogfood.Scenario.Atomic
import ProofGraph.AxiomAudit

#axiom_audit Effect4.Laws.Machine.FinalizerCredits Effect4.Laws.Program.FinalizerTransfer Effect4.Laws.Program.FinalizerCommands
#plan_status Test.Dogfood.Scenario.Atomic.cleans_once
