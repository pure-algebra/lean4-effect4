import Test.Dogfood.Scenario.Atomic
import Effect4.Laws.Program.LedgerFinalizer
import ProofGraph.AxiomAudit

#axiom_audit Effect4.Laws.Machine.Ledger Effect4.Laws.Machine.FinalizerBookkeeping Effect4.Laws.Program.FinalizerTransfer Effect4.Laws.Program.FinalizerCommands Effect4.Laws.Program.FinalizerRun Effect4.Laws.Program.LedgerRun Effect4.Laws.Program.LedgerFinalizer
#plan_status Test.Dogfood.Scenario.Atomic.cleans_once
