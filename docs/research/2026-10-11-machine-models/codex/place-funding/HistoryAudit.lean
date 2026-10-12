import Effect4.Laws.Program.LedgerFinalizer
import Effect4.Laws.Program.SourceOpportunityHistory
import Test.Dogfood.Scenario.Atomic.WriterMachine
import ProofGraph.AxiomAudit
#axiom_audit Effect4.Laws.Machine.LiftMachineFact Effect4.Laws.Program.PlaceFunding.History Effect4.Laws.Program.LedgerRun Effect4.Laws.Program.SourceOpportunityHistory Effect4.Laws.Program.LedgerFinalizer Effect4.Laws.Program.PlaceFunding.Primitive Effect4.Laws.Program.SourceOpportunityPrimitive Test.Dogfood.Scenario.Atomic.WriterMachine Effect4.Laws.Program.NativeConfiguration
