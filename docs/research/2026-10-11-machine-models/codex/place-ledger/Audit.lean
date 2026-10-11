import Effect4.Laws.Program.ReleaseCustody.NativeAccounting
import Test.Dogfood.Scenario.Atomic.WriterMachine
import ProofGraph.AxiomAudit

#axiom_audit Effect4.Laws.Machine.PlaceLedger Effect4.Laws.Program.PlaceLedgerConnect Effect4.Laws.Program.ReleaseCustody.IterationDebit Test.Dogfood.Scenario.Atomic.WriterMachine
