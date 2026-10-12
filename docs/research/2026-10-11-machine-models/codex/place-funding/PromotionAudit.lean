import Effect4.Laws.Program.LedgerFinalizer
import Effect4.Laws.Program.PlaceFunding.Commands
import ProofGraph.AxiomAudit
#axiom_audit Effect4.Laws.Machine.PlaceLedgerBalance Effect4.Laws.Program.PlaceFunding.Control Effect4.Laws.Program.PlaceFunding.Transfer Effect4.Laws.Program.PlaceFunding.Commands Effect4.Laws.Machine.EditWords Effect4.Laws.Machine.Ledger Effect4.Laws.Program.LedgerRun Effect4.Laws.Program.LedgerFinalizer
