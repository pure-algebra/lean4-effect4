import Effect4.Laws.Machine.Edits
import Effect4.Laws.Machine.EditWords
import Effect4.Laws.Machine.Ledger
import Effect4.Laws.Machine.FiberSumMessages
import Test.Machine.EditFields
import ProofGraph.AxiomAudit
#axiom_audit Effect4.Machine.Fibers Effect4.Laws.Machine.Edit Effect4.Laws.Machine.Keeps Effect4.Laws.Machine.Edits Effect4.Laws.Machine.EditWords Effect4.Laws.Machine.Ledger Effect4.Laws.Machine.FiberSumMessages Test.Machine.EditFields
