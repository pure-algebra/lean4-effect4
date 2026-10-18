import Test.Store.SeamsTransactions
import Effect4.Store.Domain.Word
import Test.Store.WordContract
import Test.Store.SeamsHeadPrinter
import ProofGraph.AxiomAudit
#axiom_audit Effect4.Store.Domain.Transaction Effect4.Store.Domain.Store Effect4.Store.Domain.Word Effect4.Store.Domain.Cas Test.Store.SeamsTransactions Test.Store.WordContract Test.Store.SeamsHeadPrinter
