import Effect4.Store.Domain.Cas
import Effect4.Store.Domain.Word
import Effect4.Store.Domain.Traits
import Effect4.Store.Domain.Genesis
import Test.Store.SeamsAdmission
import Test.Store.SeamsRead
import Test.Store.ProgramContent
import ProofGraph.AxiomAudit

#axiom_audit Effect4.Store.Carrier.Kind Effect4.Store.Domain.Node Effect4.Store.Domain.NodeRead Effect4.Store.Domain.Read Effect4.Store.Domain.Transaction Effect4.Store.Domain.Cas Effect4.Store.Domain.Store Effect4.Store.Domain.Word Effect4.Store.Domain.Traits Test.Store.SeamsAdmission Test.Store.SeamsRead Test.Store.ProgramContent
