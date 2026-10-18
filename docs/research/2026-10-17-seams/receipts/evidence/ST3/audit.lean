import Effect4.Laws.Store.Results
import Effect4.Schema.OfShape
import Effect4.Store.Domain.Action
import Effect4.Store.Domain.Cas
import Effect4.Store.Domain.Derived.Value
import Effect4.Store.Domain.Document
import Effect4.Store.Domain.Genesis
import Effect4.Store.Domain.Shape
import Effect4.Store.Domain.Store
import Effect4.Store.Domain.Word
import Test.Store.SeamsResults
import ProofGraph.AxiomAudit
#axiom_audit Effect4.Laws.Store.Results Effect4.Schema.OfShape Effect4.Store.Domain.Action Effect4.Store.Domain.Cas Effect4.Store.Domain.Derived.Value Effect4.Store.Domain.Document Effect4.Store.Domain.Genesis Effect4.Store.Domain.Shape Effect4.Store.Domain.Store Effect4.Store.Domain.Word Test.Store.SeamsResults
