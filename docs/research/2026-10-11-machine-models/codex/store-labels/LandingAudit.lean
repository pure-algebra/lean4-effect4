import Effect4.Laws.Program.RefWords
import Effect4.Laws.Program.NativeHeapExecution
import Test.Dogfood.Proofs.PrimitiveProducerReader
import ProofGraph.AxiomAudit

#axiom_audit Effect4.Laws.Program.RefWords Effect4.Laws.Program.NativeHeapExecution Test.Dogfood.Proofs.PrimitiveProducerReader
