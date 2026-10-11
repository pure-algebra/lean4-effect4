import Test.Dogfood.Proofs.HostTimeoutNumberState
import Effect4.Laws.Program.HeapSites
import ProofGraph.AxiomAudit
#axiom_audit Effect4.Laws.Program.StoreExecution Effect4.Laws.Program.NativeHeapExecution Test.Dogfood.Proofs.HostTimeoutNumberState
