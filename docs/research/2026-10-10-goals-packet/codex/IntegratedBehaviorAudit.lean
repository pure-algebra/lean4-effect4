import Effect4.Laws.Program.ReleaseCustody.Execution
import Test.Dogfood.Proofs.HostTimeoutSource
import ProofGraph.AxiomAudit

#axiom_audit Effect4.Laws.Program.ReleaseCustody.Control Effect4.Laws.Program.ReleaseCustody.Execution
#axiom_audit Test.Dogfood.Proofs.HostPayloads Test.Dogfood.Proofs.HostTimeoutSource
