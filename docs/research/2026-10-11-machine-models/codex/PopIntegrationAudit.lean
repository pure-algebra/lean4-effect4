import Effect4.Laws.Machine.AnswerFlowCausePop
import Test.Dogfood.Proofs.MachinePopTrace
import Test.Dogfood.Proofs.HostTimeoutFrames
import ProofGraph.AxiomAudit
#axiom_audit Effect4.Laws.Machine.PopTrace Effect4.Laws.Machine.AnswerFlowPop Effect4.Laws.Machine.AnswerFlowCausePop Test.Dogfood.Proofs.HostTimeoutFrames Test.Dogfood.Proofs.MachinePopTrace
