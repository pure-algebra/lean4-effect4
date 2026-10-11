import Effect4.Laws.Program.FiberSumConnect
import Effect4.Laws.Machine.AnswerFlowCausePop
import Effect4.Laws.Program.Typed.HostWalk
import Test.Machine.AnswerFlowLoop
import Test.Dogfood.Proofs.HostTimeoutFrames
import ProofGraph.AxiomAudit

#axiom_audit Effect4.Laws.Machine.FiberSum Effect4.Laws.Program.FiberSumConnect Effect4.Laws.Contracts.FramePath Effect4.Laws.Machine.PopTraceFamily Effect4.Laws.Machine.AnswerFlow Effect4.Laws.Machine.AnswerFlowFrames Effect4.Laws.Machine.AnswerFlowHooks Effect4.Laws.Machine.AnswerFlowPop Effect4.Laws.Machine.AnswerFlowCausePop Effect4.Laws.Program.Typed.Contracts Test.Dogfood.Proofs.HostTimeoutFrames Test.Machine.AnswerFlowLoop
