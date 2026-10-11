import Effect4.Laws.Machine.AnswerFlowFamily
import Effect4.Laws.Machine.AnswerFlowFamilyPop
import Effect4.Laws.Machine.AnswerFlowPop
import Effect4.Laws.Machine.AnswerFlowCausePop
import Effect4.Laws.Program.NativeFrameScope
import Test.Dogfood.Proofs.AnswerFlowFamilyReader
import ProofGraph.AxiomAudit

#axiom_audit Effect4.Laws.Machine.AnswerFlowFamily Effect4.Laws.Machine.AnswerFlowFamilyPop Effect4.Laws.Machine.AnswerFlowPop Effect4.Laws.Machine.AnswerFlowCausePop Effect4.Laws.Program.NativeFrameScope Test.Dogfood.Proofs.AnswerFlowFamilyReader
