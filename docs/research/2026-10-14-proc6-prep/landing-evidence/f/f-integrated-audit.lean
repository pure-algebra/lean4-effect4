import Effect4.Laws
import Test.Dogfood.Proofs.HostRouting
import Test.Program.AgreementContract
import ProofGraph.AxiomAudit
import ProofGraph.Plan

#axiom_audit Effect4.Laws.Program.BlockMeaning Effect4.Laws.Program.FragmentBlock Effect4.Laws.Program.Agreement.Machine Effect4.Laws.Program.Agreement.Segment Effect4.Laws.Program.Agreement.ContextSegment Effect4.Laws.Program.Agreement.ContextSteps Effect4.Laws.Program.Agreement.BlockPlain Effect4.Laws.Program.Agreement.Calls Effect4.Laws.Program.Agreement.LoopCalls Effect4.Laws.Program.Agreement.Blocks Effect4.Laws.Program.Agreement.Hosted Effect4.Laws.Program.Agreement.HostedLoop Effect4.Laws.Program.Agreement.HostedBlocks Effect4.Laws.Api.SessionMeaning Effect4.Laws.Api.SessionMeaningLoop Effect4.Laws.Api.SessionMeaningBlocks Effect4.Laws.Program.ValidatedBlocks Effect4.Laws.Run.CallTree Test.Dogfood.Proofs.HostRouting Test.Program.AgreementContract

#plan_status Effect4.Program.Agreement.contextStep_plain
#plan_status Effect4.Program.Agreement.drive_seg_receipt
#plan_status Effect4.Program.Agreement.compilesBlk
#plan_status Effect4.Program.Agreement.localRunC_to_blockB
#plan_status Effect4.Program.Agreement.hostRunBlockB_exits
#plan_status Effect4.Run.h9_blocks
