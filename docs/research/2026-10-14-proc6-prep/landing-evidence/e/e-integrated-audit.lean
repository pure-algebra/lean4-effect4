import Effect4.Laws
import ProofGraph.AxiomAudit
import ProofGraph.Plan

#axiom_audit Effect4.Laws.Program.Agreement.HostedBlocks Effect4.Laws.Api.SessionMeaningBlocks Effect4.Laws.Program.ValidatedBlocks
#plan_status Effect4.Program.Agreement.localRunC_to_blockB
#plan_status Effect4.Program.Agreement.hostRunBlockB_exits
#plan_status Effect4.Run.h9_blocks
