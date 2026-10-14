import Effect4.Laws.Program.ValidatedBlocks
import ProofGraph.AxiomAudit
import ProofGraph.Plan

#axiom_audit Effect4.Laws.Program.BlockMeaning Effect4.Laws.Program.FragmentBlock Effect4.Laws.Program.Agreement.BlockPlain Effect4.Laws.Program.Agreement.Blocks Effect4.Laws.Program.Agreement.HostedBlocks Effect4.Laws.Api.SessionMeaningBlocks Effect4.Laws.Program.ValidatedBlocks

-- The registry claim rows-block-host points to this planned theorem.
#plan_status Effect4.Run.h9_blocks

#plan_status Effect4.Program.Denote.bodiesOf_blockRows Effect4.Program.Denote.denoteBlockB_loopedDataRows Effect4.Program.Denote.denoteBlockB_approx Effect4.Program.Denote.denoteBlockB_of_asExit Effect4.Program.Denote.denoteBlockB_call Effect4.Program.Denote.denoteBlockB_invoke Effect4.Program.Denote.denoteBlockB_param Effect4.Program.Denote.denoteBlockB_provideContext Effect4.Program.Denote.denoteBlockB_provideService Effect4.Program.Denote.denoteBlockB_service Effect4.Program.Denote.denoteBlockB_context Effect4.Program.Denote.call_unfolds_at_limitB Effect4.Program.Denote.invoke_unfolds_at_limitB Effect4.Program.Agreement.PlainHooks.of_blockRows Effect4.Program.Agreement.defBodyPath_body Effect4.Program.Agreement.argSitesAt_body Effect4.Program.Agreement.compilesBlk Effect4.Program.Agreement.compilesBlk_root Effect4.Program.Agreement.hostRunBlockB_stable Effect4.Program.Agreement.localRunC_to_blockB Effect4.Program.Agreement.hostRunBlockB_exits Effect4.Run.conforms_sat_blocks Effect4.Run.agrees_hostRun_blocks
