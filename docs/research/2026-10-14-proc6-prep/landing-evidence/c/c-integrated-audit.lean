import Effect4.Laws
import ProofGraph.AxiomAudit
import ProofGraph.Plan

#axiom_audit Effect4.Laws.Program.FragmentBlock Effect4.Laws.Program.Agreement.BlockPlain
#plan_status Effect4.Program.Denote.bodiesOf_blockRows
#plan_status Effect4.Program.Agreement.PlainHooks.of_blockRows
#plan_status Effect4.Run.h9_blocks
