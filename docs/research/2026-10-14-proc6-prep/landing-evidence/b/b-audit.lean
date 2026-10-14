import Effect4.Laws.Program.BlockMeaning
import Effect4.Laws.Program.FragmentBlock
import Effect4.Laws.Program.Block
import Effect4.Laws.Program.ParamRows
import Effect4.Laws.Library.Ref.Cache
import Test.Program.BlockMeaning
import Test.Dogfood.Scenario.Todo.Cached
import Effect4.Laws.Program.ValidatedBlocks
import ProofGraph.AxiomAudit
import ProofGraph.Plan

#axiom_audit Effect4.Laws.Program.BlockMeaning Effect4.Laws.Program.FragmentBlock Effect4.Laws.Program.Block Effect4.Laws.Program.ParamRows Effect4.Laws.Library.Ref.Cache Test.Program.BlockMeaning Test.Dogfood.Scenario.Todo.Cached
#plan_status Effect4.Program.Denote.denoteBlockB_loopedDataRows
#plan_status Effect4.Program.Denote.denoteBlockB_approx
#plan_status Effect4.Program.Denote.denoteBlockB_of_asExit
#plan_status Effect4.Program.Denote.denoteBlockB_call
#plan_status Effect4.Program.Denote.denoteBlockB_invoke
#plan_status Effect4.Program.Denote.denoteBlockB_param
#plan_status Effect4.Program.Denote.denoteBlockB_provideContext
#plan_status Effect4.Program.Denote.denoteBlockB_provideService
#plan_status Effect4.Program.Denote.denoteBlockB_service
#plan_status Effect4.Program.Denote.denoteBlockB_context
#plan_status Effect4.Program.Denote.call_unfolds_at_limitB
#plan_status Effect4.Program.Denote.invoke_unfolds_at_limitB
#plan_status Effect4.Run.h9_blocks
