import Controls
import ProofGraph.AxiomAudit
import ProofGraph.Plan

#axiom_audit Controls Effect4.Laws.Program.DenoteRowsB
  Effect4.Laws.Program.Agreement.Segment Effect4.Laws.Program.Agreement.Hosted
  Effect4.Laws.Program.Agreement.LoopCalls Effect4.Laws.Program.Agreement.HostedLoop
  Effect4.Laws.Api.SessionMeaningLoop

#plan_status Effect4.Run.rows_loop_frontier
#plan_status Effect4.Run.rows_loop_frontier_host
#plan_status Effect4.Program.Agreement.localWaitC_to_rowsB
#plan_status Effect4.Program.Agreement.localRunC_compileBO
