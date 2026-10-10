import FoldProbe
import ReviewBoundaryControls
import ProofGraph.AxiomAudit
import ProofGraph.Plan

/-! Pinned landing verification. No production source changes. -/
#plan_status Effect4.Run.h8_loopedRows
#plan_status Effect4.Run.denoteRowsB_eq_session_host
#plan_status Effect4.Program.Agreement.localRunC_compileB
#axiom_audit Effect4.Laws.Program.DenoteRowsB Effect4.Laws.Program.Agreement.LoopCalls Effect4.Laws.Program.Agreement.HostedLoop Effect4.Laws.Api.SessionMeaningLoop Effect4.Laws.Api.SessionMeaning
#axiom_audit ReviewMeaning ReviewControls ReviewBoundaryControls

#axiom_audit FoldProbe
