import Effect4.Laws
import ProofGraph.AxiomAudit
import ProofGraph.Plan

#axiom_audit Effect4.Program.Compile Effect4.Laws.Program.DenoteR Effect4.Laws.Program.Agreement Effect4.Laws.Program.Intro.Sequential Effect4.Laws.Program.Intro.Weight Effect4.Laws.Program.Typed.Denotation Effect4.Laws.Program.Agreement.Machine Effect4.Laws.Program.Agreement.Segment Effect4.Laws.Program.Agreement.Hosted Effect4.Laws.Api.SessionMeaning Effect4.Laws.Api.SessionMeaningLoop Effect4.Laws.Program.Agreement.Loop Effect4.Laws.Program.Agreement.LoopCalls Effect4.Laws.Program.Agreement.BlockPlain

#plan_status Effect4.Run.h9_blocks
