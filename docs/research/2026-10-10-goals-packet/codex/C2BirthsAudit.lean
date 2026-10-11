import Test.Program.CommandFrames
import Effect4.Laws.Program.ReleaseCustody.NativeMachineShape
import ProofGraph.AxiomAudit

#axiom_audit Effect4.Laws.Program.Interference Effect4.Laws.Program.CommandFrames Effect4.Laws.Program.MaskRuns Effect4.Laws.Program.MaskBracket Effect4.Laws.Program.ReleaseCustody.NativeMachineShape Test.Program.CommandFrames
