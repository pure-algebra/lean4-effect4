import Effect4.Laws.Program.MovesConnect
import Effect4.Laws.Program.Guard.ReturnFields
import Effect4.Laws.Program.Guard.NativeStateMotion
import ProofGraph.AxiomAudit

#axiom_audit Effect4.Laws.Program.FrameMoves Effect4.Laws.Program.Moves Effect4.Laws.Program.Footprint Effect4.Laws.Program.Parking Effect4.Laws.Program.MovesConnect Effect4.Laws.Program.Guard.Interruption Effect4.Laws.Program.Guard.DeferredCause Effect4.Laws.Program.Guard.ReturnFields Effect4.Laws.Program.Guard.NativeStateMotion
