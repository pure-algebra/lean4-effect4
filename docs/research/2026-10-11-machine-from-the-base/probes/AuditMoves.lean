import Effect4.Laws.Program.MovesConnect
import Effect4.Laws.Program.Footprint
import Effect4.Laws.Program.Interference
import Effect4.Laws.Program.StackLocal
import ProofGraph.AxiomAudit

#axiom_audit Effect4.Laws.Program.Moves Effect4.Laws.Program.MovesConnect Effect4.Laws.Program.Footprint Effect4.Laws.Program.Interference Effect4.Laws.Machine.StackLocal Effect4.Laws.Program.StackLocal
