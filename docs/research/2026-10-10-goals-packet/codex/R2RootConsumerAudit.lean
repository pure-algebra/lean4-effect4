import ProofGraph.AxiomAudit
import Effect4.Laws.Program.NativeReferences
import Effect4.Laws.Program.SourceOpportunityNative
import Effect4.Laws.Program.SourceOpportunityPrimitive
import Effect4.Laws.Program.Typed.HostWalk
import Effect4.Laws.Program.Typed.Commands.Bookkeeping

#axiom_audit Effect4.Laws.Program.NativeReferences Effect4.Laws.Program.SourceOpportunityNative Effect4.Laws.Program.SourceOpportunityPrimitive Effect4.Laws.Program.Typed.HostWalk Effect4.Laws.Program.Typed.Commands.Bookkeeping
