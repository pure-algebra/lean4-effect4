import Test.Program.ReleaseCustodyScope
import Effect4.Laws.Program.Simulation.Hooks
import ProofGraph.AxiomAudit

#axiom_audit Effect4.Laws.Machine.ScopeIdentity Effect4.Laws.Program.ReleaseCustody.ScopeTransfer
  Effect4.Laws.Program.Simulation.Hooks Test.Program.ReleaseCustodyScope
