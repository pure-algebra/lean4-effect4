import Effect4.Laws.Program.ReleaseCustody.Execution
import Effect4.Laws.Program.ReleaseCustody.ScopeTransfer
import Test.Dogfood.Scenario.Workers.Assertions
import ProofGraph.AxiomAudit

#axiom_audit Effect4.Laws.Program.ReleaseCustody.Execution Effect4.Laws.Program.ReleaseCustody.Lift Effect4.Laws.Program.ReleaseCustody.Control Effect4.Laws.Program.ReleaseCustody.Evaluation Effect4.Laws.Program.ReleaseCustody.Producers Effect4.Laws.Program.ReleaseCustody.Pop Effect4.Laws.Program.ReleaseCustody.CausePop Effect4.Laws.Program.ReleaseCustody.ScopeTransfer Effect4.Laws.Machine.ScopeIdentity Test.Dogfood.Scenario.Workers.Assertions
