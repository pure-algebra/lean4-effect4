import Effect4.Laws.Machine.FiberSum
import Effect4.Laws.Machine.WriterWeights
import Effect4.Laws.Program.ReleaseCustody.Outside
import Effect4.Laws.Program.SourceOpportunityMachine
import Effect4.Laws.Program.SourceOpportunityNative
import Effect4.Laws.Program.SourceOpportunityExecution
import Test.Dogfood.Scenario.Atomic.WriterMachine
import ProofGraph.AxiomAudit
#axiom_audit Effect4.Laws.Machine.FiberSum Effect4.Laws.Machine.WriterWeights Effect4.Laws.Program.ReleaseCustody.Outside Effect4.Laws.Program.SourceOpportunityMachine Effect4.Laws.Program.SourceOpportunityNative Effect4.Laws.Program.SourceOpportunityExecution Test.Dogfood.Scenario.Atomic.WriterMachine
