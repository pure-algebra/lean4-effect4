import Effect4.Laws.Program.SourceScope
import Effect4.Laws.Program.WriterScope
import Test.Dogfood.Scenario.QueueWorkers.Source
import ProofGraph.AxiomAudit
#axiom_audit Effect4.Laws.Program.SourceScope Effect4.Laws.Program.WriterScope Test.Dogfood.Scenario.QueueWorkers.Source
