import Effect4.Laws.Program.ReleaseWriter.Actions
import Test.Dogfood.Proofs.WorkersWriterSource
import Test.Dogfood.Proofs.QueueWorkersWriter
import Test.Dogfood.Scenario.Atomic.WriterNative
import ProofGraph.AxiomAudit
#axiom_audit Effect4.Laws.Machine.PrimWeights Effect4.Laws.Machine.StoredWeights Effect4.Laws.Program.PlaceFunding.FrameControl Effect4.Laws.Program.ReleaseWriter.Weights Effect4.Laws.Program.ReleaseWriter.Source Effect4.Laws.Program.ReleaseWriter.Stored Effect4.Laws.Program.ReleaseWriter.Callbacks Effect4.Laws.Program.ReleaseWriter.Suspensions Effect4.Laws.Program.ReleaseWriter.Loops Effect4.Laws.Program.ReleaseWriter.Frames Effect4.Laws.Program.ReleaseWriter.Evaluation Effect4.Laws.Program.ReleaseWriter.Machine Effect4.Laws.Program.ReleaseWriter.Actions Test.Dogfood.Proofs.WorkersWriterSource Test.Dogfood.Proofs.QueueWorkersWriter Test.Dogfood.Scenario.Atomic.WriterPhase
