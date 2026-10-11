import Effect4.Laws.Program.ReleaseCustody.Execution
import Test.Dogfood.Scenario.SourceOpportunity
import Test.Dogfood.Proofs.HostTimeoutParkSteps
import Effect4.Laws.Program.NativeHeapReplies
import ProofGraph.AxiomAudit
#axiom_audit Effect4.Laws.Program.ReleaseCustody.Sequencing Effect4.Laws.Program.ReleaseCustody.PopSequencing Effect4.Laws.Program.ReleaseCustody.FrameSequencing Effect4.Laws.Program.ReleaseCustody.NativeSequencing Effect4.Laws.Program.NativeConfiguration Effect4.Laws.Program.NativeEvaluation Effect4.Laws.Program.NativeExecutor Effect4.Laws.Program.NativeCommands Effect4.Laws.Program.NativeHistory Effect4.Laws.Program.NativeReplies Effect4.Laws.Program.NativeHeapReplies Effect4.Laws.Program.SourceOpportunityActions Effect4.Laws.Program.SourceOpportunityMachine
#axiom_audit Test.Dogfood.Proofs.HostTimeoutState Test.Dogfood.Proofs.HostTimeoutStateSteps Test.Dogfood.Proofs.HostTimeoutRaceSteps Test.Dogfood.Proofs.HostTimeoutQueue Test.Dogfood.Proofs.HostTimeoutParkSteps
