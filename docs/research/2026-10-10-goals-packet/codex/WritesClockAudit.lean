import Test.Dogfood.Scenario.Atomic.Writes
import Test.Dogfood.Scenario.Routing
import Test.Counterexamples.Machine.Runtime.HostClockPrefix
import Test.Dogfood.Proofs.HostTimeoutEvaluation
import Effect4.Laws.Program.ReleaseCustody.Execution
import Effect4.Laws.Program.NativeReplies
import ProofGraph.AxiomAudit
#axiom_audit Test.Dogfood.Scenario.Atomic.Writes Effect4.Laws.Run.CallTree Test.Dogfood.Scenario.Routing.Calls Test.Dogfood.Scenario.Routing Test.Counterexamples.Machine.Runtime.HostClockPrefix
#axiom_audit Test.Dogfood.Proofs.HostTimeoutFlow Test.Dogfood.Proofs.HostTimeoutNative Test.Dogfood.Proofs.HostTimeoutFrames Test.Dogfood.Proofs.HostTimeoutEvaluation Effect4.Laws.Program.ReleaseCustody.PopSequencing Effect4.Laws.Program.ReleaseCustody.FrameSequencing Effect4.Laws.Program.NativeReplies
#plan_status Test.Dogfood.Scenario.Routing.unauthorized_calls_nothing
