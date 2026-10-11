import Test.Dogfood.Scenario.Routing
import Test.Dogfood.Scenario.RoutingInterrupt
import Test.Dogfood.Proofs.HostTimeoutNative
import Test.Dogfood.Scenario.SourceUse
import Effect4.Laws.Program.ReleaseCustody.Execution
import ProofGraph.AxiomAudit

#axiom_audit Effect4.Laws.Run.JournalPrefix Effect4.Laws.Run.CallTree Test.Dogfood.Scenario.Routing.Calls Test.Dogfood.Scenario.Routing Test.Dogfood.Scenario.RoutingInterrupt
#axiom_audit Test.Dogfood.Proofs.HostTimeoutSlots Test.Dogfood.Proofs.HostTimeoutFlow Test.Dogfood.Proofs.HostTimeoutNative Test.Dogfood.Scenario.SourceUse Effect4.Laws.Program.ReleaseCustody.Sequencing
#plan_status Test.Dogfood.Scenario.Routing.unauthorized_calls_nothing Test.Dogfood.Scenario.Routing.infrastructure_escapes
