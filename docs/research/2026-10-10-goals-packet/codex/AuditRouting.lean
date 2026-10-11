import Test.Dogfood.Scenario.Routing
import ProofGraph.AxiomAudit
import ProofGraph.Plan

#axiom_audit Test.Dogfood.Proofs.HostRouting Test.Dogfood.Scenario.Routing
#plan_status Test.Dogfood.Scenario.Routing.infrastructure_escapes
#plan_status Test.Dogfood.Scenario.Routing.unauthorized_calls_nothing
