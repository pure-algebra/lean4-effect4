import Effect4.Laws.Codegen.PrintTyped
import Effect4.Laws.Machine.RaceFirst
import Test.Dogfood.Scenario.Gate
import Test.Dogfood.Scenario.Atomic
import Test.Dogfood.Scenario.Workers
import Test.Dogfood.Scenario.QueueWorkers
import Test.Dogfood.Scenario.Routing
import Test.Program.Gen
import Test.Program.ProtocolPosts
import ProofGraph.AxiomAudit

#axiom_audit Effect4.Laws.Codegen.PrintTyped Effect4.Laws.Machine.RaceFirst
#axiom_audit Test.Dogfood.Scenario.Gate Test.Dogfood.Scenario.Atomic Test.Dogfood.Scenario.Workers Test.Dogfood.Scenario.QueueWorkers Test.Dogfood.Scenario.Routing

#axiom_audit Test.Program.ProtocolPosts Test.Program.Gen
