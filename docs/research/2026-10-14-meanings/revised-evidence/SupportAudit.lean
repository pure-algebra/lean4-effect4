import Effect4.Laws.Program.PlaceFunding.FlowGuarded
import Test.Dogfood.Proofs.WorkersCapturedSlots
import Test.Dogfood.Proofs.WorkersExclusivity
import ProofGraph.AxiomAudit

#axiom_audit Effect4.Laws.Program.PlaceFunding.FlowGuarded
  Test.Dogfood.Proofs.WorkersWriters
  Test.Dogfood.Proofs.WorkersSlots
  Test.Dogfood.Proofs.WorkersConnections
  Test.Dogfood.Proofs.WorkersNativeSlots
  Test.Dogfood.Proofs.WorkersCapturedSlots
  Test.Dogfood.Proofs.WorkersExclusivity
