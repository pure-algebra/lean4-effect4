import Effect4.Laws.Program.ReleaseCustody.RuntimeShape
import Test.Dogfood.Scenario.Workers.Program
import ProofGraph.AxiomAudit
set_option autoImplicit false
open Effect4 Effect4.Machine Effect4.Program
open Effect4.Program.ReleaseCustody.RuntimeShape

example (total fuel : Nat) :
    ConfigurationKept (Api.load (((Test.Dogfood.Scenario.Workers.crew total).main {rows := RowDef.names [P3WorkerQueue.take, P3WorkerQueue.runJob]} []).toOption.getD (.succeed (.lit .unit))) fuel) :=
  load _ fuel

#axiom_audit Effect4.Laws.Program.ReleaseCustody.RuntimeShape
  Effect4.Laws.Program.ReleaseCustody.PopSequencing
