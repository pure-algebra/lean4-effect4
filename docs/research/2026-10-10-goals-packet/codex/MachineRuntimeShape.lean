import Effect4.Laws.Program.ReleaseCustody.RuntimeShape
import Test.Dogfood.Scenario.Programs
import ProofGraph.AxiomAudit
set_option autoImplicit false
open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Authoring
open Effect4.Program.ReleaseCustody.RuntimeShape

example (total fuel : Nat) :
    ConfigurationKept (Api.load (Test.Dogfood.Scenario.Programs.workersProgram total) fuel) :=
  load _ fuel

#axiom_audit Effect4.Laws.Program.ReleaseCustody.RuntimeShape
  Effect4.Laws.Program.ReleaseCustody.PopSequencing
