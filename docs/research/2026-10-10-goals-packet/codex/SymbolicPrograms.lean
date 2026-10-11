import Test.Dogfood.Scenario.Programs
import ProofGraph.AxiomAudit

set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

open Effect4 Effect4.Program Effect4.Program.Authoring Effect4.Laws.Auto
open Test.Dogfood.Scenario Test.Dogfood.Scenario.Programs

-- Readers: successful builds supply the actual static acquisition facts at any job count.
example (total : Nat) (b : Api.Built) (h : Api.Author.build (Workers.crew total) = .ok b) :
    OncePlaced (Node.eff b.program) (crewAcquire 1) = true :=
  crew_acquire_once_placed total b h 1 List.mem_cons_self

example (total : Nat) (b : Api.Built) (h : Api.Author.build (QueueWorkers.crew total) = .ok b) :
    OncePlaced (Node.eff b.program) (queueAcquire 1) = true :=
  queueCrew_acquire_once_placed total b h 1 List.mem_cons_self

-- Control: a queue operation inside worker 2's loop fails the static once-placement test.
example (total : Nat) : OncePlaced (Node.eff (queueProgram total))
    [1, 1, 1, 1, 1, 1, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 1, 0, 1, 0, 0, 1, 1, 1, 1, 0, 0] = false := by
  kernel_rfl

#axiom_audit Effect4.Laws.Program.Placement Test.Dogfood.Scenario.Programs
  Test.Dogfood.Scenario.QueueWorkers.Program
