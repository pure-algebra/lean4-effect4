import Effect4.Laws.Program.Interference
import ProofGraph.AxiomAudit

set_option autoImplicit false
open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Moves

namespace R2LookupReader

/-- A real message word recovers its input first lookup without unique ids. -/
theorem message_reader (edits : List (FiberEdit Err Defect FiberId Ann))
    (m : NativeMachine) (id : FiberId) (next : NFiber)
    (found : (applyFiberEdits edits m).1.fiber? id = some next) :
    ∃ old, m.fiber? id = some old ∧ OtherEdits old next := by
  exact (InterferesWithLookup.fiberEdits edits m).backward_lookup
    (by rw [(RunMachine.applyFiberEdits_shape edits m).1]) id next found

def fiber : NFiber := RunFiber.make ⟨0⟩ (.success .unit) true (0, false) emptyCtx
def shadow : NFiber := { fiber with running := true }
def raw : NativeMachine := { Api.load (.succeed (.lit .unit)) 0 with
  fibers := [fiber, shadow], nextId := 1 }

/-- Duplicate ids do not change which predecessor the reader selects. -/
example : ∃ old, raw.fiber? fiber.id = some old ∧
    OtherEdits old {fiber with observers := [.countdown ⟨3⟩ 5]} := by
  exact message_reader [.observe fiber.id (.countdown ⟨3⟩ 5)] raw fiber.id _ rfl

end R2LookupReader

#axiom_audit Effect4.Laws.Program.Interference
