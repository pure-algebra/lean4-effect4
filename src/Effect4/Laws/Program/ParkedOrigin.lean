import Effect4.Laws.Program.ParkedShape
import Effect4.Laws.Program.Guard.ReturnFields

/-!
Concept: reactive-scheduling R11.
Consumer: Atomic and Timeout command, detached and stored matching-token reply permissions.
An old reserved token cannot match the acting fiber's newly minted park.
The existing interference word recovers every other matching continuation.
-/
set_option autoImplicit false
namespace Effect4.Program.ParkedShape
open Effect4 Effect4.Machine Effect4.Program

/-- Installing the actual actor retains the origin of every old matching token. -/
theorem installed_old_park {before : NativeMachine} {result : Guard.ReturnFields.NIter}
    (fresh : Guard.ReturnFields.FreshPark before result)
    (others : Moves.Interferes before result.machine)
    (fiber : Fiber) (member : fiber ∈ (result.machine.update result.fiber).fibers)
    (token : Nat) (below : token < before.nextToken)
    (parked : fiber.parked = .withGuard token) :
    ∃ old ∈ before.fibers, fiber.id = old.id ∧ old.parked = .withGuard token ∧
      fiber.frame.current = old.frame.current ∧ fiber.frame.stack = old.frame.stack := by
  change fiber ∈ result.machine.fibers.map _ at member
  obtain ⟨prior, inside, actual⟩ := List.mem_map.mp member
  split at actual
  · cases actual
    have minted := (fresh token parked).1
    exact False.elim ((Nat.ne_of_lt below) minted)
  · cases actual
    exact interferes_park_origin others fiber inside token parked

end Effect4.Program.ParkedShape
