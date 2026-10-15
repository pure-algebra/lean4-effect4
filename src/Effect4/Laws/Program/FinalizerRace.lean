import Effect4.Laws.Program.FinalizerPlaces

/-!
Concept: scope-lifetime-finalization, R11.
Consumer: the joint selected-source command invariant.
The actual race command instantiates the scalar model's shared place-transfer law.
It establishes one command balance, with no whole-history or progress claim.
-/
set_option autoImplicit false
namespace Effect4.Program.FinalizerSource
open Effect4 Effect4.Machine Effect4.Program

/-- The selected-source ledger is the shared frame, race and detached-program reading. -/
theorem ledger_places (root : NativeEff) (q : List Nat) :
    ledger root q = FinalizerPlaces.ledger (frameModel root q) (consumedFrame q) (producedFrame q) := rfl

/-- Launching transfers the entrant reservation into its actual spawned fiber.
The shared law retains the real pending command queue and detached snapshot. -/
theorem launch_balance (root : NativeEff) (table : RowTable) (q : List Nat)
    (machine : NativeMachine) (raceId : Nat)
    (rest : List FinalizerPlaces.SourceCommand) (snapshot : List FinalizerPlaces.SourceTask)
    (unique : (machine.races.map Race.id).Nodup) :
    letI := evaluatorFor root table
    let out := driveStep (interpOf root table) machine (.launch raceId) rest
    (ledger root q).Balanced machine (.launch raceId :: rest) snapshot out.1 out.2 snapshot := by
  rw [ledger_places]
  exact FinalizerPlaces.launch_balance root table (frameModel root q)
    (consumedFrame q) (producedFrame q) machine raceId rest snapshot unique

end Effect4.Program.FinalizerSource
