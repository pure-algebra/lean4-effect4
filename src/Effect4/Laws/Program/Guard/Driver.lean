import Effect4.Laws.Program.Guard.CommandObservations

set_option autoImplicit false
namespace Effect4.Program.Guard
open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Guard.RegistrationQueue

theorem driveStep_invariants (p : NativeEff) (table : RowTable)
    (m : NativeMachine) (command : NCmd) (rest : List NCmd)
    (state : GuardState m) (queue : GuardQueue p table m (command :: rest))
    (registration : RegistrationQueue (command :: rest)) :
    letI := evaluatorFor p table
    let result := driveStep (interpOf p table) m command rest
    GuardState result.1 ∧ GuardQueue p table result.1 result.2 ∧ RegistrationQueue result.2 :=
  ⟨guardState_driveStep p table m command rest state queue,
    guardQueue_driveStep p table m command rest state queue registration,
    registrationQueue_driveStep p table m command rest registration⟩

open Effect4.Machine.Lift

/-- The guard's loop invariant (`Guard/Contract.lean:10-14`). -/
def guardI (p : NativeEff) (table : RowTable) (m : NativeMachine) (cmds : List NCmd) : Prop :=
  GuardState m ∧ GuardQueue p table m cmds ∧ RegistrationQueue cmds

/-- `DriverContract.invariant`, from the loop lift and `driveStep_invariants`. -/
theorem guard_invariant (p : NativeEff) (table : RowTable) :
    ∀ (fuel : Nat) (m : NativeMachine) (commands : List NCmd),
      GuardState m → GuardQueue p table m commands → RegistrationQueue commands →
      letI := evaluatorFor p table
      let result := driveState (interpOf p table) fuel m commands
      GuardState result.1 ∧ GuardQueue p table result.1 result.2 ∧ RegistrationQueue result.2 := by
  intro fuel m commands state queue registration
  letI := evaluatorFor p table
  exact driveState_lift_unit (interpOf p table) (guardI p table)
    (fun m c rest _ h => driveStep_invariants p table m c rest h.1 h.2.1 h.2.2)
    fuel m commands ⟨state, queue, registration⟩

/-- `DriverContract.reserved`: the same lift at the invariant with the frame fact beside it. -/
theorem guard_reserved (p : NativeEff) (table : RowTable) :
    ∀ (fuel : Nat) (m : NativeMachine) (commands : List NCmd) (keys : List GuardKey),
      GuardState m → GuardQueue p table m commands → RegistrationQueue commands →
      ReservedKeys m keys →
      letI := evaluatorFor p table
      ReservedKeys (driveState (interpOf p table) fuel m commands).1 keys := by
  intro fuel m commands keys state queue registration reserved
  letI := evaluatorFor p table
  exact (driveState_lift_unit (interpOf p table)
    (fun m cmds => guardI p table m cmds ∧ ReservedKeys m keys)
    (fun m c rest _ h => ⟨driveStep_invariants p table m c rest h.1.1 h.1.2.1 h.1.2.2,
      reservedKeys_driveStep p table m c rest h.1.1 h.1.2.1 keys h.2⟩)
    fuel m commands ⟨⟨state, queue, registration⟩, reserved⟩).2

theorem guard_interrupted (p : NativeEff) (table : RowTable) :
    ∀ (fuel : Nat) (m : NativeMachine) (commands : List NCmd) (fiber : FiberId),
      GuardState m → GuardQueue p table m commands → RegistrationQueue commands →
      InterruptedAt m fiber →
      letI := evaluatorFor p table
      InterruptedAt (driveState (interpOf p table) fuel m commands).1 fiber := by
  intro fuel m commands fiber state queue registration before
  letI := evaluatorFor p table
  exact (driveState_lift_unit (interpOf p table)
    (fun m cmds => guardI p table m cmds ∧ InterruptedAt m fiber)
    (fun m c rest _ h => ⟨driveStep_invariants p table m c rest h.1.1 h.1.2.1 h.1.2.2,
      interruptedAt_driveStep p table m c rest h.1.1 fiber h.2⟩)
    fuel m commands ⟨⟨state, queue, registration⟩, before⟩).2

theorem guard_request (p : NativeEff) (table : RowTable) :
    ∀ (fuel : Nat) (m : NativeMachine) (commands : List NCmd)
      (fiber : FiberId) (token : Nat) (request : NativeOp × Val),
      GuardState m → GuardQueue p table m commands → RegistrationQueue commands →
      requestOf m fiber token = some request →
      letI := evaluatorFor p table
      requestOf (driveState (interpOf p table) fuel m commands).1 fiber token = some request ∨
        InterruptedAt (driveState (interpOf p table) fuel m commands).1 fiber := by
  intro fuel m commands fiber token request state queue registration before
  letI := evaluatorFor p table
  refine (driveState_lift_unit (interpOf p table)
    (fun m cmds => guardI p table m cmds ∧
      (requestOf m fiber token = some request ∨ InterruptedAt m fiber))
    (fun m c rest _ h => ⟨driveStep_invariants p table m c rest h.1.1 h.1.2.1 h.1.2.2, ?_⟩)
    fuel m commands ⟨⟨state, queue, registration⟩, Or.inl before⟩).2
  rcases h.2 with kept | interrupted
  · exact requestOrInterrupted_driveStep p table m c rest h.1.1 h.1.2.1 fiber token request kept
  · exact Or.inr (interruptedAt_driveStep p table m c rest h.1.1 fiber interrupted)

/-- **The guard's contract is an instance.** All four fields of `DriverContract` come from the
one loop lift, each at its own invariant, with the guard's per-command lemmas as premises. -/
theorem driverContract_of_lift (p : NativeEff) (table : RowTable) : DriverContract p table :=
  ⟨guard_invariant p table, guard_reserved p table, guard_request p table,
    guard_interrupted p table⟩


/-- The native command driver satisfies the internal contract for every fuel budget.
The generic loop lift supplies all four fields from the per-command facts. -/
theorem driverContract (p : NativeEff) (table : RowTable) : DriverContract p table :=
  driverContract_of_lift p table

end Effect4.Program.Guard
