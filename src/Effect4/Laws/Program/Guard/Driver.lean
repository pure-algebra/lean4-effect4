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

theorem driveState_invariants (p : NativeEff) (table : RowTable)
    (fuel : Nat) (m : NativeMachine) (commands : List NCmd)
    (state : GuardState m) (queue : GuardQueue p table m commands)
    (registration : RegistrationQueue commands) :
    letI := evaluatorFor p table
    let result := driveState (interpOf p table) fuel m commands
    GuardState result.1 ∧ GuardQueue p table result.1 result.2 ∧ RegistrationQueue result.2 := by
  letI := evaluatorFor p table
  induction fuel generalizing m commands with
  | zero => exact ⟨state, queue, registration⟩
  | succ fuel ih =>
    cases commands with
    | nil => exact ⟨state, queue, registration⟩
    | cons command rest =>
      simp only [driveState]
      split
      · exact ⟨state, queue, registration⟩
      · have next := driveStep_invariants p table m command rest state queue registration
        exact ih _ _ next.1 next.2.1 next.2.2

theorem reservedKeys_driveState (p : NativeEff) (table : RowTable)
    (fuel : Nat) (m : NativeMachine) (commands : List NCmd) (keys : List GuardKey)
    (state : GuardState m) (queue : GuardQueue p table m commands)
    (registration : RegistrationQueue commands) (reserved : ReservedKeys m keys) :
    letI := evaluatorFor p table
    ReservedKeys (driveState (interpOf p table) fuel m commands).1 keys := by
  letI := evaluatorFor p table
  induction fuel generalizing m commands with
  | zero => exact reserved
  | succ fuel ih =>
    cases commands with
    | nil => exact reserved
    | cons command rest =>
      simp only [driveState]
      split
      · exact reserved
      · have next := driveStep_invariants p table m command rest state queue registration
        exact ih _ _ next.1 next.2.1 next.2.2
          (reservedKeys_driveStep p table m command rest state queue keys reserved)

theorem interruptedAt_driveState (p : NativeEff) (table : RowTable)
    (fuel : Nat) (m : NativeMachine) (commands : List NCmd) (fiber : FiberId)
    (state : GuardState m) (queue : GuardQueue p table m commands)
    (registration : RegistrationQueue commands) (before : InterruptedAt m fiber) :
    letI := evaluatorFor p table
    InterruptedAt (driveState (interpOf p table) fuel m commands).1 fiber := by
  letI := evaluatorFor p table
  induction fuel generalizing m commands with
  | zero => exact before
  | succ fuel ih =>
    cases commands with
    | nil => exact before
    | cons command rest =>
      simp only [driveState]
      split
      · exact before
      · have next := driveStep_invariants p table m command rest state queue registration
        exact ih _ _ next.1 next.2.1 next.2.2
          (interruptedAt_driveStep p table m command rest state fiber before)

theorem requestOrInterrupted_driveState (p : NativeEff) (table : RowTable)
    (fuel : Nat) (m : NativeMachine) (commands : List NCmd)
    (fiber : FiberId) (token : Nat) (request : NativeOp × Val)
    (state : GuardState m) (queue : GuardQueue p table m commands)
    (registration : RegistrationQueue commands) (before : requestOf m fiber token = some request) :
    letI := evaluatorFor p table
    requestOf (driveState (interpOf p table) fuel m commands).1 fiber token = some request ∨
      InterruptedAt (driveState (interpOf p table) fuel m commands).1 fiber := by
  letI := evaluatorFor p table
  induction fuel generalizing m commands with
  | zero => exact Or.inl before
  | succ fuel ih =>
    cases commands with
    | nil => exact Or.inl before
    | cons command rest =>
      simp only [driveState]
      split
      · exact Or.inl before
      · have next := driveStep_invariants p table m command rest state queue registration
        rcases requestOrInterrupted_driveStep p table m command rest state queue fiber token request before with kept | interrupted
        · exact ih _ _ next.1 next.2.1 next.2.2 kept
        · exact Or.inr (interruptedAt_driveState p table fuel _ _ fiber next.1 next.2.1 next.2.2 interrupted)

/-- The native command driver satisfies the internal contract for every fuel budget.
This theorem supplies the contract; no driver assumption remains. -/
theorem driverContract (p : NativeEff) (table : RowTable) : DriverContract p table :=
  ⟨driveState_invariants p table, reservedKeys_driveState p table,
    requestOrInterrupted_driveState p table, interruptedAt_driveState p table⟩

end Effect4.Program.Guard
