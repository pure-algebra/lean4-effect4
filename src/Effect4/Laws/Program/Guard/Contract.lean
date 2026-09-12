import Effect4.Laws.Program.Guard.RegistrationQueue

set_option autoImplicit false
namespace Effect4.Program.Guard
open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Guard.RegistrationQueue

/-- Internal induction interface only. The raw answer entry handles its first resume
before entering this contract, whose queue keys are reserved against all external requests. -/
structure DriverContract (p : NativeEff) (table : RowTable) : Prop where
  invariant : ∀ (fuel : Nat) (m : NativeMachine) (commands : List NCmd),
    GuardState m → GuardQueue p table m commands → RegistrationQueue commands →
    letI := evaluatorFor p table
    let result := driveState (interpOf p table) fuel m commands
    GuardState result.1 ∧ GuardQueue p table result.1 result.2 ∧ RegistrationQueue result.2
  reserved : ∀ (fuel : Nat) (m : NativeMachine) (commands : List NCmd) (keys : List GuardKey),
    GuardState m → GuardQueue p table m commands → RegistrationQueue commands → ReservedKeys m keys →
    letI := evaluatorFor p table
    ReservedKeys (driveState (interpOf p table) fuel m commands).1 keys
  request : ∀ (fuel : Nat) (m : NativeMachine) (commands : List NCmd)
    (fiber : FiberId) (token : Nat) (request : NativeOp × Val),
    GuardState m → GuardQueue p table m commands → RegistrationQueue commands →
    requestOf m fiber token = some request →
    letI := evaluatorFor p table
    requestOf (driveState (interpOf p table) fuel m commands).1 fiber token = some request ∨
      InterruptedAt (driveState (interpOf p table) fuel m commands).1 fiber
  interrupted : ∀ (fuel : Nat) (m : NativeMachine) (commands : List NCmd) (fiber : FiberId),
    GuardState m → GuardQueue p table m commands → RegistrationQueue commands → InterruptedAt m fiber →
    letI := evaluatorFor p table
    InterruptedAt (driveState (interpOf p table) fuel m commands).1 fiber

end Effect4.Program.Guard
