import Effect4.Laws.Auto.Obligations
import Effect4.Laws.Program.Guard.Single
import Effect4.Laws.Program.Guard.OuterDriver

set_option autoImplicit false
namespace Effect4.Program.Guard.SingleGuard
open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Guard
open Effect4.Program.Guard.RegistrationQueue
def M1Clock.held_advanceState (p : NativeEff) (table : RowTable) (fuel : Nat) (millis : ClockMillis) (rounds : Nat)
    {m : NativeMachine} {fiber : FiberId} {token : Nat} {request : NativeOp × Val}
    (_h : Held m fiber token request) : ProofGraph.Obligation (letI) := ⟨⟩
#proof_wanted M1Clock.held_advanceState

end Effect4.Program.Guard.SingleGuard

namespace Effect4.Program.Guard.OuterDriver
open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Guard
open Effect4.Program.Guard.RegistrationQueue
def M1Clock.advanceState_preserved (p : NativeEff) (table : RowTable) (_driver : DriverContract p table)
    (fuel : Nat) (millis : ClockMillis) (rounds : Nat) (m : NativeMachine) (_state : GuardState m) : ProofGraph.Obligation (letI) := ⟨⟩
#proof_wanted M1Clock.advanceState_preserved

def M1Clock.guardState_advanceState (p : NativeEff) (table : RowTable) (_driver : DriverContract p table)
    (fuel : Nat) (millis : ClockMillis) (rounds : Nat) (m : NativeMachine) (_state : GuardState m) : ProofGraph.Obligation (letI) := ⟨⟩
#proof_wanted M1Clock.guardState_advanceState

def M1Clock.reservedKeys_advanceState (p : NativeEff) (table : RowTable) (_driver : DriverContract p table)
    (fuel : Nat) (millis : ClockMillis) (rounds : Nat) (m : NativeMachine) (_state : GuardState m)
    (keys : List GuardKey) (_reserved : ReservedKeys m keys) : ProofGraph.Obligation (letI) := ⟨⟩
#proof_wanted M1Clock.reservedKeys_advanceState

def M1Clock.requestOrInterrupted_advanceState (p : NativeEff) (table : RowTable)
    (_driver : DriverContract p table) (fuel : Nat) (millis : ClockMillis) (rounds : Nat) (m : NativeMachine)
    (_state : GuardState m) (fiber : FiberId) (token : Nat) (request : NativeOp × Val)
    (_before : requestOf m fiber token = some request) : ProofGraph.Obligation (letI) := ⟨⟩
#proof_wanted M1Clock.requestOrInterrupted_advanceState

def M1Clock.interruptedAt_advanceState (p : NativeEff) (table : RowTable) (_driver : DriverContract p table)
    (fuel : Nat) (millis : ClockMillis) (rounds : Nat) (m : NativeMachine) (_state : GuardState m)
    (fiber : FiberId) (_before : InterruptedAt m fiber) : ProofGraph.Obligation (letI) := ⟨⟩
#proof_wanted M1Clock.interruptedAt_advanceState

end Effect4.Program.Guard.OuterDriver
