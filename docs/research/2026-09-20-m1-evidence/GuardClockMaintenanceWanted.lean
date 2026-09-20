/-! Offline capture before clock proof maintenance; not yet elaborated. Earlier before-census imports failed. -/



namespace Effect4.Program.Guard.SingleGuard

def M1Clock.timer_fireNext_keys (timers : TimerStore) (target : ClockMillis) (code : Completion Val Err Defect FiberId Ann) : ProofGraph.Obligation (wakeKeys (timers.fireNext target code).2.wake ⊆ wakeKeys timers.wake) := ⟨⟩
#proof_wanted M1Clock.timer_fireNext_keys

def M1Clock.timer_clockStep_keys (timers : TimerStore) (millis : ClockMillis) (code : Completion Val Err Defect FiberId Ann) : ProofGraph.Obligation (wakeKeys (timers.clockStep millis code).2.wake ⊆ wakeKeys timers.wake) := ⟨⟩
#proof_wanted M1Clock.timer_clockStep_keys

def M1Clock.clockStep_storeKeys (p : NativeEff) (table : RowTable) (stores : Stores) (millis : ClockMillis) : ProofGraph.Obligation (storeKeys ((interpOf p table).clockStep millis stores).2 ⊆ storeKeys stores) := ⟨⟩
#proof_wanted M1Clock.clockStep_storeKeys

def M1Clock.clockStep_owed_safe (p : NativeEff) (table : RowTable) {m : NativeMachine}
    {fiber : FiberId} {token : Nat} {request : NativeOp × Val}
    (_h : Held m fiber token request) (millis : ClockMillis) (owed : Owed NCode)
    (_ho : ((interpOf p table).clockStep millis m.state).1 = some owed) : ProofGraph.Obligation ((owed.waiter, owed.token) ≠ (fiber, token)) := ⟨⟩
#proof_wanted M1Clock.clockStep_owed_safe

def M1Clock.held_advanceState (p : NativeEff) (table : RowTable) (fuel : Nat) (millis : ClockMillis) (rounds : Nat)
    {m : NativeMachine} {fiber : FiberId} {token : Nat} {request : NativeOp × Val}
    (_h : Held m fiber token request) : ProofGraph.Obligation (
    letI := evaluatorFor p table
    Held (advanceState (interpOf p table) fuel millis rounds m).1 fiber token request) := ⟨⟩
#proof_wanted M1Clock.held_advanceState

end Effect4.Program.Guard.SingleGuard



namespace Effect4.Program.Guard.OuterDriver

def M1Clock.timer_clockStep_keys {κ : Type} (timers : TimerStore) (millis : ClockMillis) (answer : κ) : ProofGraph.Obligation (wakeKeys (timers.clockStep millis answer).2.wake ⊆ wakeKeys timers.wake) := ⟨⟩
#proof_wanted M1Clock.timer_clockStep_keys

def M1Clock.clockStep_preserved (p : NativeEff) (table : RowTable)
    (m : NativeMachine) (millis : ClockMillis) (_state : GuardState m) : ProofGraph.Obligation (Preserved m { m with state := ((interpOf p table).clockStep millis m.state).2 }) := ⟨⟩
#proof_wanted M1Clock.clockStep_preserved

def M1Clock.clockStep_owed_facts (p : NativeEff) (table : RowTable) (m : NativeMachine)
    (millis : ClockMillis) (owed : Owed NCode)
    (_h : ((interpOf p table).clockStep millis m.state).1 = some owed) : ProofGraph.Obligation ((owed.waiter, owed.token) ∈ internalKeys m ∧ raceSites owed.code = [] ∧ owed.mode = .now) := ⟨⟩
#proof_wanted M1Clock.clockStep_owed_facts

def M1Clock.advanceTick_preserved (p : NativeEff) (table : RowTable) (_driver : DriverContract p table)
    (fuel : Nat) (millis : ClockMillis) (m : NativeMachine) (owed : Owed NCode) (_state : GuardState m)
    (_clock : ((interpOf p table).clockStep millis m.state).1 = some owed) : ProofGraph.Obligation (
    letI := evaluatorFor p table
    let mid : NativeMachine := { m with state := ((interpOf p table).clockStep millis m.state).2 }
    let drained := drainOwed mid [owed]
    Preserved m (driveState (interpOf p table) fuel drained.1 (drained.2 ++ [.drainDue])).1) := ⟨⟩
#proof_wanted M1Clock.advanceTick_preserved

def M1Clock.advanceState_preserved (p : NativeEff) (table : RowTable) (_driver : DriverContract p table)
    (fuel : Nat) (millis : ClockMillis) (rounds : Nat) (m : NativeMachine) (_state : GuardState m) : ProofGraph.Obligation (
    letI := evaluatorFor p table
    Preserved m (advanceState (interpOf p table) fuel millis rounds m).1) := ⟨⟩
#proof_wanted M1Clock.advanceState_preserved

def M1Clock.guardState_advanceState (p : NativeEff) (table : RowTable) (_driver : DriverContract p table)
    (fuel : Nat) (millis : ClockMillis) (rounds : Nat) (m : NativeMachine) (_state : GuardState m) : ProofGraph.Obligation (
    letI := evaluatorFor p table
    GuardState (advanceState (interpOf p table) fuel millis rounds m).1) := ⟨⟩
#proof_wanted M1Clock.guardState_advanceState

def M1Clock.reservedKeys_advanceState (p : NativeEff) (table : RowTable) (_driver : DriverContract p table)
    (fuel : Nat) (millis : ClockMillis) (rounds : Nat) (m : NativeMachine) (_state : GuardState m)
    (keys : List GuardKey) (_reserved : ReservedKeys m keys) : ProofGraph.Obligation (
    letI := evaluatorFor p table
    ReservedKeys (advanceState (interpOf p table) fuel millis rounds m).1 keys) := ⟨⟩
#proof_wanted M1Clock.reservedKeys_advanceState

def M1Clock.requestOrInterrupted_advanceState (p : NativeEff) (table : RowTable)
    (_driver : DriverContract p table) (fuel : Nat) (millis : ClockMillis) (rounds : Nat) (m : NativeMachine)
    (_state : GuardState m) (fiber : FiberId) (token : Nat) (request : NativeOp × Val)
    (_before : requestOf m fiber token = some request) : ProofGraph.Obligation (
    letI := evaluatorFor p table
    requestOf (advanceState (interpOf p table) fuel millis rounds m).1 fiber token = some request ∨
      InterruptedAt (advanceState (interpOf p table) fuel millis rounds m).1 fiber) := ⟨⟩
#proof_wanted M1Clock.requestOrInterrupted_advanceState

def M1Clock.interruptedAt_advanceState (p : NativeEff) (table : RowTable) (_driver : DriverContract p table)
    (fuel : Nat) (millis : ClockMillis) (rounds : Nat) (m : NativeMachine) (_state : GuardState m)
    (fiber : FiberId) (_before : InterruptedAt m fiber) : ProofGraph.Obligation (
    letI := evaluatorFor p table
    InterruptedAt (advanceState (interpOf p table) fuel millis rounds m).1 fiber) := ⟨⟩
#proof_wanted M1Clock.interruptedAt_advanceState

end Effect4.Program.Guard.OuterDriver
