-- src/Effect4/Laws/Machine/Approximation.lean
def M1Clock.advance_extends {interp : RunInterp ν σ β ε δ ι α χ St} {fuel : Nat} {millis : ClockMillis} : ProofGraph.Obligation (∀ {rounds : Nat} {m : RunMachine ν σ β ε δ ι α χ St},
      Extends m (advanceState interp fuel millis rounds m).1) := ⟨⟩
#proof_wanted M1Clock.advance_extends

-- src/Effect4/Laws/Machine/Approximation.lean
def M1Clock.advanceState_stable (interp : RunInterp ν σ β ε δ ι α χ St κ) (fuel : Nat) (millis : ClockMillis) : ProofGraph.Obligation (∀ (rounds : Nat) (m : RunMachine ν σ β ε δ ι α χ St κ φ η),
      (advanceState interp fuel millis rounds m).2 = true →
      ∀ k j, advanceState interp (fuel + k) millis (rounds + j) m =
        advanceState interp fuel millis rounds m) := ⟨⟩
#proof_wanted M1Clock.advanceState_stable

-- src/Effect4/Laws/Machine/Approximation.lean
def M1Clock.advance_trace_mono (interp : RunInterp ν σ β ε δ ι α χ St) (fuel : Nat) (millis : ClockMillis) : ProofGraph.Obligation (∀ (rounds : Nat) (m : RunMachine ν σ β ε δ ι α χ St) (k j : Nat),
      Extends (advanceState interp fuel millis rounds m).1
        (advanceState interp (fuel + k) millis (rounds + j) m).1) := ⟨⟩
#proof_wanted M1Clock.advance_trace_mono

-- src/Effect4/Laws/Machine/Book.lean
def M1Clock.book_advanceState (_hstep : StepAgrees i₁ i₂ StOk C S)
    (_hclock : ∀ millis s, StOk s →
      StOk (i₁.clockStep millis s).2 ∧ (i₁.clockStep millis s).2 = (i₂.clockStep millis s).2 ∧
        ListRel (OwedMeans C) (i₁.clockStep millis s).1.toList (i₂.clockStep millis s).1.toList)
    (fuel : Nat) (millis : ClockMillis) : ProofGraph.Obligation (∀ (rounds : Nat) (a : RunMachine ν σ β ε δ ι α χ St κ₁ φ₁ η₁)
      (b : RunMachine ν σ β ε δ ι α χ St κ₂ φ₂ η₂), MachineOk StOk a → BookMeans C S a b →
      MachineOk StOk (advanceState i₁ fuel millis rounds a).1 ∧
        BookMeans C S (advanceState i₁ fuel millis rounds a).1 (advanceState i₂ fuel millis rounds b).1 ∧
        (advanceState i₁ fuel millis rounds a).2 = (advanceState i₂ fuel millis rounds b).2) := ⟨⟩
#proof_wanted M1Clock.book_advanceState

-- src/Effect4/Laws/Machine/Handles.lean
def M1Clock.advanceState_minted_of_evaluator (_hb : KeyBounded nk sk interp)
    (_hEval : EvaluatorMinted nk sk interp) (fuel : Nat) (millis : ClockMillis) : ProofGraph.Obligation (∀ (rounds : Nat) (m : RunMachine ν σ Val Err Defect FiberId Ann Ctx Stores), MintedAt nk sk m →
      m.world.le (advanceState interp fuel millis rounds m).1.world ∧
        MintedAt nk sk (advanceState interp fuel millis rounds m).1) := ⟨⟩
#proof_wanted M1Clock.advanceState_minted_of_evaluator

-- src/Effect4/Laws/Program/Guard/OuterDriver.lean
def M1Clock.timer_clockStep_keys {κ : Type} (timers : TimerStore) (millis : ClockMillis) (answer : κ) : ProofGraph.Obligation (wakeKeys (timers.clockStep millis answer).2.wake ⊆ wakeKeys timers.wake) := ⟨⟩
#proof_wanted M1Clock.timer_clockStep_keys

-- src/Effect4/Laws/Program/Guard/OuterDriver.lean
def M1Clock.clockStep_preserved (p : NativeEff) (table : RowTable)
    (m : NativeMachine) (millis : ClockMillis) (state : GuardState m) : ProofGraph.Obligation (Preserved m { m with state := ((interpOf p table).clockStep millis m.state).2 }) := ⟨⟩
#proof_wanted M1Clock.clockStep_preserved

-- src/Effect4/Laws/Program/Guard/OuterDriver.lean
def M1Clock.clockStep_owed_facts (p : NativeEff) (table : RowTable) (m : NativeMachine)
    (millis : ClockMillis) (owed : Owed NCode)
    (_h : ((interpOf p table).clockStep millis m.state).1 = some owed) : ProofGraph.Obligation ((owed.waiter, owed.token) ∈ internalKeys m ∧ raceSites owed.code = [] ∧ owed.mode = .now) := ⟨⟩
#proof_wanted M1Clock.clockStep_owed_facts

-- src/Effect4/Laws/Program/Guard/OuterDriver.lean
def M1Clock.advanceTick_preserved (p : NativeEff) (table : RowTable) (driver : DriverContract p table)
    (fuel : Nat) (millis : ClockMillis) (m : NativeMachine) (owed : Owed NCode) (state : GuardState m)
    (clock : ((interpOf p table).clockStep millis m.state).1 = some owed) : ProofGraph.Obligation (letI) := ⟨⟩
#proof_wanted M1Clock.advanceTick_preserved

-- src/Effect4/Laws/Program/Guard/Single.lean
def M1Clock.timer_fireNext_keys (timers : TimerStore) (target : ClockMillis) (code : Effect4.Machine.Program) : ProofGraph.Obligation (wakeKeys (timers.fireNext target code).2.wake ⊆ wakeKeys timers.wake) := ⟨⟩
#proof_wanted M1Clock.timer_fireNext_keys

-- src/Effect4/Laws/Program/Guard/Single.lean
def M1Clock.timer_clockStep_keys (timers : TimerStore) (millis : ClockMillis) (code : Effect4.Machine.Program) : ProofGraph.Obligation (wakeKeys (timers.clockStep millis code).2.wake ⊆ wakeKeys timers.wake) := ⟨⟩
#proof_wanted M1Clock.timer_clockStep_keys

-- src/Effect4/Laws/Program/Guard/Single.lean
def M1Clock.clockStep_storeKeys (p : NativeEff) (table : RowTable) (stores : Stores) (millis : ClockMillis) : ProofGraph.Obligation (storeKeys ((interpOf p table).clockStep millis stores).2 ⊆ storeKeys stores) := ⟨⟩
#proof_wanted M1Clock.clockStep_storeKeys

-- src/Effect4/Laws/Program/Guard/Single.lean
def M1Clock.clockStep_owed_safe (p : NativeEff) (table : RowTable) {m : NativeMachine}
    {fiber : FiberId} {token : Nat} {request : NativeOp × Val}
    (_h : Held m fiber token request) (millis : ClockMillis) (owed : Owed NCode)
    (_ho : ((interpOf p table).clockStep millis m.state).1 = some owed) : ProofGraph.Obligation ((owed.waiter, owed.token) ≠ (fiber, token)) := ⟨⟩
#proof_wanted M1Clock.clockStep_owed_safe

-- src/Effect4/Laws/Program/Guard/Core.lean
def M1Clock.requestOf_advance_zero (p : NativeEff) (table : RowTable) (m : NativeMachine)
    (fiber : FiberId) (token : Nat) (millis : ClockMillis) : ProofGraph.Obligation (requestOf (steppedBy p 0 table m (.advance millis)) fiber token = requestOf m fiber token) := ⟨⟩
#proof_wanted M1Clock.requestOf_advance_zero

-- src/Effect4/Laws/Program/Guard/Core.lean
def M1Clock.timer_fireNext_key {κ : Type} (timers : TimerStore) (target : ClockMillis)
    (answer : κ) (owed : Owed κ) (_h : (timers.fireNext target answer).1 = some owed) : ProofGraph.Obligation ((owed.waiter, owed.token) ∈ wakeKeys timers.wake) := ⟨⟩
#proof_wanted M1Clock.timer_fireNext_key

-- src/Effect4/Laws/Program/Guard/Core.lean
def M1Clock.timer_clockStep_key {κ : Type} (timers : TimerStore) (millis : ClockMillis)
    (answer : κ) (owed : Owed κ) (_h : (timers.clockStep millis answer).1 = some owed) : ProofGraph.Obligation ((owed.waiter, owed.token) ∈ wakeKeys timers.wake) := ⟨⟩
#proof_wanted M1Clock.timer_clockStep_key

-- src/Effect4/Laws/Program/Guard/Core.lean
def M1Clock.clock_resume_not_external_key (p : NativeEff) (table : RowTable)
    (m : NativeMachine) (fiber : FiberId) (token : Nat) (millis : ClockMillis) (request : NativeOp × Val)
    (owned : RequestsOwned m) (_hr : requestOf m fiber token = some request)
    (owed : Owed NCode) (_ho : ((interpOf p table).clockStep millis m.state).1 = some owed) : ProofGraph.Obligation (owed.waiter ≠ fiber ∨ owed.token ≠ token) := ⟨⟩
#proof_wanted M1Clock.clock_resume_not_external_key

-- src/Effect4/Laws/Program/Simulation/Drive.lean
def M1Clock.clockStep_frame (root : NativeEff) (millis : ClockMillis) (s : Stores) : ProofGraph.Obligation ((interpOf root).clockStep millis s =
      ((s.timers.clockStep millis (Completion.ofExit (Exit.success Val.unit) : Completion Val Err Defect FiberId Ann)).1.map (Owed.mapCode (fun c => embed (completionPrim c))),
        { s with timers := (s.timers.clockStep millis (Completion.ofExit (Exit.success Val.unit) : Completion Val Err Defect FiberId Ann)).2 })) := ⟨⟩
#proof_wanted M1Clock.clockStep_frame

-- src/Effect4/Laws/Program/Simulation/Drive.lean
def M1Clock.clockStep_term (root : NativeEff) (millis : ClockMillis) (s : Stores) : ProofGraph.Obligation ((interpR root).clockStep millis s =
      ((s.timers.clockStep millis (Completion.ofExit (Exit.success Val.unit) : Completion Val Err Defect FiberId Ann)).1.map (Owed.mapCode denoteCompletion),
        { s with timers := (s.timers.clockStep millis (Completion.ofExit (Exit.success Val.unit) : Completion Val Err Defect FiberId Ann)).2 })) := ⟨⟩
#proof_wanted M1Clock.clockStep_term

-- src/Effect4/Laws/Program/Simulation/Drive.lean
def M1Clock.clockStep_rel (root : NativeEff) (millis : ClockMillis) (s : Stores) (_hs : StoresOk s) : ProofGraph.Obligation (StoresOk ((interpOf root).clockStep millis s).2 ∧
      ((interpOf root).clockStep millis s).2 = ((interpR root).clockStep millis s).2 ∧
      ListRel (OwedMeans (CodeMeans root)) ((interpOf root).clockStep millis s).1.toList
        ((interpR root).clockStep millis s).1.toList) := ⟨⟩
#proof_wanted M1Clock.clockStep_rel

-- src/Effect4/Laws/Program/Simulation/Evaluate.lean
def M1Clock.registerAsync_sleep (root : NativeEff) (c : List (FiberId × ExitV)) (millis : ClockMillis)
    (fid : FiberId) (tok : Nat) (s : Stores) : ProofGraph.Obligation ((interpAt root c).registerAsync (.store (.registerSleep millis)) fid tok s =
      ({ s with timers := s.timers.sleep fid tok millis }, none)) := ⟨⟩
#proof_wanted M1Clock.registerAsync_sleep

-- src/Effect4/Laws/Program/Simulation/Evaluate.lean
def M1Clock.registerAsyncR_sleep (root : NativeEff) (c : List (FiberId × ExitV)) (millis : ClockMillis)
    (fid : FiberId) (tok : Nat) (s : Stores) : ProofGraph.Obligation ((interpRAt root c).registerAsync (.store (.registerSleep millis)) fid tok s =
      ({ s with timers := s.timers.sleep fid tok millis }, none)) := ⟨⟩
#proof_wanted M1Clock.registerAsyncR_sleep

