import Effect4.Laws.Program.PlaceFunding.Transfer
import Effect4.Laws.Program.PrimitiveProducer

/-!
Concept: scope-lifetime-finalization R11.
Question: actual primitive debit serves Atomic.Cleanup.log_debits and source-opportunity histories.
The existing PrimitiveProducer witness owns the classification.
Consumers supply actual source permissions and complex producer debits.
These laws prove no source admission, initial funding, progress, or admitted-history bound.
-/
set_option autoImplicit false
namespace Effect4.Program.PlaceFunding
open Effect4 Effect4.Machine Effect4.Program
open Effect4.Program.Guard Effect4.Machine.ForkLedger.Invariant

/-- The local state, trace and acting row lift through an unchanged stored-row table.
Consumers: primitive replies and both source and Atomic frame delegation. -/
theorem NoQueue.local_debit {L : Ledger} (quiet : NoQueue L) (m : NativeMachine)
    (fiber : NFiber) (it : Moves.NIteration) (rows : it.machine.fibers = m.fibers)
    (bounded : L.spent it.machine + L.state it.machine.state + L.fiber it.fiber + L.issued m ≤
      L.spent m + L.state m.state + L.fiber fiber + L.issued it.machine) :
    L.IterDebit m fiber it := by
  unfold PlaceLedger.IterDebit PlaceLedger.outside
  simp only [funext quiet.races, funext quiet.commands, PlaceLedger.zero_sum,
    Nat.add_zero, FiberSum.outside, rows]
  omega

/-- Instance premises retain actual producer results and source permission.
Complex producers already have their own local transfer laws. -/
structure PrimitiveInputs (L : Ledger) (Free : NCode → Prop) (interp : Moves.NInterp)
    (m : NativeMachine) (fiber : NFiber) (yielding : Bool) : Prop where
  success : ∀ value, Free (.success value)
  failure : ∀ cause, Free (.failure cause)
  exitValue : ∀ exit mode, Free (interp.exitValue exit mode)
  step : L.IterDebit m fiber (evaluatePrim.stepFrame interp m fiber yielding)
  finalizer : ∀ exit, L.IterDebit m fiber (evaluatePrim.finalizerOr interp m fiber yielding exit)
  action : ∀ thunk action, fiber.frame.current = .withFiber thunk →
    interp.withFiberOf thunk = some action →
    L.IterDebit m fiber (evaluatePrim.withFiber interp m fiber yielding action)
  sync : ∀ thunk state value, fiber.frame.current = .sync thunk →
    interp.syncState thunk m.state = some (state, value) →
    L.state state + L.fiber {fiber with frame.current := .success value} ≤ L.state m.state + L.fiber fiber
  registerState : ∀ register signal cancel state code,
    fiber.frame.current = .async register signal cancel →
    interp.registerAsync register fiber.id m.nextToken m.state = (state, code) → L.state state ≤ L.state m.state
  registerReply : ∀ register signal cancel state code,
    fiber.frame.current = .async register signal cancel →
    interp.registerAsync register fiber.id m.nextToken m.state = (state, some code) → Free code
  cancel : ∀ register signal cancel state,
    fiber.frame.current = .async register signal cancel →
    interp.registerAsync register fiber.id m.nextToken m.state = (state, none) →
    L.fiber {fiber with frame.stack := .asyncFinalizer (interp.cancelName (cancel.getD interp.abortName) fiber.id m.nextToken) :: fiber.frame.stack} ≤ L.fiber fiber
  joinCancel : L.fiber {fiber with frame.stack := .asyncFinalizer (interp.cancelName interp.parkCancelName fiber.id m.nextToken) :: fiber.frame.stack} ≤ L.fiber fiber
  countdown : ∀ targets next returned parked edits,
    interp.parkOf fiber.frame.current = some (.ok (.awaitAll targets)) →
    countdownParkEdits interp m fiber targets .exitsValue false = (next, returned, parked, edits) →
    L.IterDebit m fiber ⟨next, returned, yielding, (if parked then .parked else .continue_), [], edits⟩
  race : ∀ race, interp.parkOf fiber.frame.current = some (.ok (.race race)) →
    L.IterDebit m fiber (registerRace m fiber yielding race)

/-- The shared interpretation reads the existing primitive witness once.
Source instances discharge every actual reply and writer permission. -/
theorem primitive_debit {L : Ledger} {Free : NCode → Prop}
    (quiet : NoQueue L) (control : Control L Free) (events : Events L)
    (interp : Moves.NInterp) (m : NativeMachine) (fiber : NFiber) (yielding : Bool)
    (inputs : PrimitiveInputs L Free interp m fiber yielding) :
    L.IterDebit m fiber (evaluatePrim interp m fiber yielding) := by
  have answer (next : NativeMachine) (code : NCode) (outcome : Outcome EffName EffThunk Val Err Defect FiberId Ann)
      (commands : List Native.NCmd) (rows : next.fibers = m.fibers) (trace : next.trace = m.trace)
      (bounded : L.state next.state + L.fiber {fiber with frame.current := code} ≤ L.state m.state + L.fiber fiber) :
      L.IterDebit m fiber ⟨next, {fiber with frame.current := code}, yielding, outcome, commands, []⟩ := by
    apply quiet.local_debit m fiber _ rows
    simp only [PlaceLedger.spent, PlaceLedger.issued, trace]
    dsimp only at bounded ⊢
    omega
  have parked (old : NFiber) (pending : Pending EffName Val Err Defect FiberId Ann)
      (dispatcher : Dispatcher EffName EffThunk Val Err Defect FiberId Ann) :
      L.fiber ({old with dispatcher := dispatcher}.park pending) ≤ L.fiber old :=
    control.metadata old _ rfl rfl rfl (Nat.le_refl _)
  generalize evaluated : evaluatePrim interp m fiber yielding = next
  have actual := Moves.evaluatePrim_producer interp m fiber yielding
  rw [evaluated] at actual
  cases actual with
  | step unparked ordinary noSync noSuccess noFailure noYield noAsync => exact inputs.step
  | finalizer exit selected => exact inputs.finalizer exit
  | action thunk action selected park found => exact inputs.action thunk action selected found
  | countdownPark targets next returned parked edits park counted => exact inputs.countdown targets next returned parked edits park counted
  | racePark race park => exact inputs.race race park
  | sync thunk state value selected park produced =>
    exact answer {m with state} (.success value) .answered [.drainDue] rfl rfl (inputs.sync thunk state value selected produced)
  | fallback thunk selected park missing =>
    exact answer m (.success (interp.syncValue thunk)) .answered [] rfl rfl
      (Nat.add_le_add_left (control.replace fiber _ (inputs.success _)) _)
  | rejectedPark cause park =>
    exact answer m (.failure cause) .continue_ [] rfl rfl
      (Nat.add_le_add_left (control.replace fiber _ (inputs.failure _)) _)
  | joinExited target mode other exit park found exited =>
    exact answer m (interp.exitValue exit mode) .continue_ [] rfl rfl
      (Nat.add_le_add_left (control.replace fiber _ (inputs.exitValue exit mode)) _)
  | asyncImmediate register signal cancel state code selected produced =>
    exact answer {m with state, nextToken := m.nextToken + 1} code .continue_ [.drainDue] rfl rfl
      (Nat.add_le_add (inputs.registerState register signal cancel state _ selected produced)
        (control.replace fiber code (inputs.registerReply register signal cancel state code selected produced)))
  | joinMissing target mode park missing => exact Nat.le_refl _
  | yieldNow priority selected =>
    apply quiet.local_debit m fiber _ rfl
    have dropped := control.replace fiber (.success interp.voidValue) (inputs.success _)
    have returned := parked {fiber with frame.current := .success interp.voidValue}
      ⟨m.nextToken, none, [], [], .void, false⟩
      (fiber.dispatcher.enqueue priority (.resume fiber.id m.nextToken (.success interp.voidValue)))
    have charged := events.administrative (.parkedOn fiber.id m.nextToken) rfl
    simp only [PlaceLedger.spent, PlaceLedger.issued]
    dsimp only [RunFiber.park, RunMachine.emit, RunMachine.arm]
    simp only [List.isEmpty_cons, Bool.false_eq_true, if_false, List.map_append, List.sum_append, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero]
    dsimp only [RunFiber.park] at returned dropped
    omega
  | asyncParked register signal cancel state selected produced =>
    apply quiet.local_debit m fiber _ rfl
    have stored := inputs.registerState register signal cancel state none selected produced
    have charged := events.administrative (.parkedOn fiber.id m.nextToken) rfl
    dsimp only
    split
    · have pushed := inputs.cancel register signal cancel state selected produced
      have returned := parked {fiber with frame.stack := .asyncFinalizer (interp.cancelName (cancel.getD interp.abortName) fiber.id m.nextToken) :: fiber.frame.stack}
        ⟨m.nextToken, none, [], [], .void, false⟩ fiber.dispatcher
      simp only [PlaceLedger.spent, PlaceLedger.issued]
      dsimp only [RunFiber.park, RunMachine.emit, RunMachine.arm]
      simp only [List.isEmpty_cons, Bool.false_eq_true, if_false, List.map_append, List.sum_append, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero]
      dsimp only [RunFiber.park] at returned pushed
      omega
    · have returned := parked fiber ⟨m.nextToken, none, [], [], .void, false⟩ fiber.dispatcher
      simp only [PlaceLedger.spent, PlaceLedger.issued]
      dsimp only [RunFiber.park, RunMachine.emit, RunMachine.arm]
      simp only [List.isEmpty_cons, Bool.false_eq_true, if_false, List.map_append, List.sum_append, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero]
      dsimp only [RunFiber.park] at returned
      omega
  | joinWaiting target mode other park found live =>
    apply quiet.local_debit m fiber _ rfl
    have pushed := inputs.joinCancel
    have returned := parked {fiber with frame.stack := .asyncFinalizer (interp.cancelName interp.parkCancelName fiber.id m.nextToken) :: fiber.frame.stack}
      ⟨m.nextToken, none, [], [], .void, false⟩ fiber.dispatcher
    have charged := events.administrative (.parkedOn fiber.id m.nextToken) rfl
    simp only [PlaceLedger.spent, PlaceLedger.issued]
    dsimp only [RunFiber.park, RunMachine.emit, RunMachine.arm]
    simp only [List.isEmpty_cons, Bool.false_eq_true, if_false, List.map_append, List.sum_append, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero]
    dsimp only [RunFiber.park] at returned pushed
    omega

end Effect4.Program.PlaceFunding
