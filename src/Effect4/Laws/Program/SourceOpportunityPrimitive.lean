import Effect4.Laws.Program.SourceOpportunityNative
import Effect4.Laws.Program.PrimitiveProducer

/-!
Concept: scope-lifetime-finalization R11.
Consumer: complete native source opportunity history for Atomic and Workers.
The laws compose the actual frame and native action projections.
-/
set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace Effect4.Program.SourceScope.Opportunities
open Effect4 Effect4.Machine Effect4.Program

/-- A machine edit which keeps stored frames lifts an acting-frame debit.
Consumer: primitive frame delegation and finalizer invocation. -/
theorem same_rows_debit (root : NativeEff) (q : List Nat) (m : NativeMachine)
    (fiber : SourceFiber) (next : SourceIteration) (rows : next.machine.fibers = m.fibers)
    (localBound : recorded q next.machine + frame root q next.fiber.frame ≤
      recorded q m + frame root q fiber.frame) : Debit root q m fiber next := by
  have unchanged : outside root q fiber.id next.machine = outside root q fiber.id m := by
    unfold outside
    rw [rows]
  unfold Debit
  rw [unchanged]
  omega

/-- Actual frame delegation includes its trace before the owner row is installed.
Consumer: complete primitive evaluation. -/
theorem frame_primitive_debit (root : NativeEff) (q : List Nat) (fragment : Fragment root)
    (clearFin : ClearFinalizers root q) (clearLoop : ClearLoops root q) (table : RowTable)
    (m : NativeMachine) (fiber : SourceFiber) (yielding : Bool) (held : FrameAt root fiber.frame) :
    Debit root q m fiber (evaluatePrim.stepFrame (interpAt root m.completedExits table) m fiber yielding) :=
  same_rows_debit root q m fiber _ (step_frame_table root m.completedExits table m fiber yielding).1
    (step_frame_debit root q fragment clearFin clearLoop m.completedExits table m fiber yielding held)

/-- Finalizer delegation retains the stored row table until actual settlement.
Consumer: complete primitive evaluation. -/
theorem finalizer_rows (root : NativeEff) (table : RowTable) (m : NativeMachine)
    (fiber : SourceFiber) (yielding : Bool) (exit : ExitV) :
    (evaluatePrim.finalizerOr (interpAt root m.completedExits table) m fiber yielding exit).machine.fibers = m.fibers := by
  cases exit <;> unfold evaluatePrim.finalizerOr <;> dsimp only
  all_goals split
  all_goals repeat' split
  all_goals aesop (add safe apply [((step_frame_table root m.completedExits table m fiber yielding).1)])

/-- Actual finalizer invocation includes only existing saved opportunities.
Consumer: complete primitive evaluation. -/
theorem finalizer_primitive_debit (root : NativeEff) (q : List Nat) (fragment : Fragment root)
    (clearFin : ClearFinalizers root q) (clearLoop : ClearLoops root q) (table : RowTable)
    (m : NativeMachine) (fiber : SourceFiber) (yielding : Bool) (exit : ExitV)
    (held : FrameAt root fiber.frame) :
    Debit root q m fiber (evaluatePrim.finalizerOr (interpAt root m.completedExits table) m fiber yielding exit) :=
  same_rows_debit root q m fiber _ (finalizer_rows root table m fiber yielding exit)
    (finalizer_debit root q fragment clearFin clearLoop m.completedExits table m fiber yielding exit held)

/-- Actual immediate asynchronous completions have no source opportunity.
Consumer: native Async primitive evaluation. -/
theorem register_reply_zero (root : NativeEff) (q : List Nat) (table : RowTable)
    (m : NativeMachine) (callback : EffName) (id : FiberId) (token : Nat) (code : NCode)
    (produced : ((interpAt root m.completedExits table).registerAsync callback id token m.state).2 = some code) :
    current root q code = 0 := by
  cases callback
  case registerAwait cell =>
    obtain ⟨answer, _, result⟩ := Option.map_eq_some_iff.mp produced
    rw [← result]
    exact terminal_reply_zero root q _ (completion_reply answer)
  case store callback =>
    cases callback
    case registerAwait cell =>
      obtain ⟨answer, _, result⟩ := Option.map_eq_some_iff.mp produced
      rw [← result]
      exact terminal_reply_zero root q _ (completion_reply answer)
    all_goals cases produced
  all_goals cases produced

/-- A race-free source history contains no runtime race row.
Consumer: actual race-park and race command exclusion in the application helper. -/
theorem races_nil (root : NativeEff) (m : NativeMachine) (source : RaceFreeSource root)
    (held : ConfigurationAt root m) : m.races = [] := by
  cases rows : m.races with
  | nil => rfl
  | cons race rest =>
    have member : race ∈ m.races := by rw [rows]; exact .head _
    exact False.elim (source.not_race (held.races race member).2)

/-- Actual native cancellation producers carry no source callback opportunity.
Consumer: Async cancel-frame installation in the primitive evaluator. -/
theorem async_cancel_zero (q : List Nat) (callback : EffName) (held : AsyncCancelAt callback) :
    name q callback = 0 := by
  cases callback
  case cancelAwait => rfl
  case store callback =>
    cases callback
    case cancelAwait | cancelSleep => rfl
    all_goals cases held
  all_goals cases held

/-- Owned native Async code has no active selected source opportunity.
Consumer: immediate answers and parked cancellation frames. -/
theorem async_current_zero (root : NativeEff) (q : List Nat) (register : EffName)
    (signal : Bool) (cancel : Option EffName) (held : CodeAt root (.async register signal cancel)) :
    current root q (.async register signal cancel) = 0 := by
  cases cancel with
  | none => rfl
  | some callback =>
    exact async_cancel_zero q callback (held.2 callback rfl).2

/-- An immediate native answer retains saved opportunities and the existing trace.
Consumer: Async, refused waits, Sync, and completed joins. -/
theorem answer_debit (root : NativeEff) (q : List Nat) (m next : NativeMachine)
    (fiber : SourceFiber) (yielding : Bool) (code : NCode)
    (outcome : Outcome EffName EffThunk Val Err Defect FiberId Ann) (commands : List SourceCommand)
    (rows : next.fibers = m.fibers) (trace : next.trace = m.trace)
    (zero : current root q code = 0) :
    Debit root q m fiber ⟨next, {fiber with frame := {fiber.frame with current := code}},
      yielding, outcome, commands, []⟩ := by
  apply same_rows_debit root q m fiber _ rows
  unfold recorded
  rw [trace]
  simp only [frame, zero, Nat.zero_add]
  omega

/-- Native joins deliver only an exit value or cause.
Consumer: completed-join primitive evaluation. -/
theorem exit_answer_zero (root : NativeEff) (q : List Nat) (table : RowTable)
    (m : NativeMachine) (exit : ExitV) (mode : Supervision.ObserverMode) :
    current root q ((interpAt root m.completedExits table).exitValue exit mode) = 0 := by
  cases mode <;> cases exit <;> rfl

/-- Excluding source races leaves race registration stuck without a frame edit.
Consumer: the application's complete primitive debit. -/
theorem register_race_debit (root : NativeEff) (q : List Nat) (m : NativeMachine)
    (fiber : SourceFiber) (yielding : Bool) (race : Nat) (empty : m.races = []) :
    Debit root q m fiber (registerRace m fiber yielding race) := by
  unfold registerRace RunMachine.race?
  rw [empty]
  exact Nat.le_refl _

/-- Actual primitive evaluation spends its acting frame and preserves off-owner reservations.
The source restrictions are discharged by the unchanged application programs.
Consumer: native evaluator settlement and the source-use history invariant. -/
theorem primitive_debit (root : NativeEff) (q : List Nat) (fragment : Fragment root)
    (clearFin : ClearFinalizers root q) (clearLoop : ClearLoops root q) (table : RowTable)
    (m : NativeMachine) (fiber : SourceFiber) (yielding : Bool)
    (sequential : SequentialSource root) (raceFree : RaceFreeSource root)
    (owned : ConfigurationAt root m) (held : FiberAt root fiber)
    (unique : (m.fibers.map (fun fiber => fiber.id)).Nodup) :
    Debit root q m fiber (evaluatePrim (interpAt root m.completedExits table) m fiber yielding) := by
  have actionDebit (suspended : EffThunk) (next : NAction)
      (selected : fiber.frame.current = .withFiber suspended)
      (produced : (interpAt root m.completedExits table).withFiberOf suspended = some next) :
      Debit root q m fiber (evaluatePrim.withFiber (interpAt root m.completedExits table) m fiber yielding next) := by
    have thunkOwned := held.frame.1
    rw [selected] at thunkOwned
    have nextOwned := interp_action_at root fragment m.completedExits table suspended next thunkOwned produced
    have carried := interp_action_le root q clearFin m.completedExits table suspended next thunkOwned produced
    exact native_action_debit root q table m fiber yielding next nextOwned sequential raceFree clearFin
      owned.scopes unique (by simpa only [selected, current, cata_prim] using carried)
  have cancellation (register : EffName) (signal : Bool) (cancel : Option EffName)
      (selected : fiber.frame.current = .async register signal cancel) :
      ∀ callback ∈ cancel, name q callback = 0 := by
    have callbacks := held.frame.1
    rw [selected] at callbacks
    exact fun callback member => async_cancel_zero q callback (callbacks.2 callback member).2
  have noRaces := races_nil root m raceFree owned
  have frames := frame_primitive_debit root q fragment clearFin clearLoop table m fiber yielding held.frame
  have finalizers (exit : ExitV) := finalizer_primitive_debit root q fragment clearFin clearLoop table m fiber yielding exit held.frame
  generalize evaluated : evaluatePrim (interpAt root m.completedExits table) m fiber yielding = next
  have actual := Moves.evaluatePrim_producer (interpAt root m.completedExits table) m fiber yielding
  rw [evaluated] at actual
  cases actual with
  | yieldNow priority selected =>
    unfold Debit
    simp only [recorded_emit, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, runEvent, Nat.add_zero]
    change recorded q m + outside root q fiber.id m + frame root q _ ≤ _
    dsimp only [RunFiber.park]
    simp only [frame, current, cata_prim, Nat.zero_add]
    omega
  | asyncParked register signal cancel state selected produced =>
    have empty := cancellation register signal cancel selected
    have cancellationZero : name q ((interpAt root m.completedExits table).cancelName
        (cancel.getD (interpAt root m.completedExits table).abortName) fiber.id m.nextToken) = 0 := by
      cases cancel with
      | none => rfl
      | some callback => exact empty callback rfl
    unfold Debit
    simp only [recorded_emit, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, runEvent, Nat.add_zero]
    change recorded q m + outside root q fiber.id m + frame root q _ ≤ _
    dsimp only [RunFiber.park]
    split
    · simp only [frame, List.map_cons, List.sum_cons, saved, cancellationZero, Nat.zero_add]
      exact Nat.le_refl _
    · exact Nat.le_refl _
  | countdownPark targets machine returned parked edits selected counted =>
    have debit := countdown_plan_debit root q table m fiber yielding targets .exitsValue false trivial
    rw [counted] at debit
    exact debit
  | joinWaiting target mode targetFiber park found noExit =>
    have cancelZero : name q ((interpAt root m.completedExits table).cancelName
        (interpAt root m.completedExits table).parkCancelName fiber.id m.nextToken) = 0 := rfl
    unfold Debit
    simp only [recorded_emit, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, runEvent, Nat.add_zero]
    change recorded q m + outside root q fiber.id m + frame root q _ ≤ _
    dsimp only [RunFiber.park]
    simp only [frame, List.map_cons, List.sum_cons, saved, cancelZero, Nat.zero_add]
    exact Nat.le_refl _
  | asyncImmediate register signal cancel state program selected produced =>
    have zero := register_reply_zero root q table m register fiber.id m.nextToken program
      (congrArg Prod.snd produced)
    exact answer_debit root q m {m with state, nextToken := m.nextToken + 1}
      fiber yielding program .continue_ [.drainDue] rfl rfl zero
  | racePark race park =>
    exact register_race_debit root q m fiber yielding race noRaces
  | joinExited target mode targetFiber exit park found finished =>
    exact answer_debit root q m m fiber yielding _ .continue_ [] rfl rfl
      (exit_answer_zero root q table m exit mode)
  | sync thunk state value selected park produced =>
    exact answer_debit root q m {m with state} fiber yielding (.success value) .answered [.drainDue] rfl rfl rfl
  | step unparked ordinary noSync noSuccess noFailure noYield noAsync => exact frames
  | finalizer exit selected => exact finalizers exit
  | action thunk next selected park produced => exact actionDebit thunk next selected produced
  | fallback thunk selected park missing =>
    exact answer_debit root q m m fiber yielding _ .answered [] rfl rfl rfl
  | rejectedPark cause park =>
    exact answer_debit root q m m fiber yielding _ .continue_ [] rfl rfl rfl
  | joinMissing target mode park missing => exact Nat.le_refl _

/-- A primitive exit does not edit the stored fiber rows before settlement.
Consumer: scoped-exit and native evaluator debit. -/
theorem exit_primitive_rows (root : NativeEff) (table : RowTable)
    (m : NativeMachine) (fiber : SourceFiber) (yielding : Bool) (exit : ExitV)
    (selected : fiber.frame.current = .ofExit exit) :
    (evaluatePrim (interpAt root m.completedExits table) m fiber yielding).machine.fibers = m.fibers := by
  cases exit
  all_goals unfold evaluatePrim
  all_goals simp only [selected, Prim.ofExit, interpAt, interpOf]
  all_goals exact finalizer_rows root table m fiber yielding _

/-- Scoped cleanup retains stored rows while it delivers the acting frame's exit.
Consumer: the actual complete native evaluator debit. -/
theorem exit_scoped_rows (root : NativeEff) (m : NativeMachine)
    (fiber : SourceFiber) (yielding : Bool) (exit : ExitV)
    (selected : fiber.frame.current = .ofExit exit) :
    (exitScoped root m fiber yielding exit).machine.fibers = m.fibers := by
  have fallback := exit_primitive_rows root [] m fiber yielding exit selected
  cases exit <;> unfold exitScoped <;> dsimp only
  all_goals split
  all_goals repeat' split
  all_goals aesop

/-- The actual native evaluator spends only existing source opportunities.
Consumer: complete command settlement and application source-use history. -/
theorem native_debit (root : NativeEff) (q : List Nat) (fragment : Fragment root)
    (clearFin : ClearFinalizers root q) (clearLoop : ClearLoops root q) (table : RowTable)
    (m : NativeMachine) (fiber : SourceFiber) (yielding : Bool)
    (sequential : SequentialSource root) (raceFree : RaceFreeSource root)
    (owned : ConfigurationAt root m) (held : FiberAt root fiber)
    (unique : (m.fibers.map (fun fiber => fiber.id)).Nodup) :
    Debit root q m fiber (evaluateNative root m fiber yielding table) := by
  have primitive := primitive_debit root q fragment clearFin clearLoop table m fiber yielding
    sequential raceFree owned held unique
  have scopedExit (exit : ExitV) (selected : fiber.frame.current = .ofExit exit) :
      Debit root q m fiber (exitScoped root m fiber yielding exit) :=
    same_rows_debit root q m fiber _ (exit_scoped_rows root m fiber yielding exit selected)
      (exit_scoped_debit root q fragment clearFin clearLoop m fiber yielding exit owned held.frame selected)
  unfold evaluateNative
  split
  · rename_i point selected
    split
    · rename_i body found
      exact same_rows_debit root q m fiber _ rfl
        (enter_scoped_debit root q point body found m fiber yielding selected)
    · exact primitive
  · exact scopedExit _ (by assumption)
  · exact scopedExit _ (by assumption)
  · exact primitive


end Effect4.Program.SourceScope.Opportunities
