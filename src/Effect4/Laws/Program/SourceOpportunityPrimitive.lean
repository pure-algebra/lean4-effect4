import Effect4.Laws.Program.SourceOpportunityNative
import Effect4.Laws.Program.PlaceFunding.Primitive
import Effect4.Laws.Program.PlaceFunding.Actions
import Effect4.Laws.Program.PlaceLedgerConnect

/-!
Concept: scope-lifetime-finalization R11.
Consumer: complete native source opportunity history for Atomic and Workers.
The laws compose the actual frame and native action projections.
-/
set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace Effect4.Program.SourceScope.Opportunities
open Effect4 Effect4.Machine Effect4.Program

/-- Source reservations instantiate shared row control.
Consumer: the existing primitive source debit under R11. -/
theorem source_control (root : NativeEff) (q : List Nat) :
    PlaceFunding.Control (PlaceLedgerConnect.source root q) (fun code => current root q code = 0) where
  metadata := by
    intro old next _ active saved _
    change frame root q next.frame ≤ frame root q old.frame
    simp only [frame, active, saved, Nat.le_refl]
  interruption := Machine.WriterWeights.interrupt_weight_le (weightModel root q)
  replace := by
    intro fiber code free
    change frame root q {fiber.frame with current := code} ≤ frame root q fiber.frame
    simp only [frame, free, Nat.zero_add]
    omega
  entry := by
    intro owner code flag budget context free
    simp only [PlaceLedgerConnect.source, RunFiber.make, FrameFiber.start, frame, free,
      List.map_nil, List.sum_nil, Nat.add_zero]
  clear := by
    intro fiber
    change frame root q {fiber.frame with stack := []} ≤ frame root q fiber.frame
    simp only [frame, List.map_nil, List.sum_nil, Nat.add_zero]
    omega


/-- Source accounting assigns zero weight to unrelated queued places.
Consumer: primitive and admitted-history place funding. -/
theorem source_no_queue (root : NativeEff) (q : List Nat) :
    PlaceFunding.NoQueue (PlaceLedgerConnect.source root q) :=
  ⟨fun _ => rfl, fun _ => rfl, fun _ => rfl⟩

/-- The original local source observation is the shared place reading.
Consumer: primitive interpretation and frame delegation. -/
theorem source_debit_iff (root : NativeEff) (q : List Nat) (m : NativeMachine)
    (fiber : SourceFiber) (next : SourceIteration) :
    (PlaceLedgerConnect.source root q).IterDebit m fiber next ↔ Debit root q m fiber next := by
  simp only [PlaceLedger.IterDebit, PlaceLedger.outside, PlaceLedger.spent, PlaceLedger.issued,
    PlaceLedgerConnect.source, PlaceLedger.zero_sum, Nat.zero_add, Nat.add_zero, FiberSum.outside,
    outside, recorded, Debit]

/-- Administrative events consume no selected source registration.
Consumer: primitive place accounting. -/
theorem source_events (root : NativeEff) (q : List Nat) :
    PlaceFunding.Events (PlaceLedgerConnect.source root q) where
  administrative := by
    intro recordedEvent allowed
    change runEvent q recordedEvent ≤ 0
    fun_cases runEvent q recordedEvent
    · cases allowed
    · exact Nat.le_refl _

/-- A machine edit which keeps stored frames lifts an acting-frame debit.
Consumer: primitive frame delegation and finalizer invocation. -/
theorem same_rows_debit (root : NativeEff) (q : List Nat) (m : NativeMachine)
    (fiber : SourceFiber) (next : SourceIteration) (rows : next.machine.fibers = m.fibers)
    (localBound : recorded q next.machine + frame root q next.fiber.frame ≤
      recorded q m + frame root q fiber.frame) : Debit root q m fiber next := by
  have quiet := source_no_queue root q
  have bounded : (PlaceLedgerConnect.source root q).spent next.machine +
      (PlaceLedgerConnect.source root q).state next.machine.state +
      (PlaceLedgerConnect.source root q).fiber next.fiber +
      (PlaceLedgerConnect.source root q).issued m ≤
        (PlaceLedgerConnect.source root q).spent m +
        (PlaceLedgerConnect.source root q).state m.state +
        (PlaceLedgerConnect.source root q).fiber fiber +
        (PlaceLedgerConnect.source root q).issued next.machine := by
    simpa only [PlaceLedgerConnect.source, PlaceLedger.spent, PlaceLedger.issued,
      PlaceLedger.zero_sum, Nat.add_zero, recorded] using localBound
  have debit := quiet.local_debit m fiber next rows bounded
  simpa only [PlaceLedger.IterDebit, PlaceLedger.outside, PlaceLedger.spent, PlaceLedger.issued,
    PlaceLedgerConnect.source, PlaceLedger.zero_sum, Nat.zero_add, Nat.add_zero, FiberSum.outside,
    outside, recorded, Debit] using debit

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
    current root q code = 0 :=
  terminal_reply_zero root q code
    (register_reply root m.completedExits table callback id token m.state code produced)

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

/-- The source weighs every code the native action arms install at zero.
Consumers: `native_action_debit` and the countdown arm of `primitive_debit`. -/
theorem source_action_inputs (root : NativeEff) (q : List Nat) (completed : List (FiberId × ExitV))
    (table : RowTable) :
    Machine.WriterWeights.ActionInputs (weightModel root q) (interpAt root completed table) :=
  ⟨fun _ => rfl, fun _ => rfl, fun _ _ => rfl, fun _ => rfl, fun _ _ => rfl, fun _ => rfl⟩

/-- Every native action spends only the source reservation of its actual producer: the
ledger-generic `PlaceFunding.action_debit` at the source weights. The sequential source excludes a
parallel close; a source-owned close installs no selected opportunity (`close_scope_zero`).
The race-freedom and distinct-id premises are no longer read.
Consumer: complete native evaluator and unchanged Workers/Atomic history bounds. -/
theorem native_action_debit (root : NativeEff) (q : List Nat) (table : RowTable)
    (m : NativeMachine) (fiber : SourceFiber) (yielding : Bool) (selected : NAction)
    (source : ActionAt root selected) (sequential : SequentialSource root)
    (_raceFree : RaceFreeSource root) (clear : ClearFinalizers root q)
    (scopes : ScopesAt root m.state.scopes)
    (_unique : (m.fibers.map (fun fiber => fiber.id)).Nodup)
    (carried : action root q selected ≤ current root q fiber.frame.current) :
    Debit root q m fiber (evaluatePrim.withFiber (interpAt root m.completedExits table) m fiber yielding selected) := by
  have inputs := source_action_inputs root q m.completedExits table
  have launched : Machine.WriterWeights.Carried (weightModel root q)
      (interpAt root m.completedExits table) m fiber selected := by
    cases selected
    case fork body options site => exact carried
    case forkIn body options scope site => exact carried
    case forkScoped body options site => exact carried
    case setInterruptible body flag => exact carried
    case closeScope scope exit =>
      intro state program closed
      exact close_scope_zero root q table m.completedExits scope exit _ fiber.id clear m.state state
        scopes program closed
    case closePar finalizers => exact sequential.not_parallel source.2
    all_goals exact True.intro
  exact (source_debit_iff root q m fiber _).mp
    (PlaceFunding.action_debit (source_no_queue root q) (source_events root q) (weightModel root q)
      (fun _ => rfl) _ inputs m fiber yielding selected launched (Nat.le_refl _))

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
  have asLedger (next : SourceIteration) (debit : Debit root q m fiber next) :
      (PlaceLedgerConnect.source root q).IterDebit m fiber next :=
    (source_debit_iff root q m fiber next).mpr debit
  have quiet := source_no_queue root q
  have inputs : PlaceFunding.PrimitiveInputs (PlaceLedgerConnect.source root q)
      (fun code => current root q code = 0) (interpAt root m.completedExits table) m fiber yielding := {
    success := fun _ => rfl
    failure := fun _ => rfl
    exitValue := exit_answer_zero root q table m
    step := asLedger _ (frame_primitive_debit root q fragment clearFin clearLoop table m fiber yielding held.frame)
    finalizer := fun exit => asLedger _ (finalizer_primitive_debit root q fragment clearFin clearLoop table m fiber yielding exit held.frame)
    action := fun suspended next selected produced => asLedger _ (actionDebit suspended next selected produced)
    sync := by
      intro suspended state value _ _
      simp only [PlaceLedgerConnect.source, frame, current, cata_prim, Nat.zero_add]
      omega
    registerState := fun _ _ _ _ _ _ _ => Nat.le_refl _
    registerReply := fun register _ _ _ program _ produced =>
      register_reply_zero root q table m register fiber.id m.nextToken program (congrArg Prod.snd produced)
    cancel := by
      intro register signal cancel state selected _
      have empty := cancellation register signal cancel selected
      have zero : name q ((interpAt root m.completedExits table).cancelName
          (cancel.getD (interpAt root m.completedExits table).abortName) fiber.id m.nextToken) = 0 := by
        cases cancel with
        | none => rfl
        | some callback => exact empty callback rfl
      change frame root q {fiber.frame with stack := .asyncFinalizer ((interpAt root m.completedExits table).cancelName
        (cancel.getD (interpAt root m.completedExits table).abortName) fiber.id m.nextToken) :: fiber.frame.stack} ≤ frame root q fiber.frame
      simp only [frame, List.map_cons, List.sum_cons, saved, zero, Nat.zero_add, Nat.le_refl]
    joinCancel := by
      change frame root q {fiber.frame with stack := .asyncFinalizer ((interpAt root m.completedExits table).cancelName
        (interpAt root m.completedExits table).parkCancelName fiber.id m.nextToken) :: fiber.frame.stack} ≤ frame root q fiber.frame
      simp only [frame, List.map_cons, List.sum_cons, saved, interpAt, interpOf, name, Nat.zero_add, Nat.le_refl]
    countdown := by
      intro targets machine returned parked edits _ counted
      have debit := PlaceFunding.countdown_debit quiet (source_events root q) (weightModel root q)
        (fun _ => rfl) _ (source_action_inputs root q m.completedExits table) m fiber yielding targets
        .exitsValue false (fun _ => rfl)
      rw [counted] at debit
      exact debit
    race := fun race _ => asLedger _ (register_race_debit root q m fiber yielding race (races_nil root m raceFree owned)) }
  exact (source_debit_iff root q m fiber _).mp
    (PlaceFunding.primitive_debit quiet (source_control root q) (source_events root q)
      (interpAt root m.completedExits table) m fiber yielding inputs)

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
