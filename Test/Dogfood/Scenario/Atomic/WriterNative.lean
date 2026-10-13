import Test.Dogfood.Scenario.Atomic.WriterMachine
import Test.Dogfood.Scenario.Atomic.WriterSync
import Test.Dogfood.Scenario.SourceOpportunity
import Effect4.Laws.Machine.WriterActions
import Effect4.Laws.Program.SourceOpportunityExecution

/-!
# The Atomic cleanup writer's native evaluator debit

Concept: scope-lifetime-finalization, R11, the original `Atomic.cleans_once` claim.
Question: the evaluator debit of the writer ledger `WriterMachine.ledger`, the premise
`PlaceFunding.Evaluation` of `PlaceFunding.Local`; consumer `WriterHistory.evaluation`.
The action arms come from the weight-generic `WriterWeights.action_bound` and the primitive arms
from `PlaceFunding.primitive_debit`. This module supplies the writer's weights of the installed
codes, the scoped entry and exit, and the forced-yield iteration.
Reach: the built shop, every request identity, every machine with source ownership, every fiber
and latch. It establishes no finalizer progress, release order or host observation.
-/
set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace Test.Dogfood.Scenario.Atomic.WriterNative
open Effect4 Effect4.Machine Effect4.Program Effect4.Program.SourceScope Effect4.Laws.Auto
open WriterPhase

/-- Code that carries no active note reservation of request `id`. -/
abbrev Free (id : Nat) (code : NCode) : Prop := WriterPhase.current id code = 0

/-- The writer ledger weighs no race, pending command or detached task. -/
theorem no_queue (id : Nat) : PlaceFunding.NoQueue (WriterMachine.ledger id) :=
  ⟨fun _ => rfl, fun _ => rfl, fun _ => rfl⟩

/-- The writer ledger consumes no event: a recorded start only issues credit. -/
theorem events (id : Nat) : PlaceFunding.Events (WriterMachine.ledger id) :=
  ⟨fun _ _ => Nat.zero_le _⟩

/-- A fiber row's metadata edit, interruption, replacement by free code, birth with free code
and stack clearing keep or lower its writer reservations. -/
theorem control (id : Nat) : PlaceFunding.Control (WriterMachine.ledger id) (Free id) where
  metadata := by
    intro old next _ active saved _
    change WriterPhase.frame id next.frame ≤ WriterPhase.frame id old.frame
    simp only [WriterPhase.frame, active, saved, Nat.le_refl]
  interruption := Machine.WriterWeights.interrupt_weight_le (WriterPhase.model id)
  replace := by
    intro fiber code free
    change WriterPhase.frame id {fiber.frame with current := code} ≤ WriterPhase.frame id fiber.frame
    simp only [WriterPhase.frame, free, Nat.zero_add]
    omega
  entry := by
    intro owner code flag budget context free
    simp only [WriterMachine.ledger, RunFiber.make, FrameFiber.start, WriterPhase.frame, free,
      List.map_nil, List.sum_nil, Nat.add_zero]
  clear := by
    intro fiber
    change WriterPhase.frame id {fiber.frame with stack := []} ≤ WriterPhase.frame id fiber.frame
    simp only [WriterPhase.frame, List.map_nil, List.sum_nil, Nat.add_zero]
    omega

/-- A native reply carries no note reservation. -/
theorem terminal_zero (id : Nat) (code : NCode) (reply : TerminalReply code) : Free id code := by
  cases reply <;> rfl

/-- The built shop is sequential and authors no race. -/
theorem restricted (built : Api.Built) (admitted : Api.Author.build (shop .none) = .ok built) :
    SequentialSource built.program ∧ RaceFreeSource built.program := by
  have program : Store.shopProgram = some built.program := by
    unfold Store.shopProgram
    rw [(Api.Author.build_retains admitted).1]
    rfl
  have census := SourceOpportunity.atomic_control_census
  rw [program] at census
  exact Bool.and_eq_true_iff.mp (Option.some.inj census)

/-! ## The writer debit as the shared ledger's iteration debit -/

/-- The writer's local debit is the shared ledger's iteration debit. -/
theorem debit_ledger (id : Nat) (m : NativeMachine) (fiber : SourceFiber) (next : SourceIteration)
    (debit : WriterMachine.Debit id m fiber next) : (WriterMachine.ledger id).IterDebit m fiber next := by
  simpa only [PlaceLedger.IterDebit, PlaceLedger.spent, PlaceLedger.issued, PlaceLedger.outside,
    WriterMachine.ledger, PlaceLedger.zero_sum, List.map_nil, List.sum_nil, Nat.zero_add,
    Nat.add_zero, FinalizerCredits.indicator_sum, WriterMachine.Debit, WriterMachine.outside,
    Machine.WriterWeights.outside, FiberSum.outside, FiberSum.total, WriterMachine.issued,
    Machine.FrameWeights.frame, model, frame] using debit

/-- A local frame bound with an unchanged heap and an extended trace is a writer debit. -/
theorem local_debit (id : Nat) (m : NativeMachine) (fiber : SourceFiber) (next : SourceIteration)
    (refs : next.machine.state.refs = m.state.refs) (extended : RunMachine.Extends m next.machine)
    (bounded : Machine.WriterWeights.LocalBound (model id) m fiber next) :
    WriterMachine.Debit id m fiber next := by
  have recorded := WriterMachine.issued_mono id m next.machine extended
  unfold Machine.WriterWeights.LocalBound at bounded
  change WriterMachine.outside id fiber.id next.machine + frame id next.fiber.frame ≤
    WriterMachine.outside id fiber.id m + frame id fiber.frame at bounded
  unfold WriterMachine.Debit
  rw [refs]
  omega

/-- An evaluation that keeps the stored rows and the heap owes only its acting frame's bound. -/
theorem rows_debit (id : Nat) (m : NativeMachine) (fiber : SourceFiber) (next : SourceIteration)
    (rows : next.machine.fibers = m.fibers) (refs : next.machine.state.refs = m.state.refs)
    (extended : RunMachine.Extends m next.machine)
    (bounded : frame id next.fiber.frame ≤ frame id fiber.frame) :
    (WriterMachine.ledger id).IterDebit m fiber next :=
  debit_ledger id m fiber next (local_debit id m fiber next refs extended
    (Machine.WriterWeights.rows_bound (model id) m fiber next rows bounded))

/-- Emitting events extends the trace. -/
theorem emit_extends (m : NativeMachine) (events : List Moves.REvent) :
    RunMachine.Extends m (m.emit events) := by
  unfold RunMachine.Extends
  rw [RunMachine.emit_trace]
  exact List.prefix_append _ _

/-- A popped frame with a zero-weight answer keeps no more than the old frame. -/
theorem pop_frame_le (id : Nat) (fiber : FrameFiber EffName EffThunk Val Err Defect FiberId Ann)
    (demand : Effect4.Arm) (skip : Bool) (cause : Option CauseV) (code : NCode)
    (zero : current id code = 0) :
    frame id {(fiber.getCont demand skip cause).fiber with current := code} ≤ frame id fiber := by
  have bound := pop_bound id fiber demand skip cause
  simp only [frame, zero, Nat.zero_add]
  omega

/-! ## The action arms -/

/-- The writer weighs every code the native action arms install at zero. -/
theorem action_inputs (id : Nat) (root : NativeEff) (view : List (FiberId × ExitV)) (table : RowTable) :
    Machine.WriterWeights.ActionInputs (model id) (interpAt root view table) :=
  ⟨fun _ => rfl, fun _ => rfl, fun _ _ => rfl, fun _ => rfl, fun _ _ => rfl, fun _ => rfl⟩

/-- A scope close installs a voided finalizer program or a stored walk, with no note reservation. -/
theorem close_zero (id : Nat) (scope : Nat) (exit : ExitV) (flag : Bool) (state next : Stores)
    (code : Program) (closed : storesCloseScope scope exit flag state = some (next, some code)) :
    current id (embed code) = 0 := by
  unfold storesCloseScope at closed
  cases snapshot : scopeCloseSnapshot scope exit state with
  | none => rw [snapshot] at closed; cases closed
  | some result =>
    obtain ⟨after, strategy, order⟩ := result
    simp only [snapshot, Option.pure_def] at closed
    cases order with
    | nil => cases closed
    | cons first rest =>
      cases rest with
      | nil =>
        cases closed
        change current id (embed (finProgram first exit)) + 0 = 0
        rw [show current id (embed (finProgram first exit)) = 0 from
          program_exact id (.finalizerOf first exit)]
      | cons second tail =>
        cases closed
        rfl

/-- An unsafe scope close installs a finalizer program or a stored walk, with no note reservation. -/
theorem close_unsafe_zero (id : Nat) (scope : Nat) (exit : ExitV) (flag : Bool) (state next : Stores)
    (code : Program) (closed : storesCloseScopeUnsafe scope exit flag state = some (next, some code)) :
    current id (embed code) = 0 := by
  unfold storesCloseScopeUnsafe at closed
  cases snapshot : scopeCloseSnapshot scope exit state with
  | none => rw [snapshot] at closed; cases closed
  | some result =>
    obtain ⟨after, strategy, order⟩ := result
    simp only [snapshot, Option.pure_def] at closed
    cases order with
    | nil => cases closed
    | cons first rest =>
      cases rest with
      | nil =>
        cases closed
        exact program_exact id (.finalizerOf first exit)
      | cons second tail =>
        cases closed
        rfl

/-- The native close action installs code with no note reservation. -/
theorem interp_close_zero (id : Nat) (root : NativeEff) (view : List (FiberId × ExitV))
    (table : RowTable) (scope : Nat) (exit : ExitV) (flag : Bool) (closer : FiberId)
    (state next : Stores) (program : NCode)
    (closed : (interpAt root view table).closeScope scope exit flag closer state = some (next, some program)) :
    current id program = 0 := by
  change (storesCloseScope scope exit flag state).map (fun result => (result.1, result.2.map embed)) =
    some (next, some program) at closed
  cases step : storesCloseScope scope exit flag state with
  | none => rw [step] at closed; cases closed
  | some result =>
    obtain ⟨after, code⟩ := result
    rw [step] at closed
    cases code with
    | none => cases closed
    | some code =>
      cases closed
      exact close_zero id scope exit flag state after code step

/-- The note reservation that an action's forked or masked program carries. -/
def launched (id : Nat) : NAction → Nat
  | .fork body _ _ | .forkIn body _ _ _ | .forkScoped body _ _ | .setInterruptible body _ =>
    current id body
  | _ => 0

/-- A masked source child carries at most its parent's active note reservation. -/
theorem mask_child_le (built : Api.Built) (admitted : Api.Author.build (shop .none) = .ok built)
    (id : Nat) (member : id ∈ requests) (parent : Point) (program : NCode)
    (held : ChildProgramAt built.program parent [0] program) :
    current id program ≤ WriterPhase.below id parent.path := by
  obtain ⟨effect, node, scope, code⟩ := held
  rw [code]
  exact Nat.le_trans (WriterSource.resolve_bound built admitted id member _ scope)
    (WriterSource.child_zero_le id parent.path)

/-- A forked source grandchild carries at most its parent's active note reservation. -/
theorem fork_child_le (built : Api.Built) (admitted : Api.Author.build (shop .none) = .ok built)
    (id : Nat) (member : id ∈ requests) (parent : Point) (program : NCode)
    (held : ChildProgramAt built.program parent [0, 0] program) :
    current id program ≤ WriterPhase.below id parent.path := by
  obtain ⟨effect, node, scope, code⟩ := held
  rw [code]
  exact Nat.le_trans (WriterSource.resolve_bound built admitted id member _ scope)
    (Nat.le_trans (WriterSource.child_zero_le id (parent.path ++ [0]))
      (WriterSource.child_zero_le id parent.path))

/-- An action interpreted from an owned thunk launches no more than the thunk's reservation. -/
theorem launched_le (built : Api.Built) (admitted : Api.Author.build (shop .none) = .ok built)
    (id : Nat) (member : id ∈ requests) (view : List (FiberId × ExitV)) (suspended : EffThunk)
    (next : NAction) (owned : ThunkAt built.program suspended)
    (produced : (interpAt built.program view built.table).withFiberOf suspended = some next) :
    launched id next ≤ thunk id suspended := by
  cases suspended
  case act point =>
    have children := interp_source_children built.program view built.table point next owned produced
    cases next
    case fork body options site => exact fork_child_le built admitted id member point body children
    case forkIn body options scope site => exact fork_child_le built admitted id member point body children
    case forkScoped body options site => exact fork_child_le built admitted id member point body children
    case setInterruptible body flag => exact mask_child_le built admitted id member point body children
    all_goals exact Nat.zero_le _
  case forkInAt point scope =>
    have children := scoped_fork_children built.program point scope next owned produced
    cases next
    case fork body options site => exact fork_child_le built admitted id member point body children
    case forkIn body options scope site => exact fork_child_le built admitted id member point body children
    case forkScoped body options site => exact fork_child_le built admitted id member point body children
    case setInterruptible body flag => exact mask_child_le built admitted id member point body children
    all_goals exact Nat.zero_le _
  case store stored =>
    cases stored
    case act callback =>
      cases produced
      cases callback
      case fork body options => exact Nat.le_of_eq (program_exact id body)
      case forkIn body options scope => exact Nat.le_of_eq (program_exact id body)
      case forkScoped body options => exact Nat.le_of_eq (program_exact id body)
      case setInterruptible body flag => exact Nat.le_of_eq (program_exact id body)
      all_goals exact Nat.zero_le _
    all_goals cases produced
  case provideMasked update body flag =>
    cases produced
    cases body
    case program point =>
      change 0 + WriterPhase.below id point.path + 0 ≤ WriterPhase.below id point.path
      omega
    all_goals exact Nat.zero_le _
  case restoreRegion body flag =>
    cases produced
    cases body
    case program point => exact WriterSource.resolve_bound built admitted id member point owned
    all_goals exact owned.elim
  case acquireMasked point context =>
    cases produced
    change 0 + WriterPhase.below id point.path + 0 ≤ WriterPhase.below id point.path
    omega
  case releaseMasked point previous =>
    cases produced
    change current id (resolve built.program point) + 0 + 0 ≤ WriterPhase.below id point.path
    have bound := WriterSource.resolve_bound built admitted id member point owned
    omega
  case forkLayer => exact owned.elim
  all_goals cases produced
  all_goals exact Nat.zero_le _

/-- Each fork or mask carries its producer's reservation; a close installs zero-weight code;
the sequential shop has no parallel close. -/
theorem carried (built : Api.Built) (admitted : Api.Author.build (shop .none) = .ok built)
    (id : Nat) (member : id ∈ requests) (m : NativeMachine) (fiber : SourceFiber)
    (suspended : EffThunk) (next : NAction) (selected : fiber.frame.current = .withFiber suspended)
    (owned : ThunkAt built.program suspended)
    (produced : (interpAt built.program m.completedExits built.table).withFiberOf suspended = some next) :
    Machine.WriterWeights.Carried (model id) (interpAt built.program m.completedExits built.table)
      m fiber next := by
  have bound := launched_le built admitted id member m.completedExits suspended next owned produced
  have source := interp_action_at built.program (SourceFragment.atomic_built_fragment built admitted)
    m.completedExits built.table suspended next owned produced
  have active : current id fiber.frame.current = thunk id suspended := by
    rw [selected]
  cases next
  case fork body options site => exact Nat.le_trans bound (Nat.le_of_eq active.symm)
  case forkIn body options scope site => exact Nat.le_trans bound (Nat.le_of_eq active.symm)
  case forkScoped body options site => exact Nat.le_trans bound (Nat.le_of_eq active.symm)
  case setInterruptible body flag => exact Nat.le_trans bound (Nat.le_of_eq active.symm)
  case closeScope scope exit =>
    intro state program closed
    exact interp_close_zero id built.program m.completedExits built.table scope exit _ fiber.id
      m.state state program closed
  case closePar finalizers =>
    exact (restricted built admitted).1.not_parallel source.2
  all_goals exact True.intro

/-- Every action of an owned thunk spends only its producer's reservation: the ledger-generic
`PlaceFunding.action_debit` at the writer weights, the heap kept by `action_refs`. -/
theorem action_debit (built : Api.Built) (admitted : Api.Author.build (shop .none) = .ok built)
    (id : Nat) (member : id ∈ requests) (m : NativeMachine) (fiber : SourceFiber) (yielding : Bool)
    (suspended : EffThunk) (next : NAction) (selected : fiber.frame.current = .withFiber suspended)
    (owned : ThunkAt built.program suspended)
    (produced : (interpAt built.program m.completedExits built.table).withFiberOf suspended = some next) :
    (WriterMachine.ledger id).IterDebit m fiber
      (evaluatePrim.withFiber (interpAt built.program m.completedExits built.table) m fiber yielding next) :=
  PlaceFunding.action_debit (no_queue id) (events id) (model id) (fun _ => rfl) _
    (action_inputs id built.program m.completedExits built.table) m fiber yielding next
    (carried built admitted id member m fiber suspended next selected owned produced)
    (Nat.le_of_eq (congrArg (Writer.heapCount id)
      (action_refs built.program m.completedExits built.table m fiber yielding next)))

/-! ## The primitive arms -/

/-- A countdown registration keeps the heap and spends no reservation. -/
theorem countdown_debit (id : Nat) (root : NativeEff) (table : RowTable) (m : NativeMachine)
    (fiber : SourceFiber) (yielding : Bool) (targets : List FiberId) :
    let out := countdownParkEdits (interpAt root m.completedExits table) m fiber targets .exitsValue false
    WriterMachine.Debit id m fiber ⟨out.1, out.2.1, yielding, .continue_, [], out.2.2.2⟩ := by
  have bound := Machine.WriterWeights.countdown_plan_bound (model id) (interpAt root m.completedExits table)
    (action_inputs id root m.completedExits table) m fiber yielding targets .exitsValue false (fun _ => rfl)
  refine local_debit id m fiber _ ?_ ?_ bound
  · unfold countdownParkEdits
    dsimp only
    split <;> rfl
  · unfold countdownParkEdits
    dsimp only
    split
    · exact RunMachine.Extends.refl m
    · exact emit_extends _ _

/-- Native Async cancellation names carry no reservation. -/
theorem async_cancel_zero (id : Nat) (callback : EffName) (held : AsyncCancelAt callback) :
    name id callback = 0 := by
  cases callback
  case cancelAwait => rfl
  case store callback =>
    cases callback
    case cancelAwait | cancelSleep => rfl
    all_goals cases held
  all_goals cases held

/-- Every primitive evaluation of an owned fiber spends only its acting frame's reservation or a
recorded start. -/
theorem primitive_debit (built : Api.Built) (admitted : Api.Author.build (shop .none) = .ok built)
    (id : Nat) (member : id ∈ requests) (m : NativeMachine) (fiber : SourceFiber) (yielding : Bool)
    (owned : ConfigurationAt built.program m) (held : FiberAt built.program fiber) :
    (WriterMachine.ledger id).IterDebit m fiber
      (evaluatePrim (interpAt built.program m.completedExits built.table) m fiber yielding) := by
  have inputs : PlaceFunding.PrimitiveInputs (WriterMachine.ledger id) (Free id)
      (interpAt built.program m.completedExits built.table) m fiber yielding := {
    success := fun _ => rfl
    failure := fun _ => rfl
    exitValue := fun exit mode => by cases mode <;> cases exit <;> rfl
    step := debit_ledger id m fiber _
      (WriterMachine.step_frame_debit built admitted id member m fiber yielding held.frame)
    finalizer := fun exit => debit_ledger id m fiber _
      (WriterMachine.finalizer_debit built admitted id member m fiber yielding exit held.frame)
    action := by
      intro suspended next selected produced
      have thunkOwned := held.frame.1
      rw [selected] at thunkOwned
      exact action_debit built admitted id member m fiber yielding suspended next selected thunkOwned produced
    sync := by
      intro suspended state value selected written
      have thunkOwned := held.frame.1
      rw [selected] at thunkOwned
      have bounded := WriterSync.sync_bound built admitted id m.completedExits suspended thunkOwned
        m.state state value written
      change Writer.heapCount id state.refs + (0 + (fiber.frame.stack.map (saved id)).sum) ≤
        Writer.heapCount id m.state.refs + (current id fiber.frame.current + (fiber.frame.stack.map (saved id)).sum)
      rw [selected]
      change Writer.heapCount id state.refs + (0 + (fiber.frame.stack.map (saved id)).sum) ≤
        Writer.heapCount id m.state.refs + (thunk id suspended + (fiber.frame.stack.map (saved id)).sum)
      omega
    registerState := by
      intro register signal cancel state code _ produced
      have same := register_refs built.program m.completedExits built.table register fiber.id m.nextToken m.state
      rw [produced] at same
      exact Nat.le_of_eq (congrArg (Writer.heapCount id) same)
    registerReply := fun register _ _ _ code _ produced =>
      terminal_zero id code (register_reply built.program m.completedExits built.table register fiber.id
        m.nextToken m.state code (congrArg Prod.snd produced))
    cancel := by
      intro register signal cancel state selected _
      have callbacks := held.frame.1
      rw [selected] at callbacks
      have zero : name id ((interpAt built.program m.completedExits built.table).cancelName
          (cancel.getD (interpAt built.program m.completedExits built.table).abortName) fiber.id m.nextToken) = 0 := by
        cases cancel with
        | none => rfl
        | some callback => exact async_cancel_zero id callback (callbacks.2 callback rfl).2
      simp only [WriterMachine.ledger, frame, List.map_cons, List.sum_cons, saved, zero, Nat.zero_add,
        Nat.le_refl]
    joinCancel := by
      have zero : name id ((interpAt built.program m.completedExits built.table).cancelName
          (interpAt built.program m.completedExits built.table).parkCancelName fiber.id m.nextToken) = 0 := rfl
      simp only [WriterMachine.ledger, frame, List.map_cons, List.sum_cons, saved, zero, Nat.zero_add,
        Nat.le_refl]
    countdown := by
      intro targets next returned parked edits _ counted
      have debit := countdown_debit id built.program built.table m fiber yielding targets
      rw [counted] at debit
      exact debit_ledger id m fiber _ debit
    race := by
      intro race _
      have empty := Opportunities.races_nil built.program m (restricted built admitted).2 owned
      unfold registerRace RunMachine.race?
      rw [empty]
      exact Nat.le_refl _ }
  exact PlaceFunding.primitive_debit (no_queue id) (control id) (events id) _ m fiber yielding inputs

/-! ## Scoped entry and exit -/

/-- Scoped entry moves its source reservation to its body without a new one. -/
theorem enter_scoped_debit (built : Api.Built) (admitted : Api.Author.build (shop .none) = .ok built)
    (id : Nat) (member : id ∈ requests) (point : Point) (body : NativeEff)
    (found : Node.at_ (.eff built.program) point.path = some (.eff (.scoped body)))
    (m : NativeMachine) (fiber : SourceFiber) (yielding : Bool)
    (selected : fiber.frame.current = .withFiber (.act point)) (owned : At built.program point) :
    (WriterMachine.ledger id).IterDebit m fiber (enterScoped built.program point m fiber yielding) := by
  have child := WriterSource.resolve_bound built admitted id member (point.child 0)
    (node_child_at built.program point (.eff (.scoped body)) (.eff body) 0 found owned rfl rfl).2
  have inherited := WriterSource.child_zero_le id point.path
  have bounded : current id (Prim.onExit (resolve built.program (point.child 0))
      (.scopedExit fiber.context m.state.nextName) false) ≤ current id fiber.frame.current := by
    rw [selected]
    change current id (resolve built.program (point.child 0)) + 0 + 0 ≤ WriterPhase.below id point.path
    change current id (resolve built.program (point.child 0)) ≤ WriterPhase.below id (point.path ++ [0]) at child
    omega
  refine rows_debit id m fiber _ rfl rfl (RunMachine.Extends.refl m) ?_
  change current id (Prim.onExit (resolve built.program (point.child 0))
      (.scopedExit fiber.context m.state.nextName) false) + (fiber.frame.stack.map (saved id)).sum ≤
    current id fiber.frame.current + (fiber.frame.stack.map (saved id)).sum
  omega

/-- Scoped exit installs only zero-weight close code after the actual pop, or falls back to the
primitive evaluator. -/
theorem exit_scoped_debit (built : Api.Built) (admitted : Api.Author.build (shop .none) = .ok built)
    (id : Nat) (member : id ∈ requests) (m : NativeMachine) (fiber : SourceFiber) (yielding : Bool)
    (exit : ExitV) (owned : ConfigurationAt built.program m) (held : FiberAt built.program fiber) :
    (WriterMachine.ledger id).IterDebit m fiber (exitScoped built.program m fiber yielding exit) := by
  have primitive := primitive_debit built admitted id member m fiber yielding owned held
  rw [Store.shop_table built admitted] at primitive
  cases exit with
  | success value =>
    unfold exitScoped
    dsimp only
    split
    · rename_i _ _ scope _ _
      split
      · refine rows_debit id m fiber _ rfl rfl (emit_extends m _) ?_
        exact pop_frame_le id fiber.frame .contA false none _ (WriterFrames.exit_zero id _)
      · rename_i state program closed
        have refs := close_unsafe_refs scope _ _ m.state state program closed
        cases program with
        | none =>
          refine rows_debit id m fiber _ rfl refs (emit_extends m _) ?_
          exact pop_frame_le id fiber.frame .contA false none _ (WriterFrames.exit_zero id _)
        | some code =>
          have zero := close_unsafe_zero id scope _ _ m.state state code closed
          refine rows_debit id m fiber _ rfl refs ?_ ?_
          · unfold RunMachine.Extends
            simp only [RunMachine.emit_trace, List.append_assoc]
            exact List.prefix_append _ _
          · refine pop_frame_le id fiber.frame .contA false none _ ?_
            dsimp only
            rw [WriterPhase.restoring_count]
            exact zero
    · exact primitive
  | failure cause =>
    unfold exitScoped
    dsimp only
    split
    · rename_i _ _ scope _ _
      split
      · refine rows_debit id m fiber _ rfl rfl (emit_extends m _) ?_
        exact pop_frame_le id fiber.frame .contE true (some cause) _ (WriterFrames.exit_zero id _)
      · rename_i state program closed
        have refs := close_unsafe_refs scope _ _ m.state state program closed
        cases program with
        | none =>
          refine rows_debit id m fiber _ rfl refs (emit_extends m _) ?_
          exact pop_frame_le id fiber.frame .contE true (some cause) _ (WriterFrames.exit_zero id _)
        | some code =>
          have zero := close_unsafe_zero id scope _ _ m.state state code closed
          refine rows_debit id m fiber _ rfl refs ?_ ?_
          · unfold RunMachine.Extends
            simp only [RunMachine.emit_trace, List.append_assoc]
            exact List.prefix_append _ _
          · refine pop_frame_le id fiber.frame .contE true (some cause) _ ?_
            dsimp only
            rw [WriterPhase.restoring_count]
            exact zero
    · exact primitive

/-! ## The native evaluator and the iteration -/

/-- **The writer's native evaluator debit**: one evaluation of an owned fiber spends only its
acting frame's reservation or a recorded start. Consumer: `WriterHistory.evaluation`. -/
theorem native_debit (built : Api.Built) (admitted : Api.Author.build (shop .none) = .ok built)
    (id : Nat) (member : id ∈ requests) (m : NativeMachine) (fiber : SourceFiber) (yielding : Bool)
    (owned : ConfigurationAt built.program m) (held : FiberAt built.program fiber) :
    (WriterMachine.ledger id).IterDebit m fiber (evaluateNative built.program m fiber yielding built.table) := by
  have primitive := primitive_debit built admitted id member m fiber yielding owned held
  unfold evaluateNative
  split
  · rename_i point selected
    split
    · rename_i body found
      have thunkOwned := held.frame.1
      rw [selected] at thunkOwned
      exact enter_scoped_debit built admitted id member point body found m fiber yielding selected thunkOwned
    · exact primitive
  · exact exit_scoped_debit built admitted id member m fiber yielding _ owned held
  · exact exit_scoped_debit built admitted id member m fiber yielding _ owned held
  · exact primitive

/-- **The writer's charged iteration debit**, the forced yield included: the shared
`PlaceFunding.iteration_debit` at the writer weights. Consumer: `WriterHistory.evaluation`. -/
theorem iteration_debit (built : Api.Built) (admitted : Api.Author.build (shop .none) = .ok built)
    (id : Nat) (member : id ∈ requests) (m : NativeMachine) (fiber : SourceFiber) (yielding : Bool)
    (owned : ConfigurationAt built.program m) (held : FiberAt built.program fiber) :
    letI := evaluatorFor built.program built.table
    (WriterMachine.ledger id).IterDebit m fiber
      (Machine.iteration (interpOf built.program built.table) m fiber yielding) :=
  PlaceFunding.iteration_debit (no_queue id) (events id) (model id) (fun _ => rfl)
    (fun code => Nat.le_of_eq (Nat.zero_add (current id code))) built.program built.table m fiber
    yielding owned held
    (fun n g y _ configured fibered => native_debit built admitted id member n g y configured fibered)

end Test.Dogfood.Scenario.Atomic.WriterNative
