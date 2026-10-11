import Effect4.Laws.Program.ReleaseCustody.NativeActionDebit

/-!
Concept: scope-lifetime-finalization R11.
Question: actual native evaluator accounting serves Execution.history and Workers.releases_step.
Reach: actual primitive evaluation with existing source ownership and frame sequencing.
Limit: local debit alone establishes neither history closure nor source-use uniqueness.
Unlock: frame and action transfers assemble at their actual evaluator boundary.
-/
set_option autoImplicit false
namespace Effect4.Program.ReleaseCustody.NativePrimitiveDebit
open Effect4 Effect4.Machine Effect4.Program
open Effect4.Program.ReleaseCustody Effect4.Program.ReleaseCustody.Control
open Effect4.Program.ReleaseCustody.Sequencing

/-- The native restoring wrapper carries precisely its cleanup program reservation.
Consumer: finalizerOr debit. -/
theorem finalizer_code (q : List Nat) (root : NativeEff) (completed) (table : RowTable)
    (exit : ExitV) (program : NCode) :
    currentCredits q (finalizerCode (interpAt root completed table) exit program) = currentCredits q program := by
  cases exit <;> rfl

/-- The selected native cleanup program spends at most its saved finalizer reservation.
Consumer: finalizerOr debit. -/
theorem finalizer_program (q : List Nat) (root : NativeEff) (completed) (table : RowTable)
    (name : EffName) (exit : ExitV) (body : NCode) (flag : Bool) (program : NCode)
    (found : (interpAt root completed table).finalizerProgram name exit = some program) :
    currentCredits q program ≤ futureCredits q (.onExit body name flag) := by
  cases name
  case fin point =>
    cases found
    rw [Evaluation.resolve_credits]
    exact Nat.zero_le _
  case store name =>
    cases name
    case finalizerName fin => cases found; rw [fin_program_credits]; exact Nat.le_refl _
    all_goals cases found
  case scopeClose => cases found; exact Nat.le_refl _
  case restoreCtx => cases found; exact Nat.le_refl _
  all_goals cases found

/-- The native program-finalizer boundary transfers the selected frame's reservation.
Consumer: success and failure primitive evaluation, then the admitted Workers history. -/
theorem finalizer (q : List Nat) (root : NativeEff) (completed) (table : RowTable)
    (m : NativeMachine) (fiber : Control.Fiber) (yielding : Bool) (exit : ExitV)
    (held : Kept fiber.frame.current fiber.frame.stack) :
    IterDebit q m fiber (evaluatePrim.finalizerOr (interpAt root completed table) m fiber yielding exit) := by
  have clean := NativeSequencing.exit_pop_noAdd fiber.frame held exit
  cases exit
  case success value =>
    have pop := Pop.getCont_value q fiber.frame.current fiber.frame
    unfold evaluatePrim.finalizerOr
    dsimp only
    split
    · rename_i body name flag found
      have tail := clean body name flag found
      split
      · rename_i program selected
        have produced := finalizer_program q root completed table name _ body flag program selected
        unfold Pop.valueCredits Pop.valueAnswer at pop
        rw [found] at pop
        dsimp only at pop
        unfold IterDebit
        simp only [RunMachine.emit_trace, List.countP_append, List.map_nil, List.sum_nil,
          Nat.add_zero, fiberCredits, finalizer_code, noAdd_full q _ _ tail]
        have noPush := FrameDebit.noPush_counts q _ (FrameDebit.getCont_no_push fiber.frame .contA false none)
        have counts := NativeAccounting.frame_counts q fiber.id (fiber.frame.getCont .contA false).events
        simp only [List.countP_cons, List.countP_nil,
          ReleaseTrace.releaseAt, ReleaseTrace.registeredAt, Bool.false_eq_true, if_false, Nat.add_zero,
          counts.1, counts.2, noPush.1, noPush.2]
        change _ + outsideCredits q fiber.id m + _ + _ ≤ _ + outsideCredits q fiber.id m + _ + _
        omega
      · exact NativeAccounting.step_frame q root completed table m fiber yielding
    · exact NativeAccounting.step_frame q root completed table m fiber yielding
  case failure cause =>
    have pop := CausePop.getCont_cause q fiber.frame cause
    have before := Evaluation.failure_stack_le q cause fiber.frame.current fiber.frame.stack
    unfold evaluatePrim.finalizerOr
    dsimp only
    split
    · rename_i body name flag found
      have tail := clean body name flag found
      split
      · rename_i program selected
        have produced := finalizer_program q root completed table name _ body flag program selected
        unfold CausePop.popCredits CausePop.answerCredits at pop
        rw [found] at pop
        dsimp only at pop
        unfold IterDebit
        simp only [RunMachine.emit_trace, List.countP_append, List.map_nil, List.sum_nil,
          Nat.add_zero, fiberCredits, finalizer_code, noAdd_full q _ _ tail]
        have noPush := FrameDebit.noPush_counts q _ (FrameDebit.getCont_no_push fiber.frame .contE true (some cause))
        have counts := NativeAccounting.frame_counts q fiber.id (fiber.frame.getCont .contE true (some cause)).events
        simp only [List.countP_cons, List.countP_nil,
          ReleaseTrace.releaseAt, ReleaseTrace.registeredAt, Bool.false_eq_true, if_false, Nat.add_zero,
          counts.1, counts.2, noPush.1, noPush.2]
        change _ + outsideCredits q fiber.id m + _ + _ ≤ _ + outsideCredits q fiber.id m + _ + _
        omega
      · exact NativeAccounting.step_frame q root completed table m fiber yielding
    · exact NativeAccounting.step_frame q root completed table m fiber yielding

/-- Yield parks retain the saved callback phase and enqueue only a unit answer.
Consumer: primitive and forced-yield iteration accounting. -/
theorem yielding (q : List Nat) (root : NativeEff) (table : RowTable) (m : NativeMachine)
    (fiber : Control.Fiber) (yielding : Bool) (priority : Nat)
    (current : fiber.frame.current = .yieldNowWith priority)
    (held : Kept fiber.frame.current fiber.frame.stack) :
    IterDebit q m fiber (evaluatePrim (interpAt root m.completedExits table) m fiber yielding) := by
  have stable := yield_stable (current ▸ held)
  have full (active : NCode) := stable_full q active stable
  unfold IterDebit
  simp only [evaluatePrim, current, RunMachine.emit_trace, List.countP_append,
    List.countP_cons, List.countP_nil, ReleaseTrace.releaseAt, ReleaseTrace.registeredAt,
    Bool.false_eq_true, if_false, List.map_nil, List.sum_nil, Nat.add_zero,
    fiberCredits, RunFiber.park, Dispatcher.enqueue, currentCredits, full,
    CommandDebit.insert_zero q priority (.resume fiber.id m.nextToken (.success ((interpAt root m.completedExits table).voidValue))) rfl, RunMachine.arm]
  change _ + outsideCredits q fiber.id m + _ + _ ≤ _ + outsideCredits q fiber.id m + _ + _
  omega

/-- Stored reference replies also retain the exact saved forced-yield stack.
Consumer: synchronous operation evaluation. -/
theorem stored_sync (q : List Nat) (s next : Stores) (op : SyncOp) (value : Val) (frames : List NCode)
    (unique : (s.scopes.entries.map ScopeEntry.key).Nodup) (fresh : s.ScopeKeysFresh)
    (held : Kept (.sync (.store (.op op))) frames)
    (step : syncOpStep op s = some (next, value)) :
    ScopeTransfer.storedCredits q next.scopes + stackCredits q (.success value) frames ≤
      ScopeTransfer.storedCredits q s.scopes + opCredits q op + stackCredits q (.sync (.store (.op op))) frames := by
  cases held
  case clean absent =>
    rw [noAdd_full q _ _ absent, noAdd_full q _ _ absent]
    exact Nat.add_le_add_right (ScopeTransfer.syncOp q unique fresh step) _
  case add phase => cases phase
  case constant priority next rest saved phase =>
    cases phase with
    | refGet cell =>
      have bound := ScopeTransfer.syncOp q unique fresh step
      simp only [stackCredits]
      exact Nat.add_le_add_right bound _

/-- Every actual successful sync operation accounts for its scope response and stored custody.
Consumer: complete primitive debit. -/
theorem sync_some (q : List Nat) (root : NativeEff) (table : RowTable) (m : NativeMachine)
    (fiber : Control.Fiber) (yielding : Bool) (thunk : EffThunk) (state : Stores) (value : Val)
    (current : fiber.frame.current = .sync thunk)
    (held : Kept fiber.frame.current fiber.frame.stack)
    (unique : (m.state.scopes.entries.map ScopeEntry.key).Nodup) (fresh : m.state.ScopeKeysFresh)
    (step : (interpAt root m.completedExits table).syncState thunk m.state = some (state,value)) :
    IterDebit q m fiber (evaluatePrim (interpAt root m.completedExits table) m fiber yielding) := by
  have shape : ∃ op, (thunk = .op op ∨ thunk = .store (.op op)) ∧
      syncOpStep op m.state = some (state,value) := by
    cases thunk
    case op op => exact ⟨op, Or.inl rfl, step⟩
    case store stored =>
      cases stored
      case op op => exact ⟨op, Or.inr rfl, step⟩
      all_goals cases step
    all_goals cases step
  have park : (interpAt root m.completedExits table).parkOf (.sync thunk) = none := by cases thunk <;> rfl
  obtain ⟨op, direct | stored, operation⟩ := shape
  all_goals
    subst thunk
    have debit : ScopeTransfer.storedCredits q state.scopes + stackCredits q (.success value) fiber.frame.stack ≤
        ScopeTransfer.storedCredits q m.state.scopes + opCredits q op + stackCredits q fiber.frame.current fiber.frame.stack := by
      rw [current] at held ⊢
      aesop (add safe apply [NativeDebit.sync_op, stored_sync])
    unfold IterDebit
    simp only [evaluatePrim, current, park, step, List.map_cons, List.map_nil,
      List.sum_cons, List.sum_nil, commandCredits, Nat.add_zero, outsideCredits, fiberCredits]
    unfold ScopeTransfer.storedCredits at debit
    rw [current] at debit
    simp only [currentCredits] at debit ⊢
    omega

/-- A sync thunk without a state response spends only its old active reservation.
Consumer: complete primitive debit. -/
theorem sync_none (q : List Nat) (root : NativeEff) (table : RowTable) (m : NativeMachine)
    (fiber : Control.Fiber) (yielding : Bool) (thunk : EffThunk)
    (current : fiber.frame.current = .sync thunk)
    (step : (interpAt root m.completedExits table).syncState thunk m.state = none) :
    IterDebit q m fiber (evaluatePrim (interpAt root m.completedExits table) m fiber yielding) := by
  have bound := FrameDebit.sync_stack_le q thunk ((interpAt root m.completedExits table).syncValue thunk) fiber.frame.stack
  have park : (interpAt root m.completedExits table).parkOf (.sync thunk) = none := by cases thunk <;> rfl
  unfold IterDebit
  simp only [evaluatePrim, current, park, step, List.map_nil, List.sum_nil,
    Nat.add_zero, fiberCredits, currentCredits]
  omega

/-- Actual asynchronous registration changes deferreds or timers, never scope custody.
Consumer: the async evaluator debit. -/
theorem register_scopes (root : NativeEff) (completed) (table : RowTable) (name : EffName)
    (fiber : FiberId) (token : Nat) (state : Stores) :
    ((interpAt root completed table).registerAsync name fiber token state).1.scopes = state.scopes := by
  cases name
  case store stored => cases stored <;> rfl
  all_goals rfl

/-- Immediate registration responses are the existing completion programs.
Consumer: the async evaluator debit. -/
theorem register_zero (q : List Nat) (root : NativeEff) (completed) (table : RowTable)
    (name : EffName) (fiber : FiberId) (token : Nat) (state : Stores) (code : NCode)
    (found : ((interpAt root completed table).registerAsync name fiber token state).2 = some code) :
    currentCredits q code = 0 := by
  cases name
  case registerAwait cell =>
    obtain ⟨answer, _, eq⟩ := Option.map_eq_some_iff.mp found
    rw [← eq]
    exact Execution.Outer.completion_zero q answer
  case store stored =>
    cases stored
    case registerAwait cell =>
      obtain ⟨answer, _, eq⟩ := Option.map_eq_some_iff.mp found
      rw [← eq]
      exact Execution.Outer.completion_zero q answer
    all_goals cases found
  all_goals cases found

/-- Native async registration preserves the complete foreign-release reservation.
Consumer: the full native primitive evaluator census. -/
theorem asynchronous (q : List Nat) (root : NativeEff) (table : RowTable) (m : NativeMachine)
    (fiber : Control.Fiber) (yielding : Bool) (name : EffName) (signal : Bool) (cancel : Option EffName)
    (current : fiber.frame.current = .async name signal cancel)
    (held : Kept fiber.frame.current fiber.frame.stack) :
    IterDebit q m fiber (evaluatePrim (interpAt root m.completedExits table) m fiber yielding) := by
  have absent := async_noAdd name signal cancel (current ▸ held)
  have scopes := register_scopes root m.completedExits table name fiber.id m.nextToken m.state
  cases registered : (interpAt root m.completedExits table).registerAsync name fiber.id m.nextToken m.state with
  | mk state immediate =>
    rw [registered] at scopes
    dsimp only at scopes
    cases response : immediate with
    | some code =>
      have zero := register_zero q root m.completedExits table name fiber.id m.nextToken m.state code
        (by rw [registered]; exact response)
      unfold IterDebit
      simp only [evaluatePrim, current, registered, response, List.map_cons, List.map_nil,
        List.sum_cons, List.sum_nil, commandCredits, Nat.add_zero, outsideCredits, fiberCredits,
        scopes, zero, noAdd_full q _ _ absent, currentCredits, Nat.zero_add]
      exact Nat.le_refl _
    | none =>
      unfold IterDebit
      simp only [evaluatePrim, current, registered, response]
      split
      all_goals
        simp only [RunMachine.emit, List.isEmpty_cons, List.countP_append, List.countP_cons, List.countP_nil,
          ReleaseTrace.releaseAt, ReleaseTrace.registeredAt, Bool.false_eq_true, if_false,
          List.map_nil, List.sum_nil, Nat.add_zero, outsideCredits, fiberCredits, RunFiber.park,
          scopes, noAdd_full q _ _ absent, stackCredits, futureCredits, currentCredits, Nat.zero_add]
        omega

end Effect4.Program.ReleaseCustody.NativePrimitiveDebit
