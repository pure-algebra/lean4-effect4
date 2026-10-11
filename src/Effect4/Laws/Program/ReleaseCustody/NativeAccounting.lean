import Effect4.Laws.Program.ReleaseCustody.NativeDebit
import Effect4.Laws.Program.ReleaseCustody.IterationDebit
import Effect4.Laws.Program.ReleaseCustody.NativeStacks

/-!
Concept: scope-lifetime-finalization, R11.
Question: actual evaluator debit feeds Execution.history and Workers.Assertions.releases_step.
Reach: actual native frame steps and stateful operation responses, with the checked pending stack sequence.
Limit: these clauses do not claim universal evaluator or command closure.
Unlock: IterDebit composes the scalar clauses with the actual settle adapter.
-/
set_option autoImplicit false
namespace Effect4.Program.ReleaseCustody.NativeAccounting
open Effect4 Effect4.Machine Effect4.Program
open Effect4.Program.ReleaseCustody Effect4.Program.ReleaseCustody.Control
open Effect4.Program.ReleaseCustody.RuntimeShape Effect4.Program.ReleaseCustody.Sequencing

/-- Actual frame trace projections ignore the fiber label and retain source identity.
Consumer: the running native frame clause below. -/
theorem frame_counts (q : List Nat) (id : FiberId) (events : List FrameDebit.Event) :
    (events.map (RunEvent.frame id)).countP (ReleaseTrace.releaseAt q) = FrameDebit.starts q events ∧
    (events.map (RunEvent.frame id)).countP (ReleaseTrace.registeredAt q) = FrameDebit.registrations q events := by
  have same (event : FrameDebit.Event) :
      (ReleaseTrace.releaseAt q (.frame id event), ReleaseTrace.registeredAt q (.frame id event)) =
      (ReleaseTrace.releaseAt q (.frame ⟨0⟩ event), ReleaseTrace.registeredAt q (.frame ⟨0⟩ event)) := by
    cases event
    case pushed code =>
      cases code
      case onSuccess body name =>
        cases name
        case afterScopeAdd acquired fin => cases fin <;> rfl
        all_goals rfl
      all_goals rfl
    all_goals rfl
  simp only [List.countP_map, FrameDebit.starts, FrameDebit.registrations]
  constructor
  · apply congrArg (fun predicate => events.countP predicate)
    funext event
    exact congrArg Prod.fst (same event)
  · apply congrArg (fun predicate => events.countP predicate)
    funext event
    exact congrArg Prod.snd (same event)

/-- Every actual running frame step satisfies the aggregate single-owner debit.
Consumer: evaluator delegation, then the native loop command and original Workers bound. -/
theorem step_running (q : List Nat) (root : NativeEff) (completed : List (FiberId × ExitV))
    (table : RowTable) (m : NativeMachine) (fiber : RuntimeShape.Fiber) (yielding : Bool)
    (next : Pop.Frame) (events : List FrameDebit.Event)
    (step : fiber.frame.step (interpAt root completed table).toPrimInterp = (.running next, events)) :
    IterDebit q m fiber (evaluatePrim.stepFrame (interpAt root completed table) m fiber yielding) := by
  have debit := FrameDebit.step q root completed table fiber.frame
  rw [step] at debit
  simp only [Pop.stepCredits] at debit
  have counts := frame_counts q fiber.id events
  unfold evaluatePrim.stepFrame
  rw [step]
  change IterDebit q m fiber ⟨m.emit (events.map (RunEvent.frame fiber.id)),
    {fiber with frame := next}, yielding, .continue_, [], []⟩
  unfold IterDebit
  simp only [RunMachine.emit_trace, List.countP_append, counts.1, counts.2,
    List.map_nil, List.sum_nil, Nat.add_zero]
  change m.trace.countP (ReleaseTrace.releaseAt q) + FrameDebit.starts q events + outsideCredits q fiber.id m +
      fiberCredits q {fiber with frame := next} + m.trace.countP (ReleaseTrace.registeredAt q) ≤
    m.trace.countP (ReleaseTrace.releaseAt q) + outsideCredits q fiber.id m +
      fiberCredits q fiber + (m.trace.countP (ReleaseTrace.registeredAt q) + FrameDebit.registrations q events)
  simp only [fiberCredits]
  omega

/-- The actual continuation getter retains the active code while changing saved frames.
Consumer: finished native frame debit below. -/
theorem getCont_current (fiber : Pop.Frame) (demand : Effect4.Arm) (skip : Bool) (cause : Option CauseV) :
    (fiber.getCont demand skip cause).fiber.current = fiber.current := by
  unfold FrameFiber.getCont
  split
  · rfl
  · exact SourceScope.pop_current demand skip fiber.stack _ cause

/-- Finished primitive steps start and register no release callback.
Consumer: the complete frame evaluator debit. -/
theorem finished_counts (q : List Nat) (root : NativeEff) (completed : List (FiberId × ExitV))
    (table : RowTable) (fiber : Pop.Frame) (exit : ExitV) (events : List FrameDebit.Event)
    (step : fiber.step (interpAt root completed table).toPrimInterp = (.finished exit, events)) :
    FrameDebit.starts q events = 0 ∧ FrameDebit.registrations q events = 0 := by
  cases current : fiber.current
  case success value =>
    have same := congrArg Prod.snd step
    simp only [FrameFiber.step, current] at same
    rw [← same]
    exact FrameDebit.resumeValue_counts q root completed table fiber value (some (.success value))
  case failure cause =>
    have same := congrArg Prod.snd step
    simp only [FrameFiber.step, current] at same
    rw [← same]
    exact FrameDebit.resumeCause_counts q root completed table fiber cause (some (.failure cause))
  case sync thunk =>
    have same := congrArg Prod.snd step
    simp only [FrameFiber.step, current] at same
    rw [← same]
    exact FrameDebit.resumeValue_counts q root completed table fiber _ none
  case iterator =>
    simp only [FrameFiber.step, current] at step
    split at step <;> cases step
  case whileLoop =>
    simp only [FrameFiber.step, current] at step
    split at step <;> cases step
  all_goals simp only [FrameFiber.step, current, Prod.mk.injEq, reduceCtorEq, false_and] at step

/-- A finished native frame retains its current and drains its stack without creating custody.
Consumer: complete step_frame debit below. -/
theorem step_finished (q : List Nat) (root : NativeEff) (completed : List (FiberId × ExitV))
    (table : RowTable) (m : NativeMachine) (fiber : RuntimeShape.Fiber) (yielding : Bool)
    (exit : ExitV) (events : List FrameDebit.Event)
    (step : fiber.frame.step (interpAt root completed table).toPrimInterp = (.finished exit, events)) :
    IterDebit q m fiber (evaluatePrim.stepFrame (interpAt root completed table) m fiber yielding) := by
  have zero := finished_counts q root completed table fiber.frame exit events step
  have empty := Effect4.Machine.step_finished_stack (interpAt root completed table).toPrimInterp
    fiber.frame exit (congrArg Prod.fst step)
  have same : (frameExitState fiber.frame).current = fiber.frame.current := by
    unfold frameExitState
    split <;> exact getCont_current fiber.frame _ _ _
  have counts := frame_counts q fiber.id events
  unfold evaluatePrim.stepFrame
  rw [step]
  change IterDebit q m fiber ⟨m.emit (events.map (RunEvent.frame fiber.id)),
    {fiber with frame := frameExitState fiber.frame}, yielding, .finished exit, [], []⟩
  unfold IterDebit
  simp only [RunMachine.emit_trace, List.countP_append, counts.1, counts.2, zero.1, zero.2,
    List.map_nil, List.sum_nil, Nat.add_zero]
  change m.trace.countP (ReleaseTrace.releaseAt q) + outsideCredits q fiber.id m +
      fiberCredits q {fiber with frame := frameExitState fiber.frame} + m.trace.countP (ReleaseTrace.registeredAt q) ≤
    m.trace.countP (ReleaseTrace.releaseAt q) + outsideCredits q fiber.id m +
      fiberCredits q fiber + m.trace.countP (ReleaseTrace.registeredAt q)
  simp only [fiberCredits, same, empty, stackCredits]
  omega

/-- Every actual native frame delegation satisfies single-owner accounting.
Consumer: complete native evaluator and actual loop/deliver command custody. -/
theorem step_frame (q : List Nat) (root : NativeEff) (completed : List (FiberId × ExitV))
    (table : RowTable) (m : NativeMachine) (fiber : RuntimeShape.Fiber) (yielding : Bool) :
    IterDebit q m fiber (evaluatePrim.stepFrame (interpAt root completed table) m fiber yielding) := by
  cases step : fiber.frame.step (interpAt root completed table).toPrimInterp with
  | mk next events =>
    cases next with
    | running next => exact step_running q root completed table m fiber yielding next events step
    | finished exit => exact step_finished q root completed table m fiber yielding exit events step

/-- Actual synchronous scope operations account for both stored custody and the returned response.
Consumer: native operation evaluation, then its deliver command and original Workers release bound. -/
theorem sync_answer (q : List Nat) (root : NativeEff) (table : RowTable) (m : NativeMachine)
    (fiber : RuntimeShape.Fiber) (yielding : Bool) (op : SyncOp) (state : Stores) (value : Val)
    (current : fiber.frame.current = .sync (.op op))
    (unique : (m.state.scopes.entries.map ScopeEntry.key).Nodup) (fresh : m.state.ScopeKeysFresh)
    (held : Kept fiber.frame.current fiber.frame.stack)
    (step : syncOpStep op m.state = some (state,value)) :
    IterDebit q m fiber (evaluateNative root m fiber yielding table) := by
  have debit := NativeDebit.sync_op q m.state state op value fiber.frame.stack unique fresh (current ▸ held) step
  have native : evaluateNative root m fiber yielding table =
      ⟨{m with state}, {fiber with frame := {fiber.frame with current := .success value}},
        yielding, .answered, [.drainDue], []⟩ := by
    simp only [evaluateNative, current, evaluatePrim, interpAt, interpOf, step]
  rw [native]
  unfold IterDebit
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, commandCredits, Nat.add_zero]
  unfold outsideCredits fiberCredits
  rw [current]
  simp only [currentCredits, ScopeTransfer.storedCredits] at debit ⊢
  omega

end Effect4.Program.ReleaseCustody.NativeAccounting
