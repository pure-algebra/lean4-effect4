import Effect4.Laws.Program.AnswerSlots.AllocationCommands

/-!
Concept: store-typing R4 and reactive-scheduling R9.
Consumer: the shared bare-prefix pending configuration and actual command/history lift.
A running unparked initializer can park only at its actual scheduler yield.
That yield retains the exact ignored reply class and its older saved suffix.
-/
set_option autoImplicit false
namespace Effect4.Program.AnswerSlots.AllocationAdapter
open Effect4 Effect4.Machine Effect4.Program

/-- Actual ordinary frame stepping retains the run fiber's existing parked state. -/
theorem step_frame_parked (interp : Moves.NInterp) (machine : NativeMachine)
    (fiber : SourceScope.SourceFiber) (yielding : Bool) :
    (evaluatePrim.stepFrame interp machine fiber yielding).fiber.parked = fiber.parked := by
  unfold evaluatePrim.stepFrame evaluatePrim.finishFrame
  repeat' split
  all_goals rfl

/-- Actual finalizer dispatch retains the run fiber's existing parked state. -/
theorem finalizer_parked (interp : Moves.NInterp) (machine : NativeMachine)
    (fiber : SourceScope.SourceFiber) (yielding : Bool) (exit : ExitV) :
    (evaluatePrim.finalizerOr interp machine fiber yielding exit).fiber.parked = fiber.parked := by
  unfold evaluatePrim.finalizerOr
  dsimp only
  split
  · split
    · rfl
    · exact step_frame_parked interp machine fiber yielding
  · exact step_frame_parked interp machine fiber yielding

/-- An actual pending yield retains its exact ignored saved input, or exposes actual application entry. -/
theorem yield_saved_or_entry (spec : Spec) (fragment : SourceScope.Fragment spec.root)
    (world : World) (input output : Kind spec.stable.Kind) (program : NCode) (frames : List NCode)
    (priority : Nat) (owned : CodeAt spec world input program) (pending : world.entered = false)
    (current : program = .yieldNowWith priority)
    (saved : Effect4.Contracts.Path (Edge spec fragment world) input output frames) :
    (PendingDemand spec world ∧ Effect4.Contracts.Path (Edge spec fragment world)
      (.yielded world.state.refs.length world.state.deferreds.cells.length) output frames) ∨
      ∃ point, input = .stable spec.stable.rootKind ∧ program = resolve spec.root point ∧ Entry spec world point := by
  cases owned with
  | initial stage active =>
    rcases initial_shape spec world _ _ stage active with ⟨body, name, same⟩ | same | ⟨cause, same⟩
    all_goals rw [same] at current
    all_goals cases current
  | entered source entry => exact .inr ⟨_, rfl, rfl, entry⟩
  | stable ready code => exact (pending_not_ready spec world pending ready).elim
  | yielding phase refs deferred missing contents entered =>
    refine .inl ⟨⟨phase, ?_, entered⟩, ?_⟩
    · rw [refs]
      exact contents
    · rw [refs, deferred]
      exact saved
  | success good | failure phase | allocating small stage | gateAllocating stage available
    | frontier zero phase | reading phase refs deferred missing contents entered
    | yieldThen phase held missing => cases current

/-- The actual ordinary pending primitive retains every new park's actual saved reply class. -/
theorem pending_primitive_waits_or_entry (spec : Spec) (fragment : SourceScope.Fragment spec.root)
    (view : List (FiberId × ExitV)) (machine : NativeMachine) (fiber : SourceScope.SourceFiber)
    (yielding : Bool) (input output : Kind spec.stable.Kind)
    (owned : CodeAt spec ⟨fiber.id, machine.state, false⟩ input fiber.frame.current)
    (saved : Effect4.Contracts.Path (Edge spec fragment ⟨fiber.id, machine.state, false⟩) input output fiber.frame.stack)
    (unparked : fiber.parked = .notParked) :
    (let next := evaluatePrim (interpAt spec.root view spec.table) machine fiber yielding;
      PendingWaits spec fragment ⟨fiber.id, next.machine.state, false⟩ next.fiber) ∨
      ∃ point, input = .stable spec.stable.rootKind ∧ fiber.frame.current = resolve spec.root point ∧
        Entry spec ⟨fiber.id, machine.state, false⟩ point := by
  rcases pending_ordinary_or_entry spec view ⟨fiber.id, machine.state, false⟩ input fiber.frame.current owned rfl with ordinary | entry
  swap
  · exact .inr entry
  have producer := Moves.evaluatePrim_producer (interpAt spec.root view spec.table) machine fiber yielding
  generalize actual : evaluatePrim (interpAt spec.root view spec.table) machine fiber yielding = result at producer ⊢
  dsimp only [PendingWaits]
  cases producer with
  | step =>
    apply Or.inl
    intro parked
    exact (parked ((step_frame_parked _ _ _ _).trans unparked)).elim
  | finalizer exit =>
    apply Or.inl
    intro parked
    exact (parked ((finalizer_parked _ _ _ _ _).trans unparked)).elim
  | sync | fallback | rejectedPark | joinMissing | joinExited =>
    apply Or.inl
    intro parked
    exact (parked unparked).elim
  | yieldNow priority current =>
    rcases yield_saved_or_entry spec fragment _ input output fiber.frame.current fiber.frame.stack priority owned rfl current saved with valid | entry
    · exact .inl (fun _ => ⟨output, valid.1, valid.2⟩)
    · exact .inr entry
  | action thunk action current notPark found => exact (ordinary.2.1 thunk current).elim
  | asyncImmediate name signal cancel state code current registered => exact (ordinary.2.2 name signal cancel current).elim
  | asyncParked name signal cancel state current registered => exact (ordinary.2.2 name signal cancel current).elim
  | racePark race park | countdownPark targets next returned parked edits park counted | joinWaiting target mode other park found live =>
    rw [ordinary.1] at park
    cases park
/-- The actual complete pending native evaluator retains its real parked suffix or exposes application entry. -/
theorem pending_native_waits_or_entry (spec : Spec) (fragment : SourceScope.Fragment spec.root)
    (machine : NativeMachine) (fiber : SourceScope.SourceFiber) (yielding : Bool)
    (input output : Kind spec.stable.Kind)
    (owned : CodeAt spec ⟨fiber.id, machine.state, false⟩ input fiber.frame.current)
    (saved : Effect4.Contracts.Path (Edge spec fragment ⟨fiber.id, machine.state, false⟩) input output fiber.frame.stack)
    (unparked : fiber.parked = .notParked) :
    (let next := evaluateNative spec.root machine fiber yielding spec.table;
      PendingWaits spec fragment ⟨fiber.id, next.machine.state, false⟩ next.fiber) ∨
      ∃ point, input = .stable spec.stable.rootKind ∧ fiber.frame.current = resolve spec.root point ∧
        Entry spec ⟨fiber.id, machine.state, false⟩ point := by
  rcases pending_native_primitive_or_entry spec fragment machine fiber yielding input output owned saved with same | entry
  · rw [same]
    exact pending_primitive_waits_or_entry spec fragment machine.completedExits machine fiber yielding input output owned saved unparked
  · exact .inr entry
end Effect4.Program.AnswerSlots.AllocationAdapter
