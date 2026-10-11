import Test.Dogfood.Proofs.HostTimeoutCommands

/-!
# Timeout reference values through native evaluation

Placement: host-session-protocol R6, serving `Timeout.stale_never_applies` clause four.
Consumer: the reached command assertion and exact external reply admission.
Every source write retains a number or list at the cell's outer level.
The general host envelope admits delayed reads, so this source heap assertion is necessary.
The assertion does not restrict host replies or claim progress.
-/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
namespace Test.Dogfood.Proofs.HostTimeoutHeap
open Effect4 Effect4.Machine Effect4.Program Effect4.Laws.Auto
open HostTimeoutSlots HostTimeoutFlow HostTimeoutFrames HostTimeoutEvaluation HostTimeoutCommands

/-- Finishing a pure frame step leaves every reference cell unchanged. -/
theorem finish_frame_refs (machine : Effect4.Program.NativeMachine) (fiber : NativeFiber)
    (yielding : Bool) (next : FrameStep EffName EffThunk Val Err Defect FiberId Ann)
    (events : List (FrameEvent EffName EffThunk Val Err Defect FiberId Ann)) (nested : List Guard.NCmd) :
    (evaluatePrim.finishFrame machine fiber yielding next events nested).machine.state.refs = machine.state.refs := by
  cases next <;> rfl

/-- The native frame evaluator leaves every reference cell unchanged. -/
theorem step_frame_refs (view : View) (machine : Effect4.Program.NativeMachine) (fiber : NativeFiber)
    (yielding : Bool) :
    (evaluatePrim.stepFrame (interpreter view) machine fiber yielding).machine.state.refs = machine.state.refs := by
  exact finish_frame_refs machine fiber yielding _ _ _

/-- Selecting a finalizer program leaves every reference cell unchanged. -/
theorem finalizer_refs (view : View) (machine : Effect4.Program.NativeMachine) (fiber : NativeFiber)
    (yielding : Bool) (exit : ExitV) :
    (evaluatePrim.finalizerOr (interpreter view) machine fiber yielding exit).machine.state.refs = machine.state.refs := by
  unfold evaluatePrim.finalizerOr
  dsimp only
  split
  · split
    · rfl
    · exact step_frame_refs view machine fiber yielding
  · exact step_frame_refs view machine fiber yielding

/-- Fiber bookkeeping never changes the native stores. -/
theorem modify_state (machine : Effect4.Program.NativeMachine) (id : FiberId) (fn : NativeFiber → NativeFiber) :
    (machine.modify id fn).state = machine.state := by
  unfold RunMachine.modify
  split <;> rfl

/-- A countdown's observer bookkeeping leaves every reference cell unchanged. -/
theorem countdown_refs (view : View) (machine : Effect4.Program.NativeMachine) (fiber : NativeFiber)
    (targets : List FiberId) :
    (countdownPark (interpreter view) machine fiber targets .exitsValue).1.state.refs = machine.state.refs := by
  unfold countdownPark
  dsimp only
  split <;> simp only [RunMachine.emit, modify_state]

/-- All actual Timeout fiber actions leave every reference cell unchanged. -/
theorem action_refs {B : List Val} {kind : Kind} (view : View) (machine : Effect4.Program.NativeMachine)
    (fiber : NativeFiber) (yielding : Bool) (action : NAction) (allowed : ActionAt B kind action) :
    (evaluatePrim.withFiber (interpreter view) machine fiber yielding action).machine.state.refs = machine.state.refs := by
  cases allowed with
  | race programs site entrants => rfl
  | mask kind body flag good => cases flag <;> rfl
  | cancelRace race => unfold evaluatePrim.withFiber; dsimp only; split <;> rfl
  | dropObservers token => rfl

/-- Every actual primitive head retains the timeout cell outer shapes. -/
theorem head_outer {B : List Val} {kind : Kind} (view : View) (machine : Effect4.Program.NativeMachine)
    (fiber : NativeFiber) (yielding : Bool) (head : HeadAt B kind fiber.frame.current)
    (heap : OuterHeap machine.state.refs) :
    OuterHeap (evaluatePrim (interpreter view) machine fiber yielding).machine.state.refs := by
  generalize current : fiber.frame.current = code at head
  cases head with
  | success good =>
    rename_i value
    have dispatch : evaluatePrim (interpreter view) machine fiber yielding =
        evaluatePrim.finalizerOr (interpreter view) machine fiber yielding (.success value) := by
      rw [evaluatePrim, current]; rfl
    rw [dispatch, finalizer_refs]
    exact heap
  | failure kind cause =>
    have dispatch : evaluatePrim (interpreter view) machine fiber yielding =
        evaluatePrim.finalizerOr (interpreter view) machine fiber yielding (.failure cause) := by
      rw [evaluatePrim, current]; rfl
    rw [dispatch, finalizer_refs]
    exact heap
  | sync kind thunk answer fallback operation =>
    have dispatch : evaluatePrim (interpreter view) machine fiber yielding =
        (match (interpreter view).syncState thunk machine.state with
         | some (state, value) => ⟨{machine with state},
             {fiber with frame := {fiber.frame with current := .success value}}, yielding, .answered, [.drainDue]⟩
         | none => ⟨machine, {fiber with frame := {fiber.frame with current := .success ((interpreter view).syncValue thunk)}},
             yielding, .answered, []⟩) := by
      rw [evaluatePrim, current]; kernel_rfl
    rw [dispatch]
    split
    · rename_i state value found
      exact sync_state_outer operation view machine.state state value heap found
    · exact heap
  | action kind thunk operation action good =>
    have dispatch : evaluatePrim (interpreter view) machine fiber yielding =
        evaluatePrim.withFiber (interpreter view) machine fiber yielding (operation view) := by
      rw [evaluatePrim, current]
      dsimp only
      rw [action view]
      kernel_rfl
    rw [dispatch, action_refs view machine fiber yielding _ (good view)]
    exact heap
  | external op request path =>
    rw [evaluatePrim, current]
    exact heap
  | sleep millis =>
    rw [evaluatePrim, current]
    exact heap
  | yieldNow priority => rw [evaluatePrim, current]; exact heap
  | racePark race =>
    rw [evaluatePrim, current]
    change OuterHeap (registerRace machine fiber yielding race).machine.state.refs
    unfold registerRace
    split <;> exact heap
  | awaitPark targets =>
    rw [evaluatePrim, current]
    change OuterHeap (countdownPark (interpreter view) machine fiber targets .exitsValue).1.state.refs
    rw [countdown_refs]
    exact heap
  | suspend kind point body =>
    rw [evaluatePrim, current]
    change OuterHeap (evaluatePrim.stepFrame (interpreter view) machine fiber yielding).machine.state.refs
    rw [step_frame_refs]; exact heap
  | onSuccess incoming middle body name first next =>
    rw [evaluatePrim, current]
    change OuterHeap (evaluatePrim.stepFrame (interpreter view) machine fiber yielding).machine.state.refs
    rw [step_frame_refs]; exact heap
  | constant middle body next first saved =>
    rw [evaluatePrim, current]
    change OuterHeap (evaluatePrim.stepFrame (interpreter view) machine fiber yielding).machine.state.refs
    rw [step_frame_refs]; exact heap
  | onFailure kind body name first caught =>
    rw [evaluatePrim, current]
    change OuterHeap (evaluatePrim.stepFrame (interpreter view) machine fiber yielding).machine.state.refs
    rw [step_frame_refs]; exact heap
  | onExit kind body name flag first cleanup =>
    rw [evaluatePrim, current]
    change OuterHeap (evaluatePrim.stepFrame (interpreter view) machine fiber yielding).machine.state.refs
    rw [step_frame_refs]; exact heap
  | loop name cursor cursorGood enter resume =>
    rw [evaluatePrim, current]
    change OuterHeap (evaluatePrim.stepFrame (interpreter view) machine fiber yielding).machine.state.refs
    rw [step_frame_refs]; exact heap

/-- Native interception retains the same source write assertion as actual primitive evaluation. -/
theorem native_head_outer {B : List Val} {input output : Kind}
    (machine : Effect4.Program.NativeMachine) (fiber : NativeFiber) (yielding : Bool)
    (head : HeadAt B input fiber.frame.current) (stack : StackAt B input output fiber.frame.stack)
    (heap : OuterHeap machine.state.refs) :
    OuterHeap (evaluateNative HostTimeoutSource.program machine fiber yielding
      Test.Dogfood.Scenario.Timeout.fetch.table).machine.state.refs := by
  have basic := head_outer machine.completedExits machine fiber yielding head heap
  generalize current : fiber.frame.current = code at head
  cases head with
  | success good =>
    rename_i value
    rw [evaluateNative, current]
    dsimp only
    rw [exit_scoped_free machine.completedExits machine fiber yielding (.success value) good stack]
    exact basic
  | failure kind cause =>
    rw [evaluateNative, current]
    dsimp only
    rw [exit_scoped_free machine.completedExits machine fiber yielding (.failure cause) (input := input) trivial stack]
    exact basic
  | action kind thunk operation action good =>
    unfold evaluateNative
    rw [current]
    cases thunk
    case act point =>
      dsimp only
      split
      · rename_i body found
        have absent : (interpreter machine.completedExits).withFiberOf (.act point) = none := by
          change actionAt HostTimeoutSource.program point = none
          unfold actionAt
          rw [found]
        rw [action machine.completedExits] at absent
        cases absent
      · exact basic
    all_goals exact basic
  | sync kind thunk answer fallback operation => rw [evaluateNative, current]; exact basic
  | suspend kind point body => rw [evaluateNative, current]; exact basic
  | onSuccess incoming middle body name first next => rw [evaluateNative, current]; exact basic
  | constant middle body next first saved => rw [evaluateNative, current]; exact basic
  | onFailure kind body name first caught => rw [evaluateNative, current]; exact basic
  | onExit kind body name flag first cleanup => rw [evaluateNative, current]; exact basic
  | loop name cursor cursorGood enter resume => rw [evaluateNative, current]; exact basic
  | yieldNow priority => rw [evaluateNative, current]; exact basic
  | external op request path => rw [evaluateNative, current]; exact basic
  | sleep millis => rw [evaluateNative, current]; exact basic
  | racePark race => rw [evaluateNative, current]; exact basic
  | awaitPark targets => rw [evaluateNative, current]; exact basic

/-- Every actual source-owned native evaluation keeps each cell a number or list. -/
theorem evaluate_native_outer {B : List Val} {output : Kind}
    (machine : Effect4.Program.NativeMachine) (fiber : NativeFiber) (yielding : Bool)
    (owned : FrameKind B output fiber.frame) (heap : OuterHeap machine.state.refs) :
    OuterHeap (evaluateNative HostTimeoutSource.program machine fiber yielding
      Test.Dogfood.Scenario.Timeout.fetch.table).machine.state.refs := by
  obtain ⟨input, code, stack⟩ := owned
  exact native_head_outer machine fiber yielding (code_head code) stack heap

/-- A timeout cell's outer shape fails the actual host row's string membership check. -/
theorem outer_not_string {value : Val} (outer : OuterValue value) (allocated : List String) :
    Val.hasTy value .string allocated = false := by
  cases outer <;> rfl

/-- The actual string answer row refuses every delayed read from Timeout's cells. -/
theorem read_refused (row : Row) (machine : Effect4.Program.NativeMachine) (fiber : FiberId)
    (token : Nat) (cell : RefKey) (answer : row.answer = .string) (heap : OuterHeap machine.state.refs) :
    admitAnswer row machine fiber token (.ofRefGet cell) ≠ none := by
  unfold admitAnswer
  dsimp only
  cases found : machine.state.refs[cell.index]? with
  | none => exact Option.some_ne_none _
  | some value =>
    have outer := heap value (List.mem_of_getElem? found)
    dsimp only
    rw [answer, outer_not_string outer]
    exact Option.some_ne_none _

/-- Timeout's general row envelope cannot admit a delayed reference read. -/
theorem delayed_read_refused (machine : Effect4.Program.NativeMachine) (fiber : FiberId)
    (token : Nat) (cell : RefKey) (heap : OuterHeap machine.state.refs) :
    admit Test.Dogfood.Scenario.Timeout.fetch.table machine (.answerAsync fiber token (.ofRefGet cell)) ≠ none := by
  intro admitted
  unfold admit at admitted
  repeat' split at admitted
  all_goals aesop (add safe forward [row_answer, read_refused])

/-- An admitted Timeout completion is an exit, with its exact success value or arbitrary cause. -/
theorem envelope_exit (machine : Effect4.Program.NativeMachine) (reply : RecordedReply)
    (heap : OuterHeap machine.state.refs) (accepted : Envelope Test.Dogfood.Scenario.Timeout.fetch.table machine reply) :
    ∃ exit, reply.completion = .ofExit exit := by
  cases received : reply.completion with
  | ofExit exit => exact ⟨exit, rfl⟩
  | ofRefGet cell =>
    have admitted := accepted.2.2
    rw [received] at admitted
    exact (delayed_read_refused machine reply.fiber reply.token cell heap admitted).elim

/-- The instance fallback also keeps completions as exits without restricting their causes. -/
theorem instance_envelope_exit (table : RowTable) (instanceAt : List Nat → Option (CallInstance NativeOp))
    (machine : Effect4.Program.NativeMachine) (reply : RecordedReply)
    (accepted : InstanceEnvelope table instanceAt machine reply) :
    ∃ exit, reply.completion = .ofExit exit := by
  cases received : reply.completion with
  | ofExit exit => exact ⟨exit, rfl⟩
  | ofRefGet cell =>
    obtain ⟨index, row, origin, call, _, _, _, _, _, _, admitted⟩ := accepted.2.2
    rw [received] at admitted
    cases admitted

end Test.Dogfood.Proofs.HostTimeoutHeap

/- Finite admission control: the general string row accepts a delayed read of a stored string. -/
#guard Effect4.Program.admitAnswer Test.Dogfood.P1HttpCache.getQuote.row
    { Effect4.Api.load Test.Dogfood.Proofs.HostTimeoutSource.program 0 with
      state := { Effect4.Machine.Stores.empty with refs := [Effect4.Store.Val.str "later"] } }
    ⟨0⟩ 0 (.ofRefGet ⟨0⟩) = none

/- Finite admission readers: Timeout's number/list outer shapes fail the same string column. -/
#guard Effect4.Program.admitAnswer Test.Dogfood.P1HttpCache.getQuote.row
    { Effect4.Api.load Test.Dogfood.Proofs.HostTimeoutSource.program 0 with
      state := { Effect4.Machine.Stores.empty with refs := [Effect4.Store.Val.nat 0] } }
    ⟨0⟩ 0 (.ofRefGet ⟨0⟩) = some (.answerType ⟨0⟩ 0 .string)
#guard Effect4.Program.admitAnswer Test.Dogfood.P1HttpCache.getQuote.row
    { Effect4.Api.load Test.Dogfood.Proofs.HostTimeoutSource.program 0 with
      state := { Effect4.Machine.Stores.empty with refs := [Effect4.Store.Val.list []] } }
    ⟨0⟩ 0 (.ofRefGet ⟨0⟩) = some (.answerType ⟨0⟩ 0 .string)
