import Effect4.Laws.Program.AnswerSlots.InitializedNativeShapes
import Effect4.Laws.Program.NativeActionFlow

/-!
Concept: store-typing R4 and scope-lifetime-finalization R11.
Question: actual native parks retain initialized current classes and their ordered saved suffixes.
Reach: forced yields, asynchronous registration, countdowns and administrative cancellation frames.
Limit: command admission and the shared state transport remain separate carried facts.
Consumer: the initialized crew primitive producer and release-log histories.
-/
set_option autoImplicit false
namespace Effect4.Program.AnswerSlots.Initialized
open Effect4 Effect4.Machine Effect4.Program

/-- Native cancellation is a stable identity edge at the actual world. -/
theorem async_edge (spec : Spec) (completed : List (FiberId × ExitV)) (world : World)
    (ready : Ready spec world) (name : EffName) :
    Edge spec completed world (.stable .root) (.stable .root) (.asyncFinalizer name) :=
  .mapped ready (Typed.async_edge spec.toSpec completed name)

/-- Every actual yield answers unit at its own transient or stable class. -/
theorem yield_value (spec : Spec) (world : World) (kind : Kind) (program : NCode) (priority : Nat)
    (owned : CodeAt spec world kind program) (current : program = .yieldNowWith priority) :
    ValueAt spec world kind .unit := by
  cases owned
  case initial stage =>
    rcases initial_shape spec world _ _ stage with ⟨body, name, same⟩ | same | ⟨cause, same⟩
    all_goals rw [same] at current
    all_goals cases current
  case stable ready held =>
    rw [current] at held
    exact ⟨ready, held ▸ True.intro⟩
  case yielding phase refs deferred pending => exact ⟨phase, refs, deferred, pending⟩
  all_goals cases current

/-- Yield's actual unit reply retains the parked frame's saved suffix. -/
theorem yield_frame (spec : Spec) (completed : List (FiberId × ExitV)) (world : World)
    (input output : Kind) (frame : FrameFiber EffName EffThunk Val Err Defect FiberId Ann) (priority : Nat)
    (owned : CodeAt spec world input frame.current) (current : frame.current = .yieldNowWith priority)
    (saved : Effect4.Contracts.Path (Edge spec completed world) input output frame.stack) :
    AnswerFlow.FamilyResult (model spec completed) (Edge spec completed) world output
      (.success .unit) frame.stack :=
  ⟨input, .success (yield_value spec world input frame.current priority owned current), saved⟩

/-- Registering a deferred waiter retains the number of deferred cells. -/
theorem register_length (store : DeferredStore) (cell : DeferredKey) (owner : FiberId) (token : Nat) :
    (store.register cell owner token).1.cells.length = store.cells.length := by
  unfold DeferredStore.register
  split
  · rfl
  · split
    · rfl
    · exact DeferredStore.setCell_cells_length _ _ _

/-- Native asynchronous registration changes no allocation counts. -/
theorem register_counts (spec : Spec) (completed : List (FiberId × ExitV)) (world : World)
    (name : EffName) (owner : FiberId) (token : Nat) :
    let state := ((interpAt spec.root completed spec.table).registerAsync name owner token world.state).1
    state.refs.length = world.state.refs.length ∧
      state.deferreds.cells.length = world.state.deferreds.cells.length := by
  cases name
  case registerAwait cell => exact ⟨rfl, register_length _ _ _ _⟩
  case store name =>
    cases name
    case registerAwait cell => exact ⟨rfl, register_length _ _ _ _⟩
    all_goals exact ⟨rfl, rfl⟩
  all_goals exact ⟨rfl, rfl⟩

/-- A deferred completion exposes an actual exit or reference read at the broad stable class. -/
theorem completion_code (spec : Spec) (completion : Completion Val Err Defect FiberId Ann) :
    Typed.CodeAt spec.toSpec .root (embed (completionPrim completion)) := by
  cases completion with
  | ofExit exit => cases exit <;> trivial
  | ofRefGet cell => trivial

/-- Registration's immediate completion belongs to the existing broad source class. -/
theorem register_code (spec : Spec) (completed : List (FiberId × ExitV)) (name : EffName)
    (owner : FiberId) (token : Nat) (state : Stores) :
    ∀ code ∈ ((interpAt spec.root completed spec.table).registerAsync name owner token state).2,
      Typed.CodeAt spec.toSpec .root code := by
  cases name
  case registerAwait cell =>
    intro code member
    rw [Option.mem_def] at member
    obtain ⟨answer, _, same⟩ := Option.map_eq_some_iff.mp member
    rw [← same]
    exact completion_code spec answer
  case store name =>
    cases name
    case registerAwait cell =>
      intro code member
      rw [Option.mem_def] at member
      obtain ⟨answer, _, same⟩ := Option.map_eq_some_iff.mp member
      rw [← same]
      exact completion_code spec answer
    all_goals intro code member; cases member
  all_goals intro code member; cases member

/-- Actual immediate registration transports its old saved suffix and uses the returned completion. -/
theorem immediate_frame (spec : Spec) (completed : List (FiberId × ExitV)) (world : World)
    (input output : Kind) (frame : FrameFiber EffName EffThunk Val Err Defect FiberId Ann)
    (name : EffName) (signal : Bool) (cancel : Option EffName) (token : Nat) (state : Stores) (code : NCode)
    (owned : CodeAt spec world input frame.current) (current : frame.current = .async name signal cancel)
    (saved : Effect4.Contracts.Path (Edge spec completed world) input output frame.stack)
    (registered : (interpAt spec.root completed spec.table).registerAsync name world.owner token world.state = (state, some code)) :
    AnswerFlow.FamilyResult (model spec completed) (Edge spec completed) ⟨world.owner, state⟩ output code frame.stack := by
  obtain ⟨same, ready⟩ := async_shape spec world input name signal cancel (current ▸ owned)
  subst input
  have counts := register_counts spec completed world name world.owner token
  rw [registered] at counts
  have future : Future world ⟨world.owner, state⟩ := ⟨rfl, Nat.le_of_eq counts.1.symm, Nat.le_of_eq counts.2.symm⟩
  have allowed := register_code spec completed name world.owner token world.state
  rw [registered] at allowed
  exact ⟨.stable .root, .stable (ready_future spec world _ future ready) (allowed code rfl),
    path_future spec completed world _ future _ output frame.stack saved⟩

/-- Actual asynchronous parking retains the current code and the installed cancellation edge. -/
theorem parked_frame (spec : Spec) (completed : List (FiberId × ExitV)) (world : World)
    (input output : Kind) (frame : FrameFiber EffName EffThunk Val Err Defect FiberId Ann)
    (name : EffName) (signal : Bool) (cancel : Option EffName) (token : Nat) (state : Stores)
    (owned : CodeAt spec world input frame.current) (current : frame.current = .async name signal cancel)
    (saved : Effect4.Contracts.Path (Edge spec completed world) input output frame.stack)
    (registered : (interpAt spec.root completed spec.table).registerAsync name world.owner token world.state = (state, none)) :
    let stack := if signal || cancel.isSome then
      Prim.asyncFinalizer ((interpAt spec.root completed spec.table).cancelName
        (cancel.getD (interpAt spec.root completed spec.table).abortName) world.owner token) :: frame.stack
      else frame.stack
    AnswerFlow.FamilyResult (model spec completed) (Edge spec completed) ⟨world.owner, state⟩ output frame.current stack := by
  obtain ⟨same, ready⟩ := async_shape spec world input name signal cancel (current ▸ owned)
  subst input
  have counts := register_counts spec completed world name world.owner token
  rw [registered] at counts
  have future : Future world ⟨world.owner, state⟩ := ⟨rfl, Nat.le_of_eq counts.1.symm, Nat.le_of_eq counts.2.symm⟩
  have code := code_future_ready spec world (.stable .root) frame.current owned _ future ready
  have suffix := path_future spec completed world _ future (.stable .root) output frame.stack saved
  split
  · exact ⟨.stable .root, code, .cons (async_edge spec completed _
      (ready_future spec world _ future ready) _) suffix⟩
  · exact ⟨.stable .root, code, suffix⟩

/-- Joining an already exited fiber exposes only a broad successful value or actual failure. -/
theorem joined_code (spec : Spec) (completed : List (FiberId × ExitV)) (world : World)
    (ready : Ready spec world) (exit : ExitV) (mode : Supervision.ObserverMode) :
    CodeAt spec world (.stable .root) ((interpAt spec.root completed spec.table).exitValue exit mode) := by
  cases mode
  · exact .success ⟨ready, trivial⟩
  · cases exit
    · exact .success ⟨ready, trivial⟩
    · exact .failure (.inr ready)

/-- Countdown entry uses the shared native action law rather than another countdown walk. -/
theorem countdown_frame (spec : Spec) (completed : List (FiberId × ExitV)) (world : World)
    (output : Kind) (machine : NativeMachine) (fiber : SourceScope.SourceFiber)
    (targets : List FiberId) (failFast : Bool) (ready : Ready spec world)
    (owned : CodeAt spec world (.stable .root) fiber.frame.current)
    (saved : Effect4.Contracts.Path (Edge spec completed world) (.stable .root) output fiber.frame.stack) :
    let next := (countdownParkEdits (interpAt spec.root completed spec.table) machine fiber targets .exitsValue failFast).2.1
    AnswerFlow.FamilyResult (model spec completed) (Edge spec completed) world output next.frame.current next.frame.stack := by
  apply SourceScope.countdown_family (model spec completed) (Edge spec completed)
    spec.root completed spec.table world (.stable .root) output machine fiber targets .exitsValue failFast owned saved
  · intro exits
    exact .success ⟨ready, trivial⟩
  · exact async_edge spec completed world ready _
end Effect4.Program.AnswerSlots.Initialized
