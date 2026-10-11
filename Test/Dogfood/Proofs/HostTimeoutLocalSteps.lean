import Test.Dogfood.Proofs.HostTimeoutParkSteps

/-!
Placement: host-session-protocol R6, serving `Timeout.stale_never_applies` clause four.
Consumer: all ordinary native head cases, then the concrete command and history closure.
The assertion reads the existing evaluator result; it stores no new program syntax.
-/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
namespace Test.Dogfood.Proofs.HostTimeoutLocalSteps
open Effect4 Effect4.Machine Effect4.Program Effect4.Laws.Auto
open HostTimeoutSlots HostTimeoutFlow HostTimeoutFrames HostTimeoutEvaluation HostTimeoutCommands
open Effect4.Program.Guard
open HostTimeoutHeap HostTimeoutState HostTimeoutStateSteps HostTimeoutRaceSteps HostTimeoutQueue HostTimeoutParkSteps

/-- The actual evaluator result retains its stored machine, returned fiber and nested commands. -/
def EvaluationAt (B : List Val) (classes : Classes) (result : NativeIter) : Prop :=
  ConfigurationAt B classes result.machine ∧ FiberAt B classes result.fiber ∧
    CommandsAt B classes (result.machine.update result.fiber) result.nested

/-- The ordinary primitive frame evaluator edits only its returned frame and machine events. -/
theorem step_frame_state {B : List Val} {classes : Classes} (view : View)
    (machine : Effect4.Program.NativeMachine) (fiber : NativeFiber) (yielding : Bool)
    (owned : ConfigurationAt B classes machine) (goodFiber : FiberAt B classes fiber)
    (regular : (interpreter view).parkOf fiber.frame.current = none)
    (ordinary : ∀ thunk, fiber.frame.current = .withFiber thunk → (interpreter view).withFiberOf thunk = none)
    (parked : fiber.parked = .notParked) (live : fiber.exit.isSome = false) :
    EvaluationAt B classes (evaluatePrim.stepFrame (interpreter view) machine fiber yielding) := by
  have next := (step_frame view machine fiber yielding goodFiber.frame regular ordinary).frame
  unfold EvaluationAt evaluatePrim.stepFrame
  cases pair : fiber.frame.step (interpreter view).toPrimInterp with
  | mk step events =>
    rw [evaluatePrim.stepFrame, pair] at next
    cases step with
    | running frame =>
      exact ⟨configuration_emit owned _, set_frame_live goodFiber frame next parked live,
        by intro command member; cases member⟩
    | finished exit =>
      exact ⟨configuration_emit owned _, set_frame_live goodFiber _ next parked live,
        by intro command member; cases member⟩

/-- A synchronous Timeout source head changes only its proved outer cell shapes or timer registrations. -/
theorem sync_configuration {B : List Val} {classes : Classes} (machine : Effect4.Program.NativeMachine)
    (owned : ConfigurationAt B classes machine) (view : View) (thunk : EffThunk) (allowed : SyncAt thunk)
    (next : Stores) (value : Val) (found : (interpreter view).syncState thunk machine.state = some (next, value)) :
    ConfigurationAt B classes {machine with state := next} := by
  have outer := sync_state_outer allowed view machine.state next value owned.refs found
  rcases sync_state_shape allowed view machine.state next value found with ⟨refs, equal⟩ | ⟨waiter, token, equal⟩
  · subst next
    exact ⟨owned.supply, owned.kinds, owned.fibers, owned.races, owned.timers,
      outer, owned.deferreds, owned.scopes⟩
  · subst next
    refine ⟨owned.supply, owned.kinds, owned.fibers, owned.races, ?_,
      outer, owned.deferreds, owned.scopes⟩
    intro next member
    simp only [TimerStore.cancel, WakeList.cancel] at member
    split at member
    · exact owned.timers next (List.mem_filter.mp member).1
    · exact owned.timers next member

/-- A native synchronous source operation uses only its checked source answer and cell-shape transfer. -/
theorem sync_evaluation {B : List Val} {classes : Classes} {input : Kind} (view : View)
    (machine : Effect4.Program.NativeMachine) (fiber : NativeFiber) (yielding : Bool) (thunk : EffThunk)
    (owned : ConfigurationAt B classes machine) (goodFiber : FiberAt B classes fiber)
    (current : fiber.frame.current = .sync thunk) (allowed : SyncAt thunk)
    (answer : ∀ view state next value, (interpreter view).syncState thunk state = some (next, value) → ValueAt B input value)
    (fallback : ∀ view, ValueAt B input ((interpreter view).syncValue thunk))
    (stack : StackAt B input .body fiber.frame.stack) (parked : fiber.parked = .notParked)
    (live : fiber.exit.isSome = false) : EvaluationAt B classes (evaluatePrim (interpreter view) machine fiber yielding) := by
  have dispatch : evaluatePrim (interpreter view) machine fiber yielding =
      (match (interpreter view).syncState thunk machine.state with
       | some (state, value) => ⟨{machine with state},
           {fiber with frame := {fiber.frame with current := .success value}}, yielding, .answered, [.drainDue]⟩
       | none => ⟨machine, {fiber with frame := {fiber.frame with current := .success ((interpreter view).syncValue thunk)}},
           yielding, .answered, []⟩) := by
    rw [evaluatePrim, current]
    kernel_rfl
  rw [dispatch]
  cases found : (interpreter view).syncState thunk machine.state with
  | none =>
    exact ⟨owned, reframe_live goodFiber (.head (.success (fallback view))) stack parked live,
      by intro command member; cases member⟩
  | some pair =>
    obtain ⟨state, value⟩ := pair
    refine ⟨sync_configuration machine owned view thunk allowed state value found,
      reframe_live goodFiber (.head (.success (answer view machine.state state value found))) stack parked live, ?_⟩
    intro command member
    have equal := List.mem_singleton.mp member
    subst command
    trivial

/-- Running the actual source finalizer retains the saved body through its unit cleanup program. -/
theorem finalizer_evaluation {B : List Val} {classes : Classes} {input : Kind} (view : View)
    (machine : Effect4.Program.NativeMachine) (fiber : NativeFiber) (yielding : Bool) (exit : ExitV)
    (owned : ConfigurationAt B classes machine) (goodFiber : FiberAt B classes fiber)
    (current : fiber.frame.current = Prim.ofExit exit) (goodExit : ExitAt B input exit)
    (stack : StackAt B input .body fiber.frame.stack) (parked : fiber.parked = .notParked)
    (live : fiber.exit.isSome = false) :
    EvaluationAt B classes (evaluatePrim.finalizerOr (interpreter view) machine fiber yielding exit) := by
  have typed := (finalizer_or view machine fiber yielding exit current goodExit stack).frame
  have regular : (interpreter view).parkOf fiber.frame.current = none := by cases exit <;> rw [current] <;> rfl
  have ordinary : ∀ thunk, fiber.frame.current = .withFiber thunk → (interpreter view).withFiberOf thunk = none := by
    intro thunk equal
    cases exit <;> rw [current] at equal <;> cases equal
  have fallback := step_frame_state view machine fiber yielding owned goodFiber regular ordinary parked live
  unfold evaluatePrim.finalizerOr at typed
  cases exit <;> unfold EvaluationAt evaluatePrim.finalizerOr <;> dsimp only at typed ⊢
  all_goals
    split
    · rename_i body name flag answer
      rw [answer] at typed
      dsimp only at typed
      split
      · rename_i program selected
        rw [selected] at typed
        exact ⟨configuration_emit owned _, set_frame_live goodFiber _ typed parked live,
          by intro command member; cases member⟩
      · exact fallback
    · exact fallback

/-- Removing observers retains the assertions on all remaining callbacks. -/
theorem filter_observers_fiber {B : List Val} {classes : Classes} {fiber : NativeFiber}
    (owned : FiberAt B classes fiber) (keep : Observer → Bool) :
    FiberAt B classes {fiber with observers := fiber.observers.filter keep} where
  frame := owned.frame
  park := owned.park
  pending := owned.pending
  dispatcher := owned.dispatcher
  observers := fun observer member => owned.observers observer (List.mem_filter.mp member).1
  exits := owned.exits
  terminal := owned.terminal
  children := owned.children

/-- The actual observer cancellation changes no value-bearing state. -/
theorem filter_observers_configuration {B : List Val} {classes : Classes} {machine : Effect4.Program.NativeMachine}
    (owned : ConfigurationAt B classes machine) (keep : Observer → Bool) :
    ConfigurationAt B classes {machine with fibers := (machine.fibers.map
      (fun fiber => {fiber with observers := fiber.observers.filter keep})) } where
  supply := owned.supply
  kinds := owned.kinds
  fibers := by
    intro fiber member
    obtain ⟨old, present, equal⟩ := List.mem_map.mp member
    subst fiber
    exact filter_observers_fiber (owned.fibers old present) keep
  races := owned.races
  timers := owned.timers
  refs := owned.refs
  deferreds := owned.deferreds
  scopes := owned.scopes

/-- Each actual Timeout fiber action keeps the full source assertion, including installed nested stack demands. -/
theorem with_fiber_evaluation {B : List Val} {classes : Classes} {input : Kind} (view : View)
    (machine : Effect4.Program.NativeMachine) (fiber : NativeFiber) (yielding : Bool) (action : NAction)
    (owned : ConfigurationAt B classes machine) (goodFiber : FiberAt B classes fiber)
    (allowed : ActionAt B input action) (current : CodeAt B input fiber.frame.current)
    (stack : StackAt B input .body fiber.frame.stack) (parked : fiber.parked = .notParked)
    (live : fiber.exit.isSome = false) (stored : ∃ old, machine.fiber? fiber.id = some old) :
    ∃ after, ClassLe classes after ∧
      EvaluationAt B after (evaluatePrim.withFiber (interpreter view) machine fiber yielding action) := by
  cases allowed with
  | race programs site entrants =>
    have result := begin_race_state machine fiber yielding programs site view owned goodFiber entrants stack parked live
    refine ⟨classes ++ [.body], ClassLe.append classes .body, result.1, result.2.1, ?_⟩
    intro command member
    cases member
  | mask kind body flag good =>
    refine ⟨classes, classOrder.refl classes, ?_⟩
    cases flag
    · unfold EvaluationAt evaluatePrim.withFiber FrameFiber.uninterruptible
      dsimp only
      split
      · exact ⟨owned, set_frame_live goodFiber _ ⟨input, good, .cons (.mask input true) stack⟩ parked live,
          by intro command member; cases member⟩
      · exact ⟨owned, set_frame_live goodFiber _ ⟨input, good, stack⟩ parked live,
          by intro command member; cases member⟩
    · unfold EvaluationAt evaluatePrim.withFiber FrameFiber.interruptibleRegion FrameFiber.setFiberInterruptible
      dsimp only
      split
      · exact ⟨owned, set_frame_live goodFiber _ ⟨input, good, stack⟩ parked live,
          by intro command member; cases member⟩
      · split
        · exact ⟨owned, set_frame_live goodFiber _ ⟨input, .head (.failure input _), .cons (.mask input false) stack⟩ parked live,
            by intro command member; cases member⟩
        · exact ⟨owned, set_frame_live goodFiber _ ⟨input, good, .cons (.mask input false) stack⟩ parked live,
            by intro command member; cases member⟩
  | cancelRace raceId =>
    refine ⟨classes, classOrder.refl classes, ?_⟩
    unfold EvaluationAt evaluatePrim.withFiber
    dsimp only
    split
    · exact ⟨owned, reframe_live goodFiber (.head (.success .unit)) stack parked live,
        by intro command member; cases member⟩
    · rename_i race found
      refine ⟨owned, goodFiber, ?_⟩
      intro command member
      have equal := List.mem_singleton.mp member
      subst command
      intro next lookup
      obtain ⟨old, held⟩ := stored
      have self := fiber_lookup_update_self held fiber rfl
      have equal : fiber = next := Option.some.inj (self.symm.trans lookup)
      subst next
      exact stack
  | dropObservers token =>
    refine ⟨classes, classOrder.refl classes, ?_⟩
    exact ⟨filter_observers_configuration owned _, reframe_live goodFiber (.head (.success .unit)) stack parked live,
      by intro command member; cases member⟩

/-- All fifteen native primitive source cases retain the whole Timeout assertion. -/
theorem evaluate_head_state {B : List Val} {classes : Classes} {input : Kind} (view : View)
    (machine : Effect4.Program.NativeMachine) (fiber : NativeFiber) (yielding : Bool)
    (owned : ConfigurationAt B classes machine) (goodFiber : FiberAt B classes fiber)
    (head : HeadAt B input fiber.frame.current) (stack : StackAt B input .body fiber.frame.stack)
    (parked : fiber.parked = .notParked) (live : fiber.exit.isSome = false)
    (stored : ∃ old, machine.fiber? fiber.id = some old) :
    ∃ after, ClassLe classes after ∧ EvaluationAt B after (evaluatePrim (interpreter view) machine fiber yielding) := by
  generalize current : fiber.frame.current = code at head
  cases head with
  | success good =>
    rename_i value
    have dispatch : evaluatePrim (interpreter view) machine fiber yielding =
        evaluatePrim.finalizerOr (interpreter view) machine fiber yielding (.success value) := by
      rw [evaluatePrim, current]; rfl
    rw [dispatch]
    exact ⟨classes, classOrder.refl classes,
      finalizer_evaluation view machine fiber yielding _ owned goodFiber current good stack parked live⟩
  | failure kind cause =>
    have dispatch : evaluatePrim (interpreter view) machine fiber yielding =
        evaluatePrim.finalizerOr (interpreter view) machine fiber yielding (.failure cause) := by
      rw [evaluatePrim, current]; rfl
    rw [dispatch]
    exact ⟨classes, classOrder.refl classes,
      finalizer_evaluation view machine fiber yielding _ owned goodFiber current trivial stack parked live⟩
  | sync kind thunk answer fallback operation =>
    exact ⟨classes, classOrder.refl classes,
      sync_evaluation view machine fiber yielding thunk owned goodFiber current operation answer fallback stack parked live⟩
  | action kind thunk operation action good =>
    have dispatch : evaluatePrim (interpreter view) machine fiber yielding =
        evaluatePrim.withFiber (interpreter view) machine fiber yielding (operation view) := by
      rw [evaluatePrim, current]; dsimp only; rw [action view]; kernel_rfl
    rw [dispatch]
    exact with_fiber_evaluation view machine fiber yielding _ owned goodFiber (good view)
      (by rw [current]; exact .head (.action _ _ operation action good)) stack parked live stored
  | external op request path =>
    have result := external_park_state machine fiber yielding view op request path owned goodFiber current stack
    refine ⟨classes ++ [.body], ClassLe.append classes .body, result.1, result.2.1, ?_⟩
    simp only [evaluatePrim, current]
    intro command member; cases member
  | sleep millis =>
    have result := sleep_park_state machine fiber yielding view millis owned goodFiber current stack parked live
    refine ⟨classes ++ [.unit], ClassLe.append classes .unit, result.1, result.2.1, ?_⟩
    simp only [evaluatePrim, current]
    intro command member; cases member
  | yieldNow priority =>
    have result := yield_park_state machine fiber yielding view priority owned goodFiber current stack parked live
    refine ⟨classes ++ [.unit], ClassLe.append classes .unit, result.1, result.2.1, ?_⟩
    simp only [evaluatePrim, current]
    intro command member; cases member
  | awaitPark targets =>
    have result := await_park_state machine fiber yielding view targets owned goodFiber current stack parked live
    refine ⟨classes ++ [.any], ClassLe.append classes .any, result.1, result.2.1, ?_⟩
    simp only [evaluatePrim, current]
    intro command member; cases member
  | racePark race =>
    have result := race_park_state machine fiber yielding view race owned goodFiber current
    refine ⟨classes, classOrder.refl classes, result.1, result.2.1, ?_⟩
    have dispatch : evaluatePrim (interpreter view) machine fiber yielding =
        registerRace machine fiber yielding race := by rw [evaluatePrim, current]; rfl
    rw [dispatch]
    unfold registerRace
    split
    · intro command member; cases member
    · intro command member
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with equal | equal <;> subst command <;> trivial
  | suspend kind point body =>
    have dispatch : evaluatePrim (interpreter view) machine fiber yielding =
        evaluatePrim.stepFrame (interpreter view) machine fiber yielding := by rw [evaluatePrim, current]; rfl
    rw [dispatch]
    refine ⟨classes, classOrder.refl classes, step_frame_state view machine fiber yielding owned goodFiber ?_ ?_ parked live⟩
    · rw [current]; rfl
    · intro thunk wrong; rw [current] at wrong; cases wrong
  | onSuccess incoming middle body name first next =>
    have dispatch : evaluatePrim (interpreter view) machine fiber yielding =
        evaluatePrim.stepFrame (interpreter view) machine fiber yielding := by rw [evaluatePrim, current]; rfl
    rw [dispatch]
    refine ⟨classes, classOrder.refl classes, step_frame_state view machine fiber yielding owned goodFiber ?_ ?_ parked live⟩
    · rw [current]; rfl
    · intro thunk wrong; rw [current] at wrong; cases wrong
  | constant middle body next first saved =>
    have dispatch : evaluatePrim (interpreter view) machine fiber yielding =
        evaluatePrim.stepFrame (interpreter view) machine fiber yielding := by rw [evaluatePrim, current]; rfl
    rw [dispatch]
    refine ⟨classes, classOrder.refl classes, step_frame_state view machine fiber yielding owned goodFiber ?_ ?_ parked live⟩
    · rw [current]; rfl
    · intro thunk wrong; rw [current] at wrong; cases wrong
  | onFailure kind body name first caught =>
    have dispatch : evaluatePrim (interpreter view) machine fiber yielding =
        evaluatePrim.stepFrame (interpreter view) machine fiber yielding := by rw [evaluatePrim, current]; rfl
    rw [dispatch]
    refine ⟨classes, classOrder.refl classes, step_frame_state view machine fiber yielding owned goodFiber ?_ ?_ parked live⟩
    · rw [current]; rfl
    · intro thunk wrong; rw [current] at wrong; cases wrong
  | onExit kind body name flag first cleanup =>
    have dispatch : evaluatePrim (interpreter view) machine fiber yielding =
        evaluatePrim.stepFrame (interpreter view) machine fiber yielding := by rw [evaluatePrim, current]; rfl
    rw [dispatch]
    refine ⟨classes, classOrder.refl classes, step_frame_state view machine fiber yielding owned goodFiber ?_ ?_ parked live⟩
    · rw [current]; rfl
    · intro thunk wrong; rw [current] at wrong; cases wrong
  | loop name cursor cursorGood enter resume =>
    have dispatch : evaluatePrim (interpreter view) machine fiber yielding =
        evaluatePrim.stepFrame (interpreter view) machine fiber yielding := by rw [evaluatePrim, current]; rfl
    rw [dispatch]
    refine ⟨classes, classOrder.refl classes, step_frame_state view machine fiber yielding owned goodFiber ?_ ?_ parked live⟩
    · rw [current]; rfl
    · intro thunk wrong; rw [current] at wrong; cases wrong

/-- Native source interception has no extra value-producing case for Timeout. -/
theorem evaluate_native_head_state {B : List Val} {classes : Classes} {input : Kind}
    (machine : Effect4.Program.NativeMachine) (fiber : NativeFiber) (yielding : Bool)
    (owned : ConfigurationAt B classes machine) (goodFiber : FiberAt B classes fiber)
    (head : HeadAt B input fiber.frame.current) (stack : StackAt B input .body fiber.frame.stack)
    (parked : fiber.parked = .notParked) (live : fiber.exit.isSome = false)
    (stored : ∃ old, machine.fiber? fiber.id = some old) :
    ∃ after, ClassLe classes after ∧ EvaluationAt B after (evaluateNative HostTimeoutSource.program machine fiber yielding
      Test.Dogfood.Scenario.Timeout.fetch.table) := by
  have basic := evaluate_head_state machine.completedExits machine fiber yielding owned goodFiber head stack parked live stored
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

/-- The concrete native evaluator retains all stored source and value assertions. -/
theorem evaluate_native_state {B : List Val} {classes : Classes}
    (machine : Effect4.Program.NativeMachine) (fiber : NativeFiber) (yielding : Bool)
    (owned : ConfigurationAt B classes machine) (goodFiber : FiberAt B classes fiber)
    (parked : fiber.parked = .notParked) (live : fiber.exit.isSome = false)
    (stored : ∃ old, machine.fiber? fiber.id = some old) :
    ∃ after, ClassLe classes after ∧ EvaluationAt B after
      (evaluateNative HostTimeoutSource.program machine fiber yielding Test.Dogfood.Scenario.Timeout.fetch.table) := by
  obtain ⟨input, code, stack⟩ := goodFiber.frame
  exact evaluate_native_head_state machine fiber yielding owned goodFiber (code_head code) stack parked live stored

end Test.Dogfood.Proofs.HostTimeoutLocalSteps
