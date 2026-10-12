import Test.Dogfood.Proofs.HostTimeoutQueue

/-!
Placement: host-session-protocol R6, serving `Timeout.stale_never_applies` clause four.
Consumer: all fresh park cases of the concrete native evaluator, then command history closure.
Each actual minted token receives one entry in the existing class list.
No reply admission, source program or runtime field changes here.
-/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
namespace Test.Dogfood.Proofs.HostTimeoutParkSteps
open Effect4 Effect4.Machine Effect4.Program Effect4.Laws.Auto
open HostTimeoutSlots HostTimeoutFlow HostTimeoutFrames HostTimeoutEvaluation HostTimeoutCommands
open HostTimeoutHeap HostTimeoutState HostTimeoutStateSteps HostTimeoutRaceSteps HostTimeoutQueue

/-- Installing a live active frame uses the source's explicit ordered success class. -/
theorem set_frame_live {B : List Val} {classes : Classes} {fiber : NativeFiber}
    (owned : FiberAt B classes fiber) (frame : NativeFrame) (good : FrameKind B .body frame)
    (parked : fiber.parked = .notParked) (live : fiber.exit.isSome = false) :
    FiberAt B classes {fiber with frame} where
  frame := good
  park := by intro token held; change fiber.parked = .withGuard token at held; rw [parked] at held; cases held
  pending := owned.pending
  dispatcher := owned.dispatcher
  observers := owned.observers
  exits := owned.exits
  terminal := by intro exited; change fiber.exit.isSome = true at exited; rw [live] at exited; cases exited
  children := owned.children

/-- A newly held park and its saved continuation use the same immutable token class. -/
theorem park_fiber {B : List Val} {classes : Classes} {fiber : NativeFiber} {kind : Kind}
    (owned : FiberAt B classes fiber) (pending : NPending) (token : TokenAt classes pending.token kind)
    (current : CodeAt B kind fiber.frame.current) (stack : StackAt B kind .body fiber.frame.stack)
    (resume : PendingAt classes pending) : FiberAt B classes (fiber.park pending) where
  frame := owned.frame
  park := by
    intro other held
    change Parked.withGuard pending.token = Parked.withGuard other at held
    have equal := Parked.withGuard.inj held
    subst other
    exact ⟨kind, token, current, stack⟩
  pending := by
    intro next member
    rcases List.mem_append.mp member with previous | last
    · exact owned.pending next previous
    · have equal := List.mem_singleton.mp last; subst next; exact resume
  dispatcher := owned.dispatcher
  observers := owned.observers
  exits := owned.exits
  terminal := owned.terminal
  children := owned.children

/-- The actual external registration mints a body token without obtaining any host body yet. -/
theorem external_park_state {B : List Val} {classes : Classes}
    (machine : Effect4.Program.NativeMachine) (fiber : NativeFiber) (yielding : Bool) (view : View)
    (op : NativeOp) (request : Val) (path : List Nat)
    (owned : ConfigurationAt B classes machine) (goodFiber : FiberAt B classes fiber)
    (current : fiber.frame.current = .async (.external op request path) false none)
    (stack : StackAt B .body .body fiber.frame.stack) :
    let result := evaluatePrim (interpreter view) machine fiber yielding
    ConfigurationAt B (classes ++ [.body]) result.machine ∧
      FiberAt B (classes ++ [.body]) result.fiber ∧
        CommandsAt B (classes ++ [.body]) result.machine result.nested := by
  have minted := configuration_mint owned .body (Or.inl rfl)
  have fresh : TokenAt (classes ++ [.body]) machine.nextToken .body := by
    rw [← owned.supply]
    exact token_fresh classes .body
  have code : CodeAt B .body fiber.frame.current := by
    rw [current]
    exact .head (.external op request path)
  let pending : NPending := ⟨machine.nextToken, [], [], .void, false⟩
  have park := park_fiber (fiber_extend (ClassLe.append classes .body) goodFiber)
    pending fresh code stack ⟨.body, fresh, rfl⟩
  simp only [evaluatePrim, current]
  exact ⟨configuration_emit minted _, park, by intro command member; cases member⟩

/-- The actual sleep registration mints a unit token and pushes only its declared cancellation frame. -/
theorem sleep_park_state {B : List Val} {classes : Classes}
    (machine : Effect4.Program.NativeMachine) (fiber : NativeFiber) (yielding : Bool) (view : View)
    (millis : ClockMillis) (owned : ConfigurationAt B classes machine) (goodFiber : FiberAt B classes fiber)
    (current : fiber.frame.current = .async (.store (.registerSleep millis)) true (some (.store .cancelSleep)))
    (stack : StackAt B .unit .body fiber.frame.stack) (parked : fiber.parked = .notParked)
    (live : fiber.exit.isSome = false) :
    let result := evaluatePrim (interpreter view) machine fiber yielding
    ConfigurationAt B (classes ++ [.unit]) result.machine ∧
      FiberAt B (classes ++ [.unit]) result.fiber ∧
        CommandsAt B (classes ++ [.unit]) result.machine result.nested := by
  have minted := configuration_mint owned .unit (Or.inr (Or.inl rfl))
  have fresh : TokenAt (classes ++ [.unit]) machine.nextToken .unit := by
    rw [← owned.supply]
    exact token_fresh classes .unit
  let middle : Effect4.Program.NativeMachine :=
    {machine with
      nextToken := machine.nextToken + 1
      state := {machine.state with timers := machine.state.timers.sleep fiber.id machine.nextToken millis}}
  have slept : ConfigurationAt B (classes ++ [.unit]) middle := {
    supply := minted.supply
    kinds := minted.kinds
    fibers := minted.fibers
    races := minted.races
    timers := by
      intro waiter member
      change waiter ∈ (machine.state.timers.sleep fiber.id machine.nextToken millis).wake.waiters at member
      simp only [TimerStore.sleep, WakeList.register_phase, List.mem_append, List.mem_singleton] at member
      rcases member with previous | equal
      · exact minted.timers waiter previous
      · subst waiter; exact fresh
    refs := owned.refs
    deferreds := owned.deferreds
    scopes := owned.scopes }
  let name : EffName := .withWaiter (.store .cancelSleep) fiber.id machine.nextToken
  have code : CodeAt B .unit fiber.frame.current := by rw [current]; exact .head (.sleep millis)
  have saved : StackAt B .unit .body (.asyncFinalizer name :: fiber.frame.stack) :=
    .cons (.cancel .unit name (cancel_then_failure (.sleep fiber.id machine.nextToken) .unit)) stack
  let frame : NativeFrame := {fiber.frame with stack := .asyncFinalizer name :: fiber.frame.stack}
  have framed := set_frame_live (fiber_extend (ClassLe.append classes .unit) goodFiber)
    frame ⟨.unit, code, saved⟩ parked live
  let pending : NPending := ⟨machine.nextToken, [], [], .void, false⟩
  have held := park_fiber framed pending fresh code saved ⟨.unit, fresh, rfl⟩
  simp only [frame, current] at held
  simp only [evaluatePrim, current]
  exact ⟨configuration_emit slept _, held, by intro command member; cases member⟩

/-- Editing an existing fiber transports its entire concrete assertion. -/
theorem configuration_modify {B : List Val} {classes : Classes} {machine : Effect4.Program.NativeMachine}
    (owned : ConfigurationAt B classes machine) (id : FiberId) (edit : NativeFiber → NativeFiber)
    (keeps : ∀ fiber, FiberAt B classes fiber → FiberAt B classes (edit fiber)) :
    ConfigurationAt B classes (machine.modify id edit) := by
  unfold RunMachine.modify
  split
  · exact owned
  · rename_i fiber found
    exact configuration_update owned _ (keeps fiber (configuration_fiber owned found))

/-- Adding a permitted observer changes no successful value or saved continuation. -/
theorem observer_fiber {B : List Val} {classes : Classes} {fiber : NativeFiber}
    (owned : FiberAt B classes fiber) (observer : Observer) (allowed : ObserverAt classes observer) :
    FiberAt B classes {fiber with observers := fiber.observers ++ [observer]} where
  frame := owned.frame
  park := owned.park
  pending := owned.pending
  dispatcher := owned.dispatcher
  observers := by
    intro next member
    rcases List.mem_append.mp member with previous | last
    · exact owned.observers next previous
    · have equal := List.mem_singleton.mp last; subst next; exact allowed
  exits := owned.exits
  terminal := owned.terminal
  children := owned.children

/-- The canonical countdown plan retains its freshly minted observer permission.
Consumer: actual native await and shared message-word settlement. -/
theorem countdown_plan_state {B : List Val} {classes : Classes}
    (machine : Effect4.Program.NativeMachine) (fiber : NativeFiber) (view : View) (targets : List FiberId)
    (owned : ConfigurationAt B classes machine) (goodFiber : FiberAt B classes fiber)
    (code : CodeAt B .any fiber.frame.current) (stack : StackAt B .any .body fiber.frame.stack)
    (parked : fiber.parked = .notParked) (live : fiber.exit.isSome = false) :
    let result := countdownParkEdits (interpreter view) machine fiber targets .exitsValue
    ConfigurationAt B (classes ++ [.any]) result.1 ∧
      FiberAt B (classes ++ [.any]) result.2.1 ∧ MessagesAt (classes ++ [.any]) result.2.2.2 := by
  have minted := configuration_mint owned .any (Or.inr (Or.inr rfl))
  have fresh : TokenAt (classes ++ [.any]) machine.nextToken .any := by
    rw [← owned.supply]
    exact token_fresh classes .any
  let middle : Effect4.Program.NativeMachine := {machine with nextToken := machine.nextToken + 1}
  have fiberGood := fiber_extend (ClassLe.append classes .any) goodFiber
  unfold countdownParkEdits
  dsimp only
  cases walked : countdownWalk {machine with nextToken := machine.nextToken + 1} targets [] with
  | mk exits next =>
    cases next with
    | none =>
      exact ⟨minted, reframe_live fiberGood (CodeAt.head (HeadAt.success (ValueAt.any _))) stack parked live,
        by intro message member; cases member⟩
    | some pair =>
      obtain ⟨target, remaining⟩ := pair
      let name : EffName := .withWaiter (.store .cancelPark) fiber.id machine.nextToken
      have saved : StackAt B .any .body (.asyncFinalizer name :: fiber.frame.stack) :=
        .cons (.cancel .any name (cancel_then_failure (.park fiber.id machine.nextToken) .any)) stack
      let frame : NativeFrame := {fiber.frame with stack := .asyncFinalizer name :: fiber.frame.stack}
      have framed := set_frame_live fiberGood frame ⟨.any, code, saved⟩ parked live
      let pending : NPending := ⟨machine.nextToken, remaining, exits, .exitsValue, false⟩
      have held := park_fiber framed pending fresh code saved ⟨.any, fresh, rfl⟩
      refine ⟨configuration_emit minted _, held, ?_⟩
      intro message member
      have equal := List.mem_singleton.mp member
      subst message
      exact fresh

/-- The eager countdown reader applies the canonical plan's admitted messages. -/
theorem countdown_state {B : List Val} {classes : Classes}
    (machine : Effect4.Program.NativeMachine) (fiber : NativeFiber) (view : View) (targets : List FiberId)
    (owned : ConfigurationAt B classes machine) (goodFiber : FiberAt B classes fiber)
    (code : CodeAt B .any fiber.frame.current) (stack : StackAt B .any .body fiber.frame.stack)
    (parked : fiber.parked = .notParked) (live : fiber.exit.isSome = false) :
    let result := countdownPark (interpreter view) machine fiber targets .exitsValue
    ConfigurationAt B (classes ++ [.any]) result.1 ∧ FiberAt B (classes ++ [.any]) result.2.1 := by
  have plan := countdown_plan_state machine fiber view targets owned goodFiber code stack parked live
  exact ⟨configuration_messages _ _ plan.2.2 plan.1, plan.2.1⟩

/-- A newly queued task retains its recorded token class. -/
theorem tasks_singleton {B : List Val} {classes : Classes} {task : NTask}
    (owned : TaskAt B classes task) : TasksAt B classes [task] := by
  intro next member
  have equal := List.mem_singleton.mp member
  subst next
  exact owned

/-- Appending task lists combines their existing token assertions. -/
theorem tasks_append {B : List Val} {classes : Classes} {first last : List NTask}
    (left : TasksAt B classes first) (right : TasksAt B classes last) : TasksAt B classes (first ++ last) := by
  intro task member
  rcases List.mem_append.mp member with before | after
  · exact left task before
  · exact right task after

/-- An ordered dispatcher bucket list retains every bucket's task assertion. -/
theorem buckets_cons {B : List Val} {classes : Classes}
    {head : Bucket EffName EffThunk Val Err Defect FiberId Ann} {rest : List (Bucket EffName EffThunk Val Err Defect FiberId Ann)}
    (first : TasksAt B classes head.tasks) (last : ∀ bucket ∈ rest, TasksAt B classes bucket.tasks) :
    ∀ bucket ∈ head :: rest, TasksAt B classes bucket.tasks := by
  intro bucket member
  rcases List.mem_cons.mp member with equal | tail
  · subst bucket; exact first
  · exact last bucket tail

/-- The actual priority insertion retains every old task and the new task's token class. -/
theorem insert_tasks {B : List Val} {classes : Classes} (priority : Nat) (task : NTask)
    (good : TaskAt B classes task) (buckets : List (Bucket EffName EffThunk Val Err Defect FiberId Ann))
    (owned : ∀ bucket ∈ buckets, TasksAt B classes bucket.tasks) :
    ∀ bucket ∈ Dispatcher.insert priority task buckets, TasksAt B classes bucket.tasks := by
  induction buckets with
  | nil =>
    exact buckets_cons (tasks_singleton good) (by intro bucket member; cases member)
  | cons bucket rest ih =>
    have first := owned bucket (List.mem_cons_self ..)
    have last : ∀ next ∈ rest, TasksAt B classes next.tasks :=
      fun next member => owned next (List.mem_cons_of_mem bucket member)
    simp only [Dispatcher.insert]
    split
    · exact buckets_cons (tasks_append first (tasks_singleton good)) last
    · split
      · exact buckets_cons (tasks_singleton good) (buckets_cons first last)
      · exact buckets_cons first (ih last)

/-- The native dispatcher enqueue keeps its exact task reply assertion. -/
theorem dispatcher_enqueue {B : List Val} {classes : Classes} (dispatcher : NDispatcher)
    (priority : Nat) (task : NTask) (owned : DispatcherAt B classes dispatcher) (good : TaskAt B classes task) :
    DispatcherAt B classes (dispatcher.enqueue priority task) := insert_tasks priority task good dispatcher.buckets owned

/-- Editing only a dispatcher's tasks retains every other successful-body assertion. -/
theorem dispatcher_fiber {B : List Val} {classes : Classes} {fiber : NativeFiber}
    (owned : FiberAt B classes fiber) (dispatcher : NDispatcher) (good : DispatcherAt B classes dispatcher) :
    FiberAt B classes {fiber with dispatcher} :=
  ⟨owned.frame, owned.park, owned.pending, good, owned.observers, owned.exits, owned.terminal, owned.children⟩

/-- Arming a dispatcher edits no value-bearing field. -/
theorem configuration_arm {B : List Val} {classes : Classes} {machine : Effect4.Program.NativeMachine}
    (owned : ConfigurationAt B classes machine) (id : FiberId) : ConfigurationAt B classes (machine.arm id) :=
  ⟨owned.supply, owned.kinds, owned.fibers, owned.races, owned.timers, owned.refs, owned.deferreds, owned.scopes⟩

/-- The actual yield mints a unit token and queues only the matching unit resume. -/
theorem yield_park_state {B : List Val} {classes : Classes}
    (machine : Effect4.Program.NativeMachine) (fiber : NativeFiber) (yielding : Bool) (view : View) (priority : Nat)
    (owned : ConfigurationAt B classes machine) (goodFiber : FiberAt B classes fiber)
    (current : fiber.frame.current = .yieldNowWith priority)
    (stack : StackAt B .unit .body fiber.frame.stack) (parked : fiber.parked = .notParked)
    (live : fiber.exit.isSome = false) :
    let result := evaluatePrim (interpreter view) machine fiber yielding
    ConfigurationAt B (classes ++ [.unit]) result.machine ∧
      FiberAt B (classes ++ [.unit]) result.fiber ∧
        CommandsAt B (classes ++ [.unit]) result.machine result.nested := by
  have minted := configuration_mint owned .unit (Or.inr (Or.inl rfl))
  have fresh : TokenAt (classes ++ [.unit]) machine.nextToken .unit := by
    rw [← owned.supply]
    exact token_fresh classes .unit
  have code : CodeAt B .unit (.success .unit) := .head (.success .unit)
  have started := reframe_live (fiber_extend (ClassLe.append classes .unit) goodFiber) code stack parked live
  have task : TaskAt B (classes ++ [.unit]) (.resume fiber.id machine.nextToken (.success .unit)) :=
    ⟨.unit, fresh, code⟩
  have dispatcher := dispatcher_enqueue fiber.dispatcher priority _
    (fiber_extend (ClassLe.append classes .unit) goodFiber).dispatcher task
  have queued := dispatcher_fiber started _ dispatcher
  let pending : NPending := ⟨machine.nextToken, [], [], .void, false⟩
  have held := park_fiber queued pending fresh code stack ⟨.unit, fresh, rfl⟩
  simp only [evaluatePrim, current]
  exact ⟨configuration_emit (configuration_arm minted fiber.id) _, held,
    by intro command member; cases member⟩

/-- The actual await-all source head consumes the countdown's arbitrary-data token assertion. -/
theorem await_park_state {B : List Val} {classes : Classes}
    (machine : Effect4.Program.NativeMachine) (fiber : NativeFiber) (yielding : Bool) (view : View)
    (targets : List FiberId) (owned : ConfigurationAt B classes machine) (goodFiber : FiberAt B classes fiber)
    (current : fiber.frame.current = .suspend (.park (.awaitAll targets)))
    (stack : StackAt B .any .body fiber.frame.stack) (parked : fiber.parked = .notParked)
    (live : fiber.exit.isSome = false) :
    let result := evaluatePrim (interpreter view) machine fiber yielding
    ConfigurationAt B (classes ++ [.any]) result.machine ∧
      FiberAt B (classes ++ [.any]) result.fiber ∧
        CommandsAt B (classes ++ [.any]) result.machine result.nested := by
  have code : CodeAt B .any fiber.frame.current := by rw [current]; exact .head (.awaitPark targets)
  have parkedResult := countdown_plan_state machine fiber view targets owned goodFiber code stack parked live
  simp only [evaluatePrim, current]
  exact ⟨parkedResult.1, parkedResult.2.1, by intro command member; cases member⟩

/-- The actual race registration retains its earlier body token while the host stays active. -/
theorem race_park_state {B : List Val} {classes : Classes}
    (machine : Effect4.Program.NativeMachine) (fiber : NativeFiber) (yielding : Bool) (view : View) (raceId : Nat)
    (owned : ConfigurationAt B classes machine) (goodFiber : FiberAt B classes fiber)
    (current : fiber.frame.current = .suspend (.park (.race raceId))) :
    let result := evaluatePrim (interpreter view) machine fiber yielding
    ConfigurationAt B classes result.machine ∧ FiberAt B classes result.fiber ∧
      CommandsAt B classes result.machine result.nested := by
  simp only [evaluatePrim, current]
  change ConfigurationAt B classes (registerRace machine fiber yielding raceId).machine ∧
    FiberAt B classes (registerRace machine fiber yielding raceId).fiber ∧
      CommandsAt B classes (registerRace machine fiber yielding raceId).machine
        (registerRace machine fiber yielding raceId).nested
  unfold registerRace
  split
  · exact ⟨owned, goodFiber, by intro command member; cases member⟩
  · rename_i race found
    have old := configuration_race owned found
    have registering : RaceAt B classes {race with registering := true} :=
      ⟨old.programs, old.token, old.mode, old.accepted, old.cleanup⟩
    refine ⟨configuration_update_race owned _ registering, goodFiber, ?_⟩
    intro command member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with equal | equal
    · subst command; trivial
    · subst command; trivial

end Test.Dogfood.Proofs.HostTimeoutParkSteps
