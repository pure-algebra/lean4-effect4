import Test.Dogfood.Proofs.HostTimeoutLoop

/-!
Placement: host-session-protocol R6, serving `Timeout.stale_never_applies` clause four.
Consumer: actual observe and enrollRace command closure, then native history.
Countdown callbacks discard their collected exit data through the existing arbitrary-data token class.
-/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
namespace Test.Dogfood.Proofs.HostTimeoutObservers
open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Guard
open Effect4.Program.ReleaseCustody.CommandStacks
open HostTimeoutSlots HostTimeoutFlow HostTimeoutFrames HostTimeoutEvaluation HostTimeoutCommands
open HostTimeoutHeap HostTimeoutState HostTimeoutStateSteps HostTimeoutRaceSteps HostTimeoutQueue HostTimeoutParkSteps HostTimeoutLocalSteps HostTimeoutIteration HostTimeoutSettle HostTimeoutLoop

/-- A matching countdown token forces its actual pending mode to exitsValue. -/
theorem countdown_pending_mode {classes : Classes} {pending : HostTimeoutState.NPending} {token : Nat}
    (held : TokenAt classes token .any) (same : pending.token = token)
    (good : PendingAt classes pending) : pending.resumeWith = .exitsValue := by
  obtain ⟨kind, present, mode⟩ := good
  rw [same] at present
  have equal := token_unique held present
  subst kind
  exact mode

/-- Actual interruptEach appends only evaluate commands to a queue of evaluate commands. -/
theorem interrupt_each_evaluates (machine : Effect4.Program.NativeMachine) (who : FiberId)
    (extra : ReasonAnnotations Ann) (targets : List FiberId) (commands : List NCmd)
    (held : ∀ command ∈ commands, ∃ id, command = .evaluate id) :
    ∀ command ∈ (interruptEach (interpOf HostTimeoutSource.program Test.Dogfood.Scenario.Timeout.fetch.table)
      who extra targets (machine, commands)).2, ∃ id, command = .evaluate id := by
  have produced := Edits.interrupt_commands_producer
    (interpOf HostTimeoutSource.program Test.Dogfood.Scenario.Timeout.fetch.table) (fun _ => 0)
    (fun command => ∃ id, command = .evaluate id) (fun target => ⟨rfl, target, rfl⟩)
    who extra targets (machine, commands)
  exact fun command member => (produced.2 command member).elim (held command) id

/-- The shared observer producer retains every source-bearing metadata field.
Consumer: current-record countdown updates after nested interruptions. -/
theorem metadata_fiber {B : List Val} {classes : Classes} {old next : NativeFiber}
    (owned : FiberAt B classes old) (frame : next.frame = old.frame)
    (dispatcher : next.dispatcher = old.dispatcher) (parked : next.parked = old.parked)
    (pending : ∀ entry ∈ next.pending, ∃ prior ∈ old.pending,
      entry.token = prior.token ∧ entry.resumeWith = prior.resumeWith)
    (observers : next.observers = old.observers) (exit : next.exit = old.exit)
    (children : next.children ⊆ old.children) : FiberAt B classes next where
  frame := frame ▸ owned.frame
  park := by
    intro token held
    obtain ⟨kind, found, current, stack⟩ := owned.park token (parked ▸ held)
    exact ⟨kind, found, frame ▸ current, frame ▸ stack⟩
  pending := by
    intro entry member
    obtain ⟨prior, held, token, resume⟩ := pending entry member
    obtain ⟨kind, found, mode⟩ := owned.pending prior held
    exact ⟨kind, token ▸ found, resume ▸ mode⟩
  dispatcher := dispatcher ▸ owned.dispatcher
  observers := fun observer member => owned.observers observer (observers ▸ member)
  exits := fun answer returned => owned.exits answer (exit ▸ returned)
  terminal := fun terminal => frame ▸ owned.terminal (exit ▸ terminal)
  children := by
    cases found : next.children with
    | nil => rfl
    | cons child rest =>
      have held := children (show child ∈ next.children from by rw [found]; exact List.mem_cons_self)
      rw [owned.children] at held
      cases held

/-- Updating countdown progress keeps each pending token and its declared resume mode. -/
theorem pending_progress_fiber {B : List Val} {classes : Classes} {fiber : NativeFiber}
    (owned : FiberAt B classes fiber) (edit : HostTimeoutState.NPending → HostTimeoutState.NPending)
    (token : ∀ pending, (edit pending).token = pending.token)
    (mode : ∀ pending, (edit pending).resumeWith = pending.resumeWith) :
    FiberAt B classes {fiber with pending := fiber.pending.map edit} := by
  apply metadata_fiber (next := {fiber with pending := fiber.pending.map edit})
    owned rfl rfl rfl ?_ rfl rfl (fun _ member => member)
  intro pending member
  obtain ⟨prior, held, equal⟩ := List.mem_map.mp member
  subst pending
  exact ⟨prior, held, token prior, mode prior⟩

/-- Countdown callbacks consume the shared metadata path and command producer.
The old private callback traversal is removed, including its stale original-record write. -/
theorem countdown_observer {B : List Val} {classes : Classes}
    (machine : Effect4.Program.NativeMachine) (id waiter : FiberId) (token : Nat) (exit : ExitV)
    (owned : ConfigurationAt B classes machine) (held : TokenAt classes token .any) :
    let result := fireObserver (interpOf HostTimeoutSource.program Test.Dogfood.Scenario.Timeout.fetch.table)
      id exit (machine, []) (.countdown waiter token)
    ConfigurationAt B classes result.1 ∧ CommandsAt B classes result.1 result.2 := by
  let interp := interpOf HostTimeoutSource.program Test.Dogfood.Scenario.Timeout.fetch.table
  let Edge (before after : Effect4.Program.NativeMachine)
      (edit : Machine.Edit EffName EffThunk Val Err Defect FiberId Ann Ctx Stores NCode
        (FrameFiber EffName EffThunk Val Err Defect FiberId Ann)
        (FrameEvent EffName EffThunk Val Err Defect FiberId Ann)) : Prop :=
    after = edit.apply before ∧ (ConfigurationAt B classes before → ConfigurationAt B classes after)
  let Allowed (command : NCmd) : Prop := ∀ before, CommandAt B classes before command
  have interrupted (who : FiberId) (extra : ReasonAnnotations Ann) (target : FiberId)
      (acc : Effect4.Program.NativeMachine × List NCmd) :
      Effect4.Contracts.Path Edge acc.1 (interruptEach interp who extra [target] acc).1
        (Edits.interruptWord interp who extra target acc.1) :=
    Edits.interrupt_path interp who extra
      (fun before target old found => ⟨rfl, fun initial => configuration_update initial _
        (interrupted_fiber old (configuration_fiber initial found) (some who) extra)⟩)
      (fun before target => ⟨rfl, fun initial => configuration_emit initial _⟩) target acc
  have produced := Edits.observer_producer_path_metadata (Edge := Edge) interp (fun _ => 0) Allowed
    id exit (machine, []) (.countdown waiter token)
    (fun before target old next found key frame dispatcher parked pending observers saved children =>
      ⟨rfl, fun initial => configuration_update initial next
        (metadata_fiber (configuration_fiber initial found) frame dispatcher parked pending observers saved children)⟩)
    (fun before target observer same => ⟨rfl, fun initial => by
      subst observer
      exact configuration_message before (.observe target (.countdown waiter token)) held initial⟩)
    (fun before id observer => ⟨rfl, fun initial => configuration_emit initial _⟩)
    (fun before id saved => ⟨rfl, fun initial => configuration_emit initial _⟩)
    (fun before key saved => ⟨rfl, fun initial => configuration_emit initial _⟩)
    (fun before scope key state impossible _ => by cases impossible)
    (fun before scope key impossible _ => by cases impossible)
    (fun before race next impossible => by cases impossible)
    (fun who extra targets acc => Edits.interrupts_path interp who extra (interrupted who extra) targets acc)
    (fun target => ⟨rfl, fun _ => True.intro⟩)
    (fun target next mode impossible => by cases impossible)
    (fun race host next cleanup accepted impossible => by cases impossible)
    (fun target next fiber pending exits same found member tokenSame => by
      cases same
      have good := (configuration_fiber (configuration_emit owned _) found).pending pending member
      have mode := countdown_pending_mode held tokenSame good
      exact ⟨rfl, fun _ => by
        refine ⟨.any, held, ?_⟩
        rw [mode]
        exact .head (.success (.any _))⟩)
  have preserved := Edits.run_preserves_at (fun _ _ _ edge => edge.1) (ConfigurationAt B classes)
    (fun _ _ _ edge initial => edge.2 initial) produced.1 owned
  rw [Edits.run_of_path (fun _ _ _ edge => edge.1) produced.1] at preserved
  refine ⟨preserved, ?_⟩
  intro command member
  exact (produced.2.2 command member).elim (fun impossible => nomatch impossible) (fun allowed => allowed _)

/-- Every observer admitted by the source assertion keeps its exact resume value class. -/
theorem observer_result {B : List Val} {classes : Classes}
    (machine : Effect4.Program.NativeMachine) (id : FiberId) (exit : ExitV) (observer : Observer)
    (owned : ConfigurationAt B classes machine) (good : ExitAt B .body exit)
    (allowed : ObserverAt classes observer) :
    let result := fireObserver (interpOf HostTimeoutSource.program Test.Dogfood.Scenario.Timeout.fetch.table)
      id exit (machine, []) observer
    ConfigurationAt B classes result.1 ∧ CommandsAt B classes result.1 result.2 := by
  cases observer with
  | countdown waiter token => exact countdown_observer machine id waiter token exit owned allowed
  | raceCallback race => exact ⟨race_observer_state machine id race exit [] owned good,
      race_observer_commands machine id race exit owned good⟩
  | callback key => exact ⟨configuration_emit (configuration_emit owned _) _, by intro command member; cases member⟩
  | resumeAwait waiter token mode => cases allowed
  | untrackChild parent => cases allowed
  | dropScopeFinalizer scope key => cases allowed

/-- The actual observe command retains its pending queue and all observer-produced resume evidence. -/
theorem observe_command {B : List Val} {classes : Classes}
    (machine : Effect4.Program.NativeMachine) (id : FiberId) (exit : ExitV) (observer : Observer) (rest : List NCmd)
    (owned : ConfigurationAt B classes machine)
    (queue : GuardQueue HostTimeoutSource.program Test.Dogfood.Scenario.Timeout.fetch.table machine (.observe id exit observer :: rest))
    (commands : CommandsAt B classes machine (.observe id exit observer :: rest)) :
    letI := evaluatorFor HostTimeoutSource.program Test.Dogfood.Scenario.Timeout.fetch.table
    ConfigurationAt B classes (driveStep (interpOf HostTimeoutSource.program Test.Dogfood.Scenario.Timeout.fetch.table) machine (.observe id exit observer) rest).1 ∧
      CommandsAt B classes (driveStep (interpOf HostTimeoutSource.program Test.Dogfood.Scenario.Timeout.fetch.table) machine (.observe id exit observer) rest).1
        (driveStep (interpOf HostTimeoutSource.program Test.Dogfood.Scenario.Timeout.fetch.table) machine (.observe id exit observer) rest).2 := by
  letI := evaluatorFor HostTimeoutSource.program Test.Dogfood.Scenario.Timeout.fetch.table
  have good := commands (.observe id exit observer) (List.mem_cons_self ..)
  have result := observer_result machine id exit observer owned good.1 good.2
  have links := fireObserver_links HostTimeoutSource.program Test.Dogfood.Scenario.Timeout.fetch.table machine id exit [] observer
  have tail := commands_transport (classOrder.refl classes)
    (guardQueue_tail HostTimeoutSource.program Test.Dogfood.Scenario.Timeout.fetch.table queue)
    (fun command member => commands command (List.mem_cons_of_mem _ member)) links
  exact ⟨result.1, commands_append result.2 tail⟩

end Test.Dogfood.Proofs.HostTimeoutObservers
