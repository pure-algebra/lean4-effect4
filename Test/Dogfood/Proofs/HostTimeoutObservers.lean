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

/-- Updating countdown progress keeps each pending token and its declared resume mode. -/
theorem pending_progress_fiber {B : List Val} {classes : Classes} {fiber : NativeFiber}
    (owned : FiberAt B classes fiber) (edit : HostTimeoutState.NPending → HostTimeoutState.NPending)
    (token : ∀ pending, (edit pending).token = pending.token)
    (mode : ∀ pending, (edit pending).resumeWith = pending.resumeWith) :
    FiberAt B classes {fiber with pending := fiber.pending.map edit} where
  frame := owned.frame
  park := owned.park
  pending := by
    intro pending member
    obtain ⟨old, seen, equal⟩ := List.mem_map.mp member
    subst pending
    obtain ⟨kind, held, resume⟩ := owned.pending old seen
    refine ⟨kind, ?_, ?_⟩
    · rw [token]; exact held
    · rw [mode]; exact resume
  dispatcher := owned.dispatcher
  observers := owned.observers
  exits := owned.exits
  terminal := owned.terminal
  children := owned.children

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
  induction targets generalizing machine commands with
  | nil => exact held
  | cons target targets ih =>
    cases found : machine.fiber? target with
    | none => simpa only [interruptEach, List.foldl_cons, found] using ih machine commands held
    | some fiber =>
      have next : ∀ command ∈ commands ++
          (if (interruptRecord (interpOf HostTimeoutSource.program Test.Dogfood.Scenario.Timeout.fetch.table)
            (some who) extra fiber).2 then [.evaluate target] else []), ∃ id, command = .evaluate id := by
        intro command member
        rcases List.mem_append.mp member with previous | new
        · exact held command previous
        · split at new
          · exact ⟨target, List.mem_singleton.mp new⟩
          · cases new
      simpa only [interruptEach, List.foldl_cons, found] using ih _ _ next

/-- The actual countdown callback retains all source assertions and emits only its token's arbitrary-data resume. -/
theorem countdown_observer {B : List Val} {classes : Classes}
    (machine : Effect4.Program.NativeMachine) (id waiter : FiberId) (token : Nat) (exit : ExitV)
    (owned : ConfigurationAt B classes machine) (held : TokenAt classes token .any) :
    let result := fireObserver (interpOf HostTimeoutSource.program Test.Dogfood.Scenario.Timeout.fetch.table)
      id exit (machine, []) (.countdown waiter token)
    ConfigurationAt B classes result.1 ∧ CommandsAt B classes result.1 result.2 := by
  let base := machine.emit [RunEvent.observerFired id (.countdown waiter token)]
  have emitted : ConfigurationAt B classes base := configuration_emit owned _
  simp only [fireObserver, show machine.emit _ = base from rfl]
  cases found : base.fiber? waiter with
  | none => exact ⟨emitted, by intro command member; cases member⟩
  | some fiber =>
    dsimp only
    have good := configuration_fiber emitted found
    cases pendingFound : fiber.pending.find? (fun pending => decide (pending.token = token)) with
    | none => exact ⟨emitted, by intro command member; cases member⟩
    | some pending =>
      dsimp only
      have member := List.mem_of_find?_eq_some pendingFound
      have accepted := List.find?_some (p := fun q : HostTimeoutState.NPending => decide (q.token = token)) pendingFound
      have same : pending.token = token := of_decide_eq_true accepted
      have mode := countdown_pending_mode held same (good.pending pending member)
      let interrupted := if pending.failFast && !exit.isSuccess && pending.collected.all Exit.isSuccess then
        interruptEach (interpOf HostTimeoutSource.program Test.Dogfood.Scenario.Timeout.fetch.table)
          waiter ((interpOf HostTimeoutSource.program Test.Dogfood.Scenario.Timeout.fetch.table).stackAnnotations waiter)
          pending.remaining (base, []) else (base, [])
      have interruptedGood : ConfigurationAt B classes interrupted.1 := by
        unfold interrupted
        split
        · exact interrupt_each_state base waiter _ pending.remaining [] emitted
        · exact emitted
      have interruptedCommands : ∀ command ∈ interrupted.2, ∃ target, command = .evaluate target := by
        unfold interrupted
        split
        · exact interrupt_each_evaluates base waiter _ pending.remaining [] (by intro command member; cases member)
        · intro command member; cases member
      cases walked : countdownWalk interrupted.1 pending.remaining (pending.collected ++ [exit]) with
      | mk exits next =>
        cases next with
        | none =>
          dsimp only
          have progressed := pending_progress_fiber good
            (fun q => if q.token = token then {q with waitingOn := none, remaining := [], collected := exits} else q)
            (by intro q; split <;> rfl) (by intro q; split <;> rfl)
          refine ⟨configuration_update interruptedGood _ progressed, ?_⟩
          intro command present
          simp only [List.nil_append, List.mem_append, List.mem_singleton] at present
          rcases present with previous | equal
          · obtain ⟨target, equal⟩ := interruptedCommands command previous
            subst command; trivial
          · subst command
            refine ⟨.any, held, ?_⟩
            rw [mode]
            exact .head (.success (.any _))
        | some pair =>
          obtain ⟨target, rest⟩ := pair
          dsimp only
          have observed := configuration_modify interruptedGood target
            (fun old => {old with observers := old.observers ++ [.countdown waiter token]})
            (fun old saved => observer_fiber saved (.countdown waiter token) held)
          have progressed := pending_progress_fiber good
            (fun q => if q.token = token then {q with waitingOn := some target, remaining := rest, collected := exits} else q)
            (by intro q; split <;> rfl) (by intro q; split <;> rfl)
          refine ⟨configuration_update observed _ progressed, ?_⟩
          intro command present
          simp only [List.nil_append] at present
          obtain ⟨target, equal⟩ := interruptedCommands command present
          subst command; trivial

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
