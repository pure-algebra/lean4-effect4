import Test.Dogfood.Proofs.HostTimeoutStateSteps

/-!
Placement: host-session-protocol R6, serving `Timeout.stale_never_applies` clause four.
Consumer: the actual race observer command, then registration return and the reached-run assertion.
The selected exit and cleanup result retain the source's body assertion.
These facts establish value custody, without asserting that a live race completes.
-/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
namespace Test.Dogfood.Proofs.HostTimeoutRaceSteps
open Effect4 Effect4.Machine Effect4.Program Effect4.Laws.Auto
open HostTimeoutSlots HostTimeoutFlow HostTimeoutFrames HostTimeoutEvaluation HostTimeoutCommands
open HostTimeoutHeap HostTimeoutState HostTimeoutStateSteps

/-- An existing race retains the same token class when the proof world grows. -/
theorem race_extend {B : List Val} {before after : Classes} {race : NRace}
    (later : ClassLe before after) (owned : RaceAt B before race) : RaceAt B after race where
  programs := owned.programs
  token := later race.token .body owned.token
  mode := owned.mode
  accepted := owned.accepted
  cleanup := owned.cleanup

/-- Updating an actual race record retains every other stored value assertion. -/
theorem configuration_update_race {B : List Val} {classes : Classes}
    {machine : Effect4.Program.NativeMachine} (owned : ConfigurationAt B classes machine)
    (race : NRace) (good : RaceAt B classes race) :
    ConfigurationAt B classes (machine.updateRace race) where
  supply := owned.supply
  kinds := owned.kinds
  fibers := owned.fibers
  races := by
    intro next member
    obtain ⟨old, present, equal⟩ := List.mem_map.mp member
    subst next
    split
    · exact good
    · exact owned.races old present
  timers := owned.timers
  refs := owned.refs
  deferreds := owned.deferreds
  scopes := owned.scopes

/-- Reading the actual race record supplies its token and selected-exit assertions. -/
theorem configuration_race {B : List Val} {classes : Classes} {machine : Effect4.Program.NativeMachine}
    (owned : ConfigurationAt B classes machine) {id : Nat} {race : NRace}
    (found : machine.race? id = some race) : RaceAt B classes race :=
  owned.races race (List.mem_of_find?_eq_some found)

/-- The first-exit callback keeps an earlier selected body or selects the entrant's asserted exit. -/
theorem after_exit_accepted {B : List Val} {race : NRace} (child : FiberId) (exit : ExitV)
    (mode : race.mode = .firstExit)
    (previous : ∀ answer, race.state.accepted = some answer → ExitAt B .body answer)
    (good : ExitAt B .body exit) :
    ∀ answer, (race.afterExit child exit).state.accepted = some answer → ExitAt B .body answer := by
  intro answer found
  change (Supervision.raceCompleteWith race.mode race.state child exit).accepted = some answer at found
  rw [mode] at found
  dsimp only [Supervision.raceCompleteWith] at found
  unfold Supervision.raceCompleteFirst at found
  split at found
  · rename_i live
    cases accepted : race.state.accepted with
    | none =>
      rw [accepted] at found
      dsimp only at found
      have equal := Option.some.inj found
      subst answer
      exact good
    | some earlier =>
      rw [accepted] at found
      unfold Supervision.raceComplete at found
      rw [if_pos live, accepted] at found
      dsimp only at found
      have equal := Option.some.inj found
      subst answer
      exact previous earlier accepted
  · exact previous answer found

/-- Updating cleanup publications cannot change the previously saved body result. -/
theorem after_exit_cleanup {B : List Val} {race : NRace} (child : FiberId) (exit : ExitV)
    (mode : race.mode = .firstExit)
    (previous : ∀ wait, race.state.cleanup = some wait → ExitAt B .body wait.result) :
    ∀ wait, (race.afterExit child exit).state.cleanup = some wait → ExitAt B .body wait.result := by
  intro wait found
  change (Supervision.raceCompleteWith race.mode race.state child exit).cleanup = some wait at found
  rw [mode] at found
  dsimp only [Supervision.raceCompleteWith] at found
  unfold Supervision.raceCompleteFirst at found
  split at found
  · rename_i live
    cases accepted : race.state.accepted with
    | none => rw [accepted] at found; cases found
    | some earlier =>
      rw [accepted] at found
      unfold Supervision.raceComplete at found
      rw [if_pos live, accepted] at found
      dsimp only at found
      obtain ⟨old, present, equal⟩ := Option.map_eq_some_iff.mp found
      have good := previous old present
      subst wait
      split <;> exact good
  · exact previous wait found

/-- The actual stored first-exit race carries the selected and cleanup body through its callback. -/
theorem after_exit_race {B : List Val} {classes : Classes} {race : NRace}
    (owned : RaceAt B classes race) (child : FiberId) (exit : ExitV) (good : ExitAt B .body exit) :
    RaceAt B classes (race.afterExit child exit) where
  programs := owned.programs
  token := owned.token
  mode := owned.mode
  accepted := after_exit_accepted child exit owned.mode owned.accepted good
  cleanup := after_exit_cleanup child exit owned.mode owned.cleanup

/-- Marking a selected race settled changes no value-bearing field. -/
theorem race_settled {B : List Val} {classes : Classes} {race : NRace}
    (owned : RaceAt B classes race) : RaceAt B classes {race with settled := true} :=
  ⟨owned.programs, owned.token, owned.mode, owned.accepted, owned.cleanup⟩

/-- The actual race observer retains the body class in its stored selected result. -/
theorem race_observer_state {B : List Val} {classes : Classes}
    (machine : Effect4.Program.NativeMachine) (id : FiberId) (raceId : Nat) (exit : ExitV)
    (commands : List Guard.NCmd) (owned : ConfigurationAt B classes machine)
    (good : ExitAt B .body exit) :
    ConfigurationAt B classes
      (fireObserver (interpOf HostTimeoutSource.program Test.Dogfood.Scenario.Timeout.fetch.table)
        id exit (machine, commands) (.raceCallback raceId)).1 := by
  let base := machine.emit [RunEvent.observerFired id (.raceCallback raceId)]
  have emitted : ConfigurationAt B classes base := configuration_emit owned _
  simp only [fireObserver, show machine.emit _ = base from rfl]
  split
  · exact emitted
  · rename_i race found
    have next := after_exit_race (configuration_race emitted found) id exit good
    have updated := configuration_update_race emitted _ next
    split
    · exact configuration_emit (configuration_update_race updated _ (race_settled next)) _
    · exact updated

/-- A race callback's newly queued resume carries its selected body at the race's own token. -/
theorem race_observer_commands {B : List Val} {classes : Classes}
    (machine : Effect4.Program.NativeMachine) (id : FiberId) (raceId : Nat) (exit : ExitV)
    (owned : ConfigurationAt B classes machine) (good : ExitAt B .body exit) :
    let result := fireObserver (interpOf HostTimeoutSource.program Test.Dogfood.Scenario.Timeout.fetch.table)
      id exit (machine, []) (.raceCallback raceId)
    CommandsAt B classes result.1 result.2 := by
  let base := machine.emit [RunEvent.observerFired id (.raceCallback raceId)]
  have emitted : ConfigurationAt B classes base := configuration_emit owned _
  simp only [fireObserver, show machine.emit _ = base from rfl]
  split
  · intro command member; cases member
  · rename_i race found
    have next := after_exit_race (configuration_race emitted found) id exit good
    split
    · rename_i accepted answer unsettled
      intro command member
      simp only [List.nil_append] at member
      split at member
      · cases member
      · have equal := List.mem_singleton.mp member
        subst command
        exact ⟨.body, next.token,
          race_settle (next.accepted accepted answer) [] raceId (race.afterExit id exit).state.cleanupNeeded⟩
    · intro command member; cases member

/-- A fresh native token extends the one class list at the actual machine supply. -/
theorem configuration_mint {B : List Val} {classes : Classes} {machine : Effect4.Program.NativeMachine}
    (owned : ConfigurationAt B classes machine) (kind : Kind) (allowed : GuardKind kind) :
    ConfigurationAt B (classes ++ [kind]) {machine with nextToken := machine.nextToken + 1} where
  supply := by simp only [List.length_append, List.length_singleton, owned.supply]
  kinds := by
    intro next member
    rcases List.mem_append.mp member with before | last
    · exact owned.kinds next before
    · have equal := List.mem_singleton.mp last; subst next; exact allowed
  fibers := fun fiber member => fiber_extend (ClassLe.append classes kind) (owned.fibers fiber member)
  races := fun race member => race_extend (ClassLe.append classes kind) (owned.races race member)
  timers := fun waiter member => ClassLe.append classes kind waiter.token .unit (owned.timers waiter member)
  refs := owned.refs
  deferreds := owned.deferreds
  scopes := owned.scopes

/-- Appending a freshly allocated race retains every earlier race and fiber assertion. -/
theorem configuration_append_race {B : List Val} {classes : Classes} {machine : Effect4.Program.NativeMachine}
    (owned : ConfigurationAt B classes machine) (race : NRace) (good : RaceAt B classes race) :
    ConfigurationAt B classes {machine with races := machine.races ++ [race]} where
  supply := owned.supply
  kinds := owned.kinds
  fibers := owned.fibers
  races := by
    intro next member
    rcases List.mem_append.mp member with before | last
    · exact owned.races next before
    · have equal := List.mem_singleton.mp last; subst next; exact good
  timers := owned.timers
  refs := owned.refs
  deferreds := owned.deferreds
  scopes := owned.scopes

/-- Beginning Timeout's actual first-exit race allocates a body token and retains body entrants. -/
theorem begin_race_state {B : List Val} {classes : Classes}
    (machine : Effect4.Program.NativeMachine) (fiber : NativeFiber) (yielding : Bool)
    (programs : List NCode) (site : Option (List Nat)) (view : View)
    (owned : ConfigurationAt B classes machine) (goodFiber : FiberAt B classes fiber)
    (entrants : ∀ code ∈ programs, CodeAt B .body code)
    (stack : StackAt B .body .body fiber.frame.stack) (parked : fiber.parked = .notParked)
    (live : fiber.exit.isSome = false) :
    let result := beginRace (interpreter view) machine fiber yielding programs site .firstExit
    ConfigurationAt B (classes ++ [.body]) result.machine ∧
      FiberAt B (classes ++ [.body]) result.fiber ∧
        CommandsAt B (classes ++ [.body]) result.machine result.nested := by
  have minted := configuration_mint owned .body (Or.inl rfl)
  let middle : Effect4.Program.NativeMachine :=
    {machine with nextRace := machine.nextRace + 1, nextToken := machine.nextToken + 1}
  have changed : ConfigurationAt B (classes ++ [.body]) middle :=
    ⟨minted.supply, minted.kinds, minted.fibers, minted.races, minted.timers,
      minted.refs, minted.deferreds, minted.scopes⟩
  let race : NRace := ⟨machine.nextRace, fiber.id, machine.nextToken,
    {Supervision.RaceAllState.initial [] with remaining := programs.length},
    false, programs, false, site, .firstExit, none⟩
  have fresh : TokenAt (classes ++ [.body]) machine.nextToken .body := by
    rw [← owned.supply]
    exact token_fresh classes .body
  have goodRace : RaceAt B (classes ++ [.body]) race :=
    ⟨entrants, fresh, rfl, (by intro exit found; cases found), (by intro wait found; cases found)⟩
  have stored := configuration_emit (configuration_append_race changed race goodRace)
    [RunEvent.raceStarted machine.nextRace fiber.id programs.length]
  have current := reframe_live (fiber_extend (ClassLe.append classes .body) goodFiber)
    (CodeAt.head (HeadAt.racePark (B := B) machine.nextRace)) stack parked live
  exact ⟨stored, current, by intro command member; cases member⟩

end Test.Dogfood.Proofs.HostTimeoutRaceSteps
