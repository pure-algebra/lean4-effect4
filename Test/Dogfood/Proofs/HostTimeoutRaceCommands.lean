import Test.Dogfood.Proofs.HostTimeoutObservers

/-!
Placement: host-session-protocol R6, serving `Timeout.stale_never_applies` clause four.
Consumer: the complete native command invariant and its reached history.
Race launch and enrollment use the actual stored entrant programs and selected body exits.
-/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
namespace Test.Dogfood.Proofs.HostTimeoutRaceCommands
open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Guard
open Effect4.Program.ReleaseCustody.CommandStacks
open HostTimeoutSlots HostTimeoutFlow HostTimeoutFrames HostTimeoutEvaluation HostTimeoutCommands
open HostTimeoutHeap HostTimeoutState HostTimeoutStateSteps HostTimeoutRaceSteps HostTimeoutQueue HostTimeoutParkSteps HostTimeoutLocalSteps HostTimeoutIteration HostTimeoutSettle HostTimeoutLoop HostTimeoutObservers

/-- An unowned administrative command transports the actual old pending suffix. -/
theorem unowned_tail {B : List Val} {classes : Classes} (machine : Effect4.Program.NativeMachine)
    (command : NCmd) (rest : List NCmd)
    (queue : GuardQueue HostTimeoutSource.program Test.Dogfood.Scenario.Timeout.fetch.table machine (command :: rest))
    (commands : CommandsAt B classes machine (command :: rest))
    (unowned : commandOwner machine command = none) (notExit : ∀ id, command ≠ .exitDone id) :
    letI := evaluatorFor HostTimeoutSource.program Test.Dogfood.Scenario.Timeout.fetch.table
    CommandsAt B classes
      (driveStep (interpOf HostTimeoutSource.program Test.Dogfood.Scenario.Timeout.fetch.table) machine command rest).1 rest := by
  letI := evaluatorFor HostTimeoutSource.program Test.Dogfood.Scenario.Timeout.fetch.table
  exact commands_transport (classOrder.refl classes)
    (guardQueue_tail HostTimeoutSource.program Test.Dogfood.Scenario.Timeout.fetch.table queue)
    (fun next member => commands next (List.mem_cons_of_mem _ member))
    (unowned_command_links HostTimeoutSource.program Test.Dogfood.Scenario.Timeout.fetch.table machine command rest unowned notExit)

/-- An actual daemon race entrant starts with its proved source code and an empty saved stack. -/
theorem launch_configuration {B : List Val} {classes : Classes} (machine : Effect4.Program.NativeMachine)
    (host : NativeFiber) (program : NCode) (site : List Nat) (race : Nat)
    (owned : ConfigurationAt B classes machine) (code : CodeAt B .body program) :
    ConfigurationAt B classes (launchEntrant
      (interpOf HostTimeoutSource.program Test.Dogfood.Scenario.Timeout.fetch.table) race machine host program site).1 := by
  unfold launchEntrant spawn
  dsimp only
  refine configuration_emit ?_ _
  refine ⟨owned.supply, owned.kinds, ?_, owned.races, owned.timers, owned.refs, owned.deferreds, owned.scopes⟩
  intro fiber member
  rcases List.mem_append.mp member with previous | fresh
  · exact owned.fibers fiber previous
  · have equal := List.mem_singleton.mp fresh
    subst fiber
    exact fiber_make _ program true _ _ code

/-- The actual launch command uses only the next stored body-class entrant. -/
theorem launch_command {B : List Val} {classes : Classes} (machine : Effect4.Program.NativeMachine)
    (raceId : Nat) (rest : List NCmd) (owned : ConfigurationAt B classes machine)
    (queue : GuardQueue HostTimeoutSource.program Test.Dogfood.Scenario.Timeout.fetch.table machine (.launch raceId :: rest))
    (commands : CommandsAt B classes machine (.launch raceId :: rest)) :
    letI := evaluatorFor HostTimeoutSource.program Test.Dogfood.Scenario.Timeout.fetch.table
    ConfigurationAt B classes (driveStep (interpOf HostTimeoutSource.program Test.Dogfood.Scenario.Timeout.fetch.table) machine (.launch raceId) rest).1 ∧
      CommandsAt B classes (driveStep (interpOf HostTimeoutSource.program Test.Dogfood.Scenario.Timeout.fetch.table) machine (.launch raceId) rest).1
        (driveStep (interpOf HostTimeoutSource.program Test.Dogfood.Scenario.Timeout.fetch.table) machine (.launch raceId) rest).2 := by
  letI := evaluatorFor HostTimeoutSource.program Test.Dogfood.Scenario.Timeout.fetch.table
  have tail := unowned_tail machine (.launch raceId) rest queue commands rfl (by intro id wrong; cases wrong)
  simp only [driveStep] at tail ⊢
  split
  · rename_i found
    simp only [found] at tail
    exact ⟨owned, tail⟩
  · rename_i race found
    simp only [found] at tail
    have good := configuration_race owned found
    split
    · rename_i programs
      simp only [programs] at tail
      exact ⟨owned, tail⟩
    · rename_i program more programs
      simp only [programs] at tail
      split
      · rename_i accepted
        simp only [if_pos accepted] at tail
        exact ⟨owned, tail⟩
      · rename_i accepted
        simp only [if_neg accepted] at tail
        split
        · rename_i lookup
          simp only [lookup] at tail
          exact ⟨owned, tail⟩
        · rename_i host lookup
          simp only [lookup] at tail
          have code := good.programs program (by rw [programs]; exact List.mem_cons_self ..)
          have started := launch_configuration machine host program (race.nextSite.getD []) raceId owned code
          have moreGood : RaceAt B classes {race with programs := more, nextSite := race.nextSite.map (fun site => site ++ [1])} := {
            programs := by intro code member; exact good.programs code (by rw [programs]; exact List.mem_cons_of_mem _ member)
            token := good.token
            mode := good.mode
            accepted := good.accepted
            cleanup := good.cleanup }
          refine ⟨configuration_emit (configuration_update_race started _ moreGood) _, ?_⟩
          intro command member
          simp only [List.mem_cons] at member
          rcases member with equal | equal | equal | member
          · subst command; trivial
          · subst command; trivial
          · subst command; trivial
          · exact tail command member

/-- The actual enrollment command carries a child's body exit into the race observer. -/
theorem enroll_command {B : List Val} {classes : Classes} (machine : Effect4.Program.NativeMachine)
    (raceId : Nat) (child : FiberId) (rest : List NCmd) (owned : ConfigurationAt B classes machine)
    (queue : GuardQueue HostTimeoutSource.program Test.Dogfood.Scenario.Timeout.fetch.table machine (.enrollRace raceId child :: rest))
    (commands : CommandsAt B classes machine (.enrollRace raceId child :: rest)) :
    letI := evaluatorFor HostTimeoutSource.program Test.Dogfood.Scenario.Timeout.fetch.table
    ConfigurationAt B classes (driveStep (interpOf HostTimeoutSource.program Test.Dogfood.Scenario.Timeout.fetch.table) machine (.enrollRace raceId child) rest).1 ∧
      CommandsAt B classes (driveStep (interpOf HostTimeoutSource.program Test.Dogfood.Scenario.Timeout.fetch.table) machine (.enrollRace raceId child) rest).1
        (driveStep (interpOf HostTimeoutSource.program Test.Dogfood.Scenario.Timeout.fetch.table) machine (.enrollRace raceId child) rest).2 := by
  letI := evaluatorFor HostTimeoutSource.program Test.Dogfood.Scenario.Timeout.fetch.table
  have tail := unowned_tail machine (.enrollRace raceId child) rest queue commands rfl (by intro id wrong; cases wrong)
  simp only [driveStep] at tail ⊢
  split
  · rename_i race fiber raceFound fiberFound
    simp only [raceFound, fiberFound] at tail
    have good := configuration_race owned raceFound
    have live : RaceAt B classes {race with state := {race.state with live := race.state.live ++ [child]}} :=
      ⟨good.programs, good.token, good.mode, good.accepted, good.cleanup⟩
    have updated := configuration_update_race owned _ live
    have saved := configuration_fiber owned fiberFound
    split
    · rename_i exit completed
      simp only [completed] at tail
      have result := observer_result _ child exit (.raceCallback raceId) updated (saved.exits exit completed) trivial
      exact ⟨result.1, commands_append result.2 tail⟩
    · rename_i completed
      simp only [completed] at tail
      exact ⟨configuration_modify updated child (fun old => {old with observers := old.observers ++ [.raceCallback raceId]})
        (fun old held => observer_fiber held (.raceCallback raceId) trivial), tail⟩
  · rename_i raceLook fiberLook impossible
    simp only at tail
    exact ⟨owned, tail⟩

/-- A race park source head expects a body at its saved continuation. -/
theorem race_park_frame {B : List Val} {frame : NativeFrame} (owned : FrameKind B .body frame)
    (race : Nat) (park : (interpOf HostTimeoutSource.program Test.Dogfood.Scenario.Timeout.fetch.table).parkOf frame.current = some (.ok (.race race))) :
    CodeAt B .body frame.current ∧ StackAt B .body .body frame.stack := by
  obtain ⟨input, code, stack⟩ := owned
  have head := code_head code
  generalize current : frame.current = next at head park
  cases head
  all_goals aesop (add norm simp [interpOf])

/-- Completing actual race registration either restores its accepted body or parks at the same body token. -/
theorem registration_command {B : List Val} {classes : Classes} (machine : Effect4.Program.NativeMachine)
    (raceId : Nat) (yielding : Bool) (rest : List NCmd) (owned : ConfigurationAt B classes machine)
    (guard : GuardState machine)
    (queue : GuardQueue HostTimeoutSource.program Test.Dogfood.Scenario.Timeout.fetch.table machine (.registrationDone raceId yielding :: rest))
    (commands : CommandsAt B classes machine (.registrationDone raceId yielding :: rest)) :
    letI := evaluatorFor HostTimeoutSource.program Test.Dogfood.Scenario.Timeout.fetch.table
    ConfigurationAt B classes (driveStep (interpOf HostTimeoutSource.program Test.Dogfood.Scenario.Timeout.fetch.table) machine (.registrationDone raceId yielding) rest).1 ∧
      CommandsAt B classes (driveStep (interpOf HostTimeoutSource.program Test.Dogfood.Scenario.Timeout.fetch.table) machine (.registrationDone raceId yielding) rest).1
        (driveStep (interpOf HostTimeoutSource.program Test.Dogfood.Scenario.Timeout.fetch.table) machine (.registrationDone raceId yielding) rest).2 := by
  letI := evaluatorFor HostTimeoutSource.program Test.Dogfood.Scenario.Timeout.fetch.table
  obtain ⟨race, fiber, raceFound, fiberFound, running, parked, source⟩ :=
    queue.authority (.registrationDone raceId yielding) (List.mem_cons_self ..)
  have key := fiber_id_of_lookup fiberFound
  have stored : machine.fiber? fiber.id = some fiber := by rw [key]; exact fiberFound
  have live := active_live guard stored running
  have good := configuration_fiber owned fiberFound
  have body := race_park_frame good.frame raceId source
  have goodRace := configuration_race owned raceFound
  let middle := machine.updateRace {race with registering := false}
  have middleGood : ConfigurationAt B classes middle := configuration_update_race owned _
    ⟨goodRace.programs, goodRace.token, goodRace.mode, goodRace.accepted, goodRace.cleanup⟩
  have middleLinks : StackLinks machine middle := .of_fibers rfl
  have owner : commandOwner machine (.registrationDone raceId yielding) = some fiber.id := by
    change (machine.race? raceId).map Race.host = some fiber.id
    rw [raceFound, key]; rfl
  simp only [driveStep, raceFound]
  rw [show middle.fiber? race.host = some fiber from fiberFound]
  dsimp only
  cases accepted : race.state.accepted with
  | some exit =>
    let code := (interpOf HostTimeoutSource.program Test.Dogfood.Scenario.Timeout.fetch.table).raceSettle raceId race.state.cleanupNeeded exit
    have codeGood : CodeAt B .body code := race_settle (goodRace.accepted exit accepted) [] raceId race.state.cleanupNeeded
    let next : NativeFiber := {fiber with frame := {fiber.frame with current := code}}
    have nextGood : FiberAt B classes next := reframe_live good codeGood body.2 parked live
    let result : NativeIter := ⟨middle, next, yielding, .continue_, [], []⟩
    have evaluation : EvaluationAt B classes result :=
      ⟨middleGood, nextGood, (by intro command member; cases member),
        (by intro message member; cases member)⟩
    have tail := tail_transport (.registrationDone raceId yielding) rest fiber.id (classOrder.refl classes)
      queue owner (fun command member => commands command (List.mem_cons_of_mem _ member))
      ((middleLinks.away fiber.id).trans (update_away middle next))
    exact settle_state result rest evaluation nextGood.frame tail
  | none =>
    let name := (interpOf HostTimeoutSource.program Test.Dogfood.Scenario.Timeout.fetch.table).cancelName
      ((interpOf HostTimeoutSource.program Test.Dogfood.Scenario.Timeout.fetch.table).raceCancelName raceId) fiber.id race.token
    have framed := set_frame_live good _ (push_cancel body.1 body.2 (.race raceId fiber.id race.token)) parked live
    let pending : HostTimeoutState.NPending := ⟨race.token, none, [], [], .void, false⟩
    have pushedStack : StackAt B .body .body (.asyncFinalizer name :: fiber.frame.stack) :=
      .cons (.cancel .body name (cancel_then_failure (.race raceId fiber.id race.token) .body)) body.2
    let next : NativeFiber := ({fiber with frame := {fiber.frame with stack := .asyncFinalizer name :: fiber.frame.stack}}).park pending
    have nextGood : FiberAt B classes next := park_fiber framed pending goodRace.token body.1 pushedStack
      ⟨.body, goodRace.token, rfl⟩
    let result : NativeIter := ⟨middle.emit [RunEvent.parkedOn fiber.id race.token], next, yielding, .parked, [], []⟩
    have evaluation : EvaluationAt B classes result :=
      ⟨configuration_emit middleGood _, nextGood, (by intro command member; cases member),
        (by intro message member; cases member)⟩
    have tail := tail_transport (.registrationDone raceId yielding) rest fiber.id (classOrder.refl classes)
      queue owner (fun command member => commands command (List.mem_cons_of_mem _ member))
      (((middleLinks.emit _).away fiber.id).trans (update_away result.machine next))
    exact settle_state result rest evaluation nextGood.frame tail

end Test.Dogfood.Proofs.HostTimeoutRaceCommands
