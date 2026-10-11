import Test.Dogfood.Proofs.HostTimeoutIteration

/-!
Placement: host-session-protocol R6, serving `Timeout.stale_never_applies` clause four.
Consumer: the concrete loop and delivery commands in native history.
The scheduler installs the proved returned fiber before consuming its nested commands.
-/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
namespace Test.Dogfood.Proofs.HostTimeoutSettle
open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Guard
open Effect4.Program.ReleaseCustody.CommandStacks
open HostTimeoutSlots HostTimeoutFlow HostTimeoutFrames HostTimeoutEvaluation HostTimeoutCommands
open HostTimeoutHeap HostTimeoutState HostTimeoutStateSteps HostTimeoutRaceSteps HostTimeoutQueue HostTimeoutParkSteps HostTimeoutLocalSteps HostTimeoutIteration

/-- A reverse saved-stack link transports the lookup-indexed nested overwrite demands. -/
theorem command_stack_back {B : List Val} {classes : Classes} {m n : Effect4.Program.NativeMachine}
    (command : NCmd) (held : CommandAt B classes m command) (back : StackLinks n m) :
    CommandAt B classes n command := by
  cases command with
  | finish id exit =>
    refine ⟨held.1, ?_⟩
    intro fiber found
    obtain ⟨old, seen, same⟩ := back id fiber found
    rw [← same]
    exact held.2 old seen
  | raceCancel race id yielding remaining visited =>
    intro fiber found
    obtain ⟨old, seen, same⟩ := back id fiber found
    rw [← same]
    exact held old seen
  | afterInterrupt id yielding kind =>
    refine ⟨held.1, ?_⟩
    intro fiber found
    obtain ⟨old, seen, same⟩ := back id fiber found
    rw [← same]
    exact held.2 old seen
  | evaluate id => exact held
  | loop id yielding => exact held
  | deliver id yielding => exact held
  | resume id token code => exact held
  | observe id exit observer => exact held
  | registrationDone race yielding => exact held
  | launch race => exact held
  | enrollRace race child => exact held
  | interruptTarget id who extra => exact held
  | trackChild parent child => exact held
  | exitDone id => exact held
  | closeParAwait id yielding children => exact held
  | link mode scope target who extra => exact held
  | drainDue => exact held
  | wake list phase => exact held

/-- Two installs at the same key with the same stack have the existing saved-stack relation. -/
theorem installs_stack_links (machine : Effect4.Program.NativeMachine) (before after : NativeFiber)
    (key : after.id = before.id) (stack : after.frame.stack = before.frame.stack) :
    StackLinks (machine.update before) (machine.update after) := by
  intro id fiber found
  rw [fiber_lookup_update] at found
  cases old : machine.fiber? id with
  | none => rw [old] at found; cases found
  | some previous =>
    rw [old, Option.map_some] at found
    split at found
    · have equal := Option.some.inj found
      subst fiber
      refine ⟨after, ?_, stack⟩
      rw [fiber_lookup_update, old, Option.map_some]
      rename_i same
      rw [if_pos (same.trans key.symm)]
    · have equal := Option.some.inj found
      subst fiber
      refine ⟨previous, ?_, rfl⟩
      rw [fiber_lookup_update, old, Option.map_some]
      rename_i different
      rw [if_neg (fun equal => different (equal.trans key))]

/-- Stopping the scheduler leaves all value-bearing fields intact. -/
theorem configuration_halt {B : List Val} {classes : Classes} {machine : Effect4.Program.NativeMachine}
    (owned : ConfigurationAt B classes machine) (why : Stuck) :
    ConfigurationAt B classes (machine.halt why) :=
  ⟨owned.supply, owned.kinds, owned.fibers, owned.races, owned.timers, owned.refs, owned.deferreds, owned.scopes⟩

/-- Appending commands retains their assertions at the same actual machine. -/
theorem commands_append {B : List Val} {classes : Classes} {machine : Effect4.Program.NativeMachine}
    {first second : List NCmd} (left : CommandsAt B classes machine first)
    (right : CommandsAt B classes machine second) : CommandsAt B classes machine (first ++ second) := by
  intro command member
  rcases List.mem_append.mp member with member | member
  · exact left command member
  · exact right command member

/-- Looking up an installed fiber at its own key returns that fiber whenever a row exists. -/
theorem installed_self {machine : Effect4.Program.NativeMachine} {fiber next : NativeFiber}
    (found : (machine.update fiber).fiber? fiber.id = some next) : next = fiber := by
  rw [fiber_lookup_update] at found
  cases old : machine.fiber? fiber.id with
  | none => rw [old] at found; cases found
  | some previous =>
    rw [old, Option.map_some, if_pos (fiber_id_of_lookup old)] at found
    exact (Option.some.inj found).symm

/-- The actual finish command consumes the proved scratch mask stack and body exit. -/
theorem finish_command {B : List Val} {classes : Classes} (result : NativeIter) (exit : ExitV)
    (good : ExitAt B .body exit) (masks : Masks result.fiber.frame.stack) :
    CommandAt B classes (result.machine.update result.fiber) (.finish result.fiber.id exit) := by
  refine ⟨good, ?_⟩
  intro next found
  have same := installed_self found
  subst next
  exact masks

/-- Settling an actual iteration keeps the configuration and the entire resulting command queue. -/
theorem settleOutcome_state {B : List Val} {classes : Classes} (result : NativeIter) (rest : List NCmd)
    (owned : EvaluationAt B classes result) (typed : IterKind B .body result)
    (tail : CommandsAt B classes (result.machine.update result.fiber) rest) :
    ConfigurationAt B classes (settleOutcome result.fiber.id rest result).1 ∧
      CommandsAt B classes (settleOutcome result.fiber.id rest result).1 (settleOutcome result.fiber.id rest result).2 := by
  have installed := configuration_update owned.1 _ owned.2.1
  cases outcome : result.outcome with
  | continue_ =>
    simp only [settleOutcome, outcome]
    refine ⟨installed, commands_append (commands_append owned.2.2.1 ?_) tail⟩
    intro command member
    have same := List.mem_singleton.mp member; subst command; trivial
  | answered =>
    simp only [settleOutcome, outcome]
    refine ⟨installed, commands_append (commands_append owned.2.2.1 ?_) tail⟩
    intro command member
    have same := List.mem_singleton.mp member; subst command; trivial
  | commands =>
    simp only [settleOutcome, outcome]
    exact ⟨installed, commands_append owned.2.2.1 tail⟩
  | finished exit =>
    simp only [IterKind, outcome] at typed
    simp only [settleOutcome, outcome]
    refine ⟨installed, commands_append (commands_append owned.2.2.1 ?_) tail⟩
    intro command member
    have same := List.mem_singleton.mp member; subst command
    exact finish_command result exit typed.1 typed.2.2
  | parked =>
    simp only [settleOutcome, outcome]
    split
    · let next : NativeFiber := {result.fiber with parked := .notParked, pending := []}
      have good : FiberAt B classes next :=
        ⟨owned.2.1.frame, (by intro token held; cases held), (by intro pending member; cases member),
          owned.2.1.dispatcher, owned.2.1.observers, owned.2.1.exits, owned.2.1.terminal, owned.2.1.children⟩
      have back := installs_stack_links result.machine next result.fiber rfl rfl
      have nested : CommandsAt B classes (result.machine.update next) result.nested :=
        fun command member => command_stack_back command (owned.2.2.1 command member) back
      have tailNext : CommandsAt B classes (result.machine.update next) rest :=
        fun command member => command_stack_back command (tail command member) back
      refine ⟨configuration_update owned.1 next good, commands_append (commands_append nested ?_) tailNext⟩
      intro command member
      have same := List.mem_singleton.mp member; subst command; trivial
    · let next : NativeFiber := {result.fiber with running := false}
      have good : FiberAt B classes next :=
        ⟨owned.2.1.frame, owned.2.1.park, owned.2.1.pending, owned.2.1.dispatcher,
          owned.2.1.observers, owned.2.1.exits, owned.2.1.terminal, owned.2.1.children⟩
      have back := installs_stack_links result.machine next result.fiber rfl rfl
      refine ⟨configuration_update owned.1 next good, commands_append ?_ ?_⟩
      · exact fun command member => command_stack_back command (owned.2.2.1 command member) back
      · exact fun command member => command_stack_back command (tail command member) back
  | stuck why =>
    simp only [settleOutcome, outcome]
    have good : FiberAt B classes {result.fiber with running := false} :=
      ⟨owned.2.1.frame, owned.2.1.park, owned.2.1.pending, owned.2.1.dispatcher,
        owned.2.1.observers, owned.2.1.exits, owned.2.1.terminal, owned.2.1.children⟩
    exact ⟨configuration_halt (configuration_update owned.1 _ good) why,
      by intro command member; cases member⟩

/-- The shared backward lookup reader supplies the old stack at every surviving key. -/
theorem interference_stack_back {before after : Effect4.Program.NativeMachine}
    (transport : Moves.InterferesWithLookup before after) (same : after.nextId = before.nextId) :
    StackLinks after before := by
  intro id next found
  obtain ⟨old, seen, edits⟩ := transport.backward_lookup same id next found
  exact ⟨old, seen, (StackRegion.other_edits_stack edits).symm⟩

/-- Actual settlement installs the local owner, applies admitted messages, and reads that owner again.
The shared message path and lookup relation supply the complete source-value transport. -/
theorem settle_state {B : List Val} {classes : Classes} (result : NativeIter) (rest : List NCmd)
    (owned : EvaluationAt B classes result) (typed : IterKind B .body result)
    (tail : CommandsAt B classes (result.machine.update result.fiber) rest) :
    ConfigurationAt B classes (settle result.fiber.id rest result).1 ∧
      CommandsAt B classes (settle result.fiber.id rest result).1 (settle result.fiber.id rest result).2 := by
  cases messages : result.edits with
  | nil =>
    simpa only [settle, messages] using settleOutcome_state result rest owned typed tail
  | cons message remaining =>
    let base := result.machine.update result.fiber
    let changed := applyFiberEdits (message :: remaining) base
    have installed : ConfigurationAt B classes base := configuration_update owned.1 _ owned.2.1
    have allowed : MessagesAt classes (message :: remaining) := by
      rw [← messages]
      exact owned.2.2.2
    have current : ConfigurationAt B classes changed.1 := configuration_messages base _ allowed installed
    have transport := Moves.InterferesWithLookup.fiberEdits (message :: remaining) base
    have same : changed.1.nextId = base.nextId := by rw [(RunMachine.applyFiberEdits_shape _ base).1]
    have back := interference_stack_back transport same
    cases found : changed.1.fiber? result.fiber.id with
    | none =>
      have absent := found
      dsimp only [changed, base] at absent
      simpa only [settle, messages, absent, changed, base] using
        And.intro (configuration_halt current (.unknownFiber result.fiber.id))
          (show CommandsAt B classes (changed.1.halt (.unknownFiber result.fiber.id)) [] from
            by intro command member; cases member)
    | some owner =>
      have key : owner.id = result.fiber.id := fiber_id_of_lookup found
      have good := configuration_fiber current found
      have returned := interference_stack_back (Moves.InterferesWithLookup.update found (.refl owner)) rfl
      have queueBack := returned.trans back
      have nested : CommandsAt B classes (changed.1.update owner) (changed.2 ++ result.nested) := by
        apply commands_append
        · intro command member
          obtain ⟨target, equal⟩ := (RunMachine.applyFiberEdits_shape _ base).2 command member
          subst command
          trivial
        · exact fun command member => command_stack_back command (owned.2.2.1 command member) queueBack
      have tailNext : CommandsAt B classes (changed.1.update owner) rest :=
        fun command member => command_stack_back command (tail command member) queueBack
      let next : NativeIter :=
        {result with machine := changed.1, fiber := owner, nested := changed.2 ++ result.nested, edits := []}
      have evaluation : EvaluationAt B classes next :=
        ⟨current, good, nested, by intro edit member; cases member⟩
      have nextTyped : IterKind B .body next := by
        cases outcome : result.outcome with
        | finished exit =>
          simp only [IterKind, next, outcome]
          simp only [IterKind, outcome] at typed
          obtain ⟨old, seen, stack⟩ := back result.fiber.id owner found
          have equal := installed_self seen
          subst old
          have masks : Masks owner.frame.stack := stack.symm ▸ typed.2.2
          exact ⟨typed.1, masks_current good.frame masks, masks⟩
        | _ => simpa only [IterKind, next, outcome] using good.frame
      have settled := settleOutcome_state next rest evaluation nextTyped tailNext
      have present := found
      dsimp only [changed, base] at present
      simpa only [settle, messages, present, next, changed, base, key] using settled

end Test.Dogfood.Proofs.HostTimeoutSettle
