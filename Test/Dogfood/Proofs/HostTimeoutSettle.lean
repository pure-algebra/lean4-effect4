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
theorem settle_state {B : List Val} {classes : Classes} (result : NativeIter) (rest : List NCmd)
    (owned : EvaluationAt B classes result) (typed : IterKind B .body result)
    (tail : CommandsAt B classes (result.machine.update result.fiber) rest) :
    ConfigurationAt B classes (settle result.fiber.id rest result).1 ∧
      CommandsAt B classes (settle result.fiber.id rest result).1 (settle result.fiber.id rest result).2 := by
  have installed := configuration_update owned.1 _ owned.2.1
  cases outcome : result.outcome with
  | continue_ =>
    simp only [settle, outcome]
    refine ⟨installed, commands_append (commands_append owned.2.2 ?_) tail⟩
    intro command member
    have same := List.mem_singleton.mp member; subst command; trivial
  | answered =>
    simp only [settle, outcome]
    refine ⟨installed, commands_append (commands_append owned.2.2 ?_) tail⟩
    intro command member
    have same := List.mem_singleton.mp member; subst command; trivial
  | commands =>
    simp only [settle, outcome]
    exact ⟨installed, commands_append owned.2.2 tail⟩
  | finished exit =>
    simp only [IterKind, outcome] at typed
    simp only [settle, outcome]
    refine ⟨installed, commands_append (commands_append owned.2.2 ?_) tail⟩
    intro command member
    have same := List.mem_singleton.mp member; subst command
    exact finish_command result exit typed.1 typed.2.2
  | parked =>
    simp only [settle, outcome]
    split
    · let next : NativeFiber := {result.fiber with parked := .notParked, pending := []}
      have good : FiberAt B classes next :=
        ⟨owned.2.1.frame, (by intro token held; cases held), (by intro pending member; cases member),
          owned.2.1.dispatcher, owned.2.1.observers, owned.2.1.exits, owned.2.1.terminal, owned.2.1.children⟩
      have back := installs_stack_links result.machine next result.fiber rfl rfl
      have nested : CommandsAt B classes (result.machine.update next) result.nested :=
        fun command member => command_stack_back command (owned.2.2 command member) back
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
      · exact fun command member => command_stack_back command (owned.2.2 command member) back
      · exact fun command member => command_stack_back command (tail command member) back
  | stuck why =>
    simp only [settle, outcome]
    have good : FiberAt B classes {result.fiber with running := false} :=
      ⟨owned.2.1.frame, owned.2.1.park, owned.2.1.pending, owned.2.1.dispatcher,
        owned.2.1.observers, owned.2.1.exits, owned.2.1.terminal, owned.2.1.children⟩
    exact ⟨configuration_halt (configuration_update owned.1 _ good) why,
      by intro command member; cases member⟩

end Test.Dogfood.Proofs.HostTimeoutSettle
