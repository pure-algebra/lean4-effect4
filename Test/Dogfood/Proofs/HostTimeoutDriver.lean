import Test.Dogfood.Proofs.HostTimeoutAdminCommands
import Effect4.Laws.Program.Guard.Driver

/-!
Placement: host-session-protocol R6, serving `Timeout.stale_never_applies` clause four.
Consumer: task and accepted-decision closure in actual reached native history.
The assertion covers all eighteen native commands and every fuel frontier.
-/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
namespace Test.Dogfood.Proofs.HostTimeoutDriver
open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Guard
open Effect4.Program.Guard.RegistrationQueue Effect4.Machine.Lift
open HostTimeoutSlots HostTimeoutFlow HostTimeoutFrames HostTimeoutEvaluation HostTimeoutCommands
open HostTimeoutHeap HostTimeoutState HostTimeoutStateSteps HostTimeoutRaceSteps HostTimeoutQueue HostTimeoutParkSteps HostTimeoutLocalSteps HostTimeoutIteration HostTimeoutSettle HostTimeoutLoop HostTimeoutObservers HostTimeoutRaceCommands HostTimeoutCancellation HostTimeoutExitCommands HostTimeoutAdminCommands

/-- Every actual native command retains the same body set and extends only token classes. -/
theorem command_state {B : List Val} {classes : Classes} (machine : Effect4.Program.NativeMachine)
    (command : NCmd) (rest : List NCmd) (owned : ConfigurationAt B classes machine)
    (guard : GuardState machine)
    (queue : GuardQueue HostTimeoutSource.program Test.Dogfood.Scenario.Timeout.fetch.table machine (command :: rest))
    (commands : CommandsAt B classes machine (command :: rest)) :
    letI := evaluatorFor HostTimeoutSource.program Test.Dogfood.Scenario.Timeout.fetch.table
    ∃ after, ClassLe classes after ∧
      ConfigurationAt B after (driveStep (interpOf HostTimeoutSource.program Test.Dogfood.Scenario.Timeout.fetch.table) machine command rest).1 ∧
      CommandsAt B after (driveStep (interpOf HostTimeoutSource.program Test.Dogfood.Scenario.Timeout.fetch.table) machine command rest).1
        (driveStep (interpOf HostTimeoutSource.program Test.Dogfood.Scenario.Timeout.fetch.table) machine command rest).2 := by
  letI := evaluatorFor HostTimeoutSource.program Test.Dogfood.Scenario.Timeout.fetch.table
  cases command with
  | loop id yielding => exact loop_command machine id yielding rest owned guard queue commands
  | deliver id yielding => exact deliver_command machine id yielding rest owned guard queue commands
  | evaluate id => exact ⟨classes, classOrder.refl classes, evaluate_command machine id rest owned queue commands⟩
  | resume id token code => exact ⟨classes, classOrder.refl classes, resume_command_queue machine id token code rest owned guard queue commands⟩
  | launch race => exact ⟨classes, classOrder.refl classes, launch_command machine race rest owned queue commands⟩
  | enrollRace race child => exact ⟨classes, classOrder.refl classes, enroll_command machine race child rest owned queue commands⟩
  | registrationDone race yielding => exact ⟨classes, classOrder.refl classes, registration_command machine race yielding rest owned guard queue commands⟩
  | interruptTarget id who extra => exact ⟨classes, classOrder.refl classes, interrupt_command machine id who extra rest owned queue commands⟩
  | afterInterrupt host yielding kind => exact ⟨classes, classOrder.refl classes, after_interrupt_command machine host yielding kind rest owned guard queue commands⟩
  | raceCancel race host yielding remaining visited => exact ⟨classes, classOrder.refl classes, cancel_command machine race host yielding remaining visited rest owned commands⟩
  | observe id exit observer => exact ⟨classes, classOrder.refl classes, observe_command machine id exit observer rest owned queue commands⟩
  | exitDone id => exact ⟨classes, classOrder.refl classes, exit_done_command machine id rest owned guard queue commands⟩
  | finish id exit => exact ⟨classes, classOrder.refl classes, finish_command machine id exit rest owned queue commands⟩
  | drainDue => exact ⟨classes, classOrder.refl classes, drain_command machine rest owned commands⟩
  | trackChild parent child => exact False.elim (commands _ (List.mem_cons_self ..))
  | closeParAwait host yielding children => exact False.elim (commands _ (List.mem_cons_self ..))
  | link mode scope target who extra => exact False.elim (commands _ (List.mem_cons_self ..))
  | wake list phase => exact False.elim (commands _ (List.mem_cons_self ..))

/-- The command invariant carries the existing guard and queue authority beside the source assertion. -/
def DriverAt (B : List Val) (classes : Classes) (machine : Effect4.Program.NativeMachine) (commands : List NCmd) : Prop :=
  ConfigurationAt B classes machine ∧ CommandsAt B classes machine commands ∧
    guardI HostTimeoutSource.program Test.Dogfood.Scenario.Timeout.fetch.table machine commands

/-- The complete native command loop preserves body provenance at every fuel frontier. -/
theorem drive_state (B : List Val) (fuel : Nat) (classes : Classes) (machine : Effect4.Program.NativeMachine)
    (commands : List NCmd) (held : DriverAt B classes machine commands) :
    letI := evaluatorFor HostTimeoutSource.program Test.Dogfood.Scenario.Timeout.fetch.table
    ∃ after, ClassLe classes after ∧
      DriverAt B after (driveState (interpOf HostTimeoutSource.program Test.Dogfood.Scenario.Timeout.fetch.table) fuel machine commands).1
        (driveState (interpOf HostTimeoutSource.program Test.Dogfood.Scenario.Timeout.fetch.table) fuel machine commands).2 := by
  letI := evaluatorFor HostTimeoutSource.program Test.Dogfood.Scenario.Timeout.fetch.table
  apply driveState_lift classOrder (interpOf HostTimeoutSource.program Test.Dogfood.Scenario.Timeout.fetch.table) (DriverAt B) _ fuel classes machine commands held
  intro before machine command rest _ held
  obtain ⟨after, later, source, commands⟩ := command_state machine command rest held.1 held.2.2.1 held.2.2.2.1 held.2.1
  exact ⟨after, later, source, commands,
    driveStep_invariants HostTimeoutSource.program Test.Dogfood.Scenario.Timeout.fetch.table machine command rest
      held.2.2.1 held.2.2.2.1 held.2.2.2.2⟩

end Test.Dogfood.Proofs.HostTimeoutDriver
