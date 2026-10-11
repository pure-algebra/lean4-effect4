import Test.Dogfood.Proofs.HostTimeoutExitCommands

/-!
Placement: host-session-protocol R6, serving `Timeout.stale_never_applies` clause four.
Consumer: the eighteen-command assertion in reached native history.
Administrative commands keep the source assertions and every pending continuation demand.
-/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
namespace Test.Dogfood.Proofs.HostTimeoutAdminCommands
open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Guard
open Effect4.Program.ReleaseCustody.CommandStacks
open HostTimeoutSlots HostTimeoutFlow HostTimeoutFrames HostTimeoutEvaluation HostTimeoutCommands
open HostTimeoutHeap HostTimeoutState HostTimeoutStateSteps HostTimeoutRaceSteps HostTimeoutQueue HostTimeoutParkSteps HostTimeoutLocalSteps HostTimeoutIteration HostTimeoutSettle HostTimeoutLoop HostTimeoutObservers HostTimeoutRaceCommands HostTimeoutCancellation HostTimeoutExitCommands

/-- An actual evaluate command emits only its existing owner's loop command. -/
theorem evaluate_command {B : List Val} {classes : Classes} (machine : Effect4.Program.NativeMachine)
    (id : FiberId) (rest : List NCmd) (owned : ConfigurationAt B classes machine)
    (queue : GuardQueue HostTimeoutSource.program Test.Dogfood.Scenario.Timeout.fetch.table machine (.evaluate id :: rest))
    (commands : CommandsAt B classes machine (.evaluate id :: rest)) :
    letI := evaluatorFor HostTimeoutSource.program Test.Dogfood.Scenario.Timeout.fetch.table
    ConfigurationAt B classes (driveStep (interpOf HostTimeoutSource.program Test.Dogfood.Scenario.Timeout.fetch.table) machine (.evaluate id) rest).1 ∧
      CommandsAt B classes (driveStep (interpOf HostTimeoutSource.program Test.Dogfood.Scenario.Timeout.fetch.table) machine (.evaluate id) rest).1
        (driveStep (interpOf HostTimeoutSource.program Test.Dogfood.Scenario.Timeout.fetch.table) machine (.evaluate id) rest).2 := by
  letI := evaluatorFor HostTimeoutSource.program Test.Dogfood.Scenario.Timeout.fetch.table
  refine ⟨evaluate_state machine id rest owned, ?_⟩
  have tail := unowned_tail machine (.evaluate id) rest queue commands rfl (by intro target wrong; cases wrong)
  simp only [driveStep] at tail ⊢
  split
  · rename_i found; simp only [found] at tail; exact tail
  · rename_i fiber found; simp only [found] at tail
    split
    · rename_i blocked; simp only [if_pos blocked] at tail; exact tail
    · rename_i blocked; simp only [if_neg blocked] at tail
      intro command member
      rcases List.mem_cons.mp member with equal | previous
      · subst command; trivial
      · exact tail command previous

/-- The actual guarded resume installs its token's asserted code and emits evaluate only. -/
theorem resume_command_queue {B : List Val} {classes : Classes} (machine : Effect4.Program.NativeMachine)
    (id : FiberId) (token : Nat) (code : NCode) (rest : List NCmd) (owned : ConfigurationAt B classes machine)
    (guard : GuardState machine)
    (queue : GuardQueue HostTimeoutSource.program Test.Dogfood.Scenario.Timeout.fetch.table machine (.resume id token code :: rest))
    (commands : CommandsAt B classes machine (.resume id token code :: rest)) :
    letI := evaluatorFor HostTimeoutSource.program Test.Dogfood.Scenario.Timeout.fetch.table
    ConfigurationAt B classes (driveStep (interpOf HostTimeoutSource.program Test.Dogfood.Scenario.Timeout.fetch.table) machine (.resume id token code) rest).1 ∧
      CommandsAt B classes (driveStep (interpOf HostTimeoutSource.program Test.Dogfood.Scenario.Timeout.fetch.table) machine (.resume id token code) rest).1
        (driveStep (interpOf HostTimeoutSource.program Test.Dogfood.Scenario.Timeout.fetch.table) machine (.resume id token code) rest).2 := by
  letI := evaluatorFor HostTimeoutSource.program Test.Dogfood.Scenario.Timeout.fetch.table
  refine ⟨resume_state machine id token code rest owned guard (commands _ (List.mem_cons_self ..)), ?_⟩
  have tail := unowned_tail machine (.resume id token code) rest queue commands rfl (by intro target wrong; cases wrong)
  simp only [driveStep] at tail ⊢
  split
  · rename_i found; simp only [found] at tail; exact tail
  · rename_i fiber found; simp only [found] at tail
    cases parked : fiber.parked with
    | notParked => simpa only [parked] using tail
    | withGuard held =>
      simp only [parked] at tail ⊢
      split
      · rename_i same; simp only [if_pos same] at tail
        intro command member
        rcases List.mem_cons.mp member with equal | previous
        · subst command; trivial
        · exact tail command previous
      · rename_i different; simpa only [if_neg different] using tail

/-- Recording an interrupt emits only an evaluate command and retains saved stack demands. -/
theorem interrupt_command {B : List Val} {classes : Classes} (machine : Effect4.Program.NativeMachine)
    (id : FiberId) (who : Option FiberId) (extra : ReasonAnnotations Ann) (rest : List NCmd)
    (owned : ConfigurationAt B classes machine)
    (queue : GuardQueue HostTimeoutSource.program Test.Dogfood.Scenario.Timeout.fetch.table machine (.interruptTarget id who extra :: rest))
    (commands : CommandsAt B classes machine (.interruptTarget id who extra :: rest)) :
    letI := evaluatorFor HostTimeoutSource.program Test.Dogfood.Scenario.Timeout.fetch.table
    ConfigurationAt B classes (driveStep (interpOf HostTimeoutSource.program Test.Dogfood.Scenario.Timeout.fetch.table) machine (.interruptTarget id who extra) rest).1 ∧
      CommandsAt B classes (driveStep (interpOf HostTimeoutSource.program Test.Dogfood.Scenario.Timeout.fetch.table) machine (.interruptTarget id who extra) rest).1
        (driveStep (interpOf HostTimeoutSource.program Test.Dogfood.Scenario.Timeout.fetch.table) machine (.interruptTarget id who extra) rest).2 := by
  letI := evaluatorFor HostTimeoutSource.program Test.Dogfood.Scenario.Timeout.fetch.table
  refine ⟨interrupt_state machine id who extra rest owned, ?_⟩
  have tail := unowned_tail machine (.interruptTarget id who extra) rest queue commands rfl (by intro target wrong; cases wrong)
  simp only [driveStep] at tail ⊢
  split
  · rename_i found; simp only [found] at tail; exact tail
  · rename_i fiber found; simp only [found] at tail
    intro command member
    rcases List.mem_append.mp member with fresh | previous
    · split at fresh
      · have same := List.mem_singleton.mp fresh; subst command; trivial
      · cases fresh
    · exact tail command previous

/-- Timeout has no deferred cells, so the actual due drain owes no commands. -/
theorem drain_command {B : List Val} {classes : Classes} (machine : Effect4.Program.NativeMachine)
    (rest : List NCmd) (owned : ConfigurationAt B classes machine)
    (commands : CommandsAt B classes machine (.drainDue :: rest)) :
    letI := evaluatorFor HostTimeoutSource.program Test.Dogfood.Scenario.Timeout.fetch.table
    ConfigurationAt B classes (driveStep (interpOf HostTimeoutSource.program Test.Dogfood.Scenario.Timeout.fetch.table) machine .drainDue rest).1 ∧
      CommandsAt B classes (driveStep (interpOf HostTimeoutSource.program Test.Dogfood.Scenario.Timeout.fetch.table) machine .drainDue rest).1
        (driveStep (interpOf HostTimeoutSource.program Test.Dogfood.Scenario.Timeout.fetch.table) machine .drainDue rest).2 := by
  letI := evaluatorFor HostTimeoutSource.program Test.Dogfood.Scenario.Timeout.fetch.table
  have due : (interpOf HostTimeoutSource.program Test.Dogfood.Scenario.Timeout.fetch.table).dueResumes machine.state = ([], machine.state) := by
    have drain : machine.state.deferreds.drainDue = ([], machine.state.deferreds) := by
      rw [owned.deferreds]; rfl
    simp only [interpOf]
    rw [drain]
    rfl
  simp only [driveStep, due, drainOwed, List.nil_append]
  exact ⟨owned, fun command member => commands command (List.mem_cons_of_mem _ member)⟩

end Test.Dogfood.Proofs.HostTimeoutAdminCommands
