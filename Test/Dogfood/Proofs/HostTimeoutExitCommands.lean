import Test.Dogfood.Proofs.HostTimeoutCancellation

/-!
Placement: host-session-protocol R6, serving `Timeout.stale_never_applies` clause four.
Consumer: native finish and exitDone commands, then reached history.
Published exits retain their body evidence; observer and scratch-stack clearing keep the pending suffix's owned stacks.
-/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
namespace Test.Dogfood.Proofs.HostTimeoutExitCommands
open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Guard
open Effect4.Program.ReleaseCustody.CommandStacks
open HostTimeoutSlots HostTimeoutFlow HostTimeoutFrames HostTimeoutEvaluation HostTimeoutCommands
open HostTimeoutHeap HostTimeoutState HostTimeoutStateSteps HostTimeoutRaceSteps HostTimeoutQueue HostTimeoutParkSteps HostTimeoutLocalSteps HostTimeoutIteration HostTimeoutSettle HostTimeoutLoop HostTimeoutObservers HostTimeoutRaceCommands HostTimeoutCancellation

/-- The actual source exit path emits only body-class observers, exit clearing and the due drain. -/
theorem exit_commands {B : List Val} {classes : Classes} (machine : Effect4.Program.NativeMachine)
    (fiber : NativeFiber) (exit : ExitV) (goodFiber : FiberAt B classes fiber)
    (goodExit : ExitAt B .body exit) :
    let result := exitFiber (interpOf HostTimeoutSource.program Test.Dogfood.Scenario.Timeout.fetch.table) machine fiber exit
    CommandsAt B classes result.1 result.2 := by
  have noChildren : (machine.middlewareInstalled && fiber.finalizing.isNone && !fiber.children.isEmpty) = false := by
    rw [goodFiber.children]
    simp only [List.isEmpty_nil, Bool.not_true, Bool.and_false]
  unfold exitFiber
  rw [noChildren]
  simp only [Bool.false_eq_true, ite_false]
  unfold exitFiber.exitStore
  dsimp only [RunFiber.publish]
  split
  · intro command member
    have equal := List.mem_singleton.mp member
    subst command; trivial
  · rename_i observers same
    intro command member
    rcases List.mem_append.mp member with fired | cleared
    · obtain ⟨observer, present, equal⟩ := List.mem_map.mp fired
      subst command
      exact ⟨goodExit, goodFiber.observers observer present⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at cleared
      rcases cleared with equal | equal <;> subst command <;> trivial

/-- Publishing and clearing the source owner retain every other actual saved stack. -/
theorem exit_away {B : List Val} {classes : Classes} (machine : Effect4.Program.NativeMachine)
    (fiber : NativeFiber) (exit : ExitV) (good : FiberAt B classes fiber) :
    StackLinksAway fiber.id machine
      (exitFiber (interpOf HostTimeoutSource.program Test.Dogfood.Scenario.Timeout.fetch.table) machine fiber exit).1 := by
  have noChildren : (machine.middlewareInstalled && fiber.finalizing.isNone && !fiber.children.isEmpty) = false := by
    rw [good.children]
    simp only [List.isEmpty_nil, Bool.not_true, Bool.and_false]
  let interp := interpOf HostTimeoutSource.program Test.Dogfood.Scenario.Timeout.fetch.table
  let published := fiber.publish exit
  let middle := (machine.update published).emit [RunEvent.exited published.id exit]
  have first : StackLinksAway fiber.id machine middle :=
    (update_away machine published).trans
      ((StackLinks.of_fibers (m := machine.update published) (n := middle) rfl).away fiber.id)
  unfold exitFiber
  rw [noChildren]
  simp only [Bool.false_eq_true, ite_false]
  unfold exitFiber.exitStore
  dsimp only
  split
  · change StackLinksAway fiber.id machine (middle.update (published.cleared interp))
    exact first.trans (update_away middle (published.cleared interp))
  · exact first

/-- The actual finish command publishes its asserted exit and transports the entire pending suffix. -/
theorem finish_command {B : List Val} {classes : Classes} (machine : Effect4.Program.NativeMachine)
    (id : FiberId) (exit : ExitV) (rest : List NCmd) (owned : ConfigurationAt B classes machine)
    (queue : GuardQueue HostTimeoutSource.program Test.Dogfood.Scenario.Timeout.fetch.table machine (.finish id exit :: rest))
    (commands : CommandsAt B classes machine (.finish id exit :: rest)) :
    letI := evaluatorFor HostTimeoutSource.program Test.Dogfood.Scenario.Timeout.fetch.table
    ConfigurationAt B classes (driveStep (interpOf HostTimeoutSource.program Test.Dogfood.Scenario.Timeout.fetch.table) machine (.finish id exit) rest).1 ∧
      CommandsAt B classes (driveStep (interpOf HostTimeoutSource.program Test.Dogfood.Scenario.Timeout.fetch.table) machine (.finish id exit) rest).1
        (driveStep (interpOf HostTimeoutSource.program Test.Dogfood.Scenario.Timeout.fetch.table) machine (.finish id exit) rest).2 := by
  letI := evaluatorFor HostTimeoutSource.program Test.Dogfood.Scenario.Timeout.fetch.table
  have demand := commands (.finish id exit) (List.mem_cons_self ..)
  cases found : machine.fiber? id with
  | none =>
    have tail : CommandsAt B classes machine rest :=
      fun command member => commands command (List.mem_cons_of_mem _ member)
    simpa only [driveStep, found] using And.intro owned tail
  | some fiber =>
    have good := configuration_fiber owned found
    have idle : FiberAt B classes {fiber with running := false} :=
      ⟨good.frame, good.park, good.pending, good.dispatcher, good.observers, good.exits, good.terminal, good.children⟩
    have key : fiber.id = id := fiber_id_of_lookup found
    have links : StackLinksAway id machine
        (exitFiber (interpOf HostTimeoutSource.program Test.Dogfood.Scenario.Timeout.fetch.table) machine {fiber with running := false} exit).1 := by
      intro target old different seen
      exact exit_away machine {fiber with running := false} exit idle target old
        (fun same => different (same.trans key)) seen
    have tail := tail_transport (.finish id exit) rest id (classOrder.refl classes) queue rfl
      (fun command member => commands command (List.mem_cons_of_mem _ member)) links
    simpa only [driveStep, found] using And.intro
      (exit_fiber_state machine _ exit owned idle demand.1 (demand.2 fiber found))
      (commands_append (exit_commands machine _ exit idle demand.1) tail)

/-- Clearing the published owner preserves every active command's asserted stack. -/
theorem exit_done_command {B : List Val} {classes : Classes} (machine : Effect4.Program.NativeMachine)
    (id : FiberId) (rest : List NCmd) (owned : ConfigurationAt B classes machine)
    (guard : GuardState machine)
    (queue : GuardQueue HostTimeoutSource.program Test.Dogfood.Scenario.Timeout.fetch.table machine (.exitDone id :: rest))
    (commands : CommandsAt B classes machine (.exitDone id :: rest)) :
    letI := evaluatorFor HostTimeoutSource.program Test.Dogfood.Scenario.Timeout.fetch.table
    ConfigurationAt B classes (driveStep (interpOf HostTimeoutSource.program Test.Dogfood.Scenario.Timeout.fetch.table) machine (.exitDone id) rest).1 ∧
      CommandsAt B classes (driveStep (interpOf HostTimeoutSource.program Test.Dogfood.Scenario.Timeout.fetch.table) machine (.exitDone id) rest).1
        (driveStep (interpOf HostTimeoutSource.program Test.Dogfood.Scenario.Timeout.fetch.table) machine (.exitDone id) rest).2 := by
  letI := evaluatorFor HostTimeoutSource.program Test.Dogfood.Scenario.Timeout.fetch.table
  have state := exit_done_state machine id rest owned guard (queue.authority (.exitDone id) (List.mem_cons_self ..))
  have tail : CommandsAt B classes machine rest :=
    fun command member => commands command (List.mem_cons_of_mem _ member)
  cases found : machine.fiber? id with
  | none => simpa only [driveStep, found] using And.intro owned tail
  | some fiber =>
    have key : fiber.id = id := fiber_id_of_lookup found
    have seen : machine.fiber? fiber.id = some fiber := by rw [key]; exact found
    obtain ⟨old, oldFound, exited⟩ := queue.authority (.exitDone id) (List.mem_cons_self ..)
    have equal : old = fiber := Option.some.inj (oldFound.symm.trans found)
    subst old
    have transported : CommandsAt B classes
        (machine.update (fiber.cleared (interpOf HostTimeoutSource.program Test.Dogfood.Scenario.Timeout.fetch.table))) rest := by
      intro command member
      apply command_transport command (classOrder.refl classes)
        (queue.authority command (List.mem_cons_of_mem _ member)) (tail command member)
      intro target owns prior present
      exact update_away machine (fiber.cleared (interpOf HostTimeoutSource.program Test.Dogfood.Scenario.Timeout.fetch.table)) target prior
        (exited_not_owner HostTimeoutSource.program Test.Dogfood.Scenario.Timeout.fetch.table machine guard _ queue fiber seen exited
          command (List.mem_cons_of_mem _ member) target owns) present
    simpa only [driveStep, found] using And.intro state transported

end Test.Dogfood.Proofs.HostTimeoutExitCommands
