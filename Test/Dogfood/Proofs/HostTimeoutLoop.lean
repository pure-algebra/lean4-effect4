import Test.Dogfood.Proofs.HostTimeoutSettle
import Effect4.Laws.Program.ReleaseCustody.NativeStacks

/-!
Placement: host-session-protocol R6, serving `Timeout.stale_never_applies` clause four.
Consumer: the eighteen-command assertion lifted to actual native history.
The existing guard authority supplies each active owner and protects its pending suffix.
-/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
namespace Test.Dogfood.Proofs.HostTimeoutLoop
open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Guard
open Effect4.Program.ReleaseCustody.CommandStacks Effect4.Program.ReleaseCustody.NativeStacks
open HostTimeoutSlots HostTimeoutFlow HostTimeoutFrames HostTimeoutEvaluation HostTimeoutCommands
open HostTimeoutHeap HostTimeoutState HostTimeoutStateSteps HostTimeoutRaceSteps HostTimeoutQueue HostTimeoutParkSteps HostTimeoutLocalSteps HostTimeoutIteration HostTimeoutSettle

/-- An active owner cannot have a published exit under the existing native guard. -/
theorem active_live {machine : Effect4.Program.NativeMachine} {fiber : NativeFiber}
    (guard : GuardState machine) (found : machine.fiber? fiber.id = some fiber)
    (running : fiber.running = true) : fiber.exit.isSome = false := by
  cases exited : fiber.exit.isSome with
  | false => rfl
  | true =>
    have stopped := (guard.exited fiber (List.mem_of_find?_eq_some found) exited).2
    rw [running] at stopped
    cases stopped

/-- The actual charged iteration supplies the finish exit and scratch masks as well as its frame assertion. -/
theorem iteration_kind {B : List Val} {classes : Classes}
    (machine : Effect4.Program.NativeMachine) (fiber : NativeFiber) (yielding : Bool)
    (goodFiber : FiberAt B classes fiber) (parked : fiber.parked = .notParked)
    (live : fiber.exit.isSome = false) :
    letI := evaluatorFor HostTimeoutSource.program Test.Dogfood.Scenario.Timeout.fetch.table
    IterKind B .body
      (iteration (interpOf HostTimeoutSource.program Test.Dogfood.Scenario.Timeout.fetch.table) machine fiber yielding) := by
  letI := evaluatorFor HostTimeoutSource.program Test.Dogfood.Scenario.Timeout.fetch.table
  have charged := count_op_fiber (loop_top_fiber goodFiber parked live)
  have chargedPark : (countOp (runloopTop fiber)).parked = .notParked := by
    unfold countOp runloopTop
    split <;> exact parked
  have chargedLive : (countOp (runloopTop fiber)).exit.isSome = false := by
    unfold countOp runloopTop
    split <;> exact live
  unfold iteration
  by_cases inject : (!yielding && !(countOp (runloopTop fiber)).preventYield && yieldVerdict (countOp (runloopTop fiber))) = true
  · simp only [injectYield, inject, ite_true]
    exact evaluate_native (machine.emit _) _ true
      (injected_fiber charged chargedPark chargedLive).frame
  · simp only [injectYield, inject]
    exact evaluate_native machine _ yielding charged.frame

/-- The actual loop command retains the source assertion and every pending command demand. -/
theorem loop_command {B : List Val} {classes : Classes}
    (machine : Effect4.Program.NativeMachine) (id : FiberId) (yielding : Bool) (rest : List NCmd)
    (owned : ConfigurationAt B classes machine) (guard : GuardState machine)
    (queue : GuardQueue HostTimeoutSource.program Test.Dogfood.Scenario.Timeout.fetch.table machine (.loop id yielding :: rest))
    (commands : CommandsAt B classes machine (.loop id yielding :: rest)) :
    letI := evaluatorFor HostTimeoutSource.program Test.Dogfood.Scenario.Timeout.fetch.table
    ∃ after, ClassLe classes after ∧
      ConfigurationAt B after (driveStep (interpOf HostTimeoutSource.program Test.Dogfood.Scenario.Timeout.fetch.table) machine (.loop id yielding) rest).1 ∧
      CommandsAt B after (driveStep (interpOf HostTimeoutSource.program Test.Dogfood.Scenario.Timeout.fetch.table) machine (.loop id yielding) rest).1
        (driveStep (interpOf HostTimeoutSource.program Test.Dogfood.Scenario.Timeout.fetch.table) machine (.loop id yielding) rest).2 := by
  letI := evaluatorFor HostTimeoutSource.program Test.Dogfood.Scenario.Timeout.fetch.table
  obtain ⟨fiber, found, running, parked⟩ := queue.authority (.loop id yielding) (List.mem_cons_self ..)
  have key := fiber_id_of_lookup found
  have stored : machine.fiber? fiber.id = some fiber := by rw [key]; exact found
  have live := active_live guard stored running
  have good := configuration_fiber owned found
  obtain ⟨after, later, evaluation⟩ := iteration_state machine fiber yielding owned good parked live ⟨fiber, stored⟩
  have links := Effect4.Program.ReleaseCustody.NativeStacks.iteration_links HostTimeoutSource.program Test.Dogfood.Scenario.Timeout.fetch.table machine fiber yielding
  have identity := Guard.Interruption.iteration_id HostTimeoutSource.program Test.Dogfood.Scenario.Timeout.fetch.table machine fiber yielding
  have away : StackLinksAway id machine
      ((iteration (interpOf HostTimeoutSource.program Test.Dogfood.Scenario.Timeout.fetch.table) machine fiber yielding).machine.update
        (iteration (interpOf HostTimeoutSource.program Test.Dogfood.Scenario.Timeout.fetch.table) machine fiber yielding).fiber) := by
    have install :=  update_away
      (iteration (interpOf HostTimeoutSource.program Test.Dogfood.Scenario.Timeout.fetch.table) machine fiber yielding).machine
      (iteration (interpOf HostTimeoutSource.program Test.Dogfood.Scenario.Timeout.fetch.table) machine fiber yielding).fiber
    rw [identity, key] at install
    exact (links.away id).trans install
  have tail := tail_transport (.loop id yielding) rest id later queue rfl
    (fun command member => commands command (List.mem_cons_of_mem _ member)) away
  have settled := settle_state _ rest evaluation (iteration_kind machine fiber yielding good parked live) tail
  rw [identity, key] at settled
  refine ⟨after, later, ?_⟩
  simpa only [driveStep, found] using settled

/-- The actual delivery command retains the source assertion and every pending command demand. -/
theorem deliver_command {B : List Val} {classes : Classes}
    (machine : Effect4.Program.NativeMachine) (id : FiberId) (yielding : Bool) (rest : List NCmd)
    (owned : ConfigurationAt B classes machine) (guard : GuardState machine)
    (queue : GuardQueue HostTimeoutSource.program Test.Dogfood.Scenario.Timeout.fetch.table machine (.deliver id yielding :: rest))
    (commands : CommandsAt B classes machine (.deliver id yielding :: rest)) :
    letI := evaluatorFor HostTimeoutSource.program Test.Dogfood.Scenario.Timeout.fetch.table
    ∃ after, ClassLe classes after ∧
      ConfigurationAt B after (driveStep (interpOf HostTimeoutSource.program Test.Dogfood.Scenario.Timeout.fetch.table) machine (.deliver id yielding) rest).1 ∧
      CommandsAt B after (driveStep (interpOf HostTimeoutSource.program Test.Dogfood.Scenario.Timeout.fetch.table) machine (.deliver id yielding) rest).1
        (driveStep (interpOf HostTimeoutSource.program Test.Dogfood.Scenario.Timeout.fetch.table) machine (.deliver id yielding) rest).2 := by
  letI := evaluatorFor HostTimeoutSource.program Test.Dogfood.Scenario.Timeout.fetch.table
  obtain ⟨fiber, found, running, parked⟩ := queue.authority (.deliver id yielding) (List.mem_cons_self ..)
  have key := fiber_id_of_lookup found
  have stored : machine.fiber? fiber.id = some fiber := by rw [key]; exact found
  have live := active_live guard stored running
  have good := configuration_fiber owned found
  obtain ⟨after, later, evaluation⟩ := evaluate_native_state machine fiber yielding owned good parked live ⟨fiber, stored⟩
  have links := Effect4.Program.ReleaseCustody.NativeStacks.native_links HostTimeoutSource.program Test.Dogfood.Scenario.Timeout.fetch.table machine fiber yielding
  have identity := Guard.Interruption.evaluateNative_id HostTimeoutSource.program Test.Dogfood.Scenario.Timeout.fetch.table machine fiber yielding
  have away : StackLinksAway id machine
      ((evaluateNative HostTimeoutSource.program machine fiber yielding Test.Dogfood.Scenario.Timeout.fetch.table).machine.update
        (evaluateNative HostTimeoutSource.program machine fiber yielding Test.Dogfood.Scenario.Timeout.fetch.table).fiber) := by
    have install :=  update_away
      (evaluateNative HostTimeoutSource.program machine fiber yielding Test.Dogfood.Scenario.Timeout.fetch.table).machine
      (evaluateNative HostTimeoutSource.program machine fiber yielding Test.Dogfood.Scenario.Timeout.fetch.table).fiber
    rw [identity, key] at install
    exact (links.away id).trans install
  have tail := tail_transport (.deliver id yielding) rest id later queue rfl
    (fun command member => commands command (List.mem_cons_of_mem _ member)) away
  have settled := settle_state _ rest evaluation (evaluate_native machine fiber yielding good.frame) tail
  rw [identity, key] at settled
  refine ⟨after, later, ?_⟩
  simpa only [driveStep, found] using settled

end Test.Dogfood.Proofs.HostTimeoutLoop
