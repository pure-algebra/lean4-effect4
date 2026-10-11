import Test.Dogfood.Proofs.HostTimeoutLocalSteps

/-!
Placement: host-session-protocol R6, serving `Timeout.stale_never_applies` clause four.
Consumer: the actual loop and delivery commands, then reached native history.
The source assertion covers the pending failure and forced-yield wrapper at the charged checkpoint.
-/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
namespace Test.Dogfood.Proofs.HostTimeoutIteration
open Effect4 Effect4.Machine Effect4.Program
open HostTimeoutSlots HostTimeoutFlow HostTimeoutFrames HostTimeoutEvaluation HostTimeoutCommands
open HostTimeoutHeap HostTimeoutState HostTimeoutStateSteps HostTimeoutRaceSteps HostTimeoutQueue HostTimeoutParkSteps HostTimeoutLocalSteps

/-- Charging an operation preserves the source assertion. -/
theorem count_op_fiber {B : List Val} {classes : Classes} {fiber : NativeFiber}
    (owned : FiberAt B classes fiber) : FiberAt B classes (countOp fiber) :=
  ⟨owned.frame, owned.park, owned.pending, owned.dispatcher, owned.observers,
    owned.exits, owned.terminal, owned.children⟩

/-- A deferred interruption enters failure at the same ordered saved stack. -/
theorem loop_top_fiber {B : List Val} {classes : Classes} {fiber : NativeFiber}
    (owned : FiberAt B classes fiber) (parked : fiber.parked = .notParked)
    (live : fiber.exit.isSome = false) : FiberAt B classes (runloopTop fiber) := by
  unfold runloopTop
  split
  · refine set_frame_live owned _ ?_ parked live
    obtain ⟨input, _, stack⟩ := owned.frame
    exact ⟨input, .head (.failure input _), stack⟩
  · exact owned

/-- The actual forced-yield wrapper retains its complete source continuation. -/
theorem injected_fiber {B : List Val} {classes : Classes} {fiber : NativeFiber}
    (owned : FiberAt B classes fiber) (parked : fiber.parked = .notParked)
    (live : fiber.exit.isSome = false) :
    FiberAt B classes {fiber with
      yieldOverride := none
      frame := {fiber.frame with current := .onSuccessConst (.yieldNowWith 0) fiber.frame.current}} := by
  have next : FiberAt B classes {fiber with yieldOverride := none} :=
    ⟨owned.frame, owned.park, owned.pending, owned.dispatcher, owned.observers,
      owned.exits, owned.terminal, owned.children⟩
  obtain ⟨input, code, stack⟩ := owned.frame
  exact reframe_live next (yield_before code) stack parked live

/-- The charged native loop iteration keeps every source and token assertion. -/
theorem iteration_state {B : List Val} {classes : Classes}
    (machine : Effect4.Program.NativeMachine) (fiber : NativeFiber) (yielding : Bool)
    (owned : ConfigurationAt B classes machine) (goodFiber : FiberAt B classes fiber)
    (parked : fiber.parked = .notParked) (live : fiber.exit.isSome = false)
    (stored : ∃ old, machine.fiber? fiber.id = some old) :
    letI := evaluatorFor HostTimeoutSource.program Test.Dogfood.Scenario.Timeout.fetch.table
    ∃ after, ClassLe classes after ∧ EvaluationAt B after
      (iteration (interpOf HostTimeoutSource.program Test.Dogfood.Scenario.Timeout.fetch.table) machine fiber yielding) := by
  letI := evaluatorFor HostTimeoutSource.program Test.Dogfood.Scenario.Timeout.fetch.table
  have charged := count_op_fiber (loop_top_fiber goodFiber parked live)
  have chargedPark : (countOp (runloopTop fiber)).parked = .notParked := by
    unfold countOp runloopTop
    split <;> exact parked
  have chargedLive : (countOp (runloopTop fiber)).exit.isSome = false := by
    unfold countOp runloopTop
    split <;> exact live
  have chargedId : (countOp (runloopTop fiber)).id = fiber.id := by
    unfold countOp runloopTop
    split <;> rfl
  have chargedStored : ∃ old, machine.fiber? (countOp (runloopTop fiber)).id = some old := by
    rw [chargedId]; exact stored
  unfold iteration
  by_cases inject : (!yielding && !(countOp (runloopTop fiber)).preventYield && yieldVerdict (countOp (runloopTop fiber))) = true
  · simp only [injectYield, inject, ite_true]
    exact evaluate_native_state (machine.emit _) _ true (configuration_emit owned _)
      (injected_fiber charged chargedPark chargedLive) chargedPark chargedLive chargedStored
  · simp only [injectYield, inject]
    exact evaluate_native_state machine _ yielding owned charged chargedPark chargedLive chargedStored

end Test.Dogfood.Proofs.HostTimeoutIteration
