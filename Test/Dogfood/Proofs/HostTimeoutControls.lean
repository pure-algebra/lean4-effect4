import Test.Dogfood.Proofs.HostTimeoutScheduler
import Effect4.Laws.Program.Guard.Decision

/-!
Placement: host-session-protocol R6, serving `Timeout.stale_never_applies` clause four.
Consumer: every non-answer row in the recorded Timeout run.
Host answers remain separate because their body evidence comes from actual reply application.
-/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
namespace Test.Dogfood.Proofs.HostTimeoutControls
open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Guard
open Effect4.Program.Guard.OuterDriver Effect4.Program.Guard.LocalDecision Effect4.Program.Guard.RegistrationQueue Effect4.Machine.Lift
open HostTimeoutSlots HostTimeoutFlow HostTimeoutFrames HostTimeoutEvaluation HostTimeoutCommands
open HostTimeoutHeap HostTimeoutState HostTimeoutStateSteps HostTimeoutRaceSteps HostTimeoutQueue HostTimeoutParkSteps HostTimeoutLocalSteps HostTimeoutIteration HostTimeoutSettle HostTimeoutLoop HostTimeoutObservers HostTimeoutRaceCommands HostTimeoutCancellation HostTimeoutExitCommands HostTimeoutAdminCommands HostTimeoutDriver HostTimeoutScheduler

/-- An ordinary evaluate decision enters the actual asserted command queue. -/
theorem evaluate_entry {B : List Val} {classes : Classes} (machine : Effect4.Program.NativeMachine)
    (id : FiberId) (owned : ConfigurationAt B classes machine) (guard : GuardState machine) :
    DriverAt B classes machine [.evaluate id, .drainDue] := by
  refine ⟨owned, ?_, guard, guardQueue_evaluate_drainDue HostTimeoutSource.program Test.Dogfood.Scenario.Timeout.fetch.table machine id,
    ⟨True.intro, True.intro, True.intro⟩⟩
  intro command member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with same | same <;> subst command <;> trivial

/-- Recording an external interruption changes no successful body evidence. -/
theorem interrupt_edit {B : List Val} {classes : Classes} (machine : Effect4.Program.NativeMachine)
    (id : FiberId) (fiber : NativeFiber) (who : Option FiberId) (extra : ReasonAnnotations Ann)
    (owned : ConfigurationAt B classes machine) (found : machine.fiber? id = some fiber) :
    ConfigurationAt B classes (interruptBeforeLoop HostTimeoutSource.program Test.Dogfood.Scenario.Timeout.fetch.table machine id fiber who extra) := by
  unfold interruptBeforeLoop
  dsimp only
  split
  · exact configuration_update (configuration_emit (configuration_emit owned _) _) _
      (interrupted_fiber fiber (configuration_fiber owned found) who extra)
  · exact configuration_update (configuration_emit owned _) _
      (interrupted_fiber fiber (configuration_fiber owned found) who extra)

/-- Every actual control decision preserves Timeout's source assertion at arbitrary command fuel. -/
theorem control_state {B : List Val} {classes : Classes} (machine : Effect4.Program.NativeMachine)
    (fuel : Nat) (decision : NativeDecision) (owned : ConfigurationAt B classes machine) (guard : GuardState machine)
    (control : ∀ id token answer, decision ≠ .answerAsync id token answer) :
    ∃ after, ClassLe classes after ∧ ConfigurationAt B after
      (steppedBy HostTimeoutSource.program fuel Test.Dogfood.Scenario.Timeout.fetch.table machine decision) := by
  letI := evaluatorFor HostTimeoutSource.program Test.Dogfood.Scenario.Timeout.fetch.table
  have fold := fold_lift B machine
  have entry : SchedulerAt B machine classes machine := ⟨owned, .refl guard⟩
  cases decision with
  | fire owner =>
    obtain ⟨after, later, result⟩ := fold.fireState_lift fuel classes machine owner entry
    exact ⟨after, later, result.1⟩
  | flush =>
    obtain ⟨after, later, result⟩ := fold.flushAllState_lift fuel fuel classes machine entry
    exact ⟨after, later, result.1⟩
  | advance millis =>
    obtain ⟨after, later, result⟩ := fold.advanceState_lift fuel millis fuel classes machine entry
    exact ⟨after, later, result.1⟩
  | evaluate id =>
    obtain ⟨after, later, result⟩ := drive_state B fuel classes machine _ (evaluate_entry machine id owned guard)
    exact ⟨after, later, result.1⟩
  | yieldVerdict id verdict =>
    refine ⟨classes, classOrder.refl classes, configuration_modify owned id _ ?_⟩
    intro fiber good
    exact ⟨good.frame, good.park, good.pending, good.dispatcher, good.observers, good.exits, good.terminal, good.children⟩
  | installMiddleware =>
    exact ⟨classes, classOrder.refl classes, owned.supply, owned.kinds, owned.fibers, owned.races,
      owned.timers, owned.refs, owned.deferreds, owned.scopes⟩
  | interruptFrom who extra id =>
    cases found : machine.fiber? id with
    | none => simpa only [steppedBy, stepDecisionState, found] using
        (⟨classes, classOrder.refl classes, owned⟩ : ∃ after, ClassLe classes after ∧ ConfigurationAt B after machine)
    | some fiber =>
      have key : fiber.id = id := fiber_id_of_lookup found
      have stored : machine.fiber? fiber.id = some fiber := by rw [key]; exact found
      have source := interrupt_edit machine id fiber who extra owned found
      have guarded := guardState_interruptBeforeLoop HostTimeoutSource.program Test.Dogfood.Scenario.Timeout.fetch.table machine id fiber who extra guard stored
      rw [interruptFrom_eq HostTimeoutSource.program Test.Dogfood.Scenario.Timeout.fetch.table fuel machine id fiber who extra found]
      split
      · obtain ⟨after, later, result⟩ := drive_state B fuel classes _ _ (evaluate_entry _ id source guarded)
        exact ⟨after, later, result.1⟩
      · exact ⟨classes, classOrder.refl classes, source⟩
  | answerAsync id token answer => exact False.elim (control id token answer rfl)

end Test.Dogfood.Proofs.HostTimeoutControls
