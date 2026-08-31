import Std

/-!
# Fiber representative counterexamples

This file is a self-contained breaker model.  It deliberately does not import
the production concurrency modules: the witnesses must remain executable while
the production surface is still absent.  Each theorem is finite and proves only
the named attack.
-/

namespace Effect4Test.Counterexamples.Concurrency.FiberRepresentative

abbrev FiberId := Nat

def worker : FiberId := 0
def waiter : FiberId := 1

inductive Terminal where
  | success
  | failure
  | defect
  | interrupted
  deriving DecidableEq, Repr

inductive Status where
  | runnable
  | running
  | waiting (target : FiberId)
  | finalizing (result : Terminal)
  | done (result : Terminal)
  deriving DecidableEq, Repr

inductive Mask where
  | unmasked
  | masked
  deriving DecidableEq, Repr

inductive CleanupPhase where
  | notStarted
  | pending
  | done
  deriving DecidableEq, Repr

structure MiniFiber where
  status : Status
  mask : Mask
  interruptPending : Bool
  cleanup : CleanupPhase
  cleanupRuns : Nat
  deriving DecidableEq, Repr

inductive Event where
  | ran (id : FiberId)
  | interruptRequested (id : FiberId)
  | interruptDeferred (id : FiberId)
  | interruptDelivered (id : FiberId)
  | completed (id : FiberId) (result : Terminal)
  | cleanup (id : FiberId)
  | joined (waiter target : FiberId) (result : Terminal)
  deriving DecidableEq, Repr

structure MiniMachine where
  workerState : MiniFiber
  waiterState : MiniFiber
  trace : List Event
  deriving DecidableEq, Repr

def baseFiber : MiniFiber :=
  { status := .runnable
    mask := .unmasked
    interruptPending := false
    cleanup := .notStarted
    cleanupRuns := 0 }

def raceStart : MiniMachine :=
  { workerState := baseFiber
    waiterState := baseFiber
    trace := [] }

def ranWorker : MiniMachine :=
  { raceStart with
    workerState := { baseFiber with status := .running }
    trace := [.ran worker] }

def ranWaiter : MiniMachine :=
  { raceStart with
    waiterState := { baseFiber with status := .running }
    trace := [.ran waiter] }

inductive UntapedStep : MiniMachine -> MiniMachine -> Prop where
  | chooseWorker : UntapedStep raceStart ranWorker
  | chooseWaiter : UntapedStep raceStart ranWaiter

/- E4-CONC-CE-001: omitting the scheduler choice destroys determinism. -/
theorem untaped_race_counterexample :
    ∃ left right,
      UntapedStep raceStart left ∧
      UntapedStep raceStart right ∧
      left.trace ≠ right.trace := by
  exact ⟨ranWorker, ranWaiter, .chooseWorker, .chooseWaiter, by decide⟩

def interruptThenComplete : MiniMachine :=
  { raceStart with
    workerState :=
      { baseFiber with
        status := .finalizing .interrupted }
    trace :=
      [ .interruptRequested worker
      , .interruptDelivered worker
      ] }

def completeThenInterrupt : MiniMachine :=
  { raceStart with
    workerState :=
      { baseFiber with
        status := .finalizing .success }
    trace := [.completed worker .success] }

/-
E4-CONC-CE-002: interrupt and completion order is observable. In the repaired
policy, the first decision enters finalizing and the second decision refuses
without changing the machine. These two definitions are the stopped machines
for the two exact two-decision tapes.
-/
theorem interrupt_vs_complete_counterexample :
    interruptThenComplete.workerState.status ≠
      completeThenInterrupt.workerState.status ∧
    interruptThenComplete.trace ≠ completeThenInterrupt.trace := by
  decide

def maskedStart : MiniMachine :=
  { raceStart with
    workerState := { baseFiber with mask := .masked } }

def requestWhileMasked : MiniMachine :=
  { maskedStart with
    workerState :=
      { maskedStart.workerState with interruptPending := true }
    trace :=
      [ .interruptRequested worker
      , .interruptDeferred worker
      ] }

def deliverOnUnmask : MiniMachine :=
  { requestWhileMasked with
    workerState :=
      { requestWhileMasked.workerState with
        status := .finalizing .interrupted
        mask := .unmasked
        interruptPending := false }
    trace := requestWhileMasked.trace ++ [.interruptDelivered worker] }

/- E4-CONC-CE-003: a masked request is pending, not a terminal result. -/
theorem masked_interruption_counterexample :
    requestWhileMasked.workerState.status = .runnable ∧
    requestWhileMasked.workerState.interruptPending = true ∧
    deliverOnUnmask.workerState.status = .finalizing .interrupted ∧
    deliverOnUnmask.workerState.interruptPending = false := by
  decide

def cleanupLost : MiniMachine :=
  { raceStart with
    workerState :=
      { baseFiber with
        status := .done .interrupted
        cleanup := .notStarted
        cleanupRuns := 0 }
    trace := [.completed worker .interrupted] }

def cleanupRetained : MiniMachine :=
  { raceStart with
    workerState :=
      { baseFiber with
        status := .done .interrupted
        cleanup := .done
        cleanupRuns := 1 }
    trace := [.completed worker .interrupted, .cleanup worker] }

def eraseToTerminal (machine : MiniMachine) : Option Terminal :=
  match machine.workerState.status with
  | .done result => some result
  | _ => none

theorem lost_finalizer_same_projection :
    eraseToTerminal cleanupLost = eraseToTerminal cleanupRetained := rfl

theorem lost_finalizer_count_differs :
    cleanupLost.workerState.cleanupRuns ≠
      cleanupRetained.workerState.cleanupRuns := by
  decide

theorem lost_finalizer_trace_differs :
    cleanupLost.trace ≠ cleanupRetained.trace := by
  decide

/-
E4-CONC-CE-004: projecting only the terminal error erases cleanup history.
The repaired carrier must retain operational state and trace outside the
terminal outcome.
-/
theorem lost_finalizer_counterexample :
    eraseToTerminal cleanupLost = eraseToTerminal cleanupRetained ∧
    cleanupLost.workerState.cleanupRuns ≠
      cleanupRetained.workerState.cleanupRuns ∧
    cleanupLost.trace ≠ cleanupRetained.trace := by
  exact
    ⟨lost_finalizer_same_projection,
     lost_finalizer_count_differs,
     lost_finalizer_trace_differs⟩

def joinedReady : MiniMachine :=
  { raceStart with
    workerState :=
      { baseFiber with
        status := .done .success
        cleanup := .done
        cleanupRuns := 1 }
    waiterState := { baseFiber with status := .waiting worker }
    trace := [.completed worker .success, .cleanup worker] }

def observeJoin (machine : MiniMachine) : Option Terminal × MiniMachine :=
  match machine.workerState.status with
  | .done result =>
      (some result,
       { machine with
         trace := machine.trace ++ [.joined waiter worker result] })
  | _ => (none, machine)

def firstJoin := observeJoin joinedReady
def secondJoin := observeJoin firstJoin.2

theorem first_join_result : firstJoin.1 = some .success := rfl
theorem second_join_result : secondJoin.1 = firstJoin.1 := rfl
theorem first_join_cleanup_count :
    firstJoin.2.workerState.cleanupRuns = 1 := rfl
theorem second_join_cleanup_count :
    secondJoin.2.workerState.cleanupRuns = 1 := rfl

/- E4-CONC-CE-005: join is a repeatable observation, not cleanup execution. -/
theorem double_join_counterexample :
    firstJoin.1 = some .success ∧
    secondJoin.1 = firstJoin.1 ∧
    firstJoin.2.workerState.cleanupRuns = 1 ∧
    secondJoin.2.workerState.cleanupRuns = 1 := by
  exact
    ⟨first_join_result,
     second_join_result,
     first_join_cleanup_count,
     second_join_cleanup_count⟩

/-!
E4-CONC-CE-007: a cleanup counter bounded by one does not constrain the
observable trace. This is the smallest raw state accepted by count-only
admission while recording the same cleanup twice.
-/

def duplicateCleanupTrace : MiniMachine :=
  { raceStart with
    workerState :=
      { baseFiber with
        status := .done .success
        cleanup := .done
        cleanupRuns := 1 }
    trace := [.cleanup worker, .cleanup worker] }

def cleanupEventId? : Event -> Option FiberId
  | .cleanup id => some id
  | _ => none

def cleanupEventIds (machine : MiniMachine) : List FiberId :=
  machine.trace.filterMap cleanupEventId?

def Status.active : Status -> Bool
  | .runnable | .running | .waiting _ => true
  | .finalizing _ | .done _ => false

def PreRepairFiberAdmitted (fiber : MiniFiber) : Bool :=
  decide (fiber.cleanupRuns <= 1) &&
  (match fiber.status with
    | .runnable | .running | .waiting _ =>
        decide (fiber.cleanup = .notStarted) && decide (fiber.cleanupRuns = 0)
    | .finalizing _ =>
        decide (fiber.cleanup = .pending) && decide (fiber.cleanupRuns = 0)
    | .done _ =>
        decide (fiber.cleanup = .done) && decide (fiber.cleanupRuns = 1)) &&
  (!fiber.interruptPending ||
    (decide (fiber.mask = .masked) && fiber.status.active))

def waitingTargetClosed : Status -> Bool
  | .waiting target => decide (target = worker \/ target = waiter)
  | _ => true

/-- The six pre-repair admission fields, specialized to two fixed unique IDs. -/
def PreRepairWellFormed (machine : MiniMachine) : Bool :=
  PreRepairFiberAdmitted machine.workerState &&
  PreRepairFiberAdmitted machine.waiterState &&
  waitingTargetClosed machine.workerState.status &&
  waitingTargetClosed machine.waiterState.status

theorem duplicate_cleanup_trace_counterexample :
    PreRepairWellFormed duplicateCleanupTrace = true /\
    cleanupEventIds duplicateCleanupTrace = [worker, worker] /\
    ¬ (cleanupEventIds duplicateCleanupTrace).Nodup := by
  decide

theorem terminal_alphabet_receipt (result : Terminal) :
    result = .success ∨ result = .failure ∨ result = .defect ∨
      result = .interrupted := by
  cases result with
  | success => exact Or.inl rfl
  | failure => exact Or.inr (Or.inl rfl)
  | defect => exact Or.inr (Or.inr (Or.inl rfl))
  | interrupted => exact Or.inr (Or.inr (Or.inr rfl))

/-!
E4-CONC-CE-006: implication-only operational laws are vacuous when both
relations are empty. The postconditions below are arbitrary, so this witness
covers every old one-step, two-step, and run law whose only operational
evidence is a `Step` or `Runs` premise.
-/

inductive MiniDecision where
  | schedule (id : FiberId)

inductive MiniStepResult where
  | advanced (machine : MiniMachine)

inductive MiniReplayResult where
  | finished (machine : MiniMachine)

def EmptyStep (_ : MiniMachine) (_ : MiniDecision)
    (_ : MiniStepResult) : Prop := False

def EmptyRuns (_ : MiniMachine) (_ : List MiniDecision)
    (_ : MiniReplayResult) : Prop := False

structure ImplicationOnlySpine
    (Step : MiniMachine -> MiniDecision -> MiniStepResult -> Prop)
    (Runs : MiniMachine -> List MiniDecision -> MiniReplayResult -> Prop)
    (stepPost : MiniMachine -> MiniDecision -> MiniStepResult -> Prop)
    (twoStepPost :
      MiniMachine -> MiniDecision -> MiniStepResult ->
      MiniDecision -> MiniStepResult -> Prop)
    (runsPost : MiniMachine -> List MiniDecision -> MiniReplayResult -> Prop) :
    Prop where
  stepDeterministic : forall {before decision left right},
    Step before decision left -> Step before decision right -> left = right
  fixedTapeDeterministic : forall {initial tape left right},
    Runs initial tape left -> Runs initial tape right -> left = right
  oneStepLaws : forall {before decision result},
    Step before decision result -> stepPost before decision result
  twoStepLaws : forall {before firstDecision firstResult secondDecision secondResult},
    Step before firstDecision firstResult ->
    Step before secondDecision secondResult ->
    twoStepPost before firstDecision firstResult secondDecision secondResult
  runLaws : forall {initial tape result},
    Runs initial tape result -> runsPost initial tape result

theorem empty_relations_satisfy_every_implication_only_spine
    (stepPost : MiniMachine -> MiniDecision -> MiniStepResult -> Prop)
    (twoStepPost :
      MiniMachine -> MiniDecision -> MiniStepResult ->
      MiniDecision -> MiniStepResult -> Prop)
    (runsPost : MiniMachine -> List MiniDecision -> MiniReplayResult -> Prop) :
    ImplicationOnlySpine EmptyStep EmptyRuns stepPost twoStepPost runsPost := by
  constructor
  · intro before decision left right empty
    exact empty.elim
  · intro initial tape left right empty
    exact empty.elim
  · intro before decision result empty
    exact empty.elim
  · intro before firstDecision firstResult secondDecision secondResult empty
    exact empty.elim
  · intro initial tape result empty
    exact empty.elim

#print axioms untaped_race_counterexample
#print axioms interrupt_vs_complete_counterexample
#print axioms masked_interruption_counterexample
#print axioms lost_finalizer_same_projection
#print axioms lost_finalizer_count_differs
#print axioms lost_finalizer_trace_differs
#print axioms lost_finalizer_counterexample
#print axioms first_join_result
#print axioms second_join_result
#print axioms first_join_cleanup_count
#print axioms second_join_cleanup_count
#print axioms double_join_counterexample
#print axioms duplicate_cleanup_trace_counterexample
#print axioms terminal_alphabet_receipt
#print axioms empty_relations_satisfy_every_implication_only_spine

end Effect4Test.Counterexamples.Concurrency.FiberRepresentative
