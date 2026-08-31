/-
Contract packet: `test/contracts/fiber-representative.contract.md`

Breaker-owned red battery. The implementation phase must not edit this file.
It is red until the Fiber/scheduler/interruption representative exists.
-/

import Effect4.Concurrency.Fiber
import Effect4.Concurrency.Interrupt
import Effect4.Concurrency.Scheduler

namespace Effect4
end Effect4

namespace Effect4Test.Concurrency.FiberRepresentativeContract

open Effect4

universe u

section SurfaceSnapshot

/-! D0: nominal identity and passive finite alphabets. -/

#check (@FiberId : Type)
#check (@FiberId.mk : Nat -> FiberId)
#check (@FiberId.value : FiberId -> Nat)
#synth DecidableEq FiberId
#synth Repr FiberId

#check (@FiberStatus.runnable : FiberStatus)
#check (@FiberStatus.running : FiberStatus)
#check (@FiberStatus.waiting : FiberId -> FiberStatus)
#check (@FiberStatus.finalizing : FiberStatus)
#check (@FiberStatus.done : FiberStatus)
#check (@FiberStatus.Active : FiberStatus -> Prop)
#check (@FiberStatus.active_iff : forall status,
  FiberStatus.Active status <->
    status = FiberStatus.runnable \/
    status = FiberStatus.running \/
    exists target, status = FiberStatus.waiting target)
#check (@FiberStatus.activeDecidable : forall status,
  Decidable (FiberStatus.Active status))
#synth DecidableEq FiberStatus
#synth Repr FiberStatus

#check (@InterruptMask.unmasked : InterruptMask)
#check (@InterruptMask.masked : InterruptMask)
#synth DecidableEq InterruptMask
#synth Repr InterruptMask

#check (@CleanupState.notStarted : CleanupState)
#check (@CleanupState.pending : CleanupState)
#check (@CleanupState.done : CleanupState)
#synth DecidableEq CleanupState
#synth Repr CleanupState

#check (@SchedulerRefusal.unknownFiber : FiberId -> SchedulerRefusal)
#check (@SchedulerRefusal.invalidLifecycle : FiberId -> SchedulerRefusal)
#synth DecidableEq SchedulerRefusal
#synth Repr SchedulerRefusal

#check (@InterruptBoundary : Type u -> Type u)
#check (@InterruptBoundary.mk : forall {τ : Type u}, τ -> InterruptBoundary τ)
#check (@InterruptBoundary.interrupted :
  forall {τ : Type u}, InterruptBoundary τ -> τ)

/-! D1: state with cleanup information outside terminal outcomes. -/

#check (@FiberState : Type u -> Type u)
#check (@FiberState.mk : forall {τ : Type u},
  FiberId -> FiberStatus -> Option τ -> InterruptMask -> Bool ->
    CleanupState -> Nat -> FiberState τ)
#check (@FiberState.id : forall {τ : Type u}, FiberState τ -> FiberId)
#check (@FiberState.status : forall {τ : Type u}, FiberState τ -> FiberStatus)
#check (@FiberState.terminal : forall {τ : Type u}, FiberState τ -> Option τ)
#check (@FiberState.mask : forall {τ : Type u}, FiberState τ -> InterruptMask)
#check (@FiberState.interruptPending : forall {τ : Type u}, FiberState τ -> Bool)
#check (@FiberState.cleanup : forall {τ : Type u}, FiberState τ -> CleanupState)
#check (@FiberState.cleanupCount : forall {τ : Type u}, FiberState τ -> Nat)

/-! D2: explicit scheduler decisions and observable events. -/

#check (@SchedulerDecision : Type u -> Type u)
#check (@SchedulerDecision.schedule :
  forall {τ : Type u}, FiberId -> SchedulerDecision τ)
#check (@SchedulerDecision.join :
  forall {τ : Type u}, FiberId -> FiberId -> SchedulerDecision τ)
#check (@SchedulerDecision.requestInterrupt :
  forall {τ : Type u}, FiberId -> FiberId -> SchedulerDecision τ)
#check (@SchedulerDecision.enterMask :
  forall {τ : Type u}, FiberId -> SchedulerDecision τ)
#check (@SchedulerDecision.exitMask :
  forall {τ : Type u}, FiberId -> SchedulerDecision τ)
#check (@SchedulerDecision.complete :
  forall {τ : Type u}, FiberId -> τ -> SchedulerDecision τ)
#check (@SchedulerDecision.cleanup :
  forall {τ : Type u}, FiberId -> SchedulerDecision τ)
#check (@DecisionTape : Type u -> Type u)
example (τ : Type u) : DecisionTape τ = List (SchedulerDecision τ) := rfl

#check (@Event : Type u -> Type u)
#check (@Event.scheduled : forall {τ : Type u}, FiberId -> Event τ)
#check (@Event.joinWaiting :
  forall {τ : Type u}, FiberId -> FiberId -> Event τ)
#check (@Event.joinObserved :
  forall {τ : Type u}, FiberId -> FiberId -> τ -> Event τ)
#check (@Event.interruptRequested :
  forall {τ : Type u}, FiberId -> FiberId -> Event τ)
#check (@Event.interruptDeferred : forall {τ : Type u}, FiberId -> Event τ)
#check (@Event.interruptDelivered : forall {τ : Type u}, FiberId -> Event τ)
#check (@Event.maskEntered : forall {τ : Type u}, FiberId -> Event τ)
#check (@Event.maskExited : forall {τ : Type u}, FiberId -> Event τ)
#check (@Event.completed : forall {τ : Type u}, FiberId -> τ -> Event τ)
#check (@Event.cleanupFinished : forall {τ : Type u}, FiberId -> Event τ)
#check (@Event.cleanupId? : forall {τ : Type u}, Event τ -> Option FiberId)
#check (@Event.cleanupId_eq_some : forall {τ : Type u}
    (event : Event τ) (id : FiberId),
  Event.cleanupId? event = some id <-> event = Event.cleanupFinished id)
#check (@Trace : Type u -> Type u)
example (τ : Type u) : Trace τ = List (Event τ) := rfl

#check (@Machine : Type u -> Type u)
#check (@Machine.mk : forall {τ : Type u},
  List (FiberState τ) -> Trace τ -> Machine τ)
#check (@Machine.fibers : forall {τ : Type u},
  Machine τ -> List (FiberState τ))
#check (@Machine.trace : forall {τ : Type u}, Machine τ -> Trace τ)
#check (@Machine.fiber : forall {τ : Type u},
  Machine τ -> FiberId -> Option (FiberState τ))
#check (@Machine.terminal : forall {τ : Type u},
  Machine τ -> FiberId -> Option τ)
#check (@Machine.mask : forall {τ : Type u},
  Machine τ -> FiberId -> Option InterruptMask)
#check (@Machine.interruptPending : forall {τ : Type u},
  Machine τ -> FiberId -> Option Bool)
#check (@Machine.cleanupState : forall {τ : Type u},
  Machine τ -> FiberId -> Option CleanupState)
#check (@Machine.cleanupCount : forall {τ : Type u},
  Machine τ -> FiberId -> Nat)
#check (@Machine.cleanupEventIds : forall {τ : Type u},
  Machine τ -> List FiberId)
#check (@Machine.fiber_eq_find : forall {τ : Type u}
    (machine : Machine τ) (id : FiberId),
  machine.fiber id =
    machine.fibers.find? (fun fiber => fiber.id = id))
#check (@Machine.terminal_eq : forall {τ : Type u}
    (machine : Machine τ) (id : FiberId),
  machine.terminal id = (machine.fiber id).bind FiberState.terminal)
#check (@Machine.mask_eq : forall {τ : Type u}
    (machine : Machine τ) (id : FiberId),
  machine.mask id = (machine.fiber id).map FiberState.mask)
#check (@Machine.interruptPending_eq :
  forall {τ : Type u} (machine : Machine τ) (id : FiberId),
    machine.interruptPending id =
      (machine.fiber id).map FiberState.interruptPending)
#check (@Machine.cleanupState_eq : forall {τ : Type u}
    (machine : Machine τ) (id : FiberId),
  machine.cleanupState id = (machine.fiber id).map FiberState.cleanup)
#check (@Machine.cleanupCount_eq : forall {τ : Type u}
    (machine : Machine τ) (id : FiberId),
  machine.cleanupCount id =
    ((machine.fiber id).map FiberState.cleanupCount).getD 0)
#check (@Machine.cleanupEventIds_eq : forall {τ : Type u}
    (machine : Machine τ),
  machine.cleanupEventIds = machine.trace.filterMap Event.cleanupId?)
#check (@Machine.transition : forall {τ : Type u},
  Machine τ -> FiberState τ -> List (Event τ) -> Machine τ)
#check (@Machine.transition_fibers : forall {τ : Type u}
    (before : Machine τ) (replacement : FiberState τ)
    (events : List (Event τ)),
    (Machine.transition before replacement events).fibers =
      before.fibers.map (fun current =>
        if current.id = replacement.id then replacement else current))
#check (@Machine.transition_trace : forall {τ : Type u}
    (before : Machine τ) (replacement : FiberState τ)
    (events : List (Event τ)),
    (Machine.transition before replacement events).trace =
      before.trace ++ events)
#check (@Machine.transition_cleanupEventIds : forall {τ : Type u}
    (before : Machine τ) (replacement : FiberState τ)
    (events : List (Event τ)),
  (Machine.transition before replacement events).cleanupEventIds =
    before.cleanupEventIds ++ events.filterMap Event.cleanupId?)
#check (@Machine.transition_fiber_other : forall {τ : Type u}
    (before : Machine τ) (replacement : FiberState τ)
    (events : List (Event τ)) (id : FiberId),
  replacement.id ≠ id ->
    (Machine.transition before replacement events).fiber id = before.fiber id)

#check (@Machine.WellFormed : forall {τ : Type u}, Machine τ -> Prop)
#check (@Machine.WellFormed.mk : forall {τ : Type u} {machine : Machine τ},
  (machine.fibers.map FiberState.id).Nodup ->
  (forall fiber, fiber ∈ machine.fibers -> fiber.cleanupCount <= 1) ->
  machine.cleanupEventIds.Nodup ->
  (forall id, id ∈ machine.cleanupEventIds ->
    exists fiber, fiber ∈ machine.fibers /\ fiber.id = id) ->
  (forall fiber, fiber ∈ machine.fibers ->
    (fiber.id ∈ machine.cleanupEventIds <-> fiber.cleanupCount = 1)) ->
  (forall fiber, fiber ∈ machine.fibers -> FiberStatus.Active fiber.status ->
    fiber.terminal = none /\ fiber.cleanup = CleanupState.notStarted /\
      fiber.cleanupCount = 0) ->
  (forall fiber, fiber ∈ machine.fibers ->
    fiber.status = FiberStatus.finalizing ->
    (exists result, fiber.terminal = some result) /\
      fiber.cleanup = CleanupState.pending /\ fiber.cleanupCount = 0) ->
  (forall fiber, fiber ∈ machine.fibers ->
    fiber.status = FiberStatus.done ->
    (exists result, fiber.terminal = some result) /\
      fiber.cleanup = CleanupState.done /\ fiber.cleanupCount = 1) ->
  (forall fiber, fiber ∈ machine.fibers -> fiber.interruptPending = true ->
    fiber.mask = InterruptMask.masked /\ FiberStatus.Active fiber.status) ->
  (forall fiber target, fiber ∈ machine.fibers ->
    fiber.status = FiberStatus.waiting target ->
    exists targetFiber, targetFiber ∈ machine.fibers /\
      targetFiber.id = target) ->
  Machine.WellFormed machine)
#check (@Machine.WellFormed.idsUnique :
  forall {τ : Type u} {machine : Machine τ},
  Machine.WellFormed machine ->
    (machine.fibers.map FiberState.id).Nodup)
#check (@Machine.WellFormed.cleanupBounded :
  forall {τ : Type u} {machine : Machine τ},
  Machine.WellFormed machine -> forall fiber, fiber ∈ machine.fibers ->
    fiber.cleanupCount <= 1)
#check (@Machine.WellFormed.cleanupEventsUnique :
  forall {τ : Type u} {machine : Machine τ},
  Machine.WellFormed machine -> machine.cleanupEventIds.Nodup)
#check (@Machine.WellFormed.cleanupEventsClosed :
  forall {τ : Type u} {machine : Machine τ},
  Machine.WellFormed machine -> forall id,
    id ∈ machine.cleanupEventIds ->
      exists fiber, fiber ∈ machine.fibers /\ fiber.id = id)
#check (@Machine.WellFormed.cleanupEventAgreement :
  forall {τ : Type u} {machine : Machine τ},
  Machine.WellFormed machine -> forall fiber,
    fiber ∈ machine.fibers ->
      (fiber.id ∈ machine.cleanupEventIds <-> fiber.cleanupCount = 1))
#check (@Machine.WellFormed.activeCleanup :
  forall {τ : Type u} {machine : Machine τ},
  Machine.WellFormed machine -> forall fiber,
    fiber ∈ machine.fibers -> FiberStatus.Active fiber.status ->
    fiber.terminal = none /\ fiber.cleanup = CleanupState.notStarted /\
      fiber.cleanupCount = 0)
#check (@Machine.WellFormed.finalizingCleanup :
  forall {τ : Type u} {machine : Machine τ},
  Machine.WellFormed machine -> forall fiber,
    fiber ∈ machine.fibers -> fiber.status = FiberStatus.finalizing ->
    (exists result, fiber.terminal = some result) /\
      fiber.cleanup = CleanupState.pending /\ fiber.cleanupCount = 0)
#check (@Machine.WellFormed.doneCleanup :
  forall {τ : Type u} {machine : Machine τ},
  Machine.WellFormed machine -> forall fiber,
    fiber ∈ machine.fibers -> fiber.status = FiberStatus.done ->
    (exists result, fiber.terminal = some result) /\
      fiber.cleanup = CleanupState.done /\ fiber.cleanupCount = 1)
#check (@Machine.WellFormed.pendingActive :
  forall {τ : Type u} {machine : Machine τ},
  Machine.WellFormed machine -> forall fiber,
    fiber ∈ machine.fibers -> fiber.interruptPending = true ->
    fiber.mask = InterruptMask.masked /\ FiberStatus.Active fiber.status)
#check (@Machine.WellFormed.waitingClosed :
  forall {τ : Type u} {machine : Machine τ},
  Machine.WellFormed machine -> forall fiber target,
    fiber ∈ machine.fibers -> fiber.status = FiberStatus.waiting target ->
    exists targetFiber, targetFiber ∈ machine.fibers /\
      targetFiber.id = target)
#check (@Machine.wellFormedDecidable : forall {τ : Type u}
    [DecidableEq τ] (machine : Machine τ),
  Decidable (Machine.WellFormed machine))

#check (@Machine.Finished : forall {τ : Type u}, Machine τ -> Prop)
#check (@Machine.finished_iff : forall {τ : Type u} (machine : Machine τ),
  Machine.Finished machine <->
    forall fiber, fiber ∈ machine.fibers -> fiber.status = FiberStatus.done)

/-! D3: one-decision and finite-tape relational semantics. -/

#check (@StepResult : Type u -> Type u)
#check (@StepResult.advanced : forall {τ : Type u}, Machine τ -> StepResult τ)
#check (@StepResult.refused : forall {τ : Type u},
  SchedulerRefusal -> Machine τ -> StepResult τ)
#check (@StepResult.machine : forall {τ : Type u}, StepResult τ -> Machine τ)
#check (@StepResult.machine_advanced : forall {τ : Type u} (machine : Machine τ),
  (StepResult.advanced machine).machine = machine)
#check (@StepResult.machine_refused : forall {τ : Type u}
    (refusal : SchedulerRefusal) (machine : Machine τ),
  (StepResult.refused refusal machine).machine = machine)
#check (@ReplayResult : Type u -> Type u)
#check (@ReplayResult.finished : forall {τ : Type u}, Machine τ -> ReplayResult τ)
#check (@ReplayResult.refused : forall {τ : Type u},
  SchedulerRefusal -> Machine τ -> ReplayResult τ)
#check (@ReplayResult.frontier : forall {τ : Type u}, Machine τ -> ReplayResult τ)
#check (@ReplayResult.machine : forall {τ : Type u}, ReplayResult τ -> Machine τ)
#check (@ReplayResult.machine_finished : forall {τ : Type u} (machine : Machine τ),
  (ReplayResult.finished machine).machine = machine)
#check (@ReplayResult.machine_refused : forall {τ : Type u}
    (refusal : SchedulerRefusal) (machine : Machine τ),
  (ReplayResult.refused refusal machine).machine = machine)
#check (@ReplayResult.machine_frontier : forall {τ : Type u} (machine : Machine τ),
  (ReplayResult.frontier machine).machine = machine)
#check (@Step : forall {τ : Type u}, InterruptBoundary τ ->
  Machine τ -> SchedulerDecision τ -> StepResult τ -> Prop)
#check (@Runs : forall {τ : Type u}, InterruptBoundary τ ->
  Machine τ -> DecisionTape τ -> ReplayResult τ -> Prop)
#check (@stepEval : forall {τ : Type u}, InterruptBoundary τ ->
  Machine τ -> SchedulerDecision τ -> StepResult τ)
#check (@step_iff : forall {τ : Type u} {boundary : InterruptBoundary τ}
    {before decision result},
  Step boundary before decision result <->
    result = stepEval boundary before decision)

end SurfaceSnapshot

section PassiveReceipts

#check (@FiberStatus.cases_receipt : forall status,
  status = FiberStatus.runnable \/
  status = FiberStatus.running \/
  (exists target, status = FiberStatus.waiting target) \/
  status = FiberStatus.finalizing \/
  status = FiberStatus.done)

#check (@InterruptMask.cases_receipt : forall mask,
  mask = InterruptMask.unmasked \/ mask = InterruptMask.masked)

#check (@CleanupState.cases_receipt : forall cleanup,
  cleanup = CleanupState.notStarted \/
  cleanup = CleanupState.pending \/
  cleanup = CleanupState.done)

#check (@SchedulerRefusal.cases_receipt : forall refusal,
  (exists id, refusal = SchedulerRefusal.unknownFiber id) \/
  (exists id, refusal = SchedulerRefusal.invalidLifecycle id))

#check (@SchedulerDecision.cases_receipt : forall {τ : Type u}
    (decision : SchedulerDecision τ),
  (exists id, decision = SchedulerDecision.schedule id) \/
  (exists waiter target, decision = SchedulerDecision.join waiter target) \/
  (exists requester target,
    decision = SchedulerDecision.requestInterrupt requester target) \/
  (exists id, decision = SchedulerDecision.enterMask id) \/
  (exists id, decision = SchedulerDecision.exitMask id) \/
  (exists id result, decision = SchedulerDecision.complete id result) \/
  (exists id, decision = SchedulerDecision.cleanup id))

#check (@Event.cases_receipt : forall {τ : Type u} (event : Event τ),
  (exists id, event = Event.scheduled id) \/
  (exists waiter target, event = Event.joinWaiting waiter target) \/
  (exists waiter target result,
    event = Event.joinObserved waiter target result) \/
  (exists requester target,
    event = Event.interruptRequested requester target) \/
  (exists target, event = Event.interruptDeferred target) \/
  (exists target, event = Event.interruptDelivered target) \/
  (exists id, event = Event.maskEntered id) \/
  (exists id, event = Event.maskExited id) \/
  (exists id result, event = Event.completed id result) \/
  (exists id, event = Event.cleanupFinished id))

#print axioms FiberStatus.cases_receipt
#print axioms InterruptMask.cases_receipt
#print axioms CleanupState.cases_receipt
#print axioms SchedulerRefusal.cases_receipt
#print axioms SchedulerDecision.cases_receipt
#print axioms Event.cases_receipt

end PassiveReceipts

section OperationalLaws

#check (@step_deterministic : forall {τ : Type u}
    {boundary : InterruptBoundary τ} {before decision left right},
  Step boundary before decision left ->
  Step boundary before decision right -> left = right)

#check (@fixedTape_deterministic : forall {τ : Type u}
    {boundary : InterruptBoundary τ} {initial tape left right},
  Runs boundary initial tape left -> Runs boundary initial tape right ->
    left = right)

#check (@step_preserves_wellFormed : forall {τ : Type u}
    {boundary : InterruptBoundary τ} {before decision result},
  Machine.WellFormed before -> Step boundary before decision result ->
    Machine.WellFormed result.machine)

#check (@runs_preserves_wellFormed : forall {τ : Type u}
    {boundary : InterruptBoundary τ} {initial tape result},
  Machine.WellFormed initial -> Runs boundary initial tape result ->
    Machine.WellFormed result.machine)

#check (@finite_replay_total : forall {τ : Type u}
    (boundary : InterruptBoundary τ) {initial tape},
  Machine.WellFormed initial ->
    exists result, Runs boundary initial tape result)

#check (@step_total : forall {τ : Type u}
    (boundary : InterruptBoundary τ) {before decision},
  Machine.WellFormed before ->
    exists result, Step boundary before decision result)

/-! Exact deterministic decision clauses and chronological trace deltas. -/

#check (@stepEval_schedule_missing : forall {τ : Type u}
    {boundary : InterruptBoundary τ} {before id},
  before.fiber id = none ->
  stepEval boundary before (SchedulerDecision.schedule id) =
    StepResult.refused (SchedulerRefusal.unknownFiber id) before)

#check (@stepEval_schedule_runnable : forall {τ : Type u}
    {boundary : InterruptBoundary τ} {before id fiber},
  before.fiber id = some fiber -> fiber.status = FiberStatus.runnable ->
  stepEval boundary before (SchedulerDecision.schedule id) =
    StepResult.advanced
      (Machine.transition before
        { fiber with status := FiberStatus.running }
        [Event.scheduled id]))

#check (@stepEval_schedule_invalid : forall {τ : Type u}
    {boundary : InterruptBoundary τ} {before id fiber},
  before.fiber id = some fiber -> fiber.status ≠ FiberStatus.runnable ->
  stepEval boundary before (SchedulerDecision.schedule id) =
    StepResult.refused (SchedulerRefusal.invalidLifecycle id) before)

#check (@stepEval_join_missing_waiter : forall {τ : Type u}
    {boundary : InterruptBoundary τ} {before waiter target},
  before.fiber waiter = none ->
  stepEval boundary before (SchedulerDecision.join waiter target) =
    StepResult.refused (SchedulerRefusal.unknownFiber waiter) before)

#check (@stepEval_join_missing_target :
  forall {τ : Type u} {boundary : InterruptBoundary τ}
      {before waiter target waiterState},
    before.fiber waiter = some waiterState -> before.fiber target = none ->
    stepEval boundary before (SchedulerDecision.join waiter target) =
      StepResult.refused (SchedulerRefusal.unknownFiber target) before)

#check (@stepEval_join_done :
  forall {τ : Type u} {boundary : InterruptBoundary τ}
      {before waiter target waiterState targetState result},
    before.fiber waiter = some waiterState ->
    before.fiber target = some targetState ->
    waiter ≠ target ->
    (waiterState.status = FiberStatus.running \/
      waiterState.status = FiberStatus.waiting target) ->
    targetState.status = FiberStatus.done ->
    before.terminal target = some result ->
    stepEval boundary before (SchedulerDecision.join waiter target) =
      StepResult.advanced
        (Machine.transition before
          { waiterState with status := FiberStatus.running }
          [Event.joinObserved waiter target result]))

#check (@stepEval_join_done_missing_terminal :
  forall {τ : Type u} {boundary : InterruptBoundary τ}
      {before waiter target waiterState targetState},
    before.fiber waiter = some waiterState ->
    before.fiber target = some targetState ->
    waiter ≠ target ->
    targetState.status = FiberStatus.done ->
    before.terminal target = none ->
    stepEval boundary before (SchedulerDecision.join waiter target) =
      StepResult.refused (SchedulerRefusal.invalidLifecycle target) before)

#check (@stepEval_join_waiting :
  forall {τ : Type u} {boundary : InterruptBoundary τ}
      {before waiter target waiterState targetState},
    before.fiber waiter = some waiterState ->
    before.fiber target = some targetState ->
    waiter ≠ target ->
    targetState.status ≠ FiberStatus.done ->
    waiterState.status = FiberStatus.running ->
    stepEval boundary before (SchedulerDecision.join waiter target) =
      StepResult.advanced
        (Machine.transition before
          { waiterState with status := FiberStatus.waiting target }
          [Event.joinWaiting waiter target]))

#check (@stepEval_join_invalid :
  forall {τ : Type u} {boundary : InterruptBoundary τ}
      {before waiter target waiterState targetState},
    before.fiber waiter = some waiterState ->
    before.fiber target = some targetState ->
    waiter ≠ target ->
    targetState.status ≠ FiberStatus.done ->
    waiterState.status ≠ FiberStatus.running ->
    stepEval boundary before (SchedulerDecision.join waiter target) =
      StepResult.refused (SchedulerRefusal.invalidLifecycle waiter) before)

#check (@stepEval_join_done_invalid :
  forall {τ : Type u} {boundary : InterruptBoundary τ}
      {before waiter target waiterState targetState result},
    before.fiber waiter = some waiterState ->
    before.fiber target = some targetState ->
    waiter ≠ target ->
    targetState.status = FiberStatus.done ->
    before.terminal target = some result ->
    waiterState.status ≠ FiberStatus.running ->
    waiterState.status ≠ FiberStatus.waiting target ->
    stepEval boundary before (SchedulerDecision.join waiter target) =
      StepResult.refused (SchedulerRefusal.invalidLifecycle waiter) before)

#check (@stepEval_join_self_invalid : forall {τ : Type u}
    {boundary : InterruptBoundary τ} {before id fiber},
  before.fiber id = some fiber ->
  stepEval boundary before (SchedulerDecision.join id id) =
    StepResult.refused (SchedulerRefusal.invalidLifecycle id) before)

#check (@stepEval_interrupt_missing_requester :
  forall {τ : Type u} {boundary : InterruptBoundary τ}
      {before requester target}, before.fiber requester = none ->
    stepEval boundary before
        (SchedulerDecision.requestInterrupt requester target) =
      StepResult.refused (SchedulerRefusal.unknownFiber requester) before)

#check (@stepEval_interrupt_missing_target :
  forall {τ : Type u} {boundary : InterruptBoundary τ}
      {before requester target requesterState},
    before.fiber requester = some requesterState -> before.fiber target = none ->
    stepEval boundary before
        (SchedulerDecision.requestInterrupt requester target) =
      StepResult.refused (SchedulerRefusal.unknownFiber target) before)

#check (@stepEval_interrupt_masked :
  forall {τ : Type u} {boundary : InterruptBoundary τ}
      {before requester target requesterState targetState},
    before.fiber requester = some requesterState ->
    before.fiber target = some targetState ->
    FiberStatus.Active targetState.status ->
    targetState.mask = InterruptMask.masked ->
    stepEval boundary before
        (SchedulerDecision.requestInterrupt requester target) =
      StepResult.advanced
        (Machine.transition before
          { targetState with interruptPending := true }
          [ Event.interruptRequested requester target
          , Event.interruptDeferred target ]))

#check (@stepEval_interrupt_unmasked :
  forall {τ : Type u} {boundary : InterruptBoundary τ}
      {before requester target requesterState targetState},
    before.fiber requester = some requesterState ->
    before.fiber target = some targetState ->
    FiberStatus.Active targetState.status ->
    targetState.mask = InterruptMask.unmasked ->
    stepEval boundary before
        (SchedulerDecision.requestInterrupt requester target) =
      StepResult.advanced
        (Machine.transition before
          { targetState with
            status := FiberStatus.finalizing
            terminal := some boundary.interrupted
            interruptPending := false
            cleanup := CleanupState.pending
            cleanupCount := 0 }
          [ Event.interruptRequested requester target
          , Event.interruptDelivered target ]))

#check (@stepEval_interrupt_invalid :
  forall {τ : Type u} {boundary : InterruptBoundary τ}
      {before requester target requesterState targetState},
    before.fiber requester = some requesterState ->
    before.fiber target = some targetState ->
    Not (FiberStatus.Active targetState.status) ->
    stepEval boundary before
        (SchedulerDecision.requestInterrupt requester target) =
      StepResult.refused (SchedulerRefusal.invalidLifecycle target) before)

#check (@stepEval_enterMask_missing : forall {τ : Type u}
    {boundary : InterruptBoundary τ} {before id},
  before.fiber id = none ->
  stepEval boundary before (SchedulerDecision.enterMask id) =
    StepResult.refused (SchedulerRefusal.unknownFiber id) before)

#check (@stepEval_enterMask : forall {τ : Type u}
    {boundary : InterruptBoundary τ} {before id fiber},
  before.fiber id = some fiber -> FiberStatus.Active fiber.status ->
  fiber.mask = InterruptMask.unmasked ->
  stepEval boundary before (SchedulerDecision.enterMask id) =
    StepResult.advanced
      (Machine.transition before
        { fiber with mask := InterruptMask.masked }
        [Event.maskEntered id]))

#check (@stepEval_enterMask_invalid : forall {τ : Type u}
    {boundary : InterruptBoundary τ} {before id fiber},
  before.fiber id = some fiber -> FiberStatus.Active fiber.status ->
  fiber.mask = InterruptMask.masked ->
  stepEval boundary before (SchedulerDecision.enterMask id) =
    StepResult.refused (SchedulerRefusal.invalidLifecycle id) before)

#check (@stepEval_enterMask_inactive : forall {τ : Type u}
    {boundary : InterruptBoundary τ} {before id fiber},
  before.fiber id = some fiber -> Not (FiberStatus.Active fiber.status) ->
  stepEval boundary before (SchedulerDecision.enterMask id) =
    StepResult.refused (SchedulerRefusal.invalidLifecycle id) before)

#check (@stepEval_exitMask_missing : forall {τ : Type u}
    {boundary : InterruptBoundary τ} {before id},
  before.fiber id = none ->
  stepEval boundary before (SchedulerDecision.exitMask id) =
    StepResult.refused (SchedulerRefusal.unknownFiber id) before)

#check (@stepEval_exitMask_pending : forall {τ : Type u}
    {boundary : InterruptBoundary τ} {before id fiber},
  before.fiber id = some fiber -> FiberStatus.Active fiber.status ->
  fiber.mask = InterruptMask.masked ->
  fiber.interruptPending = true ->
  stepEval boundary before (SchedulerDecision.exitMask id) =
    StepResult.advanced
      (Machine.transition before
        { fiber with
          status := FiberStatus.finalizing
          terminal := some boundary.interrupted
          mask := InterruptMask.unmasked
          interruptPending := false
          cleanup := CleanupState.pending
          cleanupCount := 0 }
        [ Event.maskExited id, Event.interruptDelivered id ]))

#check (@stepEval_exitMask_clear : forall {τ : Type u}
    {boundary : InterruptBoundary τ} {before id fiber},
  before.fiber id = some fiber -> FiberStatus.Active fiber.status ->
  fiber.mask = InterruptMask.masked ->
  fiber.interruptPending = false ->
  stepEval boundary before (SchedulerDecision.exitMask id) =
    StepResult.advanced
      (Machine.transition before
        { fiber with mask := InterruptMask.unmasked }
        [Event.maskExited id]))

#check (@stepEval_exitMask_invalid : forall {τ : Type u}
    {boundary : InterruptBoundary τ} {before id fiber},
  before.fiber id = some fiber -> FiberStatus.Active fiber.status ->
  fiber.mask = InterruptMask.unmasked ->
  stepEval boundary before (SchedulerDecision.exitMask id) =
    StepResult.refused (SchedulerRefusal.invalidLifecycle id) before)

#check (@stepEval_exitMask_inactive : forall {τ : Type u}
    {boundary : InterruptBoundary τ} {before id fiber},
  before.fiber id = some fiber -> Not (FiberStatus.Active fiber.status) ->
  stepEval boundary before (SchedulerDecision.exitMask id) =
    StepResult.refused (SchedulerRefusal.invalidLifecycle id) before)

#check (@stepEval_complete_missing : forall {τ : Type u}
    {boundary : InterruptBoundary τ} {before id result},
  before.fiber id = none ->
  stepEval boundary before (SchedulerDecision.complete id result) =
    StepResult.refused (SchedulerRefusal.unknownFiber id) before)

#check (@stepEval_complete_running : forall {τ : Type u}
    {boundary : InterruptBoundary τ} {before id fiber result},
  before.fiber id = some fiber ->
  fiber.status = FiberStatus.running ->
  fiber.mask = InterruptMask.unmasked ->
  fiber.interruptPending = false ->
  stepEval boundary before (SchedulerDecision.complete id result) =
    StepResult.advanced
      (Machine.transition before
        { fiber with
          status := FiberStatus.finalizing
          terminal := some result
          interruptPending := false
          cleanup := CleanupState.pending
          cleanupCount := 0 }
        [Event.completed id result]))

#check (@stepEval_complete_invalid : forall {τ : Type u}
    {boundary : InterruptBoundary τ} {before id fiber result},
  before.fiber id = some fiber ->
  Not (fiber.status = FiberStatus.running /\
    fiber.mask = InterruptMask.unmasked /\
    fiber.interruptPending = false) ->
  stepEval boundary before (SchedulerDecision.complete id result) =
    StepResult.refused (SchedulerRefusal.invalidLifecycle id) before)

#check (@stepEval_cleanup_missing : forall {τ : Type u}
    {boundary : InterruptBoundary τ} {before id},
  before.fiber id = none ->
  stepEval boundary before (SchedulerDecision.cleanup id) =
    StepResult.refused (SchedulerRefusal.unknownFiber id) before)

#check (@stepEval_cleanup_ready : forall {τ : Type u}
    {boundary : InterruptBoundary τ} {before id fiber result},
  before.fiber id = some fiber ->
  fiber.status = FiberStatus.finalizing ->
  fiber.terminal = some result ->
  fiber.cleanup = CleanupState.pending ->
  stepEval boundary before (SchedulerDecision.cleanup id) =
    StepResult.advanced
      (Machine.transition before
        { fiber with
          status := FiberStatus.done
          cleanup := CleanupState.done
          cleanupCount := 1 }
        [Event.cleanupFinished id]))

#check (@stepEval_cleanup_invalid : forall {τ : Type u}
    {boundary : InterruptBoundary τ} {before id fiber},
  before.fiber id = some fiber ->
  Not (exists result,
    fiber.status = FiberStatus.finalizing /\
      fiber.terminal = some result /\
      fiber.cleanup = CleanupState.pending) ->
  stepEval boundary before (SchedulerDecision.cleanup id) =
    StepResult.refused (SchedulerRefusal.invalidLifecycle id) before)

#check (@runs_nil_iff : forall {τ : Type u}
    {boundary : InterruptBoundary τ} {initial result},
  Runs boundary initial [] result <->
    Machine.WellFormed initial /\
      ((Machine.Finished initial /\
          result = ReplayResult.finished initial) \/
       (Not (Machine.Finished initial) /\
          result = ReplayResult.frontier initial)))

#check (@runs_cons_iff : forall {τ : Type u}
    {boundary : InterruptBoundary τ} {initial decision tape result},
  Runs boundary initial (decision :: tape) result <->
    Machine.WellFormed initial /\
      ((exists middle,
          Step boundary initial decision (StepResult.advanced middle) /\
          Runs boundary middle tape result) \/
       (exists refusal stopped,
          Step boundary initial decision (StepResult.refused refusal stopped) /\
          result = ReplayResult.refused refusal stopped)))

/-! Positive clauses: the operational relations cannot be empty or constant. -/

#check (@done_join_exists :
  forall {τ : Type u} (boundary : InterruptBoundary τ)
      {before waiter target waiterState targetState result},
    Machine.WellFormed before ->
    before.fiber waiter = some waiterState ->
    before.fiber target = some targetState ->
    waiter ≠ target ->
    waiterState.status = FiberStatus.running ->
    targetState.status = FiberStatus.done ->
    before.terminal target = some result ->
    exists after,
      Step boundary before (SchedulerDecision.join waiter target)
        (StepResult.advanced after) /\
      Event.joinObserved waiter target result ∈ after.trace)

#check (@waiting_join_exists :
  forall {τ : Type u} (boundary : InterruptBoundary τ)
      {before waiter target waiterState targetState},
    Machine.WellFormed before ->
    before.fiber waiter = some waiterState ->
    before.fiber target = some targetState ->
    waiter ≠ target ->
    waiterState.status = FiberStatus.running ->
    targetState.status ≠ FiberStatus.done ->
    exists after,
      Step boundary before (SchedulerDecision.join waiter target)
        (StepResult.advanced after) /\
      (after.fiber waiter).map FiberState.status =
        some (FiberStatus.waiting target) /\
      Event.joinWaiting waiter target ∈ after.trace)

#check (@masked_request_exists :
  forall {τ : Type u} (boundary : InterruptBoundary τ)
      {before requester target requesterState targetState},
    Machine.WellFormed before ->
    before.fiber requester = some requesterState ->
    before.fiber target = some targetState ->
    FiberStatus.Active targetState.status ->
    targetState.mask = InterruptMask.masked ->
    exists after,
      Step boundary before
        (SchedulerDecision.requestInterrupt requester target)
        (StepResult.advanced after) /\
      after.interruptPending target = some true /\
      Event.interruptDeferred target ∈ after.trace)

#check (@unmasked_request_exists :
  forall {τ : Type u} (boundary : InterruptBoundary τ)
      {before requester target requesterState targetState},
    Machine.WellFormed before ->
    before.fiber requester = some requesterState ->
    before.fiber target = some targetState ->
    FiberStatus.Active targetState.status ->
    targetState.mask = InterruptMask.unmasked ->
    exists after,
      Step boundary before
        (SchedulerDecision.requestInterrupt requester target)
        (StepResult.advanced after) /\
      after.terminal target = some boundary.interrupted /\
      (after.fiber target).map FiberState.status = some FiberStatus.finalizing /\
      Event.interruptDelivered target ∈ after.trace)

#check (@enter_mask_exists : forall {τ : Type u}
    (boundary : InterruptBoundary τ) {before id fiber},
  Machine.WellFormed before ->
  before.fiber id = some fiber -> FiberStatus.Active fiber.status ->
  fiber.mask = InterruptMask.unmasked ->
  exists after,
    Step boundary before (SchedulerDecision.enterMask id)
      (StepResult.advanced after) /\
    after.mask id = some InterruptMask.masked /\
    Event.maskEntered id ∈ after.trace)

#check (@pending_unmask_exists : forall {τ : Type u}
    (boundary : InterruptBoundary τ) {before target fiber},
  Machine.WellFormed before ->
  before.fiber target = some fiber -> FiberStatus.Active fiber.status ->
  fiber.mask = InterruptMask.masked -> fiber.interruptPending = true ->
  exists after,
    Step boundary before (SchedulerDecision.exitMask target)
      (StepResult.advanced after) /\
    after.terminal target = some boundary.interrupted /\
    (after.fiber target).map FiberState.status = some FiberStatus.finalizing /\
    Event.interruptDelivered target ∈ after.trace)

#check (@unmask_without_pending_exists : forall {τ : Type u}
    (boundary : InterruptBoundary τ) {before target fiber},
  Machine.WellFormed before ->
  before.fiber target = some fiber -> FiberStatus.Active fiber.status ->
  fiber.mask = InterruptMask.masked -> fiber.interruptPending = false ->
  exists after,
    Step boundary before (SchedulerDecision.exitMask target)
      (StepResult.advanced after) /\
    after.mask target = some InterruptMask.unmasked /\
    Event.maskExited target ∈ after.trace)

#check (@completion_exists : forall {τ : Type u}
    (boundary : InterruptBoundary τ) {before id fiber result},
  Machine.WellFormed before ->
  before.fiber id = some fiber ->
  fiber.status = FiberStatus.running ->
  fiber.mask = InterruptMask.unmasked ->
  fiber.interruptPending = false ->
  exists after,
    Step boundary before (SchedulerDecision.complete id result)
      (StepResult.advanced after) /\
    (after.fiber id).map FiberState.status = some FiberStatus.finalizing /\
    after.terminal id = some result /\
    after.cleanupState id = some CleanupState.pending /\
    Event.completed id result ∈ after.trace)

#check (@cleanup_exists : forall {τ : Type u}
    (boundary : InterruptBoundary τ) {before id fiber result},
  Machine.WellFormed before ->
  before.fiber id = some fiber ->
  fiber.status = FiberStatus.finalizing ->
  fiber.terminal = some result ->
  fiber.cleanup = CleanupState.pending ->
  exists after,
    Step boundary before (SchedulerDecision.cleanup id)
      (StepResult.advanced after) /\
    after.terminal id = some result /\
    after.cleanupState id = some CleanupState.done /\
    after.cleanupCount id = 1 /\
    Event.cleanupFinished id ∈ after.trace)

#check (@unknown_schedule_refuses : forall {τ : Type u}
    (boundary : InterruptBoundary τ) {before id},
  Machine.WellFormed before -> before.fiber id = none ->
  Step boundary before (SchedulerDecision.schedule id)
    (StepResult.refused (SchedulerRefusal.unknownFiber id) before))

#check (@invalid_completion_refuses : forall {τ : Type u}
    (boundary : InterruptBoundary τ) {before id fiber result},
  Machine.WellFormed before ->
  before.fiber id = some fiber ->
  Not (fiber.status = FiberStatus.running /\
    fiber.mask = InterruptMask.unmasked /\
    fiber.interruptPending = false) ->
  Step boundary before (SchedulerDecision.complete id result)
    (StepResult.refused (SchedulerRefusal.invalidLifecycle id) before))

#check (@representative_inputs_exist : forall {τ : Type u}
    (boundary : InterruptBoundary τ),
  (exists before id fiber,
    Machine.WellFormed before /\ before.fiber id = some fiber /\
      fiber.status = FiberStatus.runnable) /\
  (exists before waiter target waiterState targetState result,
    Machine.WellFormed before /\
    before.fiber waiter = some waiterState /\
    before.fiber target = some targetState /\
    waiter ≠ target /\
    waiterState.status = FiberStatus.running /\
    targetState.status = FiberStatus.done /\
    before.terminal target = some result) /\
  (exists before waiter target waiterState targetState,
    Machine.WellFormed before /\
    before.fiber waiter = some waiterState /\
    before.fiber target = some targetState /\
    waiter ≠ target /\
    waiterState.status = FiberStatus.running /\
    targetState.status ≠ FiberStatus.done) /\
  (exists before requester target requesterState targetState,
    Machine.WellFormed before /\
    before.fiber requester = some requesterState /\
    before.fiber target = some targetState /\
    FiberStatus.Active targetState.status /\
    targetState.mask = InterruptMask.masked) /\
  (exists before requester target requesterState targetState,
    Machine.WellFormed before /\
    before.fiber requester = some requesterState /\
    before.fiber target = some targetState /\
    FiberStatus.Active targetState.status /\
    targetState.mask = InterruptMask.unmasked) /\
  (exists before target fiber,
    Machine.WellFormed before /\
    before.fiber target = some fiber /\
    FiberStatus.Active fiber.status /\
    fiber.mask = InterruptMask.masked /\
    fiber.interruptPending = true) /\
  (exists before target fiber,
    Machine.WellFormed before /\
    before.fiber target = some fiber /\
    FiberStatus.Active fiber.status /\
    fiber.mask = InterruptMask.masked /\
    fiber.interruptPending = false) /\
  (exists before id fiber,
    Machine.WellFormed before /\ before.fiber id = some fiber /\
      fiber.status = FiberStatus.running /\
      fiber.mask = InterruptMask.unmasked /\
      fiber.interruptPending = false) /\
  (exists before id fiber result,
    Machine.WellFormed before /\ before.fiber id = some fiber /\
    fiber.status = FiberStatus.finalizing /\
    fiber.terminal = some result /\
    fiber.cleanup = CleanupState.pending) /\
  (exists before id,
    Machine.WellFormed before /\ before.fiber id = none))

#check (@runs_nil_finished : forall {τ : Type u}
    (boundary : InterruptBoundary τ) {initial},
  Machine.WellFormed initial -> Machine.Finished initial ->
  Runs boundary initial [] (ReplayResult.finished initial))

#check (@runs_nil_frontier : forall {τ : Type u}
    (boundary : InterruptBoundary τ) {initial},
  Machine.WellFormed initial -> Not (Machine.Finished initial) ->
  Runs boundary initial [] (ReplayResult.frontier initial))

#check (@exists_representative_finished_run : forall {τ : Type u}
    (boundary : InterruptBoundary τ),
  exists initial tape final,
    Machine.WellFormed initial /\ tape ≠ [] /\
      Runs boundary initial tape (ReplayResult.finished final))

#check (@join_agreement :
  forall {τ : Type u} {boundary : InterruptBoundary τ}
      {before after waiter target targetState result},
    Machine.WellFormed before ->
    before.fiber target = some targetState ->
    targetState.status = FiberStatus.done ->
    Step boundary before (SchedulerDecision.join waiter target)
        (StepResult.advanced after) ->
    before.terminal target = some result ->
    after.terminal target = some result /\
    after.cleanupState target = before.cleanupState target /\
    after.trace = before.trace ++ [Event.joinObserved waiter target result])

#check (@double_join_agreement :
  forall {τ : Type u} {boundary : InterruptBoundary τ}
      {before middle after waiterOne waiterTwo target targetState result},
    Machine.WellFormed before ->
    before.fiber target = some targetState ->
    targetState.status = FiberStatus.done ->
    waiterOne ≠ target -> waiterTwo ≠ target ->
    before.terminal target = some result ->
    Step boundary before (SchedulerDecision.join waiterOne target)
        (StepResult.advanced middle) ->
    Step boundary middle (SchedulerDecision.join waiterTwo target)
        (StepResult.advanced after) ->
    middle.terminal target = some result /\
    after.terminal target = some result /\
    after.cleanupCount target = before.cleanupCount target)

#check (@unmasked_interrupt_delivers :
  forall {τ : Type u} {boundary : InterruptBoundary τ}
      {before after requester target requesterState targetState},
    Machine.WellFormed before ->
    before.fiber requester = some requesterState ->
    before.fiber target = some targetState ->
    FiberStatus.Active targetState.status ->
    targetState.mask = InterruptMask.unmasked ->
    Step boundary before
        (SchedulerDecision.requestInterrupt requester target)
        (StepResult.advanced after) ->
    after.terminal target = some boundary.interrupted /\
    (after.fiber target).map FiberState.status = some FiberStatus.finalizing /\
    after.cleanupState target = some CleanupState.pending)

#check (@masked_interrupt_defers :
  forall {τ : Type u} {boundary : InterruptBoundary τ}
      {before after requester target requesterState targetState},
    Machine.WellFormed before ->
    before.fiber requester = some requesterState ->
    before.fiber target = some targetState ->
    FiberStatus.Active targetState.status ->
    targetState.mask = InterruptMask.masked ->
    Step boundary before
        (SchedulerDecision.requestInterrupt requester target)
        (StepResult.advanced after) ->
    after.interruptPending target = some true /\
      after.terminal target = before.terminal target)

#check (@unmask_delivers_pending :
  forall {τ : Type u} {boundary : InterruptBoundary τ}
      {before after target fiber},
    Machine.WellFormed before ->
    before.fiber target = some fiber -> FiberStatus.Active fiber.status ->
    fiber.mask = InterruptMask.masked -> fiber.interruptPending = true ->
    Step boundary before (SchedulerDecision.exitMask target)
        (StepResult.advanced after) ->
    after.interruptPending target = some false /\
    after.mask target = some InterruptMask.unmasked /\
    after.terminal target = some boundary.interrupted /\
    (after.fiber target).map FiberState.status = some FiberStatus.finalizing)

#check (@cleanup_count_monotone : forall {τ : Type u}
    {boundary : InterruptBoundary τ} {before decision result id},
  Machine.WellFormed before -> Step boundary before decision result ->
    before.cleanupCount id <= result.machine.cleanupCount id)

#check (@cleanup_at_most_once : forall {τ : Type u}
    {boundary : InterruptBoundary τ} {initial tape result id},
  Machine.WellFormed initial -> Runs boundary initial tape result ->
    result.machine.cleanupCount id <= 1)

#check (@cleanup_events_at_most_once : forall {τ : Type u}
    {boundary : InterruptBoundary τ} {initial tape result},
  Machine.WellFormed initial -> Runs boundary initial tape result ->
    result.machine.cleanupEventIds.Nodup)

#check (@cleanup_events_agree : forall {τ : Type u}
    {boundary : InterruptBoundary τ} {initial tape result},
  Machine.WellFormed initial -> Runs boundary initial tape result ->
    forall fiber, fiber ∈ result.machine.fibers ->
      (fiber.id ∈ result.machine.cleanupEventIds <->
        fiber.cleanupCount = 1))

#check (@cleanup_preserves_terminal :
  forall {τ : Type u} {boundary : InterruptBoundary τ}
      {before after id fiber terminal},
    Machine.WellFormed before ->
    before.fiber id = some fiber ->
    fiber.status = FiberStatus.finalizing ->
    fiber.terminal = some terminal ->
    fiber.cleanup = CleanupState.pending ->
    Step boundary before (SchedulerDecision.cleanup id)
      (StepResult.advanced after) ->
    after.terminal id = some terminal /\
    (after.fiber id).map FiberState.status = some FiberStatus.done /\
    after.cleanupState id = some CleanupState.done /\
    after.cleanupCount id = 1 /\
    after.trace = before.trace ++ [Event.cleanupFinished id])

#check (@cleanup_safe_on_finish :
  forall {τ : Type u} {boundary : InterruptBoundary τ}
      {initial tape final id terminal},
    Machine.WellFormed initial ->
    Runs boundary initial tape (ReplayResult.finished final) ->
    final.terminal id = some terminal ->
    final.cleanupState id = some CleanupState.done /\
      final.cleanupCount id = 1)

#check (@interrupt_complete_order_distinct : forall {τ : Type u}
    (boundary : InterruptBoundary τ),
  exists initial requester target success left right,
    Machine.WellFormed initial /\
    Runs boundary initial
      [ SchedulerDecision.requestInterrupt requester target
      , SchedulerDecision.complete target success ] left /\
    Runs boundary initial
      [ SchedulerDecision.complete target success
      , SchedulerDecision.requestInterrupt requester target ] right /\
    left ≠ right)

#print axioms step_deterministic
#print axioms fixedTape_deterministic
#print axioms Machine.fiber_eq_find
#print axioms Machine.terminal_eq
#print axioms Machine.mask_eq
#print axioms Machine.interruptPending_eq
#print axioms Machine.cleanupState_eq
#print axioms Machine.cleanupCount_eq
#print axioms Event.cleanupId_eq_some
#print axioms Machine.cleanupEventIds_eq
#print axioms Machine.transition_cleanupEventIds
#print axioms StepResult.machine_advanced
#print axioms StepResult.machine_refused
#print axioms ReplayResult.machine_finished
#print axioms ReplayResult.machine_refused
#print axioms ReplayResult.machine_frontier
#print axioms Machine.finished_iff
#print axioms Machine.wellFormedDecidable
#print axioms step_preserves_wellFormed
#print axioms runs_preserves_wellFormed
#print axioms finite_replay_total
#print axioms step_total
#print axioms runs_nil_iff
#print axioms runs_cons_iff
#print axioms done_join_exists
#print axioms waiting_join_exists
#print axioms masked_request_exists
#print axioms unmasked_request_exists
#print axioms enter_mask_exists
#print axioms pending_unmask_exists
#print axioms unmask_without_pending_exists
#print axioms completion_exists
#print axioms cleanup_exists
#print axioms unknown_schedule_refuses
#print axioms invalid_completion_refuses
#print axioms representative_inputs_exist
#print axioms runs_nil_finished
#print axioms runs_nil_frontier
#print axioms exists_representative_finished_run
#print axioms join_agreement
#print axioms double_join_agreement
#print axioms unmasked_interrupt_delivers
#print axioms masked_interrupt_defers
#print axioms unmask_delivers_pending
#print axioms cleanup_count_monotone
#print axioms cleanup_at_most_once
#print axioms cleanup_events_at_most_once
#print axioms cleanup_events_agree
#print axioms cleanup_preserves_terminal
#print axioms cleanup_safe_on_finish
#print axioms interrupt_complete_order_distinct

end OperationalLaws

end Effect4Test.Concurrency.FiberRepresentativeContract
