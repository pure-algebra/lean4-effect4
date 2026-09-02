import Effect4.Concurrency.Fiber

/-!
# Explicit scheduler decisions and finite replay

The scheduler is a pure transition system over first-order decisions. A
supplied finite tape fixes every representative scheduling choice; exhausting
that tape before all fibers finish is retained as a live frontier.
-/

namespace Effect4

universe u

/-- Refusals are scheduler-domain failures, not terminal observations. -/
inductive SchedulerRefusal
  | unknownFiber (id : FiberId)
  | invalidLifecycle (id : FiberId)
deriving DecidableEq, Repr

/-- Every choice consumed by the representative scheduler. -/
inductive SchedulerDecision (τ : Type u)
  | schedule (id : FiberId)
  | join (waiter target : FiberId)
  | requestInterrupt (requester target : FiberId)
  | enterMask (id : FiberId)
  | exitMask (id : FiberId)
  | complete (id : FiberId) (result : τ)
  | cleanup (id : FiberId)

/-- A finite, explicit sequence of scheduler choices. -/
abbrev DecisionTape (τ : Type u) := List (SchedulerDecision τ)

/-- Chronological observations emitted by scheduler transitions. -/
inductive Event (τ : Type u)
  | scheduled (id : FiberId)
  | joinWaiting (waiter target : FiberId)
  | joinObserved (waiter target : FiberId) (result : τ)
  | interruptRequested (requester target : FiberId)
  | interruptDeferred (target : FiberId)
  | interruptDelivered (target : FiberId)
  | maskEntered (id : FiberId)
  | maskExited (id : FiberId)
  | completed (id : FiberId) (result : τ)
  | cleanupFinished (id : FiberId)

namespace Event

/-- Project exactly the cleanup-completion observations from a trace. -/
def cleanupId? : Event τ -> Option FiberId
  | cleanupFinished id => some id
  | _ => none

theorem cleanupId_eq_some (event : Event τ) (id : FiberId) :
    cleanupId? event = some id <-> event = cleanupFinished id := by
  cases event <;> simp [cleanupId?]

end Event

/-- The append-only chronological scheduler trace. -/
abbrev Trace (τ : Type u) := List (Event τ)

/-- Fiber collection together with its retained trace. -/
structure Machine (τ : Type u) where
  fibers : List (FiberState τ)
  trace : Trace τ

namespace Machine

/-- Resolve the first fiber carrying the requested nominal identity. -/
def fiber (machine : Machine τ) (id : FiberId) : Option (FiberState τ) :=
  machine.fibers.find? (fun current => decide (current.id = id))

/-- Read a terminal observation, if both the fiber and observation exist. -/
def terminal (machine : Machine τ) (id : FiberId) : Option τ :=
  (machine.fiber id).bind FiberState.terminal

/-- Read the interruption mask of a resolved fiber. -/
def mask (machine : Machine τ) (id : FiberId) : Option InterruptMask :=
  (machine.fiber id).map FiberState.mask

/-- Read whether a resolved fiber has a deferred interruption. -/
def interruptPending (machine : Machine τ) (id : FiberId) : Option Bool :=
  (machine.fiber id).map FiberState.interruptPending

/-- Read the cleanup phase of a resolved fiber. -/
def cleanupState (machine : Machine τ) (id : FiberId) : Option CleanupState :=
  (machine.fiber id).map FiberState.cleanup

/-- Missing fibers contribute zero to the cleanup-count observation. -/
def cleanupCount (machine : Machine τ) (id : FiberId) : Nat :=
  ((machine.fiber id).map FiberState.cleanupCount).getD 0

/-- Fiber identities with an observable cleanup-completion event. -/
def cleanupEventIds (machine : Machine τ) : List FiberId :=
  machine.trace.filterMap Event.cleanupId?

theorem fiber_eq_find (machine : Machine τ) (id : FiberId) :
    machine.fiber id =
      machine.fibers.find? (fun current => current.id = id) :=
  rfl

theorem terminal_eq (machine : Machine τ) (id : FiberId) :
    machine.terminal id = (machine.fiber id).bind FiberState.terminal :=
  rfl

theorem mask_eq (machine : Machine τ) (id : FiberId) :
    machine.mask id = (machine.fiber id).map FiberState.mask :=
  rfl

theorem interruptPending_eq (machine : Machine τ) (id : FiberId) :
    machine.interruptPending id =
      (machine.fiber id).map FiberState.interruptPending :=
  rfl

theorem cleanupState_eq (machine : Machine τ) (id : FiberId) :
    machine.cleanupState id = (machine.fiber id).map FiberState.cleanup :=
  rfl

theorem cleanupCount_eq (machine : Machine τ) (id : FiberId) :
    machine.cleanupCount id =
      ((machine.fiber id).map FiberState.cleanupCount).getD 0 :=
  rfl

theorem cleanupEventIds_eq (machine : Machine τ) :
    machine.cleanupEventIds = machine.trace.filterMap Event.cleanupId? :=
  rfl

/-- Replace one identity-preserving fiber state and append emitted events. -/
def transition (before : Machine τ) (replacement : FiberState τ)
    (events : List (Event τ)) : Machine τ :=
  { fibers := before.fibers.map (fun current =>
      if current.id = replacement.id then replacement else current)
    trace := before.trace ++ events }

theorem transition_fibers (before : Machine τ) (replacement : FiberState τ)
    (events : List (Event τ)) :
    (transition before replacement events).fibers =
      before.fibers.map (fun current =>
        if current.id = replacement.id then replacement else current) :=
  rfl

theorem transition_trace (before : Machine τ) (replacement : FiberState τ)
    (events : List (Event τ)) :
    (transition before replacement events).trace = before.trace ++ events :=
  rfl

theorem transition_cleanupEventIds (before : Machine τ)
    (replacement : FiberState τ) (events : List (Event τ)) :
    (transition before replacement events).cleanupEventIds =
      before.cleanupEventIds ++ events.filterMap Event.cleanupId? := by
  simp [cleanupEventIds, transition]

private theorem find?_map_other (xs : List (FiberState τ))
    (replacement : FiberState τ) (id : FiberId)
    (hne : replacement.id ≠ id) :
    (xs.map (fun current =>
      if current.id = replacement.id then replacement else current)).find?
        (fun current => decide (current.id = id)) =
      xs.find? (fun current => decide (current.id = id)) := by
  induction xs with
  | nil => rfl
  | cons current rest ih =>
      by_cases hreplace : current.id = replacement.id
      · have hcurrent : current.id ≠ id := by
          intro heq
          exact hne (hreplace.symm.trans heq)
        simp [hreplace, hne, ih]
      · simp [hreplace]
        by_cases hcurrent : current.id = id
        · simp [hcurrent]
        · simp [hcurrent, ih]

theorem transition_fiber_other (before : Machine τ)
    (replacement : FiberState τ) (events : List (Event τ)) (id : FiberId)
    (hne : replacement.id ≠ id) :
    (transition before replacement events).fiber id = before.fiber id := by
  exact find?_map_other before.fibers replacement id hne

/-- Admission conditions needed by the scheduler safety theorems. -/
structure WellFormed (machine : Machine τ) : Prop where
  idsUnique : (machine.fibers.map FiberState.id).Nodup
  cleanupBounded : forall current, current ∈ machine.fibers ->
    current.cleanupCount <= 1
  cleanupEventsUnique : machine.cleanupEventIds.Nodup
  cleanupEventsClosed : forall id, id ∈ machine.cleanupEventIds ->
    exists current, current ∈ machine.fibers /\ current.id = id
  cleanupEventAgreement : forall current, current ∈ machine.fibers ->
    (current.id ∈ machine.cleanupEventIds <-> current.cleanupCount = 1)
  activeCleanup : forall current, current ∈ machine.fibers ->
    FiberStatus.Active current.status ->
      current.terminal = none /\
      current.cleanup = CleanupState.notStarted /\ current.cleanupCount = 0
  finalizingCleanup : forall current, current ∈ machine.fibers ->
    current.status = FiberStatus.finalizing ->
      (exists result, current.terminal = some result) /\
      current.cleanup = CleanupState.pending /\ current.cleanupCount = 0
  doneCleanup : forall current, current ∈ machine.fibers ->
    current.status = FiberStatus.done ->
      (exists result, current.terminal = some result) /\
      current.cleanup = CleanupState.done /\ current.cleanupCount = 1
  pendingActive : forall current, current ∈ machine.fibers ->
    current.interruptPending = true ->
      current.mask = InterruptMask.masked /\ FiberStatus.Active current.status
  waitingClosed : forall current target, current ∈ machine.fibers ->
    current.status = FiberStatus.waiting target ->
      exists targetFiber, targetFiber ∈ machine.fibers /\ targetFiber.id = target

private def decidableForallMem (xs : List α) (P : α -> Prop)
    (decP : forall x, Decidable (P x)) :
    Decidable (forall x, x ∈ xs -> P x) :=
  match xs with
  | [] => isTrue (by simp)
  | head :: tail =>
      match decP head with
      | isFalse hhead => isFalse (by
          intro hall
          exact hhead (hall head (by simp)))
      | isTrue hhead =>
          match decidableForallMem tail P decP with
          | isFalse htail => isFalse (by
              intro hall
              exact htail (by
                intro x hx
                exact hall x (by simp [hx])))
          | isTrue htail => isTrue (by
              intro x hx
              rcases List.mem_cons.mp hx with rfl | hx
              · exact hhead
              · exact htail x hx)

private def decidableExistsMem (xs : List α) (P : α -> Prop)
    (decP : forall x, Decidable (P x)) :
    Decidable (exists x, x ∈ xs /\ P x) :=
  match xs with
  | [] => isFalse (by simp)
  | head :: tail =>
      match decP head with
      | isTrue hhead => isTrue ⟨head, by simp, hhead⟩
      | isFalse hhead =>
          match decidableExistsMem tail P decP with
          | isTrue htail => isTrue (by
              rcases htail with ⟨x, hx, hp⟩
              exact ⟨x, by simp [hx], hp⟩)
          | isFalse htail => isFalse (by
              rintro ⟨x, hx, hp⟩
              rcases List.mem_cons.mp hx with rfl | hx
              · exact hhead hp
              · exact htail ⟨x, hx, hp⟩)

private def terminalExistsDecidable [DecidableEq τ] (current : FiberState τ) :
    Decidable (exists result, current.terminal = some result) :=
  match h : current.terminal with
  | none => isFalse (by simp)
  | some result => isTrue ⟨result, rfl⟩

private def targetExistsDecidable (fibers : List (FiberState τ))
    (target : FiberId) :
    Decidable (exists targetFiber, targetFiber ∈ fibers /\
      targetFiber.id = target) :=
  decidableExistsMem fibers (fun current => current.id = target)
    (fun _ => inferInstance)

private def waitingClosedForDecidable (fibers : List (FiberState τ))
    (current : FiberState τ) :
    Decidable (forall target, current.status = FiberStatus.waiting target ->
      exists targetFiber, targetFiber ∈ fibers /\ targetFiber.id = target) := by
  cases hstatus : current.status with
  | runnable | running | finalizing | done =>
      exact isTrue (by
        intro target impossible
        simp at impossible)
  | waiting actual =>
      match targetExistsDecidable fibers actual with
      | isTrue hexists => exact isTrue (by
          intro target heq
          have : target = actual := by simpa [hstatus] using heq.symm
          subst target
          exact hexists)
      | isFalse hmissing => exact isFalse (by
          intro hall
          exact hmissing (hall actual (by simp)))

/-- Admission is decidable for a terminal alphabet with decidable equality. -/
def wellFormedDecidable [DecidableEq τ] (machine : Machine τ) :
    Decidable (WellFormed machine) := by
  let pBound := fun current : FiberState τ => current.cleanupCount <= 1
  let pActive := fun current : FiberState τ =>
    FiberStatus.Active current.status ->
      current.terminal = none /\
      current.cleanup = CleanupState.notStarted /\ current.cleanupCount = 0
  let pFinal := fun current : FiberState τ =>
    current.status = FiberStatus.finalizing ->
      (exists result, current.terminal = some result) /\
      current.cleanup = CleanupState.pending /\ current.cleanupCount = 0
  let pDone := fun current : FiberState τ =>
    current.status = FiberStatus.done ->
      (exists result, current.terminal = some result) /\
      current.cleanup = CleanupState.done /\ current.cleanupCount = 1
  let pPending := fun current : FiberState τ =>
    current.interruptPending = true ->
      current.mask = InterruptMask.masked /\ FiberStatus.Active current.status
  let pWaiting := fun current : FiberState τ => forall target,
    current.status = FiberStatus.waiting target ->
      exists targetFiber, targetFiber ∈ machine.fibers /\
        targetFiber.id = target
  let pClosed := fun id : FiberId =>
    exists current, current ∈ machine.fibers /\ current.id = id
  let pAgreement := fun current : FiberState τ =>
    (current.id ∈ machine.cleanupEventIds <-> current.cleanupCount = 1)
  let dBound := decidableForallMem machine.fibers pBound (fun _ => inferInstance)
  let dActive := decidableForallMem machine.fibers pActive (fun current =>
    by
      dsimp [pActive]
      letI : Decidable (FiberStatus.Active current.status) :=
        FiberStatus.activeDecidable current.status
      exact inferInstance)
  let dFinal := decidableForallMem machine.fibers pFinal (fun current => by
    dsimp [pFinal]
    letI : Decidable (exists result, current.terminal = some result) :=
      terminalExistsDecidable current
    exact inferInstance)
  let dDone := decidableForallMem machine.fibers pDone (fun current => by
    dsimp [pDone]
    letI : Decidable (exists result, current.terminal = some result) :=
      terminalExistsDecidable current
    exact inferInstance)
  let dPending := decidableForallMem machine.fibers pPending (fun current => by
    dsimp [pPending]
    letI : Decidable (FiberStatus.Active current.status) :=
      FiberStatus.activeDecidable current.status
    exact inferInstance)
  let dWaiting := decidableForallMem machine.fibers pWaiting
    (waitingClosedForDecidable machine.fibers)
  let dCleanupUnique : Decidable machine.cleanupEventIds.Nodup :=
    inferInstance
  let dClosed := decidableForallMem machine.cleanupEventIds pClosed
    (fun id => targetExistsDecidable machine.fibers id)
  let dAgreement := decidableForallMem machine.fibers pAgreement
    (fun _ => inferInstance)
  exact match inferInstanceAs (Decidable
      ((machine.fibers.map (fun current : FiberState τ => current.id)).Nodup)) with
    | isFalse h => isFalse (fun wf => h wf.idsUnique)
    | isTrue hIds => match dBound with
      | isFalse h => isFalse (fun wf => h wf.cleanupBounded)
      | isTrue hBound => match dCleanupUnique with
        | isFalse h => isFalse (fun wf => h wf.cleanupEventsUnique)
        | isTrue hCleanupUnique => match dClosed with
          | isFalse h => isFalse (fun wf => h wf.cleanupEventsClosed)
          | isTrue hClosed => match dAgreement with
            | isFalse h => isFalse (fun wf => h wf.cleanupEventAgreement)
            | isTrue hAgreement => match dActive with
              | isFalse h => isFalse (fun wf => h wf.activeCleanup)
              | isTrue hActive => match dFinal with
                | isFalse h => isFalse (fun wf => h wf.finalizingCleanup)
                | isTrue hFinal => match dDone with
                  | isFalse h => isFalse (fun wf => h wf.doneCleanup)
                  | isTrue hDone => match dPending with
                    | isFalse h => isFalse (fun wf => h wf.pendingActive)
                    | isTrue hPending => match dWaiting with
                      | isFalse h => isFalse (fun wf => h (by
                          intro current hmem target
                          exact wf.waitingClosed current target hmem))
                      | isTrue hWaiting => isTrue
                          ⟨hIds, hBound, hCleanupUnique, hClosed,
                            hAgreement, hActive, hFinal, hDone, hPending, by
                              intro current target hmem
                              exact hWaiting current hmem target⟩

/-- Every retained fiber has completed cleanup. -/
def Finished (machine : Machine τ) : Prop :=
  forall current, current ∈ machine.fibers -> current.status = FiberStatus.done

theorem finished_iff (machine : Machine τ) :
    Finished machine <->
      forall current, current ∈ machine.fibers ->
        current.status = FiberStatus.done :=
  Iff.rfl

private def finishedDecidable (machine : Machine τ) :
    Decidable (Finished machine) :=
  decidableForallMem machine.fibers
    (fun current => current.status = FiberStatus.done)
    (fun _ => inferInstance)

end Machine

namespace SchedulerRefusal

theorem cases_receipt (refusal : SchedulerRefusal) :
    (exists id, refusal = unknownFiber id) \/
      (exists id, refusal = invalidLifecycle id) := by
  cases refusal <;> simp

end SchedulerRefusal

namespace SchedulerDecision

theorem cases_receipt (decision : SchedulerDecision τ) :
    (exists id, decision = schedule id) \/
    (exists waiter target, decision = join waiter target) \/
    (exists requester target, decision = requestInterrupt requester target) \/
    (exists id, decision = enterMask id) \/
    (exists id, decision = exitMask id) \/
    (exists id result, decision = complete id result) \/
    (exists id, decision = cleanup id) := by
  cases decision <;> simp

end SchedulerDecision

namespace Event

theorem cases_receipt (event : Event τ) :
    (exists id, event = scheduled id) \/
    (exists waiter target, event = joinWaiting waiter target) \/
    (exists waiter target result, event = joinObserved waiter target result) \/
    (exists requester target, event = interruptRequested requester target) \/
    (exists target, event = interruptDeferred target) \/
    (exists target, event = interruptDelivered target) \/
    (exists id, event = maskEntered id) \/
    (exists id, event = maskExited id) \/
    (exists id result, event = completed id result) \/
    (exists id, event = cleanupFinished id) := by
  cases event <;> simp

end Event

/-- Result of consuming one scheduler decision. -/
inductive StepResult (τ : Type u)
  | advanced (machine : Machine τ)
  | refused (reason : SchedulerRefusal) (machine : Machine τ)

namespace StepResult

/-- Retain the machine on both success and refusal. -/
def machine : StepResult τ -> Machine τ
  | advanced next | refused _ next => next

theorem machine_advanced (next : Machine τ) :
    (advanced next).machine = next := rfl

theorem machine_refused (reason : SchedulerRefusal) (stopped : Machine τ) :
    (refused reason stopped).machine = stopped := rfl

end StepResult

/-- Observation of replaying a finite decision tape. -/
inductive ReplayResult (τ : Type u)
  | finished (machine : Machine τ)
  | refused (reason : SchedulerRefusal) (machine : Machine τ)
  | frontier (machine : Machine τ)

namespace ReplayResult

/-- Retain the stopped machine in every replay observation. -/
def machine : ReplayResult τ -> Machine τ
  | finished stopped | refused _ stopped | frontier stopped => stopped

theorem machine_finished (stopped : Machine τ) :
    (finished stopped).machine = stopped := rfl

theorem machine_refused (reason : SchedulerRefusal) (stopped : Machine τ) :
    (refused reason stopped).machine = stopped := rfl

theorem machine_frontier (stopped : Machine τ) :
    (frontier stopped).machine = stopped := rfl

end ReplayResult

local instance activeDecision (status : FiberStatus) :
    Decidable (FiberStatus.Active status) :=
  FiberStatus.activeDecidable status

local instance finishedDecision (machine : Machine τ) :
    Decidable (Machine.Finished machine) :=
  Machine.finishedDecidable machine

/-- Pure interpretation of one explicit scheduler decision. -/
def stepEval (boundary : InterruptBoundary τ) (before : Machine τ) :
    SchedulerDecision τ -> StepResult τ
  | .schedule id =>
      match before.fiber id with
      | none => .refused (.unknownFiber id) before
      | some current =>
          if current.status = .runnable then
            .advanced (Machine.transition before
              { current with status := .running } [.scheduled id])
          else
            .refused (.invalidLifecycle id) before
  | .join waiter target =>
      match before.fiber waiter with
      | none => .refused (.unknownFiber waiter) before
      | some waiterState =>
          match before.fiber target with
          | none => .refused (.unknownFiber target) before
          | some targetState =>
              if waiter = target then
                .refused (.invalidLifecycle waiter) before
              else if targetState.status = .done then
                match before.terminal target with
                | none => .refused (.invalidLifecycle target) before
                | some result =>
                    if waiterState.status = .running \/
                        waiterState.status = .waiting target then
                      .advanced (Machine.transition before
                        { waiterState with status := .running }
                        [.joinObserved waiter target result])
                    else
                      .refused (.invalidLifecycle waiter) before
              else if waiterState.status = .running then
                .advanced (Machine.transition before
                  { waiterState with status := .waiting target }
                  [.joinWaiting waiter target])
              else
                .refused (.invalidLifecycle waiter) before
  | .requestInterrupt requester target =>
      match before.fiber requester with
      | none => .refused (.unknownFiber requester) before
      | some _requesterState =>
          match before.fiber target with
          | none => .refused (.unknownFiber target) before
          | some targetState =>
              if FiberStatus.Active targetState.status then
                if targetState.mask = .masked then
                  .advanced (Machine.transition before
                    { targetState with interruptPending := true }
                    [.interruptRequested requester target,
                      .interruptDeferred target])
                else
                  .advanced (Machine.transition before
                    { targetState with
                      status := FiberStatus.finalizing,
                      terminal := some boundary.interrupted,
                      interruptPending := false,
                      cleanup := CleanupState.pending,
                      cleanupCount := 0 }
                    [.interruptRequested requester target,
                      .interruptDelivered target])
              else
                .refused (.invalidLifecycle target) before
  | .enterMask id =>
      match before.fiber id with
      | none => .refused (.unknownFiber id) before
      | some current =>
          if FiberStatus.Active current.status then
            if current.mask = .unmasked then
              .advanced (Machine.transition before
                { current with mask := .masked } [.maskEntered id])
            else
              .refused (.invalidLifecycle id) before
          else
            .refused (.invalidLifecycle id) before
  | .exitMask id =>
      match before.fiber id with
      | none => .refused (.unknownFiber id) before
      | some current =>
          if FiberStatus.Active current.status then
            if current.mask = .masked then
              if current.interruptPending = true then
                .advanced (Machine.transition before
                  { current with
                    status := FiberStatus.finalizing,
                    terminal := some boundary.interrupted,
                    mask := InterruptMask.unmasked,
                    interruptPending := false,
                    cleanup := CleanupState.pending,
                    cleanupCount := 0 }
                  [.maskExited id, .interruptDelivered id])
              else
                .advanced (Machine.transition before
                  { current with mask := .unmasked } [.maskExited id])
            else
              .refused (.invalidLifecycle id) before
          else
            .refused (.invalidLifecycle id) before
  | .complete id result =>
      match before.fiber id with
      | none => .refused (.unknownFiber id) before
      | some current =>
          if current.status = .running /\ current.mask = .unmasked /\
              current.interruptPending = false then
            .advanced (Machine.transition before
              { current with
                status := FiberStatus.finalizing,
                terminal := some result,
                interruptPending := false,
                cleanup := CleanupState.pending,
                cleanupCount := 0 }
              [.completed id result])
          else
            .refused (.invalidLifecycle id) before
  | .cleanup id =>
      match before.fiber id with
      | none => .refused (.unknownFiber id) before
      | some current =>
          if current.status = .finalizing then
            match current.terminal with
            | none => .refused (.invalidLifecycle id) before
            | some _result =>
                if current.cleanup = .pending then
                  .advanced (Machine.transition before
                    { current with
                      status := FiberStatus.done,
                      cleanup := CleanupState.done,
                      cleanupCount := 1 }
                    [.cleanupFinished id])
                else
                  .refused (.invalidLifecycle id) before
          else
            .refused (.invalidLifecycle id) before

/-- The one-step relation is exactly the graph of `stepEval`. -/
def Step (boundary : InterruptBoundary τ) (before : Machine τ)
    (decision : SchedulerDecision τ) (result : StepResult τ) : Prop :=
  result = stepEval boundary before decision

theorem step_iff {boundary : InterruptBoundary τ} {before decision result} :
    Step boundary before decision result <->
      result = stepEval boundary before decision :=
  Iff.rfl

private def replayEval (boundary : InterruptBoundary τ) (initial : Machine τ) :
    DecisionTape τ -> ReplayResult τ
  | [] =>
      if Machine.Finished initial then .finished initial else .frontier initial
  | decision :: tape =>
      match stepEval boundary initial decision with
      | .advanced middle => replayEval boundary middle tape
      | .refused reason stopped => .refused reason stopped

/-- Replay is admitted at the initial machine and follows the supplied tape. -/
def Runs (boundary : InterruptBoundary τ) (initial : Machine τ)
    (tape : DecisionTape τ) (result : ReplayResult τ) : Prop :=
  Machine.WellFormed initial /\ result = replayEval boundary initial tape

/-! Exact interpreter equations. -/

theorem stepEval_schedule_missing {boundary : InterruptBoundary τ} {before id}
    (hmissing : before.fiber id = none) :
    stepEval boundary before (.schedule id) =
      .refused (.unknownFiber id) before := by
  simp [stepEval, hmissing]

theorem stepEval_schedule_runnable {boundary : InterruptBoundary τ}
    {before id current} (hfound : before.fiber id = some current)
    (hstatus : current.status = .runnable) :
    stepEval boundary before (.schedule id) =
      .advanced (Machine.transition before
        { current with status := .running } [.scheduled id]) := by
  simp [stepEval, hfound, hstatus]

theorem stepEval_schedule_invalid {boundary : InterruptBoundary τ}
    {before id current} (hfound : before.fiber id = some current)
    (hstatus : current.status ≠ .runnable) :
    stepEval boundary before (.schedule id) =
      .refused (.invalidLifecycle id) before := by
  simp [stepEval, hfound, hstatus]

theorem stepEval_join_missing_waiter {boundary : InterruptBoundary τ}
    {before waiter target} (hmissing : before.fiber waiter = none) :
    stepEval boundary before (.join waiter target) =
      .refused (.unknownFiber waiter) before := by
  simp [stepEval, hmissing]

theorem stepEval_join_missing_target {boundary : InterruptBoundary τ}
    {before waiter target waiterState}
    (hwaiter : before.fiber waiter = some waiterState)
    (htarget : before.fiber target = none) :
    stepEval boundary before (.join waiter target) =
      .refused (.unknownFiber target) before := by
  simp [stepEval, hwaiter, htarget]

theorem stepEval_join_done {boundary : InterruptBoundary τ}
    {before waiter target waiterState targetState result}
    (hwaiter : before.fiber waiter = some waiterState)
    (htarget : before.fiber target = some targetState)
    (hne : waiter ≠ target)
    (hwaiterStatus : waiterState.status = .running \/
      waiterState.status = .waiting target)
    (htargetStatus : targetState.status = .done)
    (hterminal : before.terminal target = some result) :
    stepEval boundary before (.join waiter target) =
      .advanced (Machine.transition before
        { waiterState with status := .running }
        [.joinObserved waiter target result]) := by
  simp [stepEval, hwaiter, htarget, hne, hwaiterStatus, htargetStatus,
    hterminal]

theorem stepEval_join_done_missing_terminal {boundary : InterruptBoundary τ}
    {before waiter target waiterState targetState}
    (hwaiter : before.fiber waiter = some waiterState)
    (htarget : before.fiber target = some targetState)
    (hne : waiter ≠ target)
    (htargetStatus : targetState.status = FiberStatus.done)
    (hterminal : before.terminal target = none) :
    stepEval boundary before (.join waiter target) =
      .refused (.invalidLifecycle target) before := by
  simp [stepEval, hwaiter, htarget, hne, htargetStatus, hterminal]

theorem stepEval_join_waiting {boundary : InterruptBoundary τ}
    {before waiter target waiterState targetState}
    (hwaiter : before.fiber waiter = some waiterState)
    (htarget : before.fiber target = some targetState)
    (hne : waiter ≠ target) (htargetStatus : targetState.status ≠ .done)
    (hwaiterStatus : waiterState.status = .running) :
    stepEval boundary before (.join waiter target) =
      .advanced (Machine.transition before
        { waiterState with status := .waiting target }
        [.joinWaiting waiter target]) := by
  simp [stepEval, hwaiter, htarget, hne, htargetStatus, hwaiterStatus]

theorem stepEval_join_invalid {boundary : InterruptBoundary τ}
    {before waiter target waiterState targetState}
    (hwaiter : before.fiber waiter = some waiterState)
    (htarget : before.fiber target = some targetState)
    (hne : waiter ≠ target) (htargetStatus : targetState.status ≠ .done)
    (hwaiterStatus : waiterState.status ≠ .running) :
    stepEval boundary before (.join waiter target) =
      .refused (.invalidLifecycle waiter) before := by
  simp [stepEval, hwaiter, htarget, hne, htargetStatus, hwaiterStatus]

theorem stepEval_join_done_invalid {boundary : InterruptBoundary τ}
    {before waiter target waiterState targetState result}
    (hwaiter : before.fiber waiter = some waiterState)
    (htarget : before.fiber target = some targetState)
    (hne : waiter ≠ target) (htargetStatus : targetState.status = .done)
    (hterminal : before.terminal target = some result)
    (hnotRunning : waiterState.status ≠ .running)
    (hnotWaiting : waiterState.status ≠ .waiting target) :
    stepEval boundary before (.join waiter target) =
      .refused (.invalidLifecycle waiter) before := by
  simp [stepEval, hwaiter, htarget, hne, htargetStatus, hterminal,
    hnotRunning, hnotWaiting]

theorem stepEval_join_self_invalid {boundary : InterruptBoundary τ}
    {before id current} (hfound : before.fiber id = some current) :
    stepEval boundary before (.join id id) =
      .refused (.invalidLifecycle id) before := by
  simp [stepEval, hfound]

theorem stepEval_interrupt_missing_requester {boundary : InterruptBoundary τ}
    {before requester target} (hmissing : before.fiber requester = none) :
    stepEval boundary before (.requestInterrupt requester target) =
      .refused (.unknownFiber requester) before := by
  simp [stepEval, hmissing]

theorem stepEval_interrupt_missing_target {boundary : InterruptBoundary τ}
    {before requester target requesterState}
    (hrequester : before.fiber requester = some requesterState)
    (htarget : before.fiber target = none) :
    stepEval boundary before (.requestInterrupt requester target) =
      .refused (.unknownFiber target) before := by
  simp [stepEval, hrequester, htarget]

theorem stepEval_interrupt_masked {boundary : InterruptBoundary τ}
    {before requester target requesterState targetState}
    (hrequester : before.fiber requester = some requesterState)
    (htarget : before.fiber target = some targetState)
    (hactive : FiberStatus.Active targetState.status)
    (hmask : targetState.mask = .masked) :
    stepEval boundary before (.requestInterrupt requester target) =
      .advanced (Machine.transition before
        { targetState with interruptPending := true }
        [.interruptRequested requester target, .interruptDeferred target]) := by
  simp [stepEval, hrequester, htarget, hactive, hmask]

theorem stepEval_interrupt_unmasked {boundary : InterruptBoundary τ}
    {before requester target requesterState targetState}
    (hrequester : before.fiber requester = some requesterState)
    (htarget : before.fiber target = some targetState)
    (hactive : FiberStatus.Active targetState.status)
    (hmask : targetState.mask = .unmasked) :
    stepEval boundary before (.requestInterrupt requester target) =
      .advanced (Machine.transition before
        { targetState with status := FiberStatus.finalizing, terminal := some boundary.interrupted, interruptPending := false, cleanup := CleanupState.pending, cleanupCount := 0 }
        [.interruptRequested requester target, .interruptDelivered target]) := by
  simp [stepEval, hrequester, htarget, hactive, hmask]

theorem stepEval_interrupt_invalid {boundary : InterruptBoundary τ}
    {before requester target requesterState targetState}
    (hrequester : before.fiber requester = some requesterState)
    (htarget : before.fiber target = some targetState)
    (hinactive : Not (FiberStatus.Active targetState.status)) :
    stepEval boundary before (.requestInterrupt requester target) =
      .refused (.invalidLifecycle target) before := by
  simp [stepEval, hrequester, htarget, hinactive]

theorem stepEval_enterMask_missing {boundary : InterruptBoundary τ} {before id}
    (hmissing : before.fiber id = none) :
    stepEval boundary before (.enterMask id) =
      .refused (.unknownFiber id) before := by
  simp [stepEval, hmissing]

theorem stepEval_enterMask {boundary : InterruptBoundary τ} {before id current}
    (hfound : before.fiber id = some current)
    (hactive : FiberStatus.Active current.status)
    (hmask : current.mask = .unmasked) :
    stepEval boundary before (.enterMask id) =
      .advanced (Machine.transition before
        { current with mask := .masked } [.maskEntered id]) := by
  simp [stepEval, hfound, hactive, hmask]

theorem stepEval_enterMask_invalid {boundary : InterruptBoundary τ}
    {before id current} (hfound : before.fiber id = some current)
    (hactive : FiberStatus.Active current.status)
    (hmask : current.mask = .masked) :
    stepEval boundary before (.enterMask id) =
      .refused (.invalidLifecycle id) before := by
  simp [stepEval, hfound, hactive, hmask]

theorem stepEval_enterMask_inactive {boundary : InterruptBoundary τ}
    {before id current} (hfound : before.fiber id = some current)
    (hinactive : Not (FiberStatus.Active current.status)) :
    stepEval boundary before (.enterMask id) =
      .refused (.invalidLifecycle id) before := by
  simp [stepEval, hfound, hinactive]

theorem stepEval_exitMask_missing {boundary : InterruptBoundary τ} {before id}
    (hmissing : before.fiber id = none) :
    stepEval boundary before (.exitMask id) =
      .refused (.unknownFiber id) before := by
  simp [stepEval, hmissing]

theorem stepEval_exitMask_pending {boundary : InterruptBoundary τ}
    {before id current} (hfound : before.fiber id = some current)
    (hactive : FiberStatus.Active current.status)
    (hmask : current.mask = .masked)
    (hpending : current.interruptPending = true) :
    stepEval boundary before (.exitMask id) =
      .advanced (Machine.transition before
        { current with status := FiberStatus.finalizing, terminal := some boundary.interrupted, mask := InterruptMask.unmasked, interruptPending := false, cleanup := CleanupState.pending, cleanupCount := 0 }
        [.maskExited id, .interruptDelivered id]) := by
  simp [stepEval, hfound, hactive, hmask, hpending]

theorem stepEval_exitMask_clear {boundary : InterruptBoundary τ}
    {before id current} (hfound : before.fiber id = some current)
    (hactive : FiberStatus.Active current.status)
    (hmask : current.mask = .masked)
    (hpending : current.interruptPending = false) :
    stepEval boundary before (.exitMask id) =
      .advanced (Machine.transition before
        { current with mask := .unmasked } [.maskExited id]) := by
  simp [stepEval, hfound, hactive, hmask, hpending]

theorem stepEval_exitMask_invalid {boundary : InterruptBoundary τ}
    {before id current} (hfound : before.fiber id = some current)
    (hactive : FiberStatus.Active current.status)
    (hmask : current.mask = .unmasked) :
    stepEval boundary before (.exitMask id) =
      .refused (.invalidLifecycle id) before := by
  simp [stepEval, hfound, hactive, hmask]

theorem stepEval_exitMask_inactive {boundary : InterruptBoundary τ}
    {before id current} (hfound : before.fiber id = some current)
    (hinactive : Not (FiberStatus.Active current.status)) :
    stepEval boundary before (.exitMask id) =
      .refused (.invalidLifecycle id) before := by
  simp [stepEval, hfound, hinactive]

theorem stepEval_complete_missing {boundary : InterruptBoundary τ}
    {before id result} (hmissing : before.fiber id = none) :
    stepEval boundary before (.complete id result) =
      .refused (.unknownFiber id) before := by
  simp [stepEval, hmissing]

theorem stepEval_complete_running {boundary : InterruptBoundary τ}
    {before id current result} (hfound : before.fiber id = some current)
    (hstatus : current.status = .running) (hmask : current.mask = .unmasked)
    (hpending : current.interruptPending = false) :
    stepEval boundary before (.complete id result) =
      .advanced (Machine.transition before
        { current with status := FiberStatus.finalizing, terminal := some result, interruptPending := false, cleanup := CleanupState.pending, cleanupCount := 0 }
        [.completed id result]) := by
  simp [stepEval, hfound, hstatus, hmask, hpending]

theorem stepEval_complete_invalid {boundary : InterruptBoundary τ}
    {before id current result} (hfound : before.fiber id = some current)
    (hinvalid : Not (current.status = .running /\ current.mask = .unmasked /\
      current.interruptPending = false)) :
    stepEval boundary before (.complete id result) =
      .refused (.invalidLifecycle id) before := by
  simp [stepEval, hfound, hinvalid]

theorem stepEval_cleanup_missing {boundary : InterruptBoundary τ} {before id}
    (hmissing : before.fiber id = none) :
    stepEval boundary before (.cleanup id) =
      .refused (.unknownFiber id) before := by
  simp [stepEval, hmissing]

theorem stepEval_cleanup_ready {boundary : InterruptBoundary τ}
    {before id current result} (hfound : before.fiber id = some current)
    (hstatus : current.status = .finalizing)
    (hterminal : current.terminal = some result)
    (hcleanup : current.cleanup = .pending) :
    stepEval boundary before (.cleanup id) =
      .advanced (Machine.transition before
        { current with status := FiberStatus.done, cleanup := CleanupState.done, cleanupCount := 1 }
        [.cleanupFinished id]) := by
  simp [stepEval, hfound, hstatus, hterminal, hcleanup]

theorem stepEval_cleanup_invalid {boundary : InterruptBoundary τ}
    {before id current} (hfound : before.fiber id = some current)
    (hinvalid : Not (exists result,
      current.status = .finalizing /\ current.terminal = some result /\
        current.cleanup = .pending)) :
    stepEval boundary before (.cleanup id) =
      .refused (.invalidLifecycle id) before := by
  simp only [stepEval, hfound]
  by_cases hstatus : current.status = .finalizing
  · simp [hstatus]
    cases hterminal : current.terminal with
    | none => simp
    | some result =>
        have hcleanup : current.cleanup ≠ .pending := by
          intro hc
          exact hinvalid ⟨result, hstatus, hterminal, hc⟩
        simp [hcleanup]
  · simp [hstatus]

/-! ## Step inversion

Every advanced step rewrites exactly one fiber. `Advance` enumerates the ten
ways that can happen: which fiber was found, what replaced it, and which events
were appended. `step_shape` proves that an interpreted decision is either a
refusal that leaves the machine untouched or one of those ten advances, so the
safety theorems below case on `Advance` instead of re-walking `stepEval`.
The shape vocabulary is private: the exported interface stays the exact
interpreter equations above and the safety theorems below. -/

private inductive Advance (boundary : InterruptBoundary τ) (before : Machine τ) :
    SchedulerDecision τ -> FiberState τ -> FiberState τ -> List (Event τ) -> Prop
  | schedule {id current}
      (hfound : before.fiber id = some current)
      (hstatus : current.status = .runnable) :
      Advance boundary before (.schedule id) current
        { current with status := .running } [.scheduled id]
  | joinDone {waiter target waiterState targetState result}
      (hwaiter : before.fiber waiter = some waiterState)
      (htarget : before.fiber target = some targetState)
      (hne : waiter ≠ target)
      (hwaiterStatus : waiterState.status = .running \/
        waiterState.status = .waiting target)
      (htargetStatus : targetState.status = .done)
      (hterminal : before.terminal target = some result) :
      Advance boundary before (.join waiter target) waiterState
        { waiterState with status := .running }
        [.joinObserved waiter target result]
  | joinWaiting {waiter target waiterState targetState}
      (hwaiter : before.fiber waiter = some waiterState)
      (htarget : before.fiber target = some targetState)
      (hne : waiter ≠ target)
      (htargetStatus : targetState.status ≠ .done)
      (hwaiterStatus : waiterState.status = .running) :
      Advance boundary before (.join waiter target) waiterState
        { waiterState with status := .waiting target }
        [.joinWaiting waiter target]
  | interruptMasked {requester target requesterState targetState}
      (hrequester : before.fiber requester = some requesterState)
      (htarget : before.fiber target = some targetState)
      (hactive : FiberStatus.Active targetState.status)
      (hmask : targetState.mask = .masked) :
      Advance boundary before (.requestInterrupt requester target) targetState
        { targetState with interruptPending := true }
        [.interruptRequested requester target, .interruptDeferred target]
  | interruptUnmasked {requester target requesterState targetState}
      (hrequester : before.fiber requester = some requesterState)
      (htarget : before.fiber target = some targetState)
      (hactive : FiberStatus.Active targetState.status)
      (hmask : targetState.mask = .unmasked) :
      Advance boundary before (.requestInterrupt requester target) targetState
        { targetState with status := FiberStatus.finalizing, terminal := some boundary.interrupted, interruptPending := false, cleanup := CleanupState.pending, cleanupCount := 0 }
        [.interruptRequested requester target, .interruptDelivered target]
  | enterMask {id current}
      (hfound : before.fiber id = some current)
      (hactive : FiberStatus.Active current.status)
      (hmask : current.mask = .unmasked) :
      Advance boundary before (.enterMask id) current
        { current with mask := .masked } [.maskEntered id]
  | exitMaskPending {id current}
      (hfound : before.fiber id = some current)
      (hactive : FiberStatus.Active current.status)
      (hmask : current.mask = .masked)
      (hpending : current.interruptPending = true) :
      Advance boundary before (.exitMask id) current
        { current with status := FiberStatus.finalizing, terminal := some boundary.interrupted, mask := InterruptMask.unmasked, interruptPending := false, cleanup := CleanupState.pending, cleanupCount := 0 }
        [.maskExited id, .interruptDelivered id]
  | exitMaskClear {id current}
      (hfound : before.fiber id = some current)
      (hactive : FiberStatus.Active current.status)
      (hmask : current.mask = .masked)
      (hpending : current.interruptPending = false) :
      Advance boundary before (.exitMask id) current
        { current with mask := .unmasked } [.maskExited id]
  | complete {id current result}
      (hfound : before.fiber id = some current)
      (hstatus : current.status = .running)
      (hmask : current.mask = .unmasked)
      (hpending : current.interruptPending = false) :
      Advance boundary before (.complete id result) current
        { current with status := FiberStatus.finalizing, terminal := some result, interruptPending := false, cleanup := CleanupState.pending, cleanupCount := 0 }
        [.completed id result]
  | cleanup {id current result}
      (hfound : before.fiber id = some current)
      (hstatus : current.status = .finalizing)
      (hterminal : current.terminal = some result)
      (hcleanup : current.cleanup = .pending) :
      Advance boundary before (.cleanup id) current
        { current with status := FiberStatus.done, cleanup := CleanupState.done, cleanupCount := 1 }
        [.cleanupFinished id]

/-- One interpreted decision is a refusal at the unchanged machine or exactly
one `Advance`. This is the only place the safety proofs walk `stepEval`. -/
private theorem step_shape {boundary : InterruptBoundary τ} {before decision result}
    (hstep : Step boundary before decision result) :
    (exists reason, result = .refused reason before) \/
    (exists current replacement events,
      Advance boundary before decision current replacement events /\
      result = .advanced (Machine.transition before replacement events)) := by
  cases decision with
  | schedule id =>
      cases hfound : before.fiber id with
      | none => exact .inl ⟨_, hstep.trans (stepEval_schedule_missing hfound)⟩
      | some current =>
          by_cases hstatus : current.status = .runnable
          · exact .inr ⟨_, _, _, .schedule hfound hstatus,
              hstep.trans (stepEval_schedule_runnable hfound hstatus)⟩
          · exact .inl ⟨_, hstep.trans (stepEval_schedule_invalid hfound hstatus)⟩
  | join waiter target =>
      cases hwaiter : before.fiber waiter with
      | none => exact .inl ⟨_, hstep.trans (stepEval_join_missing_waiter hwaiter)⟩
      | some waiterState =>
          cases htarget : before.fiber target with
          | none =>
              exact .inl ⟨_, hstep.trans (stepEval_join_missing_target hwaiter htarget)⟩
          | some targetState =>
              by_cases hne : waiter = target
              · subst hne
                exact .inl ⟨_, hstep.trans (stepEval_join_self_invalid hwaiter)⟩
              by_cases hdone : targetState.status = .done
              · cases hterminal : before.terminal target with
                | none =>
                    exact .inl ⟨_, hstep.trans (stepEval_join_done_missing_terminal
                      hwaiter htarget hne hdone hterminal)⟩
                | some result =>
                    by_cases hvalid : waiterState.status = .running \/
                        waiterState.status = .waiting target
                    · exact .inr ⟨_, _, _,
                        .joinDone hwaiter htarget hne hvalid hdone hterminal,
                        hstep.trans (stepEval_join_done hwaiter htarget hne hvalid
                          hdone hterminal)⟩
                    · exact .inl ⟨_, hstep.trans (stepEval_join_done_invalid hwaiter
                        htarget hne hdone hterminal (fun h => hvalid (.inl h))
                        (fun h => hvalid (.inr h)))⟩
              · by_cases hrunning : waiterState.status = .running
                · exact .inr ⟨_, _, _,
                    .joinWaiting hwaiter htarget hne hdone hrunning,
                    hstep.trans (stepEval_join_waiting hwaiter htarget hne hdone
                      hrunning)⟩
                · exact .inl ⟨_, hstep.trans (stepEval_join_invalid hwaiter htarget
                    hne hdone hrunning)⟩
  | requestInterrupt requester target =>
      cases hrequester : before.fiber requester with
      | none =>
          exact .inl ⟨_, hstep.trans (stepEval_interrupt_missing_requester hrequester)⟩
      | some requesterState =>
          cases htarget : before.fiber target with
          | none =>
              exact .inl ⟨_, hstep.trans
                (stepEval_interrupt_missing_target hrequester htarget)⟩
          | some targetState =>
              by_cases hactive : FiberStatus.Active targetState.status
              · cases hmask : targetState.mask with
                | masked =>
                    exact .inr ⟨_, _, _,
                      .interruptMasked hrequester htarget hactive hmask,
                      hstep.trans (stepEval_interrupt_masked hrequester htarget
                        hactive hmask)⟩
                | unmasked =>
                    exact .inr ⟨_, _, _,
                      .interruptUnmasked hrequester htarget hactive hmask,
                      hstep.trans (stepEval_interrupt_unmasked hrequester htarget
                        hactive hmask)⟩
              · exact .inl ⟨_, hstep.trans
                  (stepEval_interrupt_invalid hrequester htarget hactive)⟩
  | enterMask id =>
      cases hfound : before.fiber id with
      | none => exact .inl ⟨_, hstep.trans (stepEval_enterMask_missing hfound)⟩
      | some current =>
          by_cases hactive : FiberStatus.Active current.status
          · cases hmask : current.mask with
            | unmasked =>
                exact .inr ⟨_, _, _, .enterMask hfound hactive hmask,
                  hstep.trans (stepEval_enterMask hfound hactive hmask)⟩
            | masked =>
                exact .inl ⟨_, hstep.trans
                  (stepEval_enterMask_invalid hfound hactive hmask)⟩
          · exact .inl ⟨_, hstep.trans (stepEval_enterMask_inactive hfound hactive)⟩
  | exitMask id =>
      cases hfound : before.fiber id with
      | none => exact .inl ⟨_, hstep.trans (stepEval_exitMask_missing hfound)⟩
      | some current =>
          by_cases hactive : FiberStatus.Active current.status
          · cases hmask : current.mask with
            | masked =>
                cases hpending : current.interruptPending with
                | true =>
                    exact .inr ⟨_, _, _,
                      .exitMaskPending hfound hactive hmask hpending,
                      hstep.trans (stepEval_exitMask_pending hfound hactive hmask
                        hpending)⟩
                | false =>
                    exact .inr ⟨_, _, _,
                      .exitMaskClear hfound hactive hmask hpending,
                      hstep.trans (stepEval_exitMask_clear hfound hactive hmask
                        hpending)⟩
            | unmasked =>
                exact .inl ⟨_, hstep.trans
                  (stepEval_exitMask_invalid hfound hactive hmask)⟩
          · exact .inl ⟨_, hstep.trans (stepEval_exitMask_inactive hfound hactive)⟩
  | complete id result =>
      cases hfound : before.fiber id with
      | none => exact .inl ⟨_, hstep.trans (stepEval_complete_missing hfound)⟩
      | some current =>
          by_cases hvalid : current.status = .running /\
              current.mask = .unmasked /\ current.interruptPending = false
          · exact .inr ⟨_, _, _,
              .complete hfound hvalid.1 hvalid.2.1 hvalid.2.2,
              hstep.trans (stepEval_complete_running hfound hvalid.1 hvalid.2.1
                hvalid.2.2)⟩
          · exact .inl ⟨_, hstep.trans (stepEval_complete_invalid hfound hvalid)⟩
  | cleanup id =>
      cases hfound : before.fiber id with
      | none => exact .inl ⟨_, hstep.trans (stepEval_cleanup_missing hfound)⟩
      | some current =>
          by_cases hstatus : current.status = .finalizing
          · cases hterminal : current.terminal with
            | none =>
                refine .inl ⟨_, hstep.trans (stepEval_cleanup_invalid hfound ?_)⟩
                rintro ⟨_, _, hsome, _⟩
                rw [hterminal] at hsome
                cases hsome
            | some result =>
                by_cases hcleanup : current.cleanup = .pending
                · exact .inr ⟨_, _, _,
                    .cleanup hfound hstatus hterminal hcleanup,
                    hstep.trans (stepEval_cleanup_ready hfound hstatus hterminal
                      hcleanup)⟩
                · exact .inl ⟨_, hstep.trans (stepEval_cleanup_invalid hfound
                    (fun h => h.elim fun _ hc => hcleanup hc.2.2))⟩
          · exact .inl ⟨_, hstep.trans (stepEval_cleanup_invalid hfound
              (fun h => h.elim fun _ hs => hstatus hs.1))⟩

/-- A refused decision returns the machine it was offered. -/
private theorem step_refused_inv {boundary : InterruptBoundary τ}
    {before decision reason stopped}
    (hstep : Step boundary before decision (.refused reason stopped)) :
    stopped = before := by
  rcases step_shape hstep with ⟨_, heq⟩ | ⟨_, _, _, _, heq⟩
  · exact (StepResult.refused.inj heq).2
  · cases heq

/-- An advanced decision is one of the ten `Advance` shapes. -/
private theorem step_advanced_inv {boundary : InterruptBoundary τ}
    {before decision after}
    (hstep : Step boundary before decision (.advanced after)) :
    exists current replacement events,
      Advance boundary before decision current replacement events /\
      after = Machine.transition before replacement events := by
  rcases step_shape hstep with ⟨_, heq⟩ | ⟨current, replacement, events, hadv, heq⟩
  · cases heq
  · exact ⟨current, replacement, events, hadv, StepResult.advanced.inj heq⟩

/-- Two descriptions of the same advanced step agree on the next machine. -/
private theorem step_advanced_eq {boundary : InterruptBoundary τ}
    {before decision after next}
    (hstep : Step boundary before decision (.advanced after))
    (hexact : stepEval boundary before decision = .advanced next) :
    after = next :=
  StepResult.advanced.inj (hstep.trans hexact)

/-! ## Replacement and admission lemmas -/

private theorem find_some_mem {α : Type u} (p : α -> Bool)
    {xs : List α} {a : α} (h : xs.find? p = some a) : a ∈ xs := by
  induction xs with
  | nil => simp at h
  | cons head tail ih =>
      rw [List.find?_cons] at h
      cases hp : p head <;> simp [hp] at h
      · exact List.mem_cons_of_mem head (ih h)
      · exact h ▸ List.mem_cons_self

private theorem fiber_some_mem_eq {machine : Machine τ} {id : FiberId}
    {current : FiberState τ} (h : machine.fiber id = some current) :
    current ∈ machine.fibers /\ current.id = id := by
  constructor
  · exact find_some_mem (fun fiber : FiberState τ =>
      decide (fiber.id = id)) h
  · have hp := @List.find?_some (FiberState τ)
      (fun fiber => decide (fiber.id = id)) current machine.fibers h
    exact of_decide_eq_true hp

private theorem update_find_same (xs : List (FiberState τ))
    (id : FiberId) (current replacement : FiberState τ)
    (hfound : xs.find? (fun fiber => decide (fiber.id = id)) = some current)
    (hreplacement : replacement.id = id) :
    (xs.map (fun fiber =>
      if fiber.id = replacement.id then replacement else fiber)).find?
        (fun fiber => decide (fiber.id = id)) = some replacement := by
  induction xs with
  | nil => simp at hfound
  | cons head tail ih =>
      rw [List.map_cons, List.find?_cons]
      by_cases hreplace : head.id = replacement.id
      · rw [if_pos hreplace]
        simp [hreplacement]
      · rw [if_neg hreplace]
        have hhead : head.id ≠ id := by
          intro heq
          exact hreplace (heq.trans hreplacement.symm)
        have hfalse : decide (head.id = id) = false := by simp [hhead]
        rw [hfalse]
        rw [List.find?_cons, hfalse] at hfound
        exact ih hfound

private theorem transition_fiber_same {before : Machine τ} {id : FiberId}
    {current replacement : FiberState τ}
    (hfound : before.fiber id = some current)
    (hreplacement : replacement.id = id) (events : List (Event τ)) :
    (Machine.transition before replacement events).fiber id = some replacement :=
  update_find_same before.fibers id current replacement hfound hreplacement

private theorem updated_id (replacement current : FiberState τ) :
    (if current.id = replacement.id then replacement else current).id =
      current.id := by
  by_cases h : current.id = replacement.id <;> simp [h]

private theorem transition_ids (before : Machine τ)
    (replacement : FiberState τ) (events : List (Event τ)) :
    (Machine.transition before replacement events).fibers.map FiberState.id =
      before.fibers.map FiberState.id := by
  simp only [Machine.transition_fibers, List.map_map]
  apply List.map_congr_left
  intro current _
  exact updated_id replacement current

private theorem target_survives (before : Machine τ)
    (replacement : FiberState τ) (events : List (Event τ)) {target : FiberId}
    (h : exists targetFiber, targetFiber ∈ before.fibers /\
      targetFiber.id = target) :
    exists targetFiber,
      targetFiber ∈ (Machine.transition before replacement events).fibers /\
        targetFiber.id = target := by
  rcases h with ⟨targetFiber, hmem, hid⟩
  let afterTarget :=
    if targetFiber.id = replacement.id then replacement else targetFiber
  refine ⟨afterTarget, ?_, ?_⟩
  · rw [Machine.transition_fibers]
    exact List.mem_map_of_mem hmem
  · dsimp [afterTarget]
    rw [updated_id replacement targetFiber]
    exact hid

private structure FiberCoherent (current : FiberState τ) : Prop where
  bounded : current.cleanupCount <= 1
  active : FiberStatus.Active current.status ->
    current.terminal = none /\ current.cleanup = CleanupState.notStarted /\
      current.cleanupCount = 0
  finalizing : current.status = FiberStatus.finalizing ->
    (exists result, current.terminal = some result) /\
      current.cleanup = CleanupState.pending /\ current.cleanupCount = 0
  done : current.status = FiberStatus.done ->
    (exists result, current.terminal = some result) /\
      current.cleanup = CleanupState.done /\ current.cleanupCount = 1
  pending : current.interruptPending = true ->
    current.mask = InterruptMask.masked /\ FiberStatus.Active current.status

private theorem coherent_of_mem {machine : Machine τ}
    (hwf : Machine.WellFormed machine) {current : FiberState τ}
    (hmem : current ∈ machine.fibers) : FiberCoherent current where
  bounded := hwf.cleanupBounded current hmem
  active := hwf.activeCleanup current hmem
  finalizing := hwf.finalizingCleanup current hmem
  done := hwf.doneCleanup current hmem
  pending := hwf.pendingActive current hmem

private theorem coherent_active {current : FiberState τ}
    (hactive : FiberStatus.Active current.status)
    (hterminal : current.terminal = none)
    (hcleanup : current.cleanup = CleanupState.notStarted)
    (hcount : current.cleanupCount = 0)
    (hpending : current.interruptPending = true ->
      current.mask = InterruptMask.masked) : FiberCoherent current where
  bounded := by simp [hcount]
  active := fun _ => ⟨hterminal, hcleanup, hcount⟩
  finalizing := fun h => by simp [FiberStatus.Active, h] at hactive
  done := fun h => by simp [FiberStatus.Active, h] at hactive
  pending := fun h => ⟨hpending h, hactive⟩

private theorem coherent_finalizing {current : FiberState τ} {result : τ}
    (hstatus : current.status = FiberStatus.finalizing)
    (hterminal : current.terminal = some result)
    (hcleanup : current.cleanup = CleanupState.pending)
    (hcount : current.cleanupCount = 0)
    (hpending : current.interruptPending = false) : FiberCoherent current where
  bounded := by simp [hcount]
  active := fun active => by simp [FiberStatus.Active, hstatus] at active
  finalizing := fun _ => ⟨⟨result, hterminal⟩, hcleanup, hcount⟩
  done := fun h => by cases hstatus.symm.trans h
  pending := fun h => by simp [hpending] at h

private theorem coherent_done {current : FiberState τ} {result : τ}
    (hstatus : current.status = FiberStatus.done)
    (hterminal : current.terminal = some result)
    (hcleanup : current.cleanup = CleanupState.done)
    (hcount : current.cleanupCount = 1)
    (hpending : current.interruptPending = false) : FiberCoherent current where
  bounded := by simp [hcount]
  active := fun active => by simp [FiberStatus.Active, hstatus] at active
  finalizing := fun h => by cases hstatus.symm.trans h
  done := fun _ => ⟨⟨result, hterminal⟩, hcleanup, hcount⟩
  pending := fun h => by simp [hpending] at h

private theorem pending_false_of_inactive {machine : Machine τ}
    (hwf : Machine.WellFormed machine) {current : FiberState τ}
    (hmem : current ∈ machine.fibers)
    (hinactive : Not (FiberStatus.Active current.status)) :
    current.interruptPending = false := by
  cases hp : current.interruptPending with
  | false => rfl
  | true => exact (hinactive (hwf.pendingActive current hmem hp).2).elim

private theorem coherent_active_replacement {machine : Machine τ}
    (hwf : Machine.WellFormed machine) {current replacement : FiberState τ}
    (hmem : current ∈ machine.fibers)
    (hcurrentActive : FiberStatus.Active current.status)
    (hreplacementActive : FiberStatus.Active replacement.status)
    (hterminal : replacement.terminal = current.terminal)
    (hcleanup : replacement.cleanup = current.cleanup)
    (hcount : replacement.cleanupCount = current.cleanupCount)
    (hpending : replacement.interruptPending = true ->
      replacement.mask = InterruptMask.masked) : FiberCoherent replacement := by
  rcases hwf.activeCleanup current hmem hcurrentActive with
    ⟨currentTerminal, currentCleanup, currentCount⟩
  exact coherent_active hreplacementActive
    (hterminal.trans currentTerminal) (hcleanup.trans currentCleanup)
    (hcount.trans currentCount) hpending

private theorem transition_preserves {before : Machine τ}
    (replacement : FiberState τ) (events : List (Event τ))
    (hwf : Machine.WellFormed before) (hcoherent : FiberCoherent replacement)
    (hreplacementPresent : exists source, source ∈ before.fibers /\
      source.id = replacement.id)
    (hnewOnly : forall id, id ∈ events.filterMap Event.cleanupId? ->
      id = replacement.id)
    (hcleanupUnique :
      (before.cleanupEventIds ++ events.filterMap Event.cleanupId?).Nodup)
    (hreplacementAgreement :
      (replacement.id ∈
          before.cleanupEventIds ++ events.filterMap Event.cleanupId? <->
        replacement.cleanupCount = 1))
    (hWaiting : forall target, replacement.status = FiberStatus.waiting target ->
      exists targetFiber, targetFiber ∈ before.fibers /\ targetFiber.id = target) :
    Machine.WellFormed (Machine.transition before replacement events) where
  idsUnique := by
    rw [transition_ids]
    exact hwf.idsUnique
  cleanupBounded := by
    intro after hmem
    rw [Machine.transition_fibers] at hmem
    rcases List.mem_map.mp hmem with ⟨source, hsource, rfl⟩
    by_cases hs : source.id = replacement.id
    · simpa [hs] using hcoherent.bounded
    · simpa [hs] using hwf.cleanupBounded source hsource
  cleanupEventsUnique := by
    rw [Machine.transition_cleanupEventIds]
    exact hcleanupUnique
  cleanupEventsClosed := by
    intro id hmem
    rw [Machine.transition_cleanupEventIds] at hmem
    rcases List.mem_append.mp hmem with hold | hnew
    · exact target_survives before replacement events
        (hwf.cleanupEventsClosed id hold)
    · have hid := hnewOnly id hnew
      subst id
      exact target_survives before replacement events hreplacementPresent
  cleanupEventAgreement := by
    intro after hmem
    rw [Machine.transition_fibers] at hmem
    rcases List.mem_map.mp hmem with ⟨source, hsource, rfl⟩
    rw [Machine.transition_cleanupEventIds]
    by_cases hs : source.id = replacement.id
    · simpa [hs] using hreplacementAgreement
    · have hnotNew : source.id ∉ events.filterMap Event.cleanupId? := by
        intro hnew
        exact hs (hnewOnly source.id hnew)
      simpa [hs, hnotNew] using
        hwf.cleanupEventAgreement source hsource
  activeCleanup := by
    intro after hmem hactive
    rw [Machine.transition_fibers] at hmem
    rcases List.mem_map.mp hmem with ⟨source, hsource, rfl⟩
    by_cases hs : source.id = replacement.id
    · simpa [hs] using hcoherent.active (by simpa [hs] using hactive)
    · simpa [hs] using
        hwf.activeCleanup source hsource (by simpa [hs] using hactive)
  finalizingCleanup := by
    intro after hmem hstatus
    rw [Machine.transition_fibers] at hmem
    rcases List.mem_map.mp hmem with ⟨source, hsource, rfl⟩
    by_cases hs : source.id = replacement.id
    · simpa [hs] using hcoherent.finalizing (by simpa [hs] using hstatus)
    · simpa [hs] using
        hwf.finalizingCleanup source hsource (by simpa [hs] using hstatus)
  doneCleanup := by
    intro after hmem hstatus
    rw [Machine.transition_fibers] at hmem
    rcases List.mem_map.mp hmem with ⟨source, hsource, rfl⟩
    by_cases hs : source.id = replacement.id
    · simpa [hs] using hcoherent.done (by simpa [hs] using hstatus)
    · simpa [hs] using
        hwf.doneCleanup source hsource (by simpa [hs] using hstatus)
  pendingActive := by
    intro after hmem hpending
    rw [Machine.transition_fibers] at hmem
    rcases List.mem_map.mp hmem with ⟨source, hsource, rfl⟩
    by_cases hs : source.id = replacement.id
    · simpa [hs] using hcoherent.pending (by simpa [hs] using hpending)
    · simpa [hs] using
        hwf.pendingActive source hsource (by simpa [hs] using hpending)
  waitingClosed := by
    intro after target hmem hstatus
    rw [Machine.transition_fibers] at hmem
    rcases List.mem_map.mp hmem with ⟨source, hsource, rfl⟩
    apply target_survives before replacement events
    by_cases hs : source.id = replacement.id
    · exact hWaiting target (by simpa [hs] using hstatus)
    · exact hwf.waitingClosed source target hsource (by simpa [hs] using hstatus)

private theorem transition_preserves_noCleanup {before : Machine τ}
    {current replacement : FiberState τ} (events : List (Event τ))
    (hwf : Machine.WellFormed before) (hmem : current ∈ before.fibers)
    (hid : replacement.id = current.id)
    (hcount : replacement.cleanupCount = current.cleanupCount)
    (hfilter : events.filterMap Event.cleanupId? = [])
    (hcoherent : FiberCoherent replacement)
    (hWaiting : forall target, replacement.status = FiberStatus.waiting target ->
      exists targetFiber, targetFiber ∈ before.fibers /\ targetFiber.id = target) :
    Machine.WellFormed (Machine.transition before replacement events) := by
  apply transition_preserves replacement events hwf hcoherent
  · exact ⟨current, hmem, hid.symm⟩
  · intro id hnew
    rw [hfilter] at hnew
    simp at hnew
  · rw [hfilter]
    simpa using hwf.cleanupEventsUnique
  · rw [hfilter]
    simpa only [List.append_nil, hid, hcount] using
      hwf.cleanupEventAgreement current hmem
  · exact hWaiting

private theorem transition_preserves_cleanup {before : Machine τ}
    {current replacement : FiberState τ} {id : FiberId}
    (hwf : Machine.WellFormed before) (hmem : current ∈ before.fibers)
    (hcurrentId : current.id = id) (hreplacementId : replacement.id = id)
    (hcurrentCount : current.cleanupCount = 0)
    (hreplacementCount : replacement.cleanupCount = 1)
    (hcoherent : FiberCoherent replacement)
    (hWaiting : forall target, replacement.status = FiberStatus.waiting target ->
      exists targetFiber, targetFiber ∈ before.fibers /\ targetFiber.id = target) :
    Machine.WellFormed (Machine.transition before replacement
      [Event.cleanupFinished id]) := by
  have hnotSeen : id ∉ before.cleanupEventIds := by
    intro hseen
    have hcountOne := (hwf.cleanupEventAgreement current hmem).1 (by
      simpa [hcurrentId] using hseen)
    simp [hcurrentCount] at hcountOne
  apply transition_preserves replacement [Event.cleanupFinished id]
      hwf hcoherent
  · exact ⟨current, hmem, hcurrentId.trans hreplacementId.symm⟩
  · intro observed hnew
    have : observed = id := by
      simpa [Event.cleanupId?] using hnew
    exact this.trans hreplacementId.symm
  · rw [show [Event.cleanupFinished id].filterMap Event.cleanupId? = [id] by
      rfl, List.nodup_append]
    refine ⟨hwf.cleanupEventsUnique, by simp, ?_⟩
    intro existing hexisting added hadded
    simp at hadded
    subst added
    intro heq
    subst existing
    exact hnotSeen hexisting
  · simp [Event.cleanupId?, hreplacementId, hreplacementCount]
  · exact hWaiting

/-! ## Safety of one interpreted decision -/

theorem step_deterministic {boundary : InterruptBoundary τ}
    {before decision left right}
    (hleft : Step boundary before decision left)
    (hright : Step boundary before decision right) : left = right :=
  hleft.trans hright.symm

private theorem advance_preserves_wellFormed {boundary : InterruptBoundary τ}
    {before decision current replacement events}
    (hwf : Machine.WellFormed before)
    (hadv : Advance boundary before decision current replacement events) :
    Machine.WellFormed (Machine.transition before replacement events) := by
  cases hadv with
  | schedule hfound hstatus =>
      have hmem := (fiber_some_mem_eq hfound).1
      apply transition_preserves_noCleanup
        (replacement := _) (events := _) hwf hmem <;> try rfl
      · apply coherent_active_replacement hwf hmem
          (by simp [hstatus, FiberStatus.Active])
          (by simp [FiberStatus.Active]) <;> try rfl
        intro hpending
        exact (hwf.pendingActive _ hmem hpending).1
      · intro target hwaiting
        simp at hwaiting
  | joinDone hwaiter htarget hne hvalid hdone hterminal =>
      have hmem := (fiber_some_mem_eq hwaiter).1
      have hactive : FiberStatus.Active current.status := by
        rcases hvalid with running | waiting
        · simp [running, FiberStatus.Active]
        · simp [waiting, FiberStatus.Active]
      apply transition_preserves_noCleanup
        (replacement := _) (events := _) hwf hmem <;> try rfl
      · apply coherent_active_replacement hwf hmem hactive
          (by simp [FiberStatus.Active]) <;> try rfl
        intro hpending
        exact (hwf.pendingActive _ hmem hpending).1
      · intro joined hwaiting
        simp at hwaiting
  | joinWaiting hwaiter htarget hne hdone hrunning =>
      have hwaiterMem := (fiber_some_mem_eq hwaiter).1
      apply transition_preserves_noCleanup
        (replacement := _) (events := _) hwf hwaiterMem <;> try rfl
      · apply coherent_active_replacement hwf hwaiterMem
          (by simp [hrunning, FiberStatus.Active])
          (by simp [FiberStatus.Active]) <;> try rfl
        intro hpending
        exact (hwf.pendingActive _ hwaiterMem hpending).1
      · intro joined hwaiting
        simp at hwaiting
        subst hwaiting
        exact ⟨_, (fiber_some_mem_eq htarget).1, (fiber_some_mem_eq htarget).2⟩
  | interruptMasked hrequester htarget hactive hmask =>
      have hmem := (fiber_some_mem_eq htarget).1
      apply transition_preserves_noCleanup
        (replacement := _) (events := _) hwf hmem <;> try rfl
      · apply coherent_active_replacement hwf hmem hactive
          (by simpa) <;> try rfl
        intro _
        exact hmask
      · intro joined hwaiting
        exact hwf.waitingClosed _ joined hmem (by simpa using hwaiting)
  | interruptUnmasked hrequester htarget hactive hmask =>
      have hmem := (fiber_some_mem_eq htarget).1
      have hcount := (hwf.activeCleanup _ hmem hactive).2.2
      apply transition_preserves_noCleanup
        (replacement := _) (events := _) hwf hmem
      · rfl
      · simpa using hcount.symm
      · rfl
      · exact coherent_finalizing rfl rfl rfl rfl rfl
      · intro joined hwaiting
        simp at hwaiting
  | enterMask hfound hactive hmask =>
      have hmem := (fiber_some_mem_eq hfound).1
      apply transition_preserves_noCleanup
        (replacement := _) (events := _) hwf hmem <;> try rfl
      · apply coherent_active_replacement hwf hmem hactive
          (by simpa) <;> try rfl
        intro _
        rfl
      · intro target hwaiting
        exact hwf.waitingClosed _ target hmem (by simpa using hwaiting)
  | exitMaskPending hfound hactive hmask hpending =>
      have hmem := (fiber_some_mem_eq hfound).1
      have hcount := (hwf.activeCleanup _ hmem hactive).2.2
      apply transition_preserves_noCleanup
        (replacement := _) (events := _) hwf hmem
      · rfl
      · simpa using hcount.symm
      · rfl
      · exact coherent_finalizing rfl rfl rfl rfl rfl
      · intro target hwaiting
        simp at hwaiting
  | exitMaskClear hfound hactive hmask hpending =>
      have hmem := (fiber_some_mem_eq hfound).1
      apply transition_preserves_noCleanup
        (replacement := _) (events := _) hwf hmem <;> try rfl
      · apply coherent_active_replacement hwf hmem hactive
          (by simpa) <;> try rfl
        intro impossible
        simp [hpending] at impossible
      · intro target hwaiting
        exact hwf.waitingClosed _ target hmem (by simpa using hwaiting)
  | complete hfound hstatus hmask hpending =>
      have hmem := (fiber_some_mem_eq hfound).1
      have hactive : FiberStatus.Active current.status := by
        simp [hstatus, FiberStatus.Active]
      have hcount := (hwf.activeCleanup _ hmem hactive).2.2
      apply transition_preserves_noCleanup
        (replacement := _) (events := _) hwf hmem
      · rfl
      · simpa using hcount.symm
      · rfl
      · exact coherent_finalizing rfl rfl rfl rfl rfl
      · intro target hwaiting
        simp at hwaiting
  | cleanup hfound hstatus hterminal hcleanup =>
      have hmem := (fiber_some_mem_eq hfound).1
      have hpending := pending_false_of_inactive hwf hmem
        (by simp [hstatus, FiberStatus.Active])
      have hcount := (hwf.finalizingCleanup _ hmem hstatus).2.2
      apply transition_preserves_cleanup (replacement := _) hwf hmem
      · exact (fiber_some_mem_eq hfound).2
      · simpa using (fiber_some_mem_eq hfound).2
      · exact hcount
      · rfl
      · exact coherent_done rfl hterminal rfl rfl (by simpa using hpending)
      · intro target hwaiting
        simp at hwaiting

theorem step_preserves_wellFormed {boundary : InterruptBoundary τ}
    {before decision result} (hwf : Machine.WellFormed before)
    (hstep : Step boundary before decision result) :
    Machine.WellFormed result.machine := by
  rcases step_shape hstep with ⟨_, rfl⟩ | ⟨_, _, _, hadv, rfl⟩
  · simp only [StepResult.machine]
    exact hwf
  · exact advance_preserves_wellFormed hwf hadv

/-! ## Structural finite replay -/

theorem runs_nil_iff {boundary : InterruptBoundary τ} {initial result} :
    Runs boundary initial [] result <->
      Machine.WellFormed initial /\
        ((Machine.Finished initial /\ result = ReplayResult.finished initial) \/
         (Not (Machine.Finished initial) /\
          result = ReplayResult.frontier initial)) := by
  constructor
  · rintro ⟨hwf, hresult⟩
    refine ⟨hwf, ?_⟩
    by_cases hfinished : Machine.Finished initial
    · exact Or.inl ⟨hfinished, by
        simpa [replayEval, hfinished] using hresult⟩
    · exact Or.inr ⟨hfinished, by
        simpa [replayEval, hfinished] using hresult⟩
  · rintro ⟨hwf, hfinished | hfrontier⟩
    · exact ⟨hwf, by
        rcases hfinished with ⟨hfinished, rfl⟩
        simp [replayEval, hfinished]⟩
    · exact ⟨hwf, by
        rcases hfrontier with ⟨hfrontier, rfl⟩
        simp [replayEval, hfrontier]⟩

theorem runs_cons_iff {boundary : InterruptBoundary τ}
    {initial decision tape result} :
    Runs boundary initial (decision :: tape) result <->
      Machine.WellFormed initial /\
        ((exists middle,
            Step boundary initial decision (StepResult.advanced middle) /\
            Runs boundary middle tape result) \/
         (exists refusal stopped,
            Step boundary initial decision (StepResult.refused refusal stopped) /\
            result = ReplayResult.refused refusal stopped)) := by
  constructor
  · rintro ⟨hwf, hresult⟩
    refine ⟨hwf, ?_⟩
    cases hstep : stepEval boundary initial decision with
    | advanced middle =>
        apply Or.inl
        refine ⟨middle, hstep.symm, ?_⟩
        refine ⟨step_preserves_wellFormed hwf hstep.symm, ?_⟩
        simpa [replayEval, hstep] using hresult
    | refused refusal stopped =>
        exact Or.inr ⟨refusal, stopped, hstep.symm, by
          simpa [replayEval, hstep] using hresult⟩
  · rintro ⟨hwf, hadvanced | hrefused⟩
    · rcases hadvanced with ⟨middle, hstep, hruns⟩
      refine ⟨hwf, ?_⟩
      rw [replayEval]
      rw [show stepEval boundary initial decision =
        StepResult.advanced middle from hstep.symm]
      exact hruns.2
    · rcases hrefused with ⟨refusal, stopped, hstep, rfl⟩
      refine ⟨hwf, ?_⟩
      rw [replayEval]
      rw [show stepEval boundary initial decision =
        StepResult.refused refusal stopped from hstep.symm]

theorem fixedTape_deterministic {boundary : InterruptBoundary τ}
    {initial tape left right} (hleft : Runs boundary initial tape left)
    (hright : Runs boundary initial tape right) : left = right :=
  hleft.2.trans hright.2.symm

theorem finite_replay_total (boundary : InterruptBoundary τ) {initial tape}
    (hwf : Machine.WellFormed initial) :
    exists result, Runs boundary initial tape result :=
  ⟨replayEval boundary initial tape, hwf, rfl⟩

theorem step_total (boundary : InterruptBoundary τ) {before decision}
    (_hwf : Machine.WellFormed before) :
    exists result, Step boundary before decision result :=
  ⟨stepEval boundary before decision, rfl⟩

theorem runs_preserves_wellFormed {boundary : InterruptBoundary τ}
    {initial tape result} (hwf : Machine.WellFormed initial)
    (hruns : Runs boundary initial tape result) :
    Machine.WellFormed result.machine := by
  induction tape generalizing initial result with
  | nil =>
      rcases (runs_nil_iff.mp hruns).2 with hfinished | hfrontier
      · rcases hfinished with ⟨_, rfl⟩
        exact hwf
      · rcases hfrontier with ⟨_, rfl⟩
        exact hwf
  | cons decision tape ih =>
      rcases (runs_cons_iff.mp hruns).2 with hadvanced | hrefused
      · rcases hadvanced with ⟨middle, hstep, htail⟩
        exact ih (step_preserves_wellFormed hwf hstep) htail
      · rcases hrefused with ⟨refusal, stopped, hstep, rfl⟩
        exact step_preserves_wellFormed hwf hstep

/-! ## Inhabited operational clauses -/

theorem done_join_exists (boundary : InterruptBoundary τ)
    {before waiter target waiterState targetState result}
    (_hwf : Machine.WellFormed before)
    (hwaiter : before.fiber waiter = some waiterState)
    (htarget : before.fiber target = some targetState)
    (hne : waiter ≠ target)
    (hwaiterStatus : waiterState.status = FiberStatus.running)
    (htargetStatus : targetState.status = FiberStatus.done)
    (hterminal : before.terminal target = some result) :
    exists after,
      Step boundary before (.join waiter target) (.advanced after) /\
      Event.joinObserved waiter target result ∈ after.trace := by
  let after := Machine.transition before
    { waiterState with status := FiberStatus.running }
    [Event.joinObserved waiter target result]
  refine ⟨after, ?_, ?_⟩
  · exact (stepEval_join_done hwaiter htarget hne (Or.inl hwaiterStatus)
      htargetStatus hterminal).symm
  · simp [after, Machine.transition_trace]

theorem waiting_join_exists (boundary : InterruptBoundary τ)
    {before waiter target waiterState targetState}
    (_hwf : Machine.WellFormed before)
    (hwaiter : before.fiber waiter = some waiterState)
    (htarget : before.fiber target = some targetState)
    (hne : waiter ≠ target)
    (hwaiterStatus : waiterState.status = FiberStatus.running)
    (htargetStatus : targetState.status ≠ FiberStatus.done) :
    exists after,
      Step boundary before (.join waiter target) (.advanced after) /\
      (after.fiber waiter).map FiberState.status =
        some (FiberStatus.waiting target) /\
      Event.joinWaiting waiter target ∈ after.trace := by
  let replacement := { waiterState with status := FiberStatus.waiting target }
  let after := Machine.transition before replacement [Event.joinWaiting waiter target]
  have hreplacement : replacement.id = waiter := by
    exact (fiber_some_mem_eq hwaiter).2
  have hsame : after.fiber waiter = some replacement := by
    exact transition_fiber_same hwaiter hreplacement _
  refine ⟨after, (stepEval_join_waiting hwaiter htarget hne htargetStatus
    hwaiterStatus).symm, ?_, ?_⟩
  · simp [hsame, replacement]
  · simp [after, Machine.transition_trace]

theorem masked_request_exists (boundary : InterruptBoundary τ)
    {before requester target requesterState targetState}
    (_hwf : Machine.WellFormed before)
    (hrequester : before.fiber requester = some requesterState)
    (htarget : before.fiber target = some targetState)
    (hactive : FiberStatus.Active targetState.status)
    (hmask : targetState.mask = InterruptMask.masked) :
    exists after,
      Step boundary before (.requestInterrupt requester target) (.advanced after) /\
      after.interruptPending target = some true /\
      Event.interruptDeferred target ∈ after.trace := by
  let replacement := { targetState with interruptPending := true }
  let events : List (Event τ) := [Event.interruptRequested requester target,
    Event.interruptDeferred target]
  let after := Machine.transition before replacement events
  have hreplacement : replacement.id = target := (fiber_some_mem_eq htarget).2
  have hsame : after.fiber target = some replacement :=
    transition_fiber_same htarget hreplacement events
  refine ⟨after, (stepEval_interrupt_masked hrequester htarget hactive hmask).symm,
    ?_, ?_⟩
  · simp [Machine.interruptPending, hsame, replacement]
  · simp [after, events, Machine.transition_trace]

theorem unmasked_request_exists (boundary : InterruptBoundary τ)
    {before requester target requesterState targetState}
    (_hwf : Machine.WellFormed before)
    (hrequester : before.fiber requester = some requesterState)
    (htarget : before.fiber target = some targetState)
    (hactive : FiberStatus.Active targetState.status)
    (hmask : targetState.mask = InterruptMask.unmasked) :
    exists after,
      Step boundary before (.requestInterrupt requester target) (.advanced after) /\
      after.terminal target = some boundary.interrupted /\
      (after.fiber target).map FiberState.status = some FiberStatus.finalizing /\
      Event.interruptDelivered target ∈ after.trace := by
  let replacement := { targetState with status := FiberStatus.finalizing, terminal := some boundary.interrupted, interruptPending := false, cleanup := CleanupState.pending, cleanupCount := 0 }
  let events : List (Event τ) := [Event.interruptRequested requester target,
    Event.interruptDelivered target]
  let after := Machine.transition before replacement events
  have hreplacement : replacement.id = target := (fiber_some_mem_eq htarget).2
  have hsame : after.fiber target = some replacement :=
    transition_fiber_same htarget hreplacement events
  refine ⟨after,
    (stepEval_interrupt_unmasked hrequester htarget hactive hmask).symm,
    ?_, ?_, ?_⟩
  · simp [Machine.terminal, hsame, replacement]
  · simp [hsame, replacement]
  · simp [after, events, Machine.transition_trace]

theorem enter_mask_exists (boundary : InterruptBoundary τ) {before id current}
    (_hwf : Machine.WellFormed before)
    (hfound : before.fiber id = some current)
    (hactive : FiberStatus.Active current.status)
    (hmask : current.mask = InterruptMask.unmasked) :
    exists after,
      Step boundary before (.enterMask id) (.advanced after) /\
      after.mask id = some InterruptMask.masked /\
      Event.maskEntered id ∈ after.trace := by
  let replacement := { current with mask := InterruptMask.masked }
  let after := Machine.transition before replacement [Event.maskEntered id]
  have hreplacement : replacement.id = id := (fiber_some_mem_eq hfound).2
  have hsame : after.fiber id = some replacement :=
    transition_fiber_same hfound hreplacement _
  refine ⟨after, (stepEval_enterMask hfound hactive hmask).symm, ?_, ?_⟩
  · simp [Machine.mask, hsame, replacement]
  · simp [after, Machine.transition_trace]

theorem pending_unmask_exists (boundary : InterruptBoundary τ)
    {before target current} (_hwf : Machine.WellFormed before)
    (hfound : before.fiber target = some current)
    (hactive : FiberStatus.Active current.status)
    (hmask : current.mask = InterruptMask.masked)
    (hpending : current.interruptPending = true) :
    exists after,
      Step boundary before (.exitMask target) (.advanced after) /\
      after.terminal target = some boundary.interrupted /\
      (after.fiber target).map FiberState.status = some FiberStatus.finalizing /\
      Event.interruptDelivered target ∈ after.trace := by
  let replacement := { current with status := FiberStatus.finalizing, terminal := some boundary.interrupted, mask := InterruptMask.unmasked, interruptPending := false, cleanup := CleanupState.pending, cleanupCount := 0 }
  let events : List (Event τ) :=
    [Event.maskExited target, Event.interruptDelivered target]
  let after := Machine.transition before replacement events
  have hreplacement : replacement.id = target := (fiber_some_mem_eq hfound).2
  have hsame : after.fiber target = some replacement :=
    transition_fiber_same hfound hreplacement events
  refine ⟨after, (stepEval_exitMask_pending hfound hactive hmask hpending).symm,
    ?_, ?_, ?_⟩
  · simp [Machine.terminal, hsame, replacement]
  · simp [hsame, replacement]
  · simp [after, events, Machine.transition_trace]

theorem unmask_without_pending_exists (boundary : InterruptBoundary τ)
    {before target current} (_hwf : Machine.WellFormed before)
    (hfound : before.fiber target = some current)
    (hactive : FiberStatus.Active current.status)
    (hmask : current.mask = InterruptMask.masked)
    (hpending : current.interruptPending = false) :
    exists after,
      Step boundary before (.exitMask target) (.advanced after) /\
      after.mask target = some InterruptMask.unmasked /\
      Event.maskExited target ∈ after.trace := by
  let replacement := { current with mask := InterruptMask.unmasked }
  let after := Machine.transition before replacement [Event.maskExited target]
  have hreplacement : replacement.id = target := (fiber_some_mem_eq hfound).2
  have hsame : after.fiber target = some replacement :=
    transition_fiber_same hfound hreplacement _
  refine ⟨after, (stepEval_exitMask_clear hfound hactive hmask hpending).symm,
    ?_, ?_⟩
  · simp [Machine.mask, hsame, replacement]
  · simp [after, Machine.transition_trace]

theorem completion_exists (boundary : InterruptBoundary τ)
    {before id current result} (_hwf : Machine.WellFormed before)
    (hfound : before.fiber id = some current)
    (hstatus : current.status = FiberStatus.running)
    (hmask : current.mask = InterruptMask.unmasked)
    (hpending : current.interruptPending = false) :
    exists after,
      Step boundary before (.complete id result) (.advanced after) /\
      (after.fiber id).map FiberState.status = some FiberStatus.finalizing /\
      after.terminal id = some result /\
      after.cleanupState id = some CleanupState.pending /\
      Event.completed id result ∈ after.trace := by
  let replacement := { current with status := FiberStatus.finalizing, terminal := some result, interruptPending := false, cleanup := CleanupState.pending, cleanupCount := 0 }
  let after := Machine.transition before replacement [Event.completed id result]
  have hreplacement : replacement.id = id := (fiber_some_mem_eq hfound).2
  have hsame : after.fiber id = some replacement :=
    transition_fiber_same hfound hreplacement _
  refine ⟨after,
    (stepEval_complete_running hfound hstatus hmask hpending).symm,
    ?_, ?_, ?_, ?_⟩
  · simp [hsame, replacement]
  · simp [Machine.terminal, hsame, replacement]
  · simp [Machine.cleanupState, hsame, replacement]
  · simp [after, Machine.transition_trace]

theorem cleanup_exists (boundary : InterruptBoundary τ)
    {before id current result} (_hwf : Machine.WellFormed before)
    (hfound : before.fiber id = some current)
    (hstatus : current.status = FiberStatus.finalizing)
    (hterminal : current.terminal = some result)
    (hcleanup : current.cleanup = CleanupState.pending) :
    exists after,
      Step boundary before (.cleanup id) (.advanced after) /\
      after.terminal id = some result /\
      after.cleanupState id = some CleanupState.done /\
      after.cleanupCount id = 1 /\
      Event.cleanupFinished id ∈ after.trace := by
  let replacement := { current with status := FiberStatus.done, cleanup := CleanupState.done, cleanupCount := 1 }
  let after := Machine.transition before replacement [Event.cleanupFinished id]
  have hreplacement : replacement.id = id := (fiber_some_mem_eq hfound).2
  have hsame : after.fiber id = some replacement :=
    transition_fiber_same hfound hreplacement _
  refine ⟨after, (stepEval_cleanup_ready hfound hstatus hterminal hcleanup).symm,
    ?_, ?_, ?_, ?_⟩
  · simp [Machine.terminal, hsame, replacement, hterminal]
  · simp [Machine.cleanupState, hsame, replacement]
  · simp [Machine.cleanupCount, hsame, replacement]
  · simp [after, Machine.transition_trace]

theorem unknown_schedule_refuses (boundary : InterruptBoundary τ)
    {before id} (_hwf : Machine.WellFormed before)
    (hmissing : before.fiber id = none) :
    Step boundary before (.schedule id)
      (.refused (.unknownFiber id) before) :=
  (stepEval_schedule_missing hmissing).symm

theorem invalid_completion_refuses (boundary : InterruptBoundary τ)
    {before id current result} (_hwf : Machine.WellFormed before)
    (hfound : before.fiber id = some current)
    (hinvalid : Not (current.status = FiberStatus.running /\
      current.mask = InterruptMask.unmasked /\
      current.interruptPending = false)) :
    Step boundary before (.complete id result)
      (.refused (.invalidLifecycle id) before) :=
  (stepEval_complete_invalid hfound hinvalid).symm

theorem runs_nil_finished (boundary : InterruptBoundary τ) {initial}
    (hwf : Machine.WellFormed initial) (hfinished : Machine.Finished initial) :
    Runs boundary initial [] (.finished initial) :=
  runs_nil_iff.mpr ⟨hwf, Or.inl ⟨hfinished, rfl⟩⟩

theorem runs_nil_frontier (boundary : InterruptBoundary τ) {initial}
    (hwf : Machine.WellFormed initial)
    (hfrontier : Not (Machine.Finished initial)) :
    Runs boundary initial [] (.frontier initial) :=
  runs_nil_iff.mpr ⟨hwf, Or.inr ⟨hfrontier, rfl⟩⟩

/-! ## Join, interruption, and cleanup observations -/

private theorem done_join_shape {boundary : InterruptBoundary τ}
    {before after waiter target targetState result}
    (htarget : before.fiber target = some targetState)
    (htargetStatus : targetState.status = FiberStatus.done)
    (hstep : Step boundary before (.join waiter target) (.advanced after))
    (hterminal : before.terminal target = some result) :
    exists waiterState,
      before.fiber waiter = some waiterState /\ waiter ≠ target /\
      (waiterState.status = FiberStatus.running \/
        waiterState.status = FiberStatus.waiting target) /\
      after = Machine.transition before
        { waiterState with status := FiberStatus.running }
        [Event.joinObserved waiter target result] := by
  obtain ⟨_, _, _, hadv, rfl⟩ := step_advanced_inv hstep
  cases hadv with
  | joinDone hwaiter _ hne hvalid _ hterminal' =>
      obtain rfl := Option.some.inj (hterminal'.symm.trans hterminal)
      exact ⟨_, hwaiter, hne, hvalid, rfl⟩
  | joinWaiting _ htarget' _ hnotDone _ =>
      obtain rfl := Option.some.inj (htarget'.symm.trans htarget)
      exact (hnotDone htargetStatus).elim

private theorem done_join_preserves_target {boundary : InterruptBoundary τ}
    {before after waiter target targetState result}
    (htarget : before.fiber target = some targetState)
    (htargetStatus : targetState.status = FiberStatus.done)
    (hstep : Step boundary before (.join waiter target) (.advanced after))
    (hterminal : before.terminal target = some result) :
    after.fiber target = before.fiber target := by
  rcases done_join_shape htarget htargetStatus hstep hterminal with
    ⟨waiterState, hwaiter, hne, _, rfl⟩
  apply Machine.transition_fiber_other
  simpa [(fiber_some_mem_eq hwaiter).2] using hne

theorem join_agreement {boundary : InterruptBoundary τ}
    {before after waiter target targetState result}
    (_hwf : Machine.WellFormed before)
    (htarget : before.fiber target = some targetState)
    (htargetStatus : targetState.status = FiberStatus.done)
    (hstep : Step boundary before (.join waiter target) (.advanced after))
    (hterminal : before.terminal target = some result) :
    after.terminal target = some result /\
    after.cleanupState target = before.cleanupState target /\
    after.trace = before.trace ++ [Event.joinObserved waiter target result] := by
  rcases done_join_shape htarget htargetStatus hstep hterminal with
    ⟨waiterState, hwaiter, hne, _, rfl⟩
  have hother := Machine.transition_fiber_other before
    { waiterState with status := FiberStatus.running }
    [Event.joinObserved waiter target result] target (by
      simpa [(fiber_some_mem_eq hwaiter).2] using hne)
  constructor
  · simpa [Machine.terminal, hother] using hterminal
  constructor
  · simp [Machine.cleanupState, hother]
  · rfl

theorem double_join_agreement {boundary : InterruptBoundary τ}
    {before middle after waiterOne waiterTwo target targetState result}
    (_hwf : Machine.WellFormed before)
    (htarget : before.fiber target = some targetState)
    (htargetStatus : targetState.status = FiberStatus.done)
    (_hwaiterOne : waiterOne ≠ target) (_hwaiterTwo : waiterTwo ≠ target)
    (hterminal : before.terminal target = some result)
    (hfirst : Step boundary before (.join waiterOne target) (.advanced middle))
    (hsecond : Step boundary middle (.join waiterTwo target) (.advanced after)) :
    middle.terminal target = some result /\
    after.terminal target = some result /\
    after.cleanupCount target = before.cleanupCount target := by
  have hmiddleFiber := done_join_preserves_target htarget htargetStatus hfirst hterminal
  have hmiddleTarget : middle.fiber target = some targetState := by
    rw [hmiddleFiber, htarget]
  have hmiddleTerminal : middle.terminal target = some result := by
    simpa [Machine.terminal, hmiddleFiber] using hterminal
  have hafterFiber := done_join_preserves_target hmiddleTarget htargetStatus
    hsecond hmiddleTerminal
  refine ⟨hmiddleTerminal, ?_, ?_⟩
  · simpa [Machine.terminal, hafterFiber] using hmiddleTerminal
  · simp [Machine.cleanupCount, hafterFiber, hmiddleFiber]

theorem unmasked_interrupt_delivers {boundary : InterruptBoundary τ}
    {before after requester target requesterState targetState}
    (_hwf : Machine.WellFormed before)
    (hrequester : before.fiber requester = some requesterState)
    (htarget : before.fiber target = some targetState)
    (hactive : FiberStatus.Active targetState.status)
    (hmask : targetState.mask = InterruptMask.unmasked)
    (hstep : Step boundary before (.requestInterrupt requester target)
      (.advanced after)) :
    after.terminal target = some boundary.interrupted /\
    (after.fiber target).map FiberState.status = some FiberStatus.finalizing /\
    after.cleanupState target = some CleanupState.pending := by
  let replacement := { targetState with status := FiberStatus.finalizing, terminal := some boundary.interrupted, interruptPending := false, cleanup := CleanupState.pending, cleanupCount := 0 }
  let events : List (Event τ) :=
    [.interruptRequested requester target, .interruptDelivered target]
  obtain rfl := step_advanced_eq hstep (stepEval_interrupt_unmasked hrequester htarget hactive hmask)
  have hreplacement : replacement.id = target := (fiber_some_mem_eq htarget).2
  have hsame : (Machine.transition before replacement events).fiber target =
      some replacement := transition_fiber_same htarget hreplacement events
  dsimp [replacement, events] at hsame
  exact ⟨by simp [Machine.terminal, hsame],
    by simp [hsame],
    by simp [Machine.cleanupState, hsame]⟩

theorem masked_interrupt_defers {boundary : InterruptBoundary τ}
    {before after requester target requesterState targetState}
    (_hwf : Machine.WellFormed before)
    (hrequester : before.fiber requester = some requesterState)
    (htarget : before.fiber target = some targetState)
    (hactive : FiberStatus.Active targetState.status)
    (hmask : targetState.mask = InterruptMask.masked)
    (hstep : Step boundary before (.requestInterrupt requester target)
      (.advanced after)) :
    after.interruptPending target = some true /\
      after.terminal target = before.terminal target := by
  let replacement := { targetState with interruptPending := true }
  let events : List (Event τ) :=
    [.interruptRequested requester target, .interruptDeferred target]
  obtain rfl := step_advanced_eq hstep (stepEval_interrupt_masked hrequester htarget hactive hmask)
  have hreplacement : replacement.id = target := (fiber_some_mem_eq htarget).2
  have hsame : (Machine.transition before replacement events).fiber target =
      some replacement := transition_fiber_same htarget hreplacement events
  dsimp [replacement, events] at hsame
  constructor
  · simp [Machine.interruptPending, hsame]
  · simp [Machine.terminal, hsame, htarget]

theorem unmask_delivers_pending {boundary : InterruptBoundary τ}
    {before after target current} (_hwf : Machine.WellFormed before)
    (hfound : before.fiber target = some current)
    (hactive : FiberStatus.Active current.status)
    (hmask : current.mask = InterruptMask.masked)
    (hpending : current.interruptPending = true)
    (hstep : Step boundary before (.exitMask target) (.advanced after)) :
    after.interruptPending target = some false /\
    after.mask target = some InterruptMask.unmasked /\
    after.terminal target = some boundary.interrupted /\
    (after.fiber target).map FiberState.status = some FiberStatus.finalizing := by
  let replacement := { current with status := FiberStatus.finalizing, terminal := some boundary.interrupted, mask := InterruptMask.unmasked, interruptPending := false, cleanup := CleanupState.pending, cleanupCount := 0 }
  let events : List (Event τ) := [.maskExited target, .interruptDelivered target]
  obtain rfl := step_advanced_eq hstep (stepEval_exitMask_pending hfound hactive hmask hpending)
  have hreplacement : replacement.id = target := (fiber_some_mem_eq hfound).2
  have hsame : (Machine.transition before replacement events).fiber target =
      some replacement := transition_fiber_same hfound hreplacement events
  dsimp [replacement, events] at hsame
  exact ⟨by simp [Machine.interruptPending, hsame],
    by simp [Machine.mask, hsame],
    by simp [Machine.terminal, hsame],
    by simp [hsame]⟩

theorem cleanup_preserves_terminal {boundary : InterruptBoundary τ}
    {before after id current terminal}
    (_hwf : Machine.WellFormed before)
    (hfound : before.fiber id = some current)
    (hstatus : current.status = FiberStatus.finalizing)
    (hterminal : current.terminal = some terminal)
    (hcleanup : current.cleanup = CleanupState.pending)
    (hstep : Step boundary before (.cleanup id) (.advanced after)) :
    after.terminal id = some terminal /\
    (after.fiber id).map FiberState.status = some FiberStatus.done /\
    after.cleanupState id = some CleanupState.done /\
    after.cleanupCount id = 1 /\
    after.trace = before.trace ++ [Event.cleanupFinished id] := by
  let replacement := { current with status := FiberStatus.done, cleanup := CleanupState.done, cleanupCount := 1 }
  let events : List (Event τ) := [.cleanupFinished id]
  obtain rfl := step_advanced_eq hstep (stepEval_cleanup_ready hfound hstatus hterminal hcleanup)
  have hreplacement : replacement.id = id := (fiber_some_mem_eq hfound).2
  have hsame : (Machine.transition before replacement events).fiber id =
      some replacement := transition_fiber_same hfound hreplacement events
  dsimp [replacement, events] at hsame
  constructor
  · rw [Machine.terminal, hsame]
    exact hterminal
  constructor
  · rw [hsame]
    rfl
  constructor
  · rw [Machine.cleanupState, hsame]
    rfl
  constructor
  · rw [Machine.cleanupCount, hsame]
    rfl
  · rfl

theorem cleanup_at_most_once {boundary : InterruptBoundary τ}
    {initial tape result id} (hwf : Machine.WellFormed initial)
    (hruns : Runs boundary initial tape result) :
    result.machine.cleanupCount id <= 1 := by
  have hfinal := runs_preserves_wellFormed hwf hruns
  cases hfound : result.machine.fiber id with
  | none => simp [Machine.cleanupCount, hfound]
  | some current =>
      have hmem := (fiber_some_mem_eq hfound).1
      simpa [Machine.cleanupCount, hfound] using
        hfinal.cleanupBounded current hmem

theorem cleanup_events_at_most_once {boundary : InterruptBoundary τ}
    {initial tape result} (hwf : Machine.WellFormed initial)
    (hruns : Runs boundary initial tape result) :
    result.machine.cleanupEventIds.Nodup :=
  (runs_preserves_wellFormed hwf hruns).cleanupEventsUnique

theorem cleanup_events_agree {boundary : InterruptBoundary τ}
    {initial tape result} (hwf : Machine.WellFormed initial)
    (hruns : Runs boundary initial tape result) :
    forall current, current ∈ result.machine.fibers ->
      (current.id ∈ result.machine.cleanupEventIds <->
        current.cleanupCount = 1) :=
  (runs_preserves_wellFormed hwf hruns).cleanupEventAgreement

private theorem transition_cleanupCount_mono {before : Machine τ}
    {id : FiberId} {current replacement : FiberState τ}
    (events : List (Event τ)) (hfound : before.fiber id = some current)
    (hreplacement : replacement.id = id)
    (hcount : current.cleanupCount <= replacement.cleanupCount)
    (observed : FiberId) :
    before.cleanupCount observed <=
      (Machine.transition before replacement events).cleanupCount observed := by
  by_cases hsame : replacement.id = observed
  · rw [← hsame]
    have hfound' : before.fiber replacement.id = some current := by
      simpa [hreplacement] using hfound
    have hafter : (Machine.transition before replacement events).fiber
        replacement.id = some replacement := by
      simpa [hreplacement] using
        transition_fiber_same hfound hreplacement events
    simpa [Machine.cleanupCount, hfound', hafter] using hcount
  · have hother := Machine.transition_fiber_other before replacement events
      observed hsame
    simp [Machine.cleanupCount, hother]

/-- The fiber an `Advance` rewrites is present, and the replacement keeps its id. -/
private theorem Advance.found {boundary : InterruptBoundary τ}
    {before decision current replacement events}
    (hadv : Advance boundary before decision current replacement events) :
    exists id, before.fiber id = some current /\ replacement.id = id := by
  cases hadv with
  | schedule hfound _ => exact ⟨_, hfound, (fiber_some_mem_eq hfound).2⟩
  | joinDone hwaiter _ _ _ _ _ => exact ⟨_, hwaiter, (fiber_some_mem_eq hwaiter).2⟩
  | joinWaiting hwaiter _ _ _ _ => exact ⟨_, hwaiter, (fiber_some_mem_eq hwaiter).2⟩
  | interruptMasked _ htarget _ _ => exact ⟨_, htarget, (fiber_some_mem_eq htarget).2⟩
  | interruptUnmasked _ htarget _ _ => exact ⟨_, htarget, (fiber_some_mem_eq htarget).2⟩
  | enterMask hfound _ _ => exact ⟨_, hfound, (fiber_some_mem_eq hfound).2⟩
  | exitMaskPending hfound _ _ _ => exact ⟨_, hfound, (fiber_some_mem_eq hfound).2⟩
  | exitMaskClear hfound _ _ _ => exact ⟨_, hfound, (fiber_some_mem_eq hfound).2⟩
  | complete hfound _ _ _ => exact ⟨_, hfound, (fiber_some_mem_eq hfound).2⟩
  | cleanup hfound _ _ _ => exact ⟨_, hfound, (fiber_some_mem_eq hfound).2⟩

/-- No `Advance` lowers the rewritten fiber's cleanup count. -/
private theorem Advance.cleanupCount_le {boundary : InterruptBoundary τ}
    {before decision current replacement events}
    (hwf : Machine.WellFormed before)
    (hadv : Advance boundary before decision current replacement events) :
    current.cleanupCount <= replacement.cleanupCount := by
  cases hadv with
  | schedule _ _ => exact Nat.le_refl _
  | joinDone _ _ _ _ _ _ => exact Nat.le_refl _
  | joinWaiting _ _ _ _ _ => exact Nat.le_refl _
  | interruptMasked _ _ _ _ => exact Nat.le_refl _
  | enterMask _ _ _ => exact Nat.le_refl _
  | exitMaskClear _ _ _ _ => exact Nat.le_refl _
  | interruptUnmasked _ htarget hactive _ =>
      have hzero := (hwf.activeCleanup _ (fiber_some_mem_eq htarget).1 hactive).2.2
      simp [hzero]
  | exitMaskPending hfound hactive _ _ =>
      have hzero := (hwf.activeCleanup _ (fiber_some_mem_eq hfound).1 hactive).2.2
      simp [hzero]
  | complete hfound hstatus _ _ =>
      have hzero := (hwf.activeCleanup _ (fiber_some_mem_eq hfound).1
        (by simp [hstatus, FiberStatus.Active])).2.2
      simp [hzero]
  | cleanup hfound _ _ _ =>
      exact hwf.cleanupBounded _ (fiber_some_mem_eq hfound).1

private theorem advance_cleanupCount_mono {boundary : InterruptBoundary τ}
    {before decision current replacement events}
    (hwf : Machine.WellFormed before)
    (hadv : Advance boundary before decision current replacement events)
    (observed : FiberId) :
    before.cleanupCount observed <=
      (Machine.transition before replacement events).cleanupCount observed := by
  obtain ⟨id, hfound, hid⟩ := Advance.found hadv
  exact transition_cleanupCount_mono events hfound hid
    (Advance.cleanupCount_le hwf hadv) observed

theorem cleanup_count_monotone {boundary : InterruptBoundary τ}
    {before decision result id} (hwf : Machine.WellFormed before)
    (hstep : Step boundary before decision result) :
    before.cleanupCount id <= result.machine.cleanupCount id := by
  rcases step_shape hstep with ⟨_, rfl⟩ | ⟨_, _, _, hadv, rfl⟩
  · exact Nat.le_refl _
  · exact advance_cleanupCount_mono hwf hadv id

private theorem replay_finished_implies_finished
    (boundary : InterruptBoundary τ) (initial : Machine τ)
    (tape : DecisionTape τ) (final : Machine τ)
    (hresult : replayEval boundary initial tape = ReplayResult.finished final) :
    Machine.Finished final := by
  induction tape generalizing initial with
  | nil =>
      by_cases hfinished : Machine.Finished initial
      · simp [replayEval, hfinished] at hresult
        cases hresult
        exact hfinished
      · simp [replayEval, hfinished] at hresult
  | cons decision tape ih =>
      cases hstep : stepEval boundary initial decision with
      | advanced middle =>
          exact ih middle (by simpa [replayEval, hstep] using hresult)
      | refused refusal stopped =>
          simp [replayEval, hstep] at hresult

theorem cleanup_safe_on_finish {boundary : InterruptBoundary τ}
    {initial tape final id terminal}
    (hwf : Machine.WellFormed initial)
    (hruns : Runs boundary initial tape (ReplayResult.finished final))
    (hterminal : final.terminal id = some terminal) :
    final.cleanupState id = some CleanupState.done /\
      final.cleanupCount id = 1 := by
  have hfinalWf := runs_preserves_wellFormed hwf hruns
  have hfinished := replay_finished_implies_finished boundary initial tape final
    hruns.2.symm
  cases hfound : final.fiber id with
  | none => simp [Machine.terminal, hfound] at hterminal
  | some current =>
      have hmem := (fiber_some_mem_eq hfound).1
      have hdone := hfinished current hmem
      have hcleanup := hfinalWf.doneCleanup current hmem hdone
      exact ⟨by simp [Machine.cleanupState, hfound, hcleanup.2.1],
        by simp [Machine.cleanupCount, hfound, hcleanup.2.2]⟩

/-! ## Ground machines used by non-vacuity and ordering witnesses -/

private def witnessRequesterId : FiberId := ⟨0⟩
private def witnessTargetId : FiberId := ⟨1⟩

private def witnessActive (id : FiberId)
    (mask : InterruptMask := InterruptMask.unmasked)
    (pending : Bool := false) : FiberState τ :=
  { id := id
    status := FiberStatus.running
    terminal := none
    mask := mask
    interruptPending := pending
    cleanup := CleanupState.notStarted
    cleanupCount := 0 }

private def witnessRunnable (id : FiberId) : FiberState τ :=
  { witnessActive id with status := FiberStatus.runnable }

private def witnessFinalizing (id : FiberId) (result : τ) : FiberState τ :=
  { id := id
    status := FiberStatus.finalizing
    terminal := some result
    mask := InterruptMask.unmasked
    interruptPending := false
    cleanup := CleanupState.pending
    cleanupCount := 0 }

private def witnessDone (id : FiberId) (result : τ) : FiberState τ :=
  { id := id
    status := FiberStatus.done
    terminal := some result
    mask := InterruptMask.unmasked
    interruptPending := false
    cleanup := CleanupState.done
    cleanupCount := 1 }

private def witnessMachine (fibers : List (FiberState τ)) : Machine τ :=
  ⟨fibers, []⟩

private def witnessDoneMachine (result : τ) : Machine τ :=
  ⟨[witnessActive witnessRequesterId,
      witnessDone witnessTargetId result],
    [Event.cleanupFinished witnessTargetId]⟩

private theorem witnessMachine_wellFormed {fibers : List (FiberState τ)}
    (hids : (fibers.map FiberState.id).Nodup)
    (hcoherent : forall current, current ∈ fibers -> FiberCoherent current)
    (hcountZero : forall current, current ∈ fibers ->
      current.cleanupCount = 0)
    (hnoWaiting : forall current, current ∈ fibers -> forall target,
      current.status ≠ FiberStatus.waiting target) :
    Machine.WellFormed (witnessMachine fibers) where
  idsUnique := hids
  cleanupBounded := by
    intro current hmem
    exact (hcoherent current hmem).bounded
  cleanupEventsUnique := by
    simp [witnessMachine, Machine.cleanupEventIds]
  cleanupEventsClosed := by
    simp [witnessMachine, Machine.cleanupEventIds]
  cleanupEventAgreement := by
    intro current hmem
    simp [witnessMachine, Machine.cleanupEventIds, hcountZero current hmem]
  activeCleanup := by
    intro current hmem
    exact (hcoherent current hmem).active
  finalizingCleanup := by
    intro current hmem
    exact (hcoherent current hmem).finalizing
  doneCleanup := by
    intro current hmem
    exact (hcoherent current hmem).done
  pendingActive := by
    intro current hmem
    exact (hcoherent current hmem).pending
  waitingClosed := by
    intro current target hmem hstatus
    exact False.elim (hnoWaiting current hmem target hstatus)

private theorem witnessActive_coherent (id : FiberId) (mask : InterruptMask) :
    FiberCoherent (witnessActive (τ := τ) id mask false) := by
  constructor <;> simp [witnessActive, FiberStatus.Active]

private theorem witnessPending_coherent (id : FiberId) :
    FiberCoherent (witnessActive (τ := τ) id InterruptMask.masked true) := by
  constructor <;> simp [witnessActive, FiberStatus.Active]

private theorem witnessRunnable_coherent (id : FiberId) :
    FiberCoherent (witnessRunnable (τ := τ) id) := by
  constructor <;> simp [witnessRunnable, witnessActive, FiberStatus.Active]

private theorem witnessFinalizing_coherent (id : FiberId) (result : τ) :
    FiberCoherent (witnessFinalizing id result) := by
  constructor <;> simp [witnessFinalizing, FiberStatus.Active]

private theorem witnessDone_coherent (id : FiberId) (result : τ) :
    FiberCoherent (witnessDone id result) := by
  constructor <;> simp [witnessDone, FiberStatus.Active]

private theorem witnessDoneMachine_wellFormed (result : τ) :
    Machine.WellFormed (witnessDoneMachine result) where
  idsUnique := by
    simp [witnessDoneMachine, witnessActive, witnessDone,
      witnessRequesterId, witnessTargetId]
  cleanupBounded := by
    simp [witnessDoneMachine, witnessActive, witnessDone]
  cleanupEventsUnique := by
    simp [witnessDoneMachine, Machine.cleanupEventIds, Event.cleanupId?]
  cleanupEventsClosed := by
    intro id hmem
    simp [witnessDoneMachine, Machine.cleanupEventIds,
      Event.cleanupId?] at hmem
    subst id
    exact ⟨witnessDone witnessTargetId result,
      by simp [witnessDoneMachine], rfl⟩
  cleanupEventAgreement := by
    intro current hmem
    simp [witnessDoneMachine] at hmem
    rcases hmem with rfl | rfl
    · simp [witnessDoneMachine, Machine.cleanupEventIds, Event.cleanupId?,
        witnessActive, witnessRequesterId, witnessTargetId]
    · simp [witnessDoneMachine, Machine.cleanupEventIds, Event.cleanupId?,
        witnessDone]
  activeCleanup := by
    simp [witnessDoneMachine, witnessActive, witnessDone,
      FiberStatus.Active]
  finalizingCleanup := by
    simp [witnessDoneMachine, witnessActive, witnessDone]
  doneCleanup := by
    simp [witnessDoneMachine, witnessActive, witnessDone]
  pendingActive := by
    simp [witnessDoneMachine, witnessActive, witnessDone]
  waitingClosed := by
    intro current target hmem hstatus
    simp [witnessDoneMachine] at hmem
    rcases hmem with rfl | rfl <;>
      simp [witnessActive, witnessDone] at hstatus

private theorem witnessSingle_wellFormed {current : FiberState τ}
    (hcoherent : FiberCoherent current)
    (hcount : current.cleanupCount = 0)
    (hnoWaiting : forall target,
      current.status ≠ FiberStatus.waiting target) :
    Machine.WellFormed (witnessMachine [current]) := by
  apply witnessMachine_wellFormed
  · simp
  · intro candidate hmem
    simp at hmem
    subst candidate
    exact hcoherent
  · intro candidate hmem
    simp at hmem
    subst candidate
    exact hcount
  · intro candidate hmem target
    simp at hmem
    subst candidate
    exact hnoWaiting target

private theorem witnessPair_wellFormed {left right : FiberState τ}
    (hids : left.id ≠ right.id)
    (hleft : FiberCoherent left) (hright : FiberCoherent right)
    (hleftCount : left.cleanupCount = 0)
    (hrightCount : right.cleanupCount = 0)
    (hleftNoWaiting : forall target,
      left.status ≠ FiberStatus.waiting target)
    (hrightNoWaiting : forall target,
      right.status ≠ FiberStatus.waiting target) :
    Machine.WellFormed (witnessMachine [left, right]) := by
  apply witnessMachine_wellFormed
  · simp [hids]
  · intro candidate hmem
    simp at hmem
    rcases hmem with rfl | rfl
    · exact hleft
    · exact hright
  · intro candidate hmem
    simp at hmem
    rcases hmem with rfl | rfl
    · exact hleftCount
    · exact hrightCount
  · intro candidate hmem target
    simp at hmem
    rcases hmem with rfl | rfl
    · exact hleftNoWaiting target
    · exact hrightNoWaiting target

private def witnessOrderInitial : Machine τ :=
  witnessMachine [witnessActive witnessRequesterId,
    witnessActive witnessTargetId]

private theorem witnessOrderInitial_wellFormed :
    Machine.WellFormed (witnessOrderInitial : Machine τ) where
  idsUnique := by
    simp [witnessOrderInitial, witnessMachine, witnessActive,
      witnessRequesterId, witnessTargetId]
  cleanupBounded := by
    simp [witnessOrderInitial, witnessMachine, witnessActive]
  cleanupEventsUnique := by
    simp [witnessOrderInitial, witnessMachine, Machine.cleanupEventIds]
  cleanupEventsClosed := by
    simp [witnessOrderInitial, witnessMachine, Machine.cleanupEventIds]
  cleanupEventAgreement := by
    intro current hmem
    simp [witnessOrderInitial, witnessMachine] at hmem
    rcases hmem with rfl | rfl <;>
      simp [witnessOrderInitial, witnessMachine, Machine.cleanupEventIds,
        witnessActive]
  activeCleanup := by
    simp [witnessOrderInitial, witnessMachine, witnessActive,
      FiberStatus.Active]
  finalizingCleanup := by
    simp [witnessOrderInitial, witnessMachine, witnessActive]
  doneCleanup := by
    simp [witnessOrderInitial, witnessMachine, witnessActive]
  pendingActive := by
    simp [witnessOrderInitial, witnessMachine, witnessActive]
  waitingClosed := by
    intro current target hmem hstatus
    simp [witnessOrderInitial, witnessMachine, witnessActive] at hmem
    rcases hmem with rfl | rfl <;> simp at hstatus

theorem representative_inputs_exist (boundary : InterruptBoundary τ) :
    (exists (before : Machine τ) (id : FiberId) (fiber : FiberState τ),
      Machine.WellFormed before /\ before.fiber id = some fiber /\
        fiber.status = FiberStatus.runnable) /\
    (exists (before : Machine τ) (waiter target : FiberId)
      (waiterState targetState : FiberState τ) (result : τ),
      Machine.WellFormed before /\
      before.fiber waiter = some waiterState /\
      before.fiber target = some targetState /\
      waiter ≠ target /\
      waiterState.status = FiberStatus.running /\
      targetState.status = FiberStatus.done /\
      before.terminal target = some result) /\
    (exists (before : Machine τ) (waiter target : FiberId)
      (waiterState targetState : FiberState τ),
      Machine.WellFormed before /\
      before.fiber waiter = some waiterState /\
      before.fiber target = some targetState /\
      waiter ≠ target /\
      waiterState.status = FiberStatus.running /\
      targetState.status ≠ FiberStatus.done) /\
    (exists (before : Machine τ) (requester target : FiberId)
      (requesterState targetState : FiberState τ),
      Machine.WellFormed before /\
      before.fiber requester = some requesterState /\
      before.fiber target = some targetState /\
      FiberStatus.Active targetState.status /\
      targetState.mask = InterruptMask.masked) /\
    (exists (before : Machine τ) (requester target : FiberId)
      (requesterState targetState : FiberState τ),
      Machine.WellFormed before /\
      before.fiber requester = some requesterState /\
      before.fiber target = some targetState /\
      FiberStatus.Active targetState.status /\
      targetState.mask = InterruptMask.unmasked) /\
    (exists (before : Machine τ) (target : FiberId) (fiber : FiberState τ),
      Machine.WellFormed before /\
      before.fiber target = some fiber /\
      FiberStatus.Active fiber.status /\
      fiber.mask = InterruptMask.masked /\
      fiber.interruptPending = true) /\
    (exists (before : Machine τ) (target : FiberId) (fiber : FiberState τ),
      Machine.WellFormed before /\
      before.fiber target = some fiber /\
      FiberStatus.Active fiber.status /\
      fiber.mask = InterruptMask.masked /\
      fiber.interruptPending = false) /\
    (exists (before : Machine τ) (id : FiberId) (fiber : FiberState τ),
      Machine.WellFormed before /\ before.fiber id = some fiber /\
        fiber.status = FiberStatus.running /\
        fiber.mask = InterruptMask.unmasked /\
        fiber.interruptPending = false) /\
    (exists (before : Machine τ) (id : FiberId) (fiber : FiberState τ)
      (result : τ),
      Machine.WellFormed before /\ before.fiber id = some fiber /\
      fiber.status = FiberStatus.finalizing /\
      fiber.terminal = some result /\
      fiber.cleanup = CleanupState.pending) /\
    (exists (before : Machine τ) (id : FiberId),
      Machine.WellFormed before /\ before.fiber id = none) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · refine ⟨witnessMachine [witnessRunnable witnessTargetId],
      witnessTargetId, witnessRunnable witnessTargetId, ?_, rfl, rfl⟩
    exact witnessSingle_wellFormed (witnessRunnable_coherent witnessTargetId)
      rfl
      (by intro target; simp [witnessRunnable, witnessActive])
  · refine ⟨witnessDoneMachine boundary.interrupted,
      witnessRequesterId, witnessTargetId,
      witnessActive witnessRequesterId,
      witnessDone witnessTargetId boundary.interrupted,
      boundary.interrupted, ?_, rfl, rfl, ?_, rfl, rfl, rfl⟩
    · exact witnessDoneMachine_wellFormed boundary.interrupted
    · decide
  · refine ⟨witnessMachine
        [witnessActive witnessRequesterId, witnessRunnable witnessTargetId],
      witnessRequesterId, witnessTargetId,
      witnessActive witnessRequesterId, witnessRunnable witnessTargetId,
      ?_, rfl, rfl, ?_, rfl, ?_⟩
    · exact witnessPair_wellFormed (by
          simp [witnessActive, witnessRunnable, witnessRequesterId,
            witnessTargetId])
        (witnessActive_coherent witnessRequesterId InterruptMask.unmasked)
        (witnessRunnable_coherent witnessTargetId)
        rfl rfl
        (by intro target; simp [witnessActive])
        (by intro target; simp [witnessRunnable, witnessActive])
    · simp [witnessRequesterId, witnessTargetId]
    · simp [witnessRunnable, witnessActive]
  · refine ⟨witnessMachine
        [witnessActive witnessRequesterId,
          witnessActive witnessTargetId InterruptMask.masked false],
      witnessRequesterId, witnessTargetId,
      witnessActive witnessRequesterId,
      witnessActive witnessTargetId InterruptMask.masked false,
      ?_, rfl, rfl, ?_, rfl⟩
    · exact witnessPair_wellFormed (by
          simp [witnessActive, witnessRequesterId, witnessTargetId])
        (witnessActive_coherent witnessRequesterId InterruptMask.unmasked)
        (witnessActive_coherent witnessTargetId InterruptMask.masked)
        rfl rfl
        (by intro target; simp [witnessActive])
        (by intro target; simp [witnessActive])
    · simp [witnessActive, FiberStatus.Active]
  · refine ⟨witnessOrderInitial, witnessRequesterId, witnessTargetId,
      witnessActive witnessRequesterId, witnessActive witnessTargetId,
      witnessOrderInitial_wellFormed, rfl, rfl, ?_, rfl⟩
    simp [witnessActive, FiberStatus.Active]
  · refine ⟨witnessMachine
        [witnessActive witnessTargetId InterruptMask.masked true],
      witnessTargetId,
      witnessActive witnessTargetId InterruptMask.masked true,
      ?_, rfl, ?_, rfl, rfl⟩
    · exact witnessSingle_wellFormed (witnessPending_coherent witnessTargetId)
        rfl
        (by intro target; simp [witnessActive])
    · simp [witnessActive, FiberStatus.Active]
  · refine ⟨witnessMachine
        [witnessActive witnessTargetId InterruptMask.masked false],
      witnessTargetId,
      witnessActive witnessTargetId InterruptMask.masked false,
      ?_, rfl, ?_, rfl, rfl⟩
    · exact witnessSingle_wellFormed
        (witnessActive_coherent witnessTargetId InterruptMask.masked)
        rfl
        (by intro target; simp [witnessActive])
    · simp [witnessActive, FiberStatus.Active]
  · refine ⟨witnessMachine [witnessActive witnessTargetId],
      witnessTargetId, witnessActive witnessTargetId, ?_, rfl,
      rfl, rfl, rfl⟩
    exact witnessSingle_wellFormed
      (witnessActive_coherent witnessTargetId InterruptMask.unmasked)
      rfl
      (by intro target; simp [witnessActive])
  · refine ⟨witnessMachine
        [witnessFinalizing witnessTargetId boundary.interrupted],
      witnessTargetId,
      witnessFinalizing witnessTargetId boundary.interrupted,
      boundary.interrupted, ?_, rfl, rfl, rfl, rfl⟩
    exact witnessSingle_wellFormed
      (witnessFinalizing_coherent witnessTargetId boundary.interrupted)
      rfl
      (by intro target; simp [witnessFinalizing])
  · refine ⟨witnessMachine [], witnessTargetId, ?_, rfl⟩
    exact witnessMachine_wellFormed (by simp) (by simp) (by simp) (by simp)

private def witnessFinishedInitial : Machine τ :=
  witnessMachine [witnessActive witnessTargetId]

private def witnessFinishedMiddle (boundary : InterruptBoundary τ) : Machine τ :=
  Machine.transition witnessFinishedInitial
    (witnessFinalizing witnessTargetId boundary.interrupted)
    [.completed witnessTargetId boundary.interrupted]

private def witnessFinishedFinal (boundary : InterruptBoundary τ) : Machine τ :=
  Machine.transition (witnessFinishedMiddle boundary)
    (witnessDone witnessTargetId boundary.interrupted)
    [.cleanupFinished witnessTargetId]

private theorem witnessFinishedInitial_wellFormed :
    Machine.WellFormed (witnessFinishedInitial : Machine τ) := by
  exact witnessSingle_wellFormed
    (witnessActive_coherent witnessTargetId InterruptMask.unmasked)
    rfl
    (by intro target; simp [witnessActive])

theorem exists_representative_finished_run (boundary : InterruptBoundary τ) :
    exists initial tape final,
      Machine.WellFormed initial /\ tape ≠ [] /\
        Runs boundary initial tape (ReplayResult.finished final) := by
  refine ⟨witnessFinishedInitial,
    [.complete witnessTargetId boundary.interrupted,
      .cleanup witnessTargetId],
    witnessFinishedFinal boundary,
    witnessFinishedInitial_wellFormed, by simp, ?_⟩
  exact ⟨witnessFinishedInitial_wellFormed, rfl⟩

private theorem witnessOrder_left (boundary : InterruptBoundary τ) :
    replayEval boundary witnessOrderInitial
      [.requestInterrupt witnessRequesterId witnessTargetId,
        .complete witnessTargetId boundary.interrupted] =
      .refused (.invalidLifecycle witnessTargetId)
        (Machine.transition witnessOrderInitial
          { witnessActive (τ := τ) witnessTargetId with
            status := FiberStatus.finalizing
            terminal := some boundary.interrupted
            interruptPending := false
            cleanup := CleanupState.pending
            cleanupCount := 0 }
          [.interruptRequested witnessRequesterId witnessTargetId,
            .interruptDelivered witnessTargetId]) := by
  rfl

private theorem witnessOrder_right (boundary : InterruptBoundary τ) :
    replayEval boundary witnessOrderInitial
      [.complete witnessTargetId boundary.interrupted,
        .requestInterrupt witnessRequesterId witnessTargetId] =
      .refused (.invalidLifecycle witnessTargetId)
        (Machine.transition witnessOrderInitial
          { witnessActive (τ := τ) witnessTargetId with
            status := FiberStatus.finalizing
            terminal := some boundary.interrupted
            interruptPending := false
            cleanup := CleanupState.pending
            cleanupCount := 0 }
          [.completed witnessTargetId boundary.interrupted]) := by
  rfl

private theorem witnessOrder_distinct (boundary : InterruptBoundary τ) :
    replayEval boundary witnessOrderInitial
      [.requestInterrupt witnessRequesterId witnessTargetId,
        .complete witnessTargetId boundary.interrupted] ≠
    replayEval boundary witnessOrderInitial
      [.complete witnessTargetId boundary.interrupted,
        .requestInterrupt witnessRequesterId witnessTargetId] := by
  rw [witnessOrder_left, witnessOrder_right]
  intro equal
  have machinesEqual := congrArg ReplayResult.machine equal
  have tracesEqual := congrArg Machine.trace machinesEqual
  simp [ReplayResult.machine, Machine.transition, witnessOrderInitial,
    witnessMachine] at tracesEqual

theorem interrupt_complete_order_distinct (boundary : InterruptBoundary τ) :
    exists initial requester target success left right,
      Machine.WellFormed initial /\
      Runs boundary initial
        [.requestInterrupt requester target,
          .complete target success] left /\
      Runs boundary initial
        [.complete target success,
          .requestInterrupt requester target] right /\
      left ≠ right := by
  refine ⟨witnessOrderInitial, witnessRequesterId, witnessTargetId,
    boundary.interrupted,
    replayEval boundary witnessOrderInitial
      [.requestInterrupt witnessRequesterId witnessTargetId,
        .complete witnessTargetId boundary.interrupted],
    replayEval boundary witnessOrderInitial
      [.complete witnessTargetId boundary.interrupted,
        .requestInterrupt witnessRequesterId witnessTargetId],
    witnessOrderInitial_wellFormed, ?_, ?_, witnessOrder_distinct boundary⟩
  · exact ⟨witnessOrderInitial_wellFormed, rfl⟩
  · exact ⟨witnessOrderInitial_wellFormed, rfl⟩

end Effect4
