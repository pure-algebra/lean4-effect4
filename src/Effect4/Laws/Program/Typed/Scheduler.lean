import Effect4.Laws.Program.Typed.Stack
import Effect4.Laws.Program.Typed.State
import Effect4.Laws.Program.Guard.Core
import Effect4.Laws.Program.Guard.RegistrationQueue
import Effect4.Laws.Program.ReasonsR

/-!
H1 scheduler statements, without a command-preservation proof. The predicates inspect the
actual tables and finite buffered payloads. The exact reference code-site traversal is OPEN
(H1-RCODE-SITES); this file supplies neither a head-only approximation nor a predicate over
all possible continuation answers. The direct race-registration authority is settled.
-/
set_option autoImplicit false
namespace Effect4.Program.Typed
open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Sched Effect4.Program.Denote

abbrev RPending := Pending EffName Val Err Defect FiberId Ann
abbrev RRace := Race EffName EffThunk Val Err Defect FiberId Ann RProgram

/-- The checker's two result types, not the source fiber type in both modes. -/
def observerDeliveredType (mode : Supervision.ObserverMode) (sourceTy : EffTy) : EffTy :=
  match mode with
  | .joinEffect => sourceTy
  | .awaitValue => EffTy.pure (.exitOf sourceTy.answer sourceTy.error)

def observerDeliveredExit (mode : Supervision.ObserverMode) (exit : ExitV) : ExitV :=
  match mode with
  | .joinEffect => exit
  | .awaitValue => .success (reifyExitVal exit)

/-- Reification is exactly the value at Exit<A,E> in FitsExit's definition. -/
theorem reifyExitVal_fits (w : World) (ty : EffTy) (exit : ExitV)
    (typed : FitsExit w ty exit) :
    Fits w (reifyExitVal exit) (.exitOf ty.answer ty.error) := typed

theorem observerDeliveredExit_fits (w : World) (ty : EffTy) (exit : ExitV)
    (mode : Supervision.ObserverMode) (typed : FitsExit w ty exit) :
    FitsExit w (observerDeliveredType mode ty) (observerDeliveredExit mode exit) := by
  cases mode with
  | joinEffect => exact typed
  | awaitValue => exact reifyExitVal_fits w ty exit typed

/-- The actual interpreter hook constructs the result just typed above. -/
theorem observer_exitValue_typed (root : ProgramSource) (w : World) (ty : EffTy)
    (exit : ExitV) (mode : Supervision.ObserverMode) (typed : ExitOk w ty exit) :
    TypedProg root w (observerDeliveredType mode ty)
      ((interpR root.program).exitValue exit mode) := by
  cases mode with
  | joinEffect => exact TypedProg.pure typed
  | awaitValue =>
    exact TypedProg.pure (strongExit_success w _ _ (reifyExitVal_fits w ty exit typed.1))

/-- Only the two exit columns are aggregated; requirement transport is H2's separate debt.
Declared columns are compared in the checker's order (decisions row 137, `Ty.subN`). -/
def FiberColumnsBelow (w : World) (id : FiberId) (answer error : Ty) : Prop :=
  ∃ ty, w.Γ id = some ty ∧ Ty.subN ty.answer answer = true ∧ Ty.subN ty.error error = true

/-- A race's one result declaration owns every buffered value and each unlaunched program.
Existing live fiber declarations are constrained; missing fibers are not invented. Columns are
compared in the checker's order (decisions row 137, `Ty.subN`). -/
structure RacePayload (root : ProgramSource) (w : World) (race : RRace)
    (resultTy : EffTy) : Prop where
  token : w.Θ race.host race.token = some resultTy
  failures : ExitOk w resultTy (.failure ⟨race.state.failures⟩)
  winner : ∀ pair ∈ race.state.winner, Fits w pair.2 resultTy.answer
  accepted : ∀ exit ∈ race.state.accepted, ExitOk w resultTy exit
  cleanup : ∀ wait ∈ race.state.cleanup, ExitOk w resultTy wait.result
  live : ∀ id ∈ race.state.live, ∀ childTy, w.Γ id = some childTy →
    Ty.subN childTy.answer resultTy.answer = true ∧ Ty.subN childTy.error resultTy.error = true
  programs : ∀ code ∈ race.programs, ∃ childTy, TypedProg root w childTy code ∧
    Ty.subN childTy.answer resultTy.answer = true ∧ Ty.subN childTy.error resultTy.error = true

/-- The finite pending record reached by a countdown observer. Joins also use Pending with
void metadata, so this predicate is attached only through an actual countdown observer. -/
structure CountdownPayload (w : World) (m : RState) (waiter : FiberId)
    (pending : RPending) (answer error : Ty) (tokenTy : EffTy) : Prop where
  token : w.Θ waiter pending.token = some tokenTy
  collected : ∀ exit ∈ pending.collected,
    ExitOk w ⟨answer, error, Env.Requirement.empty⟩ exit
  targets : ∀ id ∈ pending.waitingOn.toList ++ pending.remaining,
    ∀ fiber, m.fiber? id = some fiber → FiberColumnsBelow w fiber.id answer error
  resume : match pending.resumeWith with
    | .exitsValue => tokenTy = EffTy.pure (.list (.exitOf answer error))
    | .void => tokenTy = EffTy.pure .unit
    | .continueWith (.restore saved) => ExitOk w tokenTy saved
    | .continueWith _ => ExitOk w tokenTy outsideExit

/-- Follow exactly fireObserver's waiter and pending lookups. Missing lookups are inert.
The supplied condition shares the aggregate witnesses with all buffered values. -/
def CountdownAt (w : World) (m : RState) (waiter : FiberId) (token : Nat)
    (incoming : Ty → Ty → Prop) : Prop :=
  match m.fiber? waiter with
  | none => True
  | some fiber =>
    match fiber.pending.find? (fun pending => pending.token = token) with
    | none => True
    | some pending => ∃ answer error tokenTy,
        CountdownPayload w m waiter pending answer error tokenTy ∧ incoming answer error

/-- A stored observer's source declaration is connected to the destination token; a stored
scope-finalizer drop names a scope the store holds (row 139; `Stores.ScopeLive`, row 156's
predicate at the machine's store). -/
def StoredObserverOk (root : ProgramSource) (w : World) (m : RState)
    (source : FiberId) : Observer → Prop
  | .resumeAwait waiter token mode => ∃ sourceTy,
      w.Γ source = some sourceTy ∧ w.Θ waiter token = some (observerDeliveredType mode sourceTy)
  | .countdown waiter token => CountdownAt w m waiter token (FiberColumnsBelow w source)
  | .raceCallback raceId =>
    match m.race? raceId with
    | none => True
    | some race => ∃ resultTy, RacePayload root w race resultTy ∧
        (source ∈ race.state.live → FiberColumnsBelow w source resultTy.answer resultTy.error)
  -- `fireObserver` halts on an absent scope (`Machine/Fibers.lean:1668-1671`; row 139)
  | .dropScopeFinalizer scope _ => m.state.ScopeLive scope
  | .untrackChild _ | .callback _ => True

/-- A queued observer must type what it can deliver or buffer, including a race callback
while registration is still active; a scope-finalizer drop names a scope the store holds
(`Stores.ScopeLive`). The two remaining no-payload variants keep their machine guards. -/
def ObserverCommandOk (root : ProgramSource) (w : World) (m : RState)
    (source : FiberId) (exit : ExitV) : Observer → Prop
  | .resumeAwait waiter token mode => ∃ sourceTy,
      w.Γ source = some sourceTy ∧
      w.Θ waiter token = some (observerDeliveredType mode sourceTy) ∧ ExitOk w sourceTy exit
  | .countdown waiter token => CountdownAt w m waiter token
      (fun answer error => ExitOk w ⟨answer, error, Env.Requirement.empty⟩ exit)
  | .raceCallback raceId =>
    match m.race? raceId with
    | none => True
    | some race => ∃ resultTy, RacePayload root w race resultTy ∧
        (source ∈ race.state.live → ExitOk w resultTy exit)
  -- `fireObserver` halts on an absent scope (`Machine/Fibers.lean:1668-1671`; row 139)
  | .dropScopeFinalizer scope _ => m.state.ScopeLive scope
  | .untrackChild _ | .callback _ => True

/-- Enrollment may fire an already-exited entrant immediately, so queueing only a typed
observe command is insufficient. This clause uses the same declared result as RacePayload. -/
def EnrollRaceOk (root : ProgramSource) (w : World) (m : RState)
    (raceId : Nat) (child : FiberId) : Prop :=
  match m.race? raceId, m.fiber? child with
  | some race, some fiber => ∃ resultTy, RacePayload root w race resultTy ∧
      FiberColumnsBelow w fiber.id resultTy.answer resultTy.error
  | _, _ => True

structure ObserverState (root : ProgramSource) (w : World) (m : RState) : Prop where
  pendingOwner : ∀ fiber ∈ m.fibers, ∀ pending ∈ fiber.pending,
    (w.Θ fiber.id pending.token).isSome = true
  observers : ∀ fiber ∈ m.fibers, ∀ observer ∈ fiber.observers,
    StoredObserverOk root w m fiber.id observer

/-! ### Transport between machines with the same lookups

The observer correlations read the machine only through `fiber?`, `race?` and the store, but a
countdown's payload is a structure over the machine, so two machines that agree on those lookups
need a transport, not a definitional rewrite. -/

theorem countdownAt_congr {w : World} {m m' : RState} {waiter : FiberId} {token : Nat}
    {incoming : Ty → Ty → Prop} (fibers : ∀ id, m'.fiber? id = m.fiber? id)
    (h : CountdownAt w m waiter token incoming) : CountdownAt w m' waiter token incoming := by
  unfold CountdownAt at h ⊢
  rw [fibers]
  cases found : m.fiber? waiter with
  | none => trivial
  | some fiber =>
    rw [found] at h
    dsimp only at h ⊢
    cases hp : fiber.pending.find? (fun pending => pending.token = token) with
    | none => trivial
    | some pending =>
      rw [hp] at h
      dsimp only at h
      obtain ⟨answer, error, tokenTy, payload, incomingOk⟩ := h
      refine ⟨answer, error, tokenTy, ⟨payload.token, payload.collected, ?_, payload.resume⟩,
        incomingOk⟩
      intro id member target lookup
      rw [fibers] at lookup
      exact payload.targets id member target lookup

theorem storedObserverOk_congr {root : ProgramSource} {w : World} {m m' : RState}
    {source : FiberId} (fibers : ∀ id, m'.fiber? id = m.fiber? id)
    (races : ∀ race, m'.race? race = m.race? race) (state : m'.state = m.state) (o : Observer)
    (h : StoredObserverOk root w m source o) : StoredObserverOk root w m' source o := by
  cases o with
  | resumeAwait waiter token mode => exact h
  | countdown waiter token => exact countdownAt_congr fibers h
  | raceCallback raceId =>
    unfold StoredObserverOk at h ⊢
    dsimp only at h ⊢
    rw [races]
    exact h
  | dropScopeFinalizer scope key =>
    unfold StoredObserverOk at h ⊢
    dsimp only at h ⊢
    rw [state]
    exact h
  | untrackChild parent => trivial
  | callback key => trivial

theorem observerCommandOk_congr {root : ProgramSource} {w : World} {m m' : RState}
    {source : FiberId} {exit : ExitV} (fibers : ∀ id, m'.fiber? id = m.fiber? id)
    (races : ∀ race, m'.race? race = m.race? race) (state : m'.state = m.state) (o : Observer)
    (h : ObserverCommandOk root w m source exit o) : ObserverCommandOk root w m' source exit o := by
  cases o with
  | resumeAwait waiter token mode => exact h
  | countdown waiter token => exact countdownAt_congr fibers h
  | raceCallback raceId =>
    unfold ObserverCommandOk at h ⊢
    dsimp only at h ⊢
    rw [races]
    exact h
  | dropScopeFinalizer scope key =>
    unfold ObserverCommandOk at h ⊢
    dsimp only at h ⊢
    rw [state]
    exact h
  | untrackChild parent => trivial
  | callback key => trivial

/-- Settled guard state clauses on the shared machine. No reference code-site condition
is claimed here: frameCodes/internalCodes remain H1-RCODE-SITES. -/
structure SchedulerState (m : RState) : Prop where
  fiberIds : (m.fibers.map RunFiber.id).Nodup
  fibersBelow : ∀ fiber ∈ m.fibers, fiber.id.value < m.nextId
  raceIds : (m.races.map Race.id).Nodup
  racesBelow : ∀ race ∈ m.races, race.id < m.nextRace
  raceHosts : ∀ race ∈ m.races, ∃ fiber, m.fiber? race.host = some fiber
  keysBelow : Guard.InternalKeysBelow m
  requestsBelow : ∀ fiber token request, requestOfR m fiber token = some request → token < m.nextToken
  requestsOwned : ∀ fiber token request, requestOfR m fiber token = some request →
    (fiber, token) ∉ Guard.internalKeys m
  pendingShape : ∀ fiber ∈ m.fibers, Guard.PendingShape fiber
  parkedIdle : ∀ fiber ∈ m.fibers, fiber.parked ≠ .notParked → fiber.running = false
  parkedBelow : ∀ fiber ∈ m.fibers, ∀ token,
    fiber.parked = .withGuard token → token < m.nextToken
  exited : ∀ fiber ∈ m.fibers, fiber.exit.isSome = true →
    fiber.parked = .notParked ∧ fiber.running = false
  /-- Decisions row 134 (c): an exited fiber's saved stack is empty. Only `RunFiber.publish`
  (`Machine/Fibers.lean:1750`) writes an exit, from a queued `finish`, whose fiber's stack is
  empty (`CommandDeliveryOk`'s `finish` clause); `exitDone`'s clear keeps it empty. -/
  exitedStack : ∀ fiber ∈ m.fibers, fiber.exit.isSome = true → fiber.frame.stack = []
  deferredCause : ∀ fiber ∈ m.fibers, fiber.frame.deferredInterrupt = true →
    fiber.frame.interruptedCause.isSome = true

/-- The reference evaluator consumes this operation directly; interpR.parkOf is none. -/
def raceRegistrationR : RProgram → Option Nat
  | .vis (.inr (.raceRegister raceId)) _ => some raceId
  | _ => none

/-- A concrete reply must meet the actual saved stack, independently of whatever type
certified the current administrative operation. This names a local delivery boundary. -/
def StackReply (root : ProgramSource) (w : World) (fiber : RFiber) (replyTy : EffTy) : Prop :=
  ∃ final, w.Γ fiber.id = some final ∧
    Contracts.StackAccepts (TypedProg root) ExitOk (frameProtocols root) w replyTy final
      fiber.frame.stack ∧ Contracts.InterruptProvenance fiber.frame

/-- The direct registration marker owns a real race on this fiber, and the race token's
result meets this host's saved continuation. This finite current-code clause covers both
immediate buffered settlement and parking; it is not the open recursive code-site scan. -/
def RegistrationState (root : ProgramSource) (w : World) (m : RState) : Prop :=
  ∀ fiber ∈ m.fibers, ∀ raceId, raceRegistrationR fiber.frame.current = some raceId →
    ∃ race resultTy, m.race? raceId = some race ∧ race.host = fiber.id ∧
      w.Θ race.host race.token = some resultTy ∧ StackReply root w fiber resultTy

/-- A loaded code with no direct registration marker needs no race/token correlation yet. -/
theorem registrationState_load (root : ProgramSource) (w : World) (fuel compileFuel : Nat)
    (noMarker : raceRegistrationR (denoteR root.program root.program (rootPoint compileFuel)) = none) :
    RegistrationState root w (loadR root.program fuel compileFuel) := by
  intro fiber hf raceId marker
  change fiber ∈ [_] at hf
  rw [List.mem_singleton] at hf
  subst fiber
  change raceRegistrationR (denoteR root.program root.program (rootPoint compileFuel)) = some raceId at marker
  rw [noMarker] at marker
  cases marker

/-- The existing await protocol certifies a finite list of declared target columns.
This is a command-admission requirement; the runtime's missing-target behavior is unchanged. -/
def FiberListColumns (w : World) (targets : List FiberId) (answer error : Ty) : Prop :=
  ∀ id ∈ targets, FiberColumnsBelow w id answer error

/-- asVoid(awaitCode kind) has a unit answer. joinEffect can retain the target's typed
failures; awaitValue and awaitAll return encoded exits as successful values. -/
def AfterInterruptReply (w : World) : ParkKind → EffTy → Prop
  | .join target .joinEffect, replyTy => ∃ sourceTy, w.Γ target = some sourceTy ∧
      replyTy = ⟨.unit, sourceTy.error, Env.Requirement.empty⟩
  | .join target .awaitValue, replyTy => ∃ sourceTy, w.Γ target = some sourceTy ∧
      replyTy = EffTy.pure .unit
  | .awaitAll targets, replyTy => ∃ answer error, FiberListColumns w targets answer error ∧
      replyTy = EffTy.pure .unit
  | .race _, _ => False

/-- Commands with no carried code can still install a concrete reply or an iterator frame.
Their finite targets and result columns must meet the actual host stack. This does not ask
that an evaluated transition be typed, and does not quantify over unknown code continuations. -/
def CommandDeliveryOk (root : ProgramSource) (w : World) (m : RState) : RCmd → Prop
  | .afterInterrupt host _ kind => ∀ fiber, m.fiber? host = some fiber →
      ∃ replyTy, AfterInterruptReply w kind replyTy ∧ StackReply root w fiber replyTy
  | .raceCancel _ host _ remaining visited => ∀ fiber, m.fiber? host = some fiber →
      ∃ answer error, FiberListColumns w (visited ++ remaining) answer error ∧
        StackReply root w fiber (EffTy.pure .unit)
  /- Decisions row 134 (c): a queued `finish` names a fiber whose saved stack is empty: the loop
  queues it only from the `finished` outcome (`settle`), after `frameExitState` drained the
  stack. -/
  | .finish host _ => ∀ fiber, m.fiber? host = some fiber → fiber.frame.stack = []
  | .closeParAwait host _ targets => ∀ fiber, m.fiber? host = some fiber →
      ∃ answer error, FiberListColumns w targets answer error ∧
        (frameProtocols root).iterator w
          ⟨.list (.exitOf answer error), error, Env.Requirement.empty⟩
          ⟨.unit, error, Env.Requirement.empty⟩ (interpR root.program).closeDoneName ∧
        StackReply root w fiber ⟨.unit, error, Env.Requirement.empty⟩
  | _ => True

def CommandAuthorityR (m : RState) : RCmd → Prop
  | .loop fiber _ | .deliver fiber _ | .finish fiber _ => Guard.ActiveAt m fiber
  | .afterInterrupt fiber _ _ | .closeParAwait fiber _ _ | .raceCancel _ fiber _ _ _ =>
      Guard.ActiveAt m fiber
  | .registrationDone raceId _ =>
      ∃ race fiber, m.race? raceId = some race ∧ m.fiber? race.host = some fiber ∧
        fiber.running = true ∧ fiber.parked = .notParked ∧
        raceRegistrationR fiber.frame.current = some raceId
  | .launch raceId | .enrollRace raceId _ =>
      ∃ race, m.race? raceId = some race ∧ Guard.ActiveAt m race.host
  | .exitDone fiber => ∃ found, m.fiber? fiber = some found ∧ found.exit.isSome = true
  | _ => True

structure ReservedKeysR (m : RState) (keys : List Guard.GuardKey) : Prop where
  below : ∀ key ∈ keys, key.2 < m.nextToken
  disjoint : ∀ fiber token request, requestOfR m fiber token = some request →
    (fiber, token) ∉ keys

def QueueFresh (m : RState) (commands : List RCmd) : Prop :=
  ∀ key ∈ commands.flatMap Guard.commandKeys, key.2 < m.nextToken

/-- The result obligation on resumeAwait is about the actual delivered program. -/
theorem observerCommand_resume_typed (root : ProgramSource) (w : World) (m : RState)
    (source waiter : FiberId) (token : Nat) (mode : Supervision.ObserverMode) (exit : ExitV)
    (typed : ObserverCommandOk root w m source exit (.resumeAwait waiter token mode)) :
    Contracts.ResumeOk (TypedProg root) w waiter token
      ((interpR root.program).exitValue exit mode) := by
  obtain ⟨sourceTy, _, declared, exitTyped⟩ := typed
  intro tokenTy htoken
  rw [declared] at htoken
  cases htoken
  exact observer_exitValue_typed root w sourceTy exit mode exitTyped

/-- A loaded machine has no active external request, regardless of the loaded code. -/
theorem requestOfR_load_none (program : NativeEff) (fuel compileFuel : Nat)
    (fiber : FiberId) (token : Nat) :
    requestOfR (loadR program fuel compileFuel) fiber token = none := by
  unfold requestOfR
  cases hf : (loadR program fuel compileFuel).fiber? fiber with
  | none => rfl
  | some found =>
    have member := List.mem_of_find?_eq_some hf
    change found ∈ [_] at member
    rw [List.mem_singleton] at member
    subst found
    rfl

theorem schedulerState_load (program : NativeEff) (fuel compileFuel : Nat) :
    SchedulerState (loadR program fuel compileFuel) := by
  constructor
  · exact List.nodup_cons.mpr ⟨List.not_mem_nil, List.nodup_nil⟩
  · intro fiber hf
    change fiber ∈ [_] at hf
    rw [List.mem_singleton] at hf
    subst fiber
    exact Nat.zero_lt_succ 0
  · exact List.nodup_nil
  · intro race hr; cases hr
  · intro race hr; cases hr
  · intro key hk; cases hk
  · intro fiber token request hr
    rw [requestOfR_load_none] at hr
    cases hr
  · intro fiber token request hr
    rw [requestOfR_load_none] at hr
    cases hr
  · intro fiber hf
    change fiber ∈ [_] at hf
    rw [List.mem_singleton] at hf
    subst fiber
    rfl
  · intro fiber hf hp
    change fiber ∈ [_] at hf
    rw [List.mem_singleton] at hf
    subst fiber
    exact False.elim (hp rfl)
  · intro fiber hf token hp
    change fiber ∈ [_] at hf
    rw [List.mem_singleton] at hf
    subst fiber
    cases hp
  · intro fiber hf hx
    change fiber ∈ [_] at hf
    rw [List.mem_singleton] at hf
    subst fiber
    cases hx
  · intro fiber hf hx
    change fiber ∈ [_] at hf
    rw [List.mem_singleton] at hf
    subst fiber
    cases hx
  · intro fiber hf hd
    change fiber ∈ [_] at hf
    rw [List.mem_singleton] at hf
    subst fiber
    cases hd

theorem observerState_load (root : ProgramSource) (w : World) (fuel compileFuel : Nat) :
    ObserverState root w (loadR root.program fuel compileFuel) := by
  constructor
  · intro fiber hf pending hp
    change fiber ∈ [_] at hf
    rw [List.mem_singleton] at hf
    subst fiber
    cases hp
  · intro fiber hf observer ho
    change fiber ∈ [_] at hf
    rw [List.mem_singleton] at hf
    subst fiber
    cases ho

end Effect4.Program.Typed
