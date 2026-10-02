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

/-- A queued enrollment names an id below `nextId` (decisions row 134 (e)), so fresh allocation
cannot activate a previously absent target. Missing old targets remain inert. Enrollment may
fire an already-exited entrant immediately; its columns use the same declared result as
`RacePayload`. -/
def EnrollRaceOk (root : ProgramSource) (w : World) (m : RState)
    (raceId : Nat) (child : FiberId) : Prop :=
  child.value < m.nextId ∧
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
  /-- Decisions row 134 (d): no stored observer holds a race's key (F5). The registration's
  no-answer park writes a `void` pending record at that key (`Machine/Fibers.lean:1925-1929`),
  which a countdown observer there would read at its own type; a race takes a fresh token, above
  every key an observer holds (`keysBelow`). -/
  raceObservers : ∀ raceId race, m.race? raceId = some race → ∀ fiber ∈ m.fibers,
    ∀ o ∈ fiber.observers, (race.host, race.token) ∉ Guard.observerKeys o
  /-- Decisions row 134 (e): every fiber id the scheduler's records name is below `nextId` (F6), so
  a fiber spawned at `nextId` (`spawn`, `Machine/Fibers.lean:948-966`) is constrained by none of
  them: a race's live set (`RacePayload.live`), a countdown's targets
  (`CountdownPayload.targets`) and a stored observer's keys. -/
  liveBelow : ∀ raceId race, m.race? raceId = some race → ∀ id ∈ race.state.live,
    id.value < m.nextId
  targetsBelow : ∀ fiber ∈ m.fibers, ∀ p ∈ fiber.pending,
    ∀ id ∈ p.waitingOn.toList ++ p.remaining, id.value < m.nextId
  observersBelow : ∀ fiber ∈ m.fibers, ∀ o ∈ fiber.observers, ∀ k ∈ Guard.observerKeys o,
    k.1.value < m.nextId

/-- The reference evaluator consumes this operation directly; interpR.parkOf is none. -/
def raceRegistrationR : RProgram → Option Nat
  | .vis (.inr (.raceRegister raceId)) _ => some raceId
  | _ => none

/-! ## Decisions row 188 (b): registration markers under injected yields -/

/-- **A registration arrow** (decisions row 188 (b), `E4-TYPED-CE-033`). `beginRace` leaves a race's
registration marker current with `loop` queued (`Machine/Fibers.lean:919-931`); a budget-triggered
`injectYield` (`:1056-1064`; the term core's `yieldBefore`, `Laws/Program/InterpR.lean:89-91`)
saves it in a success callback around `Yield`. The callback returns the marker, which is no typed
code: its reply is the race's. As an arrow of the host's stack it goes from `tin` to the race
token's declared type: every success answer returns race `raceId`'s marker, the race exists on
this machine with this host, and a failure skips into the rest at the token's type (the reply
`registrationDone` delivers once the walk makes the marker current again, `RegistrationState`).
The correlation sits on the arrow, so typed code cannot forge it. -/
inductive RegistrationArrow (w : World) (m : RState) (host : FiberId) :
    EffTy → EffTy → ScopeFrame → Prop
  | mk {tin resultTy : EffTy} {next : ExitV → RProgram} {raceId : Nat} {race : RRace}
      (marker : ∀ v, raceRegistrationR (next (.success v)) = some raceId)
      (skip : ∀ w', w.leHost w' → ∀ c, ExitOk w' tin (.failure c) → ExitOk w' resultTy (.failure c))
      (found : m.race? raceId = some race) (hosted : race.host = host)
      (token : w.Θ race.host race.token = some resultTy) :
      RegistrationArrow w m host tin resultTy (.resume .onSuccess next)

/-- A host stack's arrows: the ordinary frames and the registration arrows. -/
def HostEdge (root : ProgramSource) (w : World) (m : RState) (host : FiberId)
    (tin tout : EffTy) (frame : ScopeFrame) : Prop :=
  Contracts.FrameAccepts (TypedProg root) ExitOk (frameProtocols root) w tin tout frame ∨
    RegistrationArrow w m host tin tout frame

/-- **A host's saved stack**: the frame path over `HostEdge` (any number of registration arrows
compose, `hostStack_push`). With no registration arrow it is `StackAccepts`
(`hostStack_of_stackAccepts`). -/
abbrev HostStack (root : ProgramSource) (w : World) (m : RState) (host : FiberId) :
    EffTy → EffTy → List ScopeFrame → Prop :=
  Contracts.FramePath (HostEdge root w m host)

/-- A host's saved frame at `final`: its current code typed over a `HostStack`, with recorded
interrupts only. With no registration arrow in the stack this is `SavedOk` (`codeOk_of_saved`). -/
def CodeOk (root : ProgramSource) (w : World) (m : RState) (host : FiberId) (final : EffTy)
    (x : RSaved) : Prop :=
  ∃ tin, TypedProg root w tin x.current ∧ HostStack root w m host tin final x.stack ∧
    Contracts.InterruptProvenance x

/-- The race facts the registration arrows read move to a machine whose races keep their host
and token. -/
def RacesKept (m m' : RState) : Prop :=
  ∀ r race, m.race? r = some race →
    ∃ race', m'.race? r = some race' ∧ race'.host = race.host ∧ race'.token = race.token

theorem racesKept_of_eq {m m' : RState} (races : ∀ r, m'.race? r = m.race? r) : RacesKept m m' :=
  fun r race h => ⟨race, (races r).trans h, rfl, rfl⟩

theorem registrationArrow_mono {w w' : World} {m : RState} {host : FiberId} {a b : EffTy}
    {frame : ScopeFrame} (ord : w.leHost w') (h : RegistrationArrow w m host a b frame) :
    RegistrationArrow w' m host a b frame := by
  cases h with
  | mk marker skip found hosted token =>
    exact .mk marker (fun w'' o c hc => skip w'' (leHost_trans _ _ _ ord o) c hc) found hosted
      (ord.1.2.2.2.2.2.1 _ _ _ token)

theorem registrationArrow_races {w : World} {m m' : RState} {host : FiberId} {a b : EffTy}
    {frame : ScopeFrame} (kept : RacesKept m m') (h : RegistrationArrow w m host a b frame) :
    RegistrationArrow w m' host a b frame := by
  cases h with
  | mk marker skip found hosted token =>
    obtain ⟨race', found', host', token'⟩ := kept _ _ found
    exact .mk marker skip found' (host'.trans hosted) (by rw [host', token']; exact token)

theorem hostStack_of_stackAccepts {root : ProgramSource} {w : World} {m : RState}
    {host : FiberId} {tin final : EffTy} {stack : List ScopeFrame}
    (h : Contracts.StackAccepts (TypedProg root) ExitOk (frameProtocols root) w tin final stack) :
    HostStack root w m host tin final stack :=
  (Contracts.framePath_of_stackAccepts h).map fun _ _ _ e => .inl e

theorem codeOk_of_saved {root : ProgramSource} {w : World} {m : RState} {host : FiberId}
    {final : EffTy} {x : RSaved}
    (h : Contracts.SavedOk (TypedProg root) ExitOk (frameProtocols root) w final x) :
    CodeOk root w m host final x := by
  obtain ⟨tin, code, stack, provenance⟩ := h
  exact ⟨tin, code, hostStack_of_stackAccepts stack, provenance⟩

theorem hostStack_mono {root : ProgramSource} {w w' : World} {m : RState} {host : FiberId}
    {tin final : EffTy} {stack : List ScopeFrame} (ord : w.leHost w')
    (h : HostStack root w m host tin final stack) : HostStack root w' m host tin final stack :=
  h.map fun _ _ _ e => e.imp (Contracts.frameAccepts_mono ord) (registrationArrow_mono ord)

theorem hostStack_races {root : ProgramSource} {w : World} {m m' : RState} {host : FiberId}
    {tin final : EffTy} {stack : List ScopeFrame} (kept : RacesKept m m')
    (h : HostStack root w m host tin final stack) : HostStack root w m' host tin final stack :=
  h.map fun _ _ _ e => e.imp id (registrationArrow_races kept)

/-- A frame pushed on a host stack. -/
theorem hostStack_push {root : ProgramSource} {w : World} {m : RState} {host : FiberId}
    {a b final : EffTy} {f : ScopeFrame} {stack : List ScopeFrame}
    (hf : Contracts.FrameAccepts (TypedProg root) ExitOk (frameProtocols root) w a b f)
    (h : HostStack root w m host b final stack) : HostStack root w m host a final (f :: stack) :=
  .cons (.inl hf) h

theorem codeOk_mono {root : ProgramSource} {w w' : World} {m : RState} {host : FiberId}
    {final : EffTy} {x : RSaved} (ord : w.leHost w') (h : CodeOk root w m host final x) :
    CodeOk root w' m host final x := by
  obtain ⟨tin, code, stack, provenance⟩ := h
  exact ⟨tin, typedProg_mono root w w' tin x.current ord code, hostStack_mono ord stack, provenance⟩

theorem codeOk_races {root : ProgramSource} {w : World} {m m' : RState} {host : FiberId}
    {final : EffTy} {x : RSaved} (kept : RacesKept m m') (h : CodeOk root w m host final x) :
    CodeOk root w m' host final x := by
  obtain ⟨tin, code, stack, provenance⟩ := h
  exact ⟨tin, code, hostStack_races kept stack, provenance⟩

/-- **A position arrow** (decisions row 188 (b)), for the generated position clause, which reads no
machine: a success callback whose every success answer is a registration marker, typed by the
failures it skips alone. Its race correlation is the machine clauses' (`RegistrationArrow`). -/
inductive PositionArrow (w : World) : EffTy → EffTy → ScopeFrame → Prop
  | mk {tin middle : EffTy} {next : ExitV → RProgram}
      (marker : ∀ v, (raceRegistrationR (next (.success v))).isSome = true)
      (skip : ∀ w', w.leHost w' → ∀ c, ExitOk w' tin (.failure c) → ExitOk w' middle (.failure c)) :
      PositionArrow w tin middle (.resume .onSuccess next)

def PositionEdge (root : ProgramSource) (w : World) (tin tout : EffTy) (frame : ScopeFrame) : Prop :=
  Contracts.FrameAccepts (TypedProg root) ExitOk (frameProtocols root) w tin tout frame ∨
    PositionArrow w tin tout frame

/-- **The generated position clause's path**: ordinary arrows and position arrows. -/
abbrev PositionStack (root : ProgramSource) (w : World) : EffTy → EffTy → List ScopeFrame → Prop :=
  Contracts.FramePath (PositionEdge root w)

theorem positionArrow_mono {w w' : World} {a b : EffTy} {frame : ScopeFrame} (ord : w.leHost w')
    (h : PositionArrow w a b frame) : PositionArrow w' a b frame := by
  cases h with
  | mk marker skip => exact .mk marker (fun w'' o c hc => skip w'' (leHost_trans _ _ _ ord o) c hc)

/-- Forgetting a registration arrow's correlation leaves a position arrow (one-way). -/
theorem positionArrow_of_registration {w : World} {m : RState} {host : FiberId} {a b : EffTy}
    {frame : ScopeFrame} (h : RegistrationArrow w m host a b frame) : PositionArrow w a b frame := by
  cases h with
  | mk marker skip _ _ _ => exact .mk (fun v => by rw [marker v]; rfl) skip

theorem positionStack_of_stackAccepts {root : ProgramSource} {w : World} {tin final : EffTy}
    {stack : List ScopeFrame}
    (h : Contracts.StackAccepts (TypedProg root) ExitOk (frameProtocols root) w tin final stack) :
    PositionStack root w tin final stack :=
  (Contracts.framePath_of_stackAccepts h).map fun _ _ _ e => .inl e

theorem positionStack_mono {root : ProgramSource} {w w' : World} {tin final : EffTy}
    {stack : List ScopeFrame} (ord : w.leHost w') (h : PositionStack root w tin final stack) :
    PositionStack root w' tin final stack :=
  h.map fun _ _ _ e => e.imp (Contracts.frameAccepts_mono ord) (positionArrow_mono ord)

/-- A host stack is a position stack: the race correlation is forgotten. -/
theorem positionStack_of_host {root : ProgramSource} {w : World} {m : RState} {host : FiberId}
    {tin final : EffTy} {stack : List ScopeFrame} (h : HostStack root w m host tin final stack) :
    PositionStack root w tin final stack :=
  h.map fun _ _ _ e => e.imp id positionArrow_of_registration

/-- A concrete reply must meet the actual saved stack, independently of whatever type
certified the current administrative operation. This names a local delivery boundary. The stack
may hold row 188 (b)'s injected registration callback (`HostStack`): every reply consumer
(`afterInterrupt`, `raceCancel`, `closeParAwait`, a registration's delivery) carries it. -/
def StackReply (root : ProgramSource) (w : World) (m : RState) (fiber : RFiber) (replyTy : EffTy) :
    Prop :=
  ∃ final, w.Γ fiber.id = some final ∧ HostStack root w m fiber.id replyTy final fiber.frame.stack ∧
    Contracts.InterruptProvenance fiber.frame

theorem stackReply_races {root : ProgramSource} {w : World} {m m' : RState} {fiber : RFiber}
    {replyTy : EffTy} (kept : RacesKept m m') (h : StackReply root w m fiber replyTy) :
    StackReply root w m' fiber replyTy := by
  obtain ⟨final, declared, stack, provenance⟩ := h
  exact ⟨final, declared, hostStack_races kept stack, provenance⟩

/-- The direct registration marker owns a real race on this fiber, and the race token's
result meets this host's saved continuation. This finite current-code clause covers both
immediate buffered settlement and parking; it is not the open recursive code-site scan. -/
def RegistrationState (root : ProgramSource) (w : World) (m : RState) : Prop :=
  ∀ fiber ∈ m.fibers, ∀ raceId, raceRegistrationR fiber.frame.current = some raceId →
    ∃ race resultTy, m.race? raceId = some race ∧ race.host = fiber.id ∧
      w.Θ race.host race.token = some resultTy ∧ StackReply root w m fiber resultTy

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
      ∃ replyTy, AfterInterruptReply w kind replyTy ∧ StackReply root w m fiber replyTy
  | .raceCancel _ host _ remaining visited => ∀ fiber, m.fiber? host = some fiber →
      ∃ answer error, FiberListColumns w (visited ++ remaining) answer error ∧
        StackReply root w m fiber (EffTy.pure .unit)
  /- Decisions row 134 (c): a queued `finish` names a fiber whose saved stack is empty: the loop
  queues it only from the `finished` outcome (`settle`), after `frameExitState` drained the
  stack. -/
  | .finish host _ => ∀ fiber, m.fiber? host = some fiber → fiber.frame.stack = []
  | .closeParAwait host _ targets => ∀ fiber, m.fiber? host = some fiber →
      ∃ answer error, FiberListColumns w targets answer error ∧
        (frameProtocols root).iterator w
          ⟨.list (.exitOf answer error), error, Env.Requirement.empty⟩
          ⟨.unit, error, Env.Requirement.empty⟩ (interpR root.program).closeDoneName ∧
        StackReply root w m fiber ⟨.unit, error, Env.Requirement.empty⟩
  | _ => True

/-- The delivery reads see the fiber table only positively: a declaration exists, a column bound,
a reply stack's final type. They move along any world extension. -/
theorem fiberListColumns_mono {w w' : World} (ext : ∀ id t, w.Γ id = some t → w'.Γ id = some t)
    {targets : List FiberId} {answer error : Ty} (h : FiberListColumns w targets answer error) :
    FiberListColumns w' targets answer error := by
  intro id hid
  obtain ⟨t, declared, ha, he⟩ := h id hid
  exact ⟨t, ext _ _ declared, ha, he⟩

theorem afterInterruptReply_mono {w w' : World} (ext : ∀ id t, w.Γ id = some t → w'.Γ id = some t)
    {kind : ParkKind} {replyTy : EffTy} (h : AfterInterruptReply w kind replyTy) :
    AfterInterruptReply w' kind replyTy := by
  cases kind with
  | join target mode =>
    cases mode <;> (obtain ⟨sourceTy, declared, eq⟩ := h; exact ⟨sourceTy, ext _ _ declared, eq⟩)
  | awaitAll targets =>
    obtain ⟨answer, error, cols, eq⟩ := h
    exact ⟨answer, error, fiberListColumns_mono ext cols, eq⟩
  | race _ => exact h

theorem stackReply_mono {root : ProgramSource} {w w' : World} {m m' : RState} {fiber : RFiber}
    {replyTy : EffTy} (ord : w.leHost w') (ext : ∀ id t, w.Γ id = some t → w'.Γ id = some t)
    (kept : RacesKept m m') (h : StackReply root w m fiber replyTy) :
    StackReply root w' m' fiber replyTy := by
  obtain ⟨final, declared, stack, provenance⟩ := h
  exact ⟨final, ext _ _ declared, hostStack_mono ord (hostStack_races kept stack), provenance⟩

/-- **The delivery facts are monotone**: they read the world only positively, the machine only at
the command's owner (`Guard.commandOwner`, the host of every command that installs a reply), and
the races only through their host and token (row 188 (b)'s registration arrows). So they move
along a world extension to any machine that agrees at the owner and keeps the races' host and
token: a trace edit, a race edit, an allocation (`Commands/Launch.lean`). -/
theorem commandDelivery_mono {root : ProgramSource} {w w' : World} {m m' : RState}
    (ord : w.leHost w') (ext : ∀ id t, w.Γ id = some t → w'.Γ id = some t) (kept : RacesKept m m')
    {c : RCmd} (owner : ∀ o, Guard.commandOwner m c = some o → m'.fiber? o = m.fiber? o)
    (h : CommandDeliveryOk root w m c) : CommandDeliveryOk root w' m' c := by
  cases c with
  | afterInterrupt host _ kind =>
    intro f hf
    rw [owner host rfl] at hf
    obtain ⟨replyTy, reply, stack⟩ := h f hf
    exact ⟨replyTy, afterInterruptReply_mono ext reply, stackReply_mono ord ext kept stack⟩
  | raceCancel _ host _ remaining visited =>
    intro f hf
    rw [owner host rfl] at hf
    obtain ⟨answer, error, cols, stack⟩ := h f hf
    exact ⟨answer, error, fiberListColumns_mono ext cols, stackReply_mono ord ext kept stack⟩
  | closeParAwait host _ targets =>
    intro f hf
    rw [owner host rfl] at hf
    obtain ⟨answer, error, cols, protocol, stack⟩ := h f hf
    exact ⟨answer, error, fiberListColumns_mono ext cols, iteratorProtocol_mono ord protocol,
      stackReply_mono ord ext kept stack⟩
  | finish host _ =>
    intro f hf
    rw [owner host rfl] at hf
    exact h f hf
  | _ => trivial

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

/-- A queued command's owner exists: it is active, or it hosts the race the command completes. -/
theorem commandOwner_found {m : RState} {c : RCmd} (authority : CommandAuthorityR m c) {o : FiberId}
    (h : Guard.commandOwner m c = some o) : ∃ f, m.fiber? o = some f := by
  cases c with
  | registrationDone raceId _ =>
    obtain ⟨race, fiber, found, host, _⟩ := authority
    rw [show Guard.commandOwner m (.registrationDone raceId _) = (m.race? raceId).map Race.host
      from rfl, found, Option.map_some] at h
    cases h
    exact ⟨fiber, host⟩
  | _ => cases h <;> (obtain ⟨f, hf, _, _⟩ := authority; exact ⟨f, hf⟩)

/-- **Authority is monotone in the fiber table**: it reads fibers only through lookups that find
them (`ActiveAt`, an exited fiber, a race host) and races by id, so a machine that finds every old
fiber unchanged and keeps the races keeps it. -/
theorem commandAuthority_mono {m m' : RState}
    (look : ∀ id f, m.fiber? id = some f → m'.fiber? id = some f)
    (races : ∀ r, m'.race? r = m.race? r) {c : RCmd} (h : CommandAuthorityR m c) :
    CommandAuthorityR m' c := by
  have active : ∀ {id}, Guard.ActiveAt m id → Guard.ActiveAt m' id := by
    intro id a
    obtain ⟨f, hf, running, parked⟩ := a
    exact ⟨f, look _ _ hf, running, parked⟩
  cases c with
  | loop _ _ | deliver _ _ | finish _ _ | afterInterrupt _ _ _ | closeParAwait _ _ _
  | raceCancel _ _ _ _ _ => exact active h
  | registrationDone _ _ =>
    obtain ⟨race, fiber, found, host, running, parked, marker⟩ := h
    exact ⟨race, fiber, (races _).trans found, look _ _ host, running, parked, marker⟩
  | launch _ | enrollRace _ _ =>
    obtain ⟨race, found, a⟩ := h
    exact ⟨race, (races _).trans found, active a⟩
  | exitDone _ =>
    obtain ⟨found, hf, exited⟩ := h
    exact ⟨found, look _ _ hf, exited⟩
  | _ => trivial

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
  · intro raceId race hr; cases hr
  · intro raceId race hr; cases hr
  · intro fiber hf p hp
    change fiber ∈ [_] at hf
    rw [List.mem_singleton] at hf
    subst fiber
    cases hp
  · intro fiber hf o ho
    change fiber ∈ [_] at hf
    rw [List.mem_singleton] at hf
    subst fiber
    cases ho

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
