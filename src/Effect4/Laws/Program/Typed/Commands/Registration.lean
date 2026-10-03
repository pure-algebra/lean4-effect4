import Effect4.Laws.Program.Typed.Commands.Race

/-!
# Registration completion and key-local park transport

Placement: semantics Concept 4, scheduler step preservation;
`registrationDone_preserves`, decisions row 134(d), historical CE-028.
The park adds a pending record at the race token. Stored and queued observer exclusion
allows the other countdown correlations to retain their meaning. The ordinary observer
view forbids every new park, so the restricted view below permits exactly this exception.
Every helper supplies the unchanged command obligation at this module's foot.

The actual accepted, deferred-interrupt and ordinary park branches retain configuration
typing at the same world. This proves neither unique ownership of every internal token,
progress, fairness, live-host behavior nor target execution. The theory and prior checked
candidate are recorded in `docs/research/2026-10-02-codex-lead/registration-receipt.md`.
-/

set_option autoImplicit false
namespace Effect4.Program.Typed
open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Sched Effect4.Program.Denote
open Contracts

/-! ## 1. A park at a key no observer holds

`ObsView` demands `PendingWeaker`: no pending lookup finds a new park. A park adds one at the
park's own key, so the edit gives the view only away from that key; the countdown correlations
read a pending record only at their observer's key, and decisions row 134 (d)
(`SchedulerState.raceObservers`, `QueueOk.raceObservers`) excludes the race key from every
stored and queued observer. -/

/-- `PendingWeaker` away from one token: a lookup at any other token finds an old park. -/
def PendingWeakerOff (token₀ : Nat) (old new : List RPending) : Prop :=
  ∀ token p, token ≠ token₀ → new.find? (fun q => q.token = token) = some p →
    old.find? (fun q => q.token = token) = some p

/-- A fiber with no pending record parks once: only its own token finds the new record. -/
theorem pendingWeakerOff_single (p : RPending) : PendingWeakerOff p.token [] [p] := by
  intro token q hne h
  have miss : decide (p.token = token) = false := decide_eq_false fun same => hne same.symm
  rw [List.find?_cons, miss] at h
  cases h

/-- `ObsView` away from one key: lookups keep ids, races, scopes and every fiber, and a pending
lookup finds no new park except at `key`. -/
structure ObsViewOff (key : Guard.GuardKey) (m m' : RState) : Prop where
  fibers : ∀ id f', m'.fiber? id = some f' → ∃ f, m.fiber? id = some f ∧ f'.id = f.id ∧
    ∀ token p, (id, token) ≠ key → f'.pending.find? (fun q => q.token = token) = some p →
      f.pending.find? (fun q => q.token = token) = some p
  exists_ : ∀ id, (m.fiber? id).isSome = true → (m'.fiber? id).isSome = true
  races : ∀ race, m'.race? race = m.race? race
  scopes : ∀ sc, m.state.ScopeLive sc → m'.state.ScopeLive sc

/-- `countdownAt_view` away from one key. -/
theorem countdownAt_off {w : World} {m m' : RState} {key : Guard.GuardKey}
    (view : ObsViewOff key m m') {waiter : FiberId} {token : Nat} {incoming : Ty → Ty → Prop}
    (off : (waiter, token) ≠ key) (h : CountdownAt w m waiter token incoming) :
    CountdownAt w m' waiter token incoming := by
  unfold CountdownAt at h ⊢
  cases h' : m'.fiber? waiter with
  | none => trivial
  | some f' =>
    obtain ⟨f, h0, _, weak⟩ := view.fibers waiter f' h'
    rw [h0] at h
    dsimp only at h ⊢
    cases hfind : f'.pending.find? (fun pending => pending.token = token) with
    | none => trivial
    | some pending =>
      rw [weak token pending off hfind] at h
      dsimp only at h ⊢
      obtain ⟨answer, error, tokenTy, payload, incomingOk⟩ := h
      refine ⟨answer, error, tokenTy, ⟨payload.token, payload.collected, ?_, payload.resume⟩,
        incomingOk⟩
      intro id member target lookup
      obtain ⟨old, hold, hid, _⟩ := view.fibers id target lookup
      rw [hid]
      exact payload.targets id member old hold

theorem storedObserverOk_off {root : ProgramSource} {w : World} {m m' : RState}
    {key : Guard.GuardKey} (view : ObsViewOff key m m') {source : FiberId} (o : Observer)
    (off : key ∉ Guard.observerKeys o) (h : StoredObserverOk root w m source o) :
    StoredObserverOk root w m' source o := by
  cases o with
  | resumeAwait waiter token mode => exact h
  | countdown waiter token =>
    refine countdownAt_off view (fun same => off ?_) h
    rw [← same]
    exact List.mem_singleton_self _
  | raceCallback raceId =>
    unfold StoredObserverOk at h ⊢
    dsimp only at h ⊢
    rw [view.races]
    exact h
  | dropScopeFinalizer scope k => exact view.scopes scope h
  | untrackChild parent => trivial
  | callback k => trivial

theorem observerCommandOk_off {root : ProgramSource} {w : World} {m m' : RState}
    {key : Guard.GuardKey} (view : ObsViewOff key m m') {source : FiberId} {exit : ExitV}
    (o : Observer) (off : key ∉ Guard.observerKeys o)
    (h : ObserverCommandOk root w m source exit o) : ObserverCommandOk root w m' source exit o := by
  cases o with
  | resumeAwait waiter token mode => exact h
  | countdown waiter token =>
    refine countdownAt_off view (fun same => off ?_) h
    rw [← same]
    exact List.mem_singleton_self _
  | raceCallback raceId =>
    unfold ObserverCommandOk at h ⊢
    dsimp only at h ⊢
    rw [view.races]
    exact h
  | dropScopeFinalizer scope k => exact view.scopes scope h
  | untrackChild parent => trivial
  | callback k => trivial

theorem enrollRaceOk_off {root : ProgramSource} {w : World} {m m' : RState}
    {key : Guard.GuardKey} (view : ObsViewOff key m m') (ids : m.nextId ≤ m'.nextId)
    {raceId : Nat} {child : FiberId}
    (h : EnrollRaceOk root w m raceId child) : EnrollRaceOk root w m' raceId child := by
  unfold EnrollRaceOk at h ⊢
  obtain ⟨below, h⟩ := h
  refine ⟨Nat.lt_of_lt_of_le below ids, ?_⟩
  rw [view.races]
  cases hr : m.race? raceId with
  | none => trivial
  | some race =>
    cases h' : m'.fiber? child with
    | none => trivial
    | some c' =>
      obtain ⟨c, h0, hid, _⟩ := view.fibers child c' h'
      rw [hr, h0] at h
      dsimp only at h ⊢
      rw [hid]
      exact h

/-- `fiberTyped_transport` away from one key: the fiber's stored observers do not hold it. -/
theorem fiberTyped_transport_off {root : ProgramSource} {w : World} {m m' : RState} {x : RFiber}
    {key : Guard.GuardKey} (h : FiberTyped root w m x) (view : ObsViewOff key m m')
    (off : ∀ o ∈ x.observers, key ∉ Guard.observerKeys o) (nextId : m.nextId ≤ m'.nextId)
    (nextToken : m.nextToken ≤ m'.nextToken) : FiberTyped root w m' x := by
  refine ⟨h.ok, h.delivery_races (racesKept_of_eq view.races), Nat.lt_of_lt_of_le h.below nextId,
    h.pendingShape, h.parkedIdle,
    fun token hp => Nat.lt_of_lt_of_le (h.parkedBelow token hp) nextToken, h.exited,
    h.exitedStack, h.deferredCause, h.pendingOwner,
    fun o ho => storedObserverOk_off view o (off o ho) (h.observers o ho),
    fun raceId marker => ?_, h.code_races (racesKept_of_eq view.races), h.tokens,
    fun r race hr o ho => h.raceObservers r race ((view.races r).symm.trans hr) o ho,
    fun p hp id hid => Nat.lt_of_lt_of_le (h.targetsBelow p hp id hid) nextId,
    fun o ho k hk => Nat.lt_of_lt_of_le (h.observersBelow o ho k hk) nextId, h.children⟩
  obtain ⟨race, resultTy, found, host, token, reply⟩ := h.registration raceId marker
  exact ⟨race, resultTy, (view.races raceId).trans found, host, token,
    stackReply_races (racesKept_of_eq view.races) reply⟩

/-- `queueOk_transport` away from one key: no queued observer holds it, and the fiber-id
supply does not shrink. -/
theorem queueOk_transport_off {root : ProgramSource} {w : World} {m m' : RState} {q : List RCmd}
    {key : Guard.GuardKey} (queue : QueueOk root w m q) (view : ObsViewOff key m m')
    (ids : m.nextId ≤ m'.nextId)
    (off : ∀ s e o, .observe s e o ∈ q → key ∉ Guard.observerKeys o)
    (authority : ∀ c ∈ q, CommandAuthorityR m c → CommandAuthorityR m' c)
    (delivery : ∀ c ∈ q, CommandDeliveryOk root w m c → CommandDeliveryOk root w m' c)
    (requests : ∀ fiber token r, requestOfR m' fiber token = some r → requestOfR m fiber token = some r)
    (tokens : m.nextToken ≤ m'.nextToken) : QueueOk root w m' q := by
  have same : Guard.commandOwner (Code := RProgram) m' = Guard.commandOwner m := by
    funext c
    cases c with
    | registrationDone raceId yielding =>
      simp only [Guard.commandOwner, view.races]
    | _ => rfl
  have owners : q.filterMap (Guard.commandOwner m') = q.filterMap (Guard.commandOwner m) := by
    rw [same]
  refine ⟨queue.payload, fun c hc => authority c hc (queue.authority c hc),
    fun c hc => delivery c hc (queue.delivery c hc), owners ▸ queue.owners, queue.registration,
    ⟨fun k hk => Nat.lt_of_lt_of_le (queue.keys.below k hk) tokens,
      fun fiber token r hr hk => queue.keys.disjoint fiber token r (requests fiber token r hr) hk⟩,
    fun s e o ho => ⟨Nat.lt_of_lt_of_le (queue.observer s e o ho).1 ids,
      observerCommandOk_off view o (off s e o ho) (queue.observer s e o ho).2⟩,
    fun r c hc => enrollRaceOk_off view ids (queue.enroll r c hc), queue.noRaceAfterInterrupt,
    fun md sc tg ir ex hl => ?_,
    fun s e o ho r race hr => queue.raceObservers s e o ho r race ((view.races r).symm.trans hr)⟩
  obtain ⟨live, present⟩ := queue.links md sc tg ir ex hl
  exact ⟨view.scopes sc live, view.exists_ tg present⟩

/-- `obsView_rupdate` for an edit that adds a park at one token of the edited fiber. -/
theorem obsViewOff_rupdate {m : RState} {f g : RFiber} (hf : m.fiber? f.id = some f)
    (hid : g.id = f.id) {token₀ : Nat} (pending : PendingWeakerOff token₀ f.pending g.pending) :
    ObsViewOff (g.id, token₀) m (m.update g) := by
  refine ⟨fun id f' h' => ?_, fun id h => ?_, fun _ => rfl, fun _ h => h⟩
  · rw [rfiber?_update] at h'
    cases h0 : m.fiber? id with
    | none =>
      rw [h0] at h'
      cases h'
    | some x =>
      rw [h0, Option.map_some] at h'
      cases h'
      by_cases hx : x.id = g.id
      · rw [if_pos hx]
        have same : x = f := rfiber?_same hf h0 (hx.trans hid)
        subst same
        refine ⟨x, rfl, hid, fun token p off found => pending token p (fun t => off ?_) found⟩
        have idEq : id = g.id := (rfiber?_id h0).symm.trans hx
        rw [idEq, t]
      · rw [if_neg hx]
        exact ⟨x, rfl, rfl, fun _ _ _ found => found⟩
  · rw [rfiber?_update, Option.isSome_map]
    exact h

/-- **A park edit by an owner-free fiber keeps `I`**: `configTyped_rupdate_owner` with the pending
lookup weakened only at the park's key `(g.id, token₀)`, which no stored and no queued observer
holds. The fiber-edit guarantee builder `note.md` §4 asks for, at a park. -/
theorem configTyped_rupdate_park {root : ProgramSource} {rootTy : EffTy} {w : World}
    {m : RState} {q : List RCmd} {f g : RFiber} (typed : ConfigTyped root rootTy w m q)
    (hf : m.fiber? f.id = some f) (hid : g.id = f.id) {token₀ : Nat}
    (pending : PendingWeakerOff token₀ f.pending g.pending)
    (storedOff : ∀ x ∈ m.fibers, ∀ o ∈ x.observers, (g.id, token₀) ∉ Guard.observerKeys o)
    (queuedOff : ∀ s e o, .observe s e o ∈ q → (g.id, token₀) ∉ Guard.observerKeys o)
    (free : f.id ∉ q.filterMap (Guard.commandOwner m))
    (keys : ∀ k ∈ Guard.fiberKeys g, k ∈ Guard.internalKeys m ∨
      (k.2 < m.nextToken ∧ requestOfR m k.1 k.2 = none))
    (request : ∀ token r, requestOfR (m.update g) g.id token = some r →
      requestOfR m f.id token = some r)
    (auth : ∀ c ∈ q, CommandAuthorityR m c → CommandAuthorityR (m.update g) c)
    (readG : g.running = true → ReadsCode g.id q → raceRegistrationR g.frame.current = none →
      ∀ ty, w.Γ g.id = some ty → SavedOk (TypedProg root) ExitOk (frameProtocols root) w ty g.frame)
    (fresh : FiberTyped root w (m.update g) g) : ConfigTyped root rootTy w (m.update g) q := by
  have view : ObsViewOff (g.id, token₀) m (m.update g) := obsViewOff_rupdate hf hid pending
  obtain ⟨machine, code, queue⟩ := typed
  refine ⟨machineTyped_of (machineWide_rupdate machine.wide hid keys request) (fun x hx => ?_),
    ?_, queueOk_transport_off queue view (Nat.le_refl _) queuedOff auth
      (fun c hc h => commandDelivery_owner hid free c hc h) ?_ (Nat.le_refl _)⟩
  · rcases mem_rupdate hx with rfl | ⟨hold, _⟩
    · exact fresh
    · exact fiberTyped_transport_off (machine.fiber hold) view (storedOff _ hold) (Nat.le_refl _)
        (Nat.le_refl _)
  · intro x hx hrun reads marker ty declared
    rcases mem_rupdate hx with rfl | ⟨hold, _⟩
    · exact Or.inl (codeOk_of_saved (readG hrun reads marker ty declared))
    · exact (code x hold hrun reads marker ty declared).races (racesKept_of_eq view.races)
  · intro fiber token r hr
    by_cases same : fiber = g.id
    · subst same
      rw [hid]
      exact request token r hr
    · rw [requestOfR_congr (rfiber?_update_other same)] at hr
      exact hr

/-- A race registration marker is no external request: a host parked on it has none. -/
theorem externalRequestR_of_marker {p : RProgram} {raceId : Nat}
    (h : raceRegistrationR p = some raceId) : externalRequestR p = none := by
  unfold raceRegistrationR at h
  split at h
  · rfl
  · cases h

/-! ## 2. The race's cancel frame

`registrationDone`'s park pushes `AsyncFinalizer (cancelName (raceCancelName race) host token)`
(`Machine/Fibers.lean:1928-1929`). At the term instance its cancel program is
`fiberInterruptAll` of the live entrants (`denoteCancel`, `denoteStoreCancel`,
`Laws/Program/InterpR.lean:205-215`; `raceCancelName`, `:362`), which answers `unit` and never
fails with a typed error, then the incoming failure. So the frame passes the race's type through
(`frameProtocols`' `asyncFinalizer` clause). -/

theorem raceCancelThenFail_typed (root : ProgramSource) {w : World} {ty : EffTy} (raceId : Nat)
    (host : FiberId) (token : Nat) {cause : CauseV} (typed : ExitOk w ty (.failure cause)) :
    TypedProg root w ty ((interpR root.program).cancelThenFail
      ((interpR root.program).cancelName ((interpR root.program).raceCancelName raceId) host token)
      cause) := by
  show TypedProg root w ty ((guardR .onSuccess (fiberValR (.cancelRace raceId) rfl)).bind
    (seqR fun _ => .pure (.failure cause)))
  refine seq_typed_clean root (mid := EffTy.pure .unit) ?_
    (fun w' o _ _ => TypedProg.pure (strongExit_mono _ _ _ _ o typed)) rfl
  refine TypedProg.fiber (fun _ h => nomatch h) (fun _ h => nomatch h) (fun _ h => nomatch h)
    (fun _ _ _ h => nomatch h) PUnit.unit trivial ?_
  intro w' _ ans post
  have unit : ans = Val.unit := post
  subst unit
  exact TypedProg.pure ⟨trivial, trivial⟩

/-- The race's cancel frame on top of a stack accepted at the race's type. -/
theorem stackAccepts_raceFinalizer (root : ProgramSource) {w : World} {ty final : EffTy}
    (raceId : Nat) (host : FiberId) (token : Nat) {stack : List ScopeFrame}
    (h : StackAccepts (TypedProg root) ExitOk (frameProtocols root) w ty final stack) :
    StackAccepts (TypedProg root) ExitOk (frameProtocols root) w ty final
      (.asyncFinalizer ((interpR root.program).cancelName
        ((interpR root.program).raceCancelName raceId) host token) :: stack) :=
  .cons (.asyncFinalizer _ fun _ _ => ⟨rfl, fun _ _ _ typed _ =>
    raceCancelThenFail_typed root raceId host token typed⟩) h

/-- The race's cancellation frame pushed on a host stack (decisions row 188 (b)). -/
theorem hostStack_raceFinalizer (root : ProgramSource) {w : World} {m : RState} {ty final : EffTy}
    (raceId : Nat) (host : FiberId) (token : Nat) {owner : FiberId} {stack : List ScopeFrame}
    (h : HostStack root w m owner ty final stack) :
    HostStack root w m owner ty final
      (.asyncFinalizer ((interpR root.program).cancelName
        ((interpR root.program).raceCancelName raceId) host token) :: stack) :=
  hostStack_push (.asyncFinalizer _ fun _ _ => ⟨rfl, fun _ _ _ typed _ =>
    raceCancelThenFail_typed root raceId host token typed⟩) h

/-! ## 3. The step -/

/-- **`registrationDone` keeps `I`** at the same world (Concept 4, scheduler step preservation;
`Machine/Fibers.lean:1912-1931`). The head's authority names the race and its running, unparked
host on the race's marker; `RegistrationState` gives the race token's declared type `resultTy`
and a host stack accepting it (`StackReply`); `RaceOk` gives the race column at that type
(`RacePayload`), which does not read `registering`. An accepted exit is typed by the column and
installed as `raceSettle` (`raceSettle_typed`) under the queued `loop`. With no answer the cancel
frame is pushed (`stackAccepts_raceFinalizer`): a deferred interrupt clears the park and the
queued `loop` reads the marker, which `ReadCode` leaves to `RegistrationState`; otherwise the host
parks idle at the race key with a `void` record, which no observer reads (decisions row 134 (d);
`configTyped_rupdate_park`), and the race retains its declared token. -/
theorem registrationDone_preserves (root : ProgramSource) (rootTy : EffTy) (raceId : Nat)
    (yielding : Bool) : StepPreserves root rootTy (.registrationDone raceId yielding) := by
  intro w m rest _ typed
  refine ⟨w, leHost_refl w, ?_⟩
  have tail := configTyped_tail typed
  have wide := typed.machine.wide
  obtain ⟨race, f, hr, hfound, running, parked, marker⟩ : ∃ race f, m.race? raceId = some race ∧
      m.fiber? race.host = some f ∧ f.running = true ∧ f.parked = .notParked ∧
      raceRegistrationR f.frame.current = some raceId :=
    typed.queue.authority _ List.mem_cons_self
  have fid : f.id = race.host := rfiber?_id hfound
  have hf : m.fiber? f.id = some f := by rw [fid]; exact hfound
  have hmem : f ∈ m.fibers := rfiber?_mem hf
  have old : FiberTyped root w m f := typed.machine.fiber hmem
  have live : f.exit = none := by
    cases hx : f.exit with
    | none => rfl
    | some _ =>
      have idle := (old.exited (by rw [hx]; rfl)).2
      rw [running] at idle
      cases idle
  obtain ⟨race₀, resultTy, found₀, _, declared, final, hfinal, stackOk, prov⟩ :=
    old.registration raceId marker
  have e₀ : race = race₀ := Option.some.inj (hr.symm.trans found₀)
  subst e₀
  have hrace : race ∈ m.races := List.mem_of_find?_eq_some hr
  obtain ⟨resultTy', payload⟩ := wide.races race hrace
  have e₁ : resultTy = resultTy' := Option.some.inj (declared.symm.trans payload.token)
  subst e₁
  have rid : race.id = raceId := rrace?_id hr
  have hr' : m.race? race.id = some race := by rw [rid]; exact hr
  have payload' : RacePayload root w { race with registering := false } resultTy :=
    ⟨payload.token, payload.failures, payload.winner, payload.accepted, payload.cleanup,
      payload.live, payload.programs⟩
  have freeF : f.id ∉ rest.filterMap (Guard.commandOwner m) := by
    rw [fid]
    exact owner_free typed.queue (by simp only [Guard.commandOwner, hr, Option.map_some])
  have finalOf : ∀ ty, w.Γ f.id = some ty → ty = final := by
    intro ty d
    rw [hfinal] at d
    cases d
    rfl
  simp only [driveStep]
  rw [hr]
  dsimp only
  split
  · next hnone => exact nomatch (hnone.symm.trans hfound)
  · next f' hf' =>
    have e₂ : f = f' := Option.some.inj (hfound.symm.trans hf')
    subst e₂
    split
    -- the accepted exit: the settle program continues the same entry (`:1920-1926`)
    · next exit hacc =>
      have code := raceSettle_typed root (w := w) raceId race.state.cleanupNeeded
        (payload.accepted exit hacc)
      let g : RFiber := { f with frame := { f.frame with
        current := (interpR root.program).raceSettle raceId race.state.cleanupNeeded exit } }
      have look : (m.update g).fiber? g.id = some g := rfiber?_update_self hf rfl
      have view : ObsView m (m.update g) := obsView_rupdate (g := g) hf rfl (PendingWeaker.refl _)
      have moved := fiberTyped_transport old view (Nat.le_refl _) (Nat.le_refl _)
      have provG : InterruptProvenance g.frame := ⟨prov.recorded, prov.deferred⟩
      have notMarker : raceRegistrationR g.frame.current = none := raceRegistrationR_typed code
      have codeG : ∀ ty, w.Γ g.id = some ty → CodeOk root w (m.update g) g.id ty g.frame := by
        intro ty d
        rw [finalOf ty d]
        exact ⟨resultTy, code, hostStack_races (racesKept_of_eq view.races) stackOk, provG⟩
      have frameOk : ∀ ty, w.Γ g.id = some ty →
          ∃ tin, PositionStack root w tin ty g.frame.stack ∧ InterruptProvenance g.frame := by
        intro ty d
        rw [finalOf ty d]
        exact ⟨resultTy, positionStack_of_host stackOk, provG⟩
      have fresh : FiberTyped root w (m.update g) g :=
        { ok := ⟨⟨frameOk⟩, moved.ok.c1, moved.ok.c2, moved.ok.c3, moved.ok.c4, moved.ok.c5⟩
          delivery := fun _ h => by
            rw [show g.parked = f.parked from rfl, parked] at h
            cases h
          below := moved.below
          pendingShape := moved.pendingShape
          parkedIdle := moved.parkedIdle
          parkedBelow := moved.parkedBelow
          exited := moved.exited
          exitedStack := fun hx => absurd (moved.exited hx).2 (by rw [running]; decide)
          deferredCause := moved.deferredCause
          pendingOwner := moved.pendingOwner
          observers := moved.observers
          registration := fun _ marker' => by
            rw [notMarker] at marker'
            cases marker'
          code := fun _ _ _ _ ty d => codeG ty d
          tokens := moved.tokens
          raceObservers := moved.raceObservers
          targetsBelow := moved.targetsBelow
          observersBelow := moved.observersBelow
          children := moved.children }
      have noRequest : ∀ tok r, requestOfR (m.update g) g.id tok = some r →
          requestOfR m f.id tok = some r := by
        intro tok r hreq
        have off : g.parked ≠ .withGuard tok := by
          rw [show g.parked = f.parked from rfl, parked]
          exact fun h => nomatch h
        rw [requestOfR_of_not_parked look off] at hreq
        cases hreq
      have edited := configTyped_rupdate_code (g := g) tail hf rfl (PendingWeaker.refl _) rfl
        (fun p => ⟨p.recorded, p.deferred⟩) (fun k hk => Or.inl (fiberKeys_internal hmem hk))
        noRequest (fun c hc h => commandAuthority_flags (g := g) hf rfl rfl rfl rfl freeF c hc h)
        (fun _ _ _ ty d => Or.inl (codeG ty d)) fresh
      have freeG : g.id ∉ rest.filterMap (Guard.commandOwner (m.update g)) := by
        rw [commandOwner_update]
        exact freeF
      have looped := configTyped_cons_loop edited look running parked freeG yielding
        fun _ ty d => codeG ty d
      have hrU : (m.update g).race? race.id = some race := hr'
      exact configTyped_updateRace looped hrU rfl rfl rfl (new := { race with registering := false })
        payload' (fun _ h => Or.inl h)
    · -- no answer: push the race's cancel frame and park on the race token (`:1927-1931`)
      have stackP : HostStack root w m f.id resultTy final
          (.asyncFinalizer ((interpR root.program).cancelName
            ((interpR root.program).raceCancelName raceId) f.id race.token) :: f.frame.stack) :=
        hostStack_raceFinalizer root raceId f.id race.token stackOk
      unfold settle
      dsimp only
      split
      · -- a deferred interrupt: the park is cleared, the same entry continues (`:662-667`)
        let g : RFiber := { f with
          frame := { f.frame with stack := .asyncFinalizer ((interpR root.program).cancelName
            ((interpR root.program).raceCancelName raceId) f.id race.token) :: f.frame.stack }
          parked := .notParked
          pending := [] }
        have look : (m.update g).fiber? g.id = some g := rfiber?_update_self hf rfl
        have hpOf : g.pending = [] := rfl
        have cleared : PendingWeaker f.pending g.pending := by
          intro _ _ h
          rw [hpOf] at h
          cases h
        have view : ObsView m (m.update g) := obsView_rupdate (g := g) hf rfl cleared
        have moved := fiberTyped_transport old view (Nat.le_refl _) (Nat.le_refl _)
        have provG : InterruptProvenance g.frame := ⟨prov.recorded, prov.deferred⟩
        have markerG : raceRegistrationR g.frame.current = some raceId := marker
        have frameOk : ∀ ty, w.Γ g.id = some ty →
            ∃ tin, PositionStack root w tin ty g.frame.stack ∧ InterruptProvenance g.frame := by
          intro ty d
          rw [finalOf ty d]
          exact ⟨resultTy, positionStack_of_host stackP, provG⟩
        have registrationG : ∀ raceId', raceRegistrationR g.frame.current = some raceId' →
            ∃ race' resultTy', (m.update g).race? raceId' = some race' ∧ race'.host = g.id ∧
              w.Θ race'.host race'.token = some resultTy' ∧
                StackReply root w (m.update g) g resultTy' := by
          intro raceId' marker'
          have e : raceId = raceId' := Option.some.inj (markerG.symm.trans marker')
          subst e
          exact ⟨race, resultTy, hr, fid.symm, declared, final, hfinal,
            hostStack_races (racesKept_of_eq view.races) stackP, provG⟩
        have pendingOk : ∀ p ∈ g.pending, ∃ id, (w.Θ id p.token).isSome = true :=
          fun _ hp => absurd hp List.not_mem_nil
        have fresh : FiberTyped root w (m.update g) g :=
          { ok := ⟨⟨frameOk⟩, pendingOk, moved.ok.c2, moved.ok.c3, moved.ok.c4, moved.ok.c5⟩
            delivery := fun _ h => by
              rw [show g.parked = .notParked from rfl] at h
              cases h
            below := moved.below
            pendingShape := by
              show g.pending = []
              exact hpOf
            parkedIdle := fun h => absurd (show g.parked = .notParked from rfl) h
            parkedBelow := fun _ h => by
              rw [show g.parked = .notParked from rfl] at h
              cases h
            exited := fun hx => by
              rw [show g.exit = none from live] at hx
              cases hx
            exitedStack := fun hx => by
              rw [show g.exit = none from live] at hx
              cases hx
            deferredCause := moved.deferredCause
            pendingOwner := fun _ hp => absurd hp List.not_mem_nil
            observers := moved.observers
            registration := registrationG
            code := fun _ h => by
              rw [show g.running = true from running] at h
              cases h
            tokens := fun _ h => by
              rw [show g.parked = .notParked from rfl] at h
              cases h
            raceObservers := moved.raceObservers
            targetsBelow := fun _ hp => absurd hp List.not_mem_nil
            observersBelow := moved.observersBelow
            children := moved.children }
        have noRequest : ∀ tok r, requestOfR (m.update g) g.id tok = some r →
            requestOfR m f.id tok = some r := by
          intro tok r hreq
          have off : g.parked ≠ .withGuard tok := by
            rw [show g.parked = .notParked from rfl]
            exact fun h => nomatch h
          rw [requestOfR_of_not_parked look off] at hreq
          cases hreq
        have edited := configTyped_rupdate_owner (g := g) tail hf rfl cleared
          freeF (fun k hk => Or.inl (fiberKeys_internal hmem hk)) noRequest
          (fun c hc h => commandAuthority_flags (g := g) hf rfl rfl parked.symm rfl freeF c hc h)
          (fun _ _ h => nomatch (h.symm.trans markerG)) fresh
        have freeG : g.id ∉ rest.filterMap (Guard.commandOwner (m.update g)) := by
          rw [commandOwner_update]
          exact freeF
        have looped := configTyped_cons_loop edited look running rfl freeG yielding
          fun h => nomatch (h.symm.trans markerG)
        have hrU : (m.update g).race? race.id = some race := hr'
        exact configTyped_emit (configTyped_updateRace looped hrU rfl rfl rfl
          (new := { race with registering := false }) payload' (fun _ h => Or.inl h))
          [RunEvent.parkedOn f.id race.token]
      · -- the park: idle at the race key, a `void` record that no observer reads (row 134 (d))
        let pend : RPending := ⟨race.token, none, [], [], Resume.void, false⟩
        let g : RFiber := { f with
          frame := { f.frame with stack := .asyncFinalizer ((interpR root.program).cancelName
            ((interpR root.program).raceCancelName raceId) f.id race.token) :: f.frame.stack }
          parked := .withGuard race.token
          pending := f.pending ++ [pend]
          running := false }
        have hpend : f.pending = [] := by
          have shape := old.pendingShape
          unfold Guard.PendingShape at shape
          rw [parked] at shape
          exact shape
        have hpOf : g.pending = f.pending ++ [pend] := rfl
        have look : (m.update g).fiber? g.id = some g := rfiber?_update_self hf rfl
        have keyEq : (g.id, race.token) = (race.host, race.token) := by
          rw [show g.id = race.host from fid]
        have weakOff : PendingWeakerOff race.token f.pending g.pending := by
          rw [hpOf, hpend]
          exact pendingWeakerOff_single pend
        have view : ObsViewOff (g.id, race.token) m (m.update g) := obsViewOff_rupdate (g := g) hf rfl weakOff
        have provG : InterruptProvenance g.frame := ⟨prov.recorded, prov.deferred⟩
        have markerG : raceRegistrationR g.frame.current = some raceId := marker
        have tokenOf : ∀ token, g.parked = .withGuard token → token = race.token := by
          intro token h
          have h' : Parked.withGuard race.token = .withGuard token := h
          injection h' with e
          exact e.symm
        have declaredG : w.Θ g.id race.token = some resultTy := by
          rw [show g.id = race.host from fid]
          exact declared
        have frameOk : ∀ ty, w.Γ g.id = some ty →
            ∃ tin, PositionStack root w tin ty g.frame.stack ∧ InterruptProvenance g.frame := by
          intro ty d
          rw [finalOf ty d]
          exact ⟨resultTy, positionStack_of_host stackP, provG⟩
        have registrationG : ∀ raceId', raceRegistrationR g.frame.current = some raceId' →
            ∃ race' resultTy', (m.update g).race? raceId' = some race' ∧ race'.host = g.id ∧
              w.Θ race'.host race'.token = some resultTy' ∧
                StackReply root w (m.update g) g resultTy' := by
          intro raceId' marker'
          have e : raceId = raceId' := Option.some.inj (markerG.symm.trans marker')
          subst e
          exact ⟨race, resultTy, hr, fid.symm, declared, final, hfinal,
            hostStack_races (racesKept_of_eq view.races) stackP, provG⟩
        have pendingOk : ∀ p ∈ g.pending, ∃ id, (w.Θ id p.token).isSome = true := by
          intro p hp
          rw [hpOf] at hp
          rcases List.mem_append.mp hp with h | h
          · exact old.ok.c1 p h
          · rw [List.mem_singleton] at h
            subst h
            refine ⟨g.id, ?_⟩
            show (w.Θ g.id race.token).isSome = true
            rw [declaredG]
            rfl
        have pendingOwnerG : ∀ p ∈ g.pending, (w.Θ g.id p.token).isSome = true := by
          intro p hp
          rw [hpOf] at hp
          rcases List.mem_append.mp hp with h | h
          · exact old.pendingOwner p h
          · rw [List.mem_singleton] at h
            subst h
            show (w.Θ g.id race.token).isSome = true
            rw [declaredG]
            rfl
        have targetsG : ∀ p ∈ g.pending, ∀ id ∈ p.waitingOn.toList ++ p.remaining,
            id.value < m.nextId := by
          intro p hp id hid
          rw [hpOf] at hp
          rcases List.mem_append.mp hp with h | h
          · exact old.targetsBelow p h id hid
          · rw [List.mem_singleton] at h
            subst h
            have hnil : pend.waitingOn.toList ++ pend.remaining = [] := rfl
            rw [hnil] at hid
            exact absurd hid List.not_mem_nil
        have observersG : ∀ o ∈ g.observers, StoredObserverOk root w (m.update g) g.id o := by
          intro o ho
          refine storedObserverOk_off view o ?_ (old.observers o ho)
          rw [keyEq]
          exact old.raceObservers raceId race hr o ho
        have fresh : FiberTyped root w (m.update g) g :=
          { ok := ⟨⟨frameOk⟩, pendingOk, old.ok.c2, old.ok.c3, old.ok.c4, old.ok.c5⟩
            delivery := fun token h => by
              rw [tokenOf token h]
              exact ⟨resultTy, final, declaredG, hfinal,
                hostStack_races (racesKept_of_eq view.races) stackP, provG⟩
            below := old.below
            pendingShape := by
              show ∃ p, g.pending = [p] ∧ p.token = race.token
              rw [hpOf, hpend]
              exact ⟨pend, rfl, rfl⟩
            parkedIdle := fun _ => rfl
            parkedBelow := fun token h => by
              rw [tokenOf token h]
              exact wide.keysBelow _ (raceKey_internal hrace)
            exited := fun hx => by
              rw [show g.exit = none from live] at hx
              cases hx
            exitedStack := fun hx => by
              rw [show g.exit = none from live] at hx
              cases hx
            deferredCause := old.deferredCause
            pendingOwner := pendingOwnerG
            observers := observersG
            registration := registrationG
            code := fun _ _ h => nomatch (h.symm.trans markerG)
            tokens := fun token h => by
              rw [tokenOf token h, declaredG]
              rfl
            raceObservers := old.raceObservers
            targetsBelow := targetsG
            observersBelow := old.observersBelow
            children := old.children }
        have noRequest : ∀ tok r, requestOfR (m.update g) g.id tok = some r →
            requestOfR m f.id tok = some r := by
          intro tok r hreq
          by_cases hp : g.parked = .withGuard tok
          · rw [requestOfR_of_parked look hp, externalRequestR_of_marker markerG] at hreq
            cases hreq
          · rw [requestOfR_of_not_parked look hp] at hreq
            cases hreq
        have edited := configTyped_rupdate_park (g := g) tail hf rfl weakOff
          (fun x hx o ho => by
            rw [keyEq]
            exact (typed.machine.fiber hx).raceObservers raceId race hr o ho)
          (fun s e o ho => by
            rw [keyEq]
            exact typed.queue.raceObservers s e o (List.mem_cons_of_mem _ ho) raceId race hr)
          freeF (fun k hk => Or.inl (fiberKeys_internal hmem hk)) noRequest
          (fun c hc h => commandAuthority_unowned (g := g) hf rfl live freeF tail.queue.registration c hc h)
          (fun h => Bool.noConfusion h) fresh
        have hrU : (m.update g).race? race.id = some race := hr'
        exact configTyped_emit (configTyped_updateRace edited hrU rfl rfl rfl
          (new := { race with registering := false }) payload' (fun _ h => Or.inl h))
          [RunEvent.parkedOn f.id race.token]

end Effect4.Program.Typed
