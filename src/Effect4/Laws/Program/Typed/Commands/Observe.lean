import Effect4.Laws.Program.Typed.Commands.Launch

/-!
# Laws.Program.Typed.Commands.Observe — `observe` keeps the typed configuration

The last arm of wave 2's first command group (seat D3): `observe` fires one observer of an exited
fiber (`fireObserver`, `Machine/Fibers.lean:1660-1726`). Its one halting arm, a scope-finalizer
drop on an absent scope (`:1669-1671`), is excluded by `ObserverCommandOk`'s `Stores.ScopeLive`.

The resume, untrack, drop and callback arms are short. The race callback is
`observe_raceCallback` (`Bookkeeping.lean`). The countdown arm (`:1673-1705`) is the long one:
it advances the waiter's pending record, so every correlation that reads that record
(`CountdownAt`, keyed by the waiter and the token) is re-proved over the new record, and every
other one moves by a view that agrees on all other records (`ExceptView`). The new record is
typed at the countdown's columns, pinned by the token's declaration when the record resumes with
the exits (`Resume.exitsValue`) and at `unknown` otherwise, where no column is read.
-/

set_option autoImplicit false
namespace Effect4.Program.Typed
open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Sched Effect4.Program.Denote
open Contracts

/-! ## A view that agrees on every pending record but one -/

/-- Pending records agree at every token the predicate does not skip. -/
def PendingExcept (old new : List RPending) (skip : Nat → Prop) : Prop :=
  ∀ token p, ¬ skip token → new.find? (fun q => q.token = token) = some p →
    old.find? (fun q => q.token = token) = some p

/-- Two machines whose lookups agree, whose pending records agree except at `key`, whose races
agree and whose second store holds every scope the first does. -/
structure ExceptView (m m' : RState) (key : FiberId × Nat) : Prop where
  fibers : ∀ id f', m'.fiber? id = some f' → ∃ f, m.fiber? id = some f ∧ f'.id = f.id ∧
    PendingExcept f.pending f'.pending (fun token => (id, token) = key)
  exists_ : ∀ id, (m.fiber? id).isSome = true → (m'.fiber? id).isSome = true
  races : ∀ r, m'.race? r = m.race? r
  scopes : ∀ sc, m.state.ScopeLive sc → m'.state.ScopeLive sc

theorem ExceptView.obs_trans {m m' m'' : RState} {key : FiberId × Nat} (a : ObsView m m')
    (b : ExceptView m' m'' key) : ExceptView m m'' key := by
  refine ⟨fun id f'' h'' => ?_, fun id h => b.exists_ id (a.exists_ id h),
    fun r => (b.races r).trans (a.races r), fun sc h => b.scopes sc (a.scopes sc h)⟩
  obtain ⟨f', h', hid', except⟩ := b.fibers id f'' h''
  obtain ⟨f, h, hid, weak⟩ := a.fibers id f' h'
  exact ⟨f, h, hid'.trans hid, fun token p skip hp => weak token p (except token p skip hp)⟩

/-- A countdown correlation at another key moves along the view. -/
theorem countdownAt_except {w : World} {m m' : RState} {key : FiberId × Nat}
    (view : ExceptView m m' key) {waiter : FiberId} {token : Nat} {incoming : Ty → Ty → Prop}
    (hne : (waiter, token) ≠ key) (h : CountdownAt w m waiter token incoming) :
    CountdownAt w m' waiter token incoming := by
  unfold CountdownAt at h ⊢
  cases h' : m'.fiber? waiter with
  | none => trivial
  | some f' =>
    obtain ⟨f, h0, _, except⟩ := view.fibers waiter f' h'
    rw [h0] at h
    dsimp only at h ⊢
    cases hfind : f'.pending.find? (fun pending => pending.token = token) with
    | none => trivial
    | some pending =>
      rw [except token pending hne hfind] at h
      dsimp only at h ⊢
      obtain ⟨answer, error, tokenTy, payload, incomingOk⟩ := h
      refine ⟨answer, error, tokenTy, ⟨payload.token, payload.collected, ?_, payload.resume⟩,
        incomingOk⟩
      intro id member target lookup
      obtain ⟨old, hold, hid, _⟩ := view.fibers id target lookup
      rw [hid]
      exact payload.targets id member old hold

/-- An observer that is not the countdown at `key`. -/
def OffKey (key : FiberId × Nat) (o : Observer) : Prop :=
  ∀ waiter token, o = .countdown waiter token → (waiter, token) ≠ key

/-- Being off the key is decided by the observer's shape and one key comparison. -/
instance (key : FiberId × Nat) (o : Observer) : Decidable (OffKey key o) := by
  cases o with
  | countdown waiter token =>
    exact if h : (waiter, token) = key then isFalse (fun off => off waiter token rfl h)
      else isTrue (fun w t ho => by cases ho; exact h)
  | resumeAwait _ _ _ => exact isTrue (fun _ _ ho => nomatch ho)
  | raceCallback _ => exact isTrue (fun _ _ ho => nomatch ho)
  | dropScopeFinalizer _ _ => exact isTrue (fun _ _ ho => nomatch ho)
  | untrackChild _ => exact isTrue (fun _ _ ho => nomatch ho)
  | callback _ => exact isTrue (fun _ _ ho => nomatch ho)

theorem storedObserverOk_except {root : ProgramSource} {w : World} {m m' : RState}
    {key : FiberId × Nat} (view : ExceptView m m' key) {source : FiberId} (o : Observer)
    (off : OffKey key o) (h : StoredObserverOk root w m source o) :
    StoredObserverOk root w m' source o := by
  cases o with
  | resumeAwait waiter token mode => exact h
  | countdown waiter token => exact countdownAt_except view (off waiter token rfl) h
  | raceCallback raceId =>
    unfold StoredObserverOk at h ⊢
    dsimp only at h ⊢
    rw [view.races]
    exact h
  | dropScopeFinalizer scope key => exact view.scopes scope h
  | untrackChild parent => trivial
  | callback key => trivial

theorem observerCommandOk_except {root : ProgramSource} {w : World} {m m' : RState}
    {key : FiberId × Nat} (view : ExceptView m m' key) {source : FiberId} {exit : ExitV}
    (o : Observer) (off : OffKey key o) (h : ObserverCommandOk root w m source exit o) :
    ObserverCommandOk root w m' source exit o := by
  cases o with
  | resumeAwait waiter token mode => exact h
  | countdown waiter token => exact countdownAt_except view (off waiter token rfl) h
  | raceCallback raceId =>
    unfold ObserverCommandOk at h ⊢
    dsimp only at h ⊢
    rw [view.races]
    exact h
  | dropScopeFinalizer scope key => exact view.scopes scope h
  | untrackChild parent => trivial
  | callback key => trivial

theorem enrollRaceOk_except {root : ProgramSource} {w : World} {m m' : RState}
    {key : FiberId × Nat} (view : ExceptView m m' key) (ids : m.nextId ≤ m'.nextId)
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

/-- A fiber's clauses move along the view, its observers at `key` re-proved by the caller. -/
theorem fiberTyped_except {root : ProgramSource} {w : World} {m m' : RState} {x : RFiber}
    {key : FiberId × Nat} (h : FiberTyped root w m x) (view : ExceptView m m' key)
    (nextId : m.nextId ≤ m'.nextId) (nextToken : m.nextToken ≤ m'.nextToken)
    (keyed : ∀ o ∈ x.observers, ¬ OffKey key o → StoredObserverOk root w m' x.id o) :
    FiberTyped root w m' x := by
  refine ⟨h.ok, h.delivery_races (racesKept_of_eq view.races), Nat.lt_of_lt_of_le h.below nextId,
    h.pendingShape, h.parkedIdle,
    fun token hp => Nat.lt_of_lt_of_le (h.parkedBelow token hp) nextToken, h.exited,
    h.exitedStack, h.deferredCause, h.pendingOwner, fun o ho => ?_, fun raceId marker => ?_,
    h.code_races (racesKept_of_eq view.races), h.tokens,
    fun r race hr o ho => h.raceObservers r race ((view.races r).symm.trans hr) o ho,
    fun p hp id hid => Nat.lt_of_lt_of_le (h.targetsBelow p hp id hid) nextId,
    fun o ho k hk => Nat.lt_of_lt_of_le (h.observersBelow o ho k hk) nextId⟩
  · by_cases off : OffKey key o
    · exact storedObserverOk_except view o off (h.observers o ho)
    · exact keyed o ho off
  · obtain ⟨race, resultTy, found, host, token, reply⟩ := h.registration raceId marker
    exact ⟨race, resultTy, (view.races raceId).trans found, host, token,
      stackReply_races (racesKept_of_eq view.races) reply⟩

/-- The view after replacing one fiber's record by one that agrees on every pending record but
the one at `key`. -/
theorem exceptView_rupdate {m : RState} {y g : RFiber} (hy : m.fiber? y.id = some y)
    (hid : g.id = y.id) {key : FiberId × Nat}
    (agree : PendingExcept y.pending g.pending (fun token => (y.id, token) = key)) :
    ExceptView m (m.update g) key := by
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
        have same : x = y := rfiber?_same hy h0 (hx.trans hid)
        subst same
        have idx : id = x.id := (rfiber?_id h0).symm
        refine ⟨x, rfl, hid, fun token p skip hp => agree token p ?_ hp⟩
        rw [← idx]
        exact skip
      · rw [if_neg hx]
        exact ⟨x, rfl, rfl, fun token p _ hp => hp⟩
  · rw [rfiber?_update, Option.isSome_map]
    exact h

/-- A queued command's delivery facts read an active host's stack; replacing an idle fiber's
record keeps them all. -/
theorem commandDelivery_idle {root : ProgramSource} {w : World} {m : RState} {y g : RFiber}
    (hy : m.fiber? y.id = some y) (hid : g.id = y.id) (idle : y.running = false) (c : RCmd)
    (hauth : CommandAuthorityR m c) (h : CommandDeliveryOk root w m c) :
    CommandDeliveryOk root w (m.update g) c := by
  have other : ∀ host, Guard.ActiveAt m host → host ≠ g.id := by
    rintro host ⟨x, hx, running, _⟩ same
    rw [same, hid] at hx
    rw [hy] at hx
    cases hx
    rw [idle] at running
    cases running
  have kept : RacesKept m (m.update g) := racesKept_of_eq fun _ => rfl
  cases c with
  | afterInterrupt host _ kind =>
    intro f' hf'
    rw [rfiber?_update_other (other host hauth)] at hf'
    obtain ⟨replyTy, ok, reply⟩ := h f' hf'
    exact ⟨replyTy, ok, stackReply_races kept reply⟩
  | raceCancel _ host _ remaining visited =>
    intro f' hf'
    rw [rfiber?_update_other (other host hauth)] at hf'
    obtain ⟨answer, error, cols, reply⟩ := h f' hf'
    exact ⟨answer, error, cols, stackReply_races kept reply⟩
  | closeParAwait host _ targets =>
    intro f' hf'
    rw [rfiber?_update_other (other host hauth)] at hf'
    obtain ⟨answer, error, cols, protocol, reply⟩ := h f' hf'
    exact ⟨answer, error, cols, protocol, stackReply_races kept reply⟩
  | finish host _ =>
    intro f' hf'
    rw [rfiber?_update_other (other host hauth)] at hf'
    exact h f' hf'
  | evaluate _ => trivial
  | loop _ _ => trivial
  | deliver _ _ => trivial
  | resume _ _ _ => trivial
  | launch _ => trivial
  | enrollRace _ _ => trivial
  | registrationDone _ _ => trivial
  | interruptTarget _ _ _ => trivial
  | trackChild _ _ => trivial
  | observe _ _ _ => trivial
  | exitDone _ => trivial
  | link _ _ _ _ _ => trivial
  | drainDue => trivial
  | wake _ _ => trivial

/-- **Replacing an idle fiber's record keeps `I`** when the new record is typed on the new machine,
agrees with the old on every pending record but the one at `key`, and every correlation that
reads the record at `key` (a stored countdown observer on another fiber, a queued countdown
`observe`) is re-proved there. The replaced fiber is idle and unexited, so no queued command's
authority or delivery reads it (`commandAuthority_idle`, `commandDelivery_idle`). -/
theorem configTyped_replace {root : ProgramSource} {rootTy : EffTy} {w : World} {M : RState}
    {Q : List RCmd} (typed : ConfigTyped root rootTy w M Q) {y g : RFiber}
    (hy : M.fiber? y.id = some y) (hid : g.id = y.id) (idle : y.running = false)
    (live : y.exit = none) (gIdle : g.running = false) {key : FiberId × Nat}
    (agree : PendingExcept y.pending g.pending (fun token => (y.id, token) = key))
    (keys : ∀ k ∈ Guard.fiberKeys g, k ∈ Guard.internalKeys M ∨
      (k.2 < M.nextToken ∧ requestOfR M k.1 k.2 = none))
    (request : ∀ token r, requestOfR (M.update g) g.id token = some r →
      requestOfR M y.id token = some r)
    (keyed : ∀ x ∈ M.fibers, x.id ≠ y.id → ∀ o ∈ x.observers, ¬ OffKey key o →
      StoredObserverOk root w (M.update g) x.id o)
    (keyedQ : ∀ src ex o, .observe src ex o ∈ Q → ¬ OffKey key o →
      ObserverCommandOk root w (M.update g) src ex o)
    (fresh : FiberTyped root w (M.update g) g) : ConfigTyped root rootTy w (M.update g) Q := by
  have view := exceptView_rupdate hy hid agree
  obtain ⟨machine, code, queue⟩ := typed
  have requests : ∀ fiber token r, requestOfR (M.update g) fiber token = some r →
      requestOfR M fiber token = some r := by
    intro fiber token r hr
    by_cases same : fiber = g.id
    · subst same
      rw [hid]
      exact request token r hr
    · rw [requestOfR_congr (rfiber?_update_other same)] at hr
      exact hr
  refine ⟨machineTyped_of (machineWide_rupdate machine.wide hid keys request) (fun x hx => ?_),
    fun x hx hrun reads marker ty declared => ?_, ?_⟩
  · rcases mem_rupdate hx with rfl | ⟨hold, hne⟩
    · exact fresh
    · exact fiberTyped_except (machine.fiber hold) view (Nat.le_refl _) (Nat.le_refl _)
        (keyed x hold (by rw [← hid]; exact hne))
  · rcases mem_rupdate hx with rfl | ⟨hold, _⟩
    · rw [gIdle] at hrun
      cases hrun
    · exact codeOk_races (racesKept_of_eq view.races) (code x hold hrun reads marker ty declared)
  · have same : Guard.commandOwner (Code := RProgram) (M.update g) = Guard.commandOwner M :=
      commandOwner_update M g
    refine ⟨queue.payload,
      fun c hc => commandAuthority_idle hy hid idle live c (queue.authority c hc),
      fun c hc => commandDelivery_idle hy hid idle c (queue.authority c hc) (queue.delivery c hc),
      by rw [same]; exact queue.owners, queue.registration,
      ⟨queue.keys.below, fun fiber token r hr hk => queue.keys.disjoint fiber token r
        (requests fiber token r hr) hk⟩,
      fun s e o ho => ?_, fun r c hc => enrollRaceOk_except view (Nat.le_refl _) (queue.enroll r c hc),
      queue.noRaceAfterInterrupt, fun md sc tg ir ex hl => ?_,
      fun s e o ho r race hr => queue.raceObservers s e o ho r race ((view.races r).symm.trans hr)⟩
    · refine ⟨(queue.observer s e o ho).1, ?_⟩
      by_cases off : OffKey key o
      · exact observerCommandOk_except view o off (queue.observer s e o ho).2
      · exact keyedQ s e o ho off
    · obtain ⟨live', present⟩ := queue.links md sc tg ir ex hl
      exact ⟨view.scopes sc live', view.exists_ tg present⟩

/-! ## The fail-fast interrupt walk -/

/-- The fields of a fiber an interrupt keeps: id, exit, running flag, observers, dispatcher; and
its park with its current code, unless it unparks. -/
def KeptFields (x' x : RFiber) : Prop :=
  x'.id = x.id ∧ x'.exit = x.exit ∧ x'.running = x.running ∧ x'.observers = x.observers ∧
    x'.dispatcher = x.dispatcher ∧
    ((x'.parked = x.parked ∧ x'.frame.current = x.frame.current) ∨ x'.parked = .notParked)

theorem KeptFields.refl (x : RFiber) : KeptFields x x :=
  ⟨rfl, rfl, rfl, rfl, rfl, Or.inl ⟨rfl, rfl⟩⟩

theorem KeptFields.trans {x'' x' x : RFiber} (a : KeptFields x'' x') (b : KeptFields x' x) :
    KeptFields x'' x := by
  refine ⟨a.1.trans b.1, a.2.1.trans b.2.1, a.2.2.1.trans b.2.2.1, a.2.2.2.1.trans b.2.2.2.1,
    a.2.2.2.2.1.trans b.2.2.2.2.1, ?_⟩
  rcases a.2.2.2.2.2 with ⟨pa, ca⟩ | na
  · rcases b.2.2.2.2.2 with ⟨pb, cb⟩ | nb
    · exact Or.inl ⟨pa.trans pb, ca.trans cb⟩
    · exact Or.inr (pa.trans nb)
  · exact Or.inr na

/-- An interrupt record keeps the fields `KeptFields` names. -/
theorem interruptRecord_fields (root : ProgramSource) (who : Option FiberId)
    (extra : ReasonAnnotations Ann) (t : RFiber) :
    KeptFields (interruptRecord (interpR root.program) who extra t).1 t := by
  unfold interruptRecord
  by_cases hx : t.exit.isSome = true
  · rw [if_pos hx]
    exact KeptFields.refl t
  · rw [if_neg hx]
    dsimp only
    split
    · split
      · split
        · exact ⟨rfl, rfl, rfl, rfl, rfl, Or.inl ⟨rfl, rfl⟩⟩
        · exact ⟨rfl, rfl, rfl, rfl, rfl, Or.inr rfl⟩
      · exact ⟨rfl, rfl, rfl, rfl, rfl, Or.inl ⟨rfl, rfl⟩⟩
    · split
      · split
        · exact ⟨rfl, rfl, rfl, rfl, rfl, Or.inl ⟨rfl, rfl⟩⟩
        · exact ⟨rfl, rfl, rfl, rfl, rfl, Or.inr rfl⟩
      · exact ⟨rfl, rfl, rfl, rfl, rfl, Or.inl ⟨rfl, rfl⟩⟩

/-- A machine whose fibers are the old ones up to what interrupts change. -/
structure InterruptView (m m' : RState) : Prop where
  lookup : ∀ id x', m'.fiber? id = some x' → ∃ x, m.fiber? id = some x ∧ KeptFields x' x
  lookupFwd : ∀ id x, m.fiber? id = some x → ∃ x', m'.fiber? id = some x' ∧ KeptFields x' x
  member : ∀ x' ∈ m'.fibers, ∃ x ∈ m.fibers, KeptFields x' x
  races : m'.races = m.races
  state : m'.state = m.state
  nextId : m'.nextId = m.nextId
  nextToken : m'.nextToken = m.nextToken

theorem InterruptView.refl (m : RState) : InterruptView m m :=
  ⟨fun _ x h => ⟨x, h, KeptFields.refl x⟩, fun _ x h => ⟨x, h, KeptFields.refl x⟩,
    fun x h => ⟨x, h, KeptFields.refl x⟩, rfl, rfl, rfl, rfl⟩

theorem InterruptView.trans {m m' m'' : RState} (a : InterruptView m m')
    (b : InterruptView m' m'') : InterruptView m m'' := by
  refine ⟨fun id x'' h => ?_, fun id x h => ?_, fun x'' h => ?_, b.races.trans a.races,
    b.state.trans a.state, b.nextId.trans a.nextId, b.nextToken.trans a.nextToken⟩
  · obtain ⟨x', h', k'⟩ := b.lookup id x'' h
    obtain ⟨x, h0, k⟩ := a.lookup id x' h'
    exact ⟨x, h0, k'.trans k⟩
  · obtain ⟨x', h', k'⟩ := a.lookupFwd id x h
    obtain ⟨x'', h'', k''⟩ := b.lookupFwd id x' h'
    exact ⟨x'', h'', k''.trans k'⟩
  · obtain ⟨x', h', k'⟩ := b.member x'' h
    obtain ⟨x, h0, k⟩ := a.member x' h'
    exact ⟨x, h0, k'.trans k⟩

/-- Events are no clause's: an interrupt view survives an emit. -/
theorem InterruptView.emit {m m' : RState} (v : InterruptView m m')
    (events : List (RunEvent EffName EffThunk Val Err Defect FiberId Ann Ctx RProgram Unit)) :
    InterruptView m (m'.emit events) :=
  ⟨v.lookup, v.lookupFwd, v.member, v.races, v.state, v.nextId, v.nextToken⟩

/-- Replacing a fiber by a record that keeps the interrupt-kept fields. -/
theorem interruptView_rupdate {m : RState} {f g : RFiber} (hf : m.fiber? f.id = some f)
    (kept : KeptFields g f) : InterruptView m (m.update g) := by
  refine ⟨fun id x' h => ?_, fun id x h => ?_, fun x' h => ?_, rfl, rfl, rfl, rfl⟩
  · rw [rfiber?_update] at h
    cases h0 : m.fiber? id with
    | none =>
      rw [h0] at h
      cases h
    | some x =>
      rw [h0, Option.map_some] at h
      cases h
      by_cases hx : x.id = g.id
      · rw [if_pos hx]
        have same : x = f := rfiber?_same hf h0 (hx.trans kept.1)
        subst same
        exact ⟨x, rfl, kept⟩
      · rw [if_neg hx]
        exact ⟨x, rfl, KeptFields.refl x⟩
  · rw [rfiber?_update, h, Option.map_some]
    by_cases hx : x.id = g.id
    · rw [if_pos hx]
      have same : x = f := rfiber?_same hf h (hx.trans kept.1)
      subst same
      exact ⟨g, rfl, kept⟩
    · rw [if_neg hx]
      exact ⟨x, rfl, KeptFields.refl x⟩
  · rcases mem_rupdate h with rfl | ⟨hold, _⟩
    · exact ⟨f, rfiber?_mem hf, kept⟩
    · exact ⟨x', hold, KeptFields.refl x'⟩

/-- An interrupt view drops pending records, never adds one: an observer view. -/
theorem obsView_of_pending {m m' : RState} (view : InterruptView m m')
    (pending : ∀ id x', m'.fiber? id = some x' → ∀ x, m.fiber? id = some x →
      PendingWeaker x.pending x'.pending) : ObsView m m' := by
  refine ⟨fun id x' h => ?_, fun id h => ?_, fun r => ?_, fun sc h => ?_⟩
  · obtain ⟨x, h0, kept⟩ := view.lookup id x' h
    exact ⟨x, h0, kept.1, pending id x' h x h0⟩
  · obtain ⟨x, hx⟩ := Option.isSome_iff_exists.mp h
    obtain ⟨x', h', _⟩ := view.lookupFwd id x hx
    rw [h']
    rfl
  · unfold RunMachine.race?
    rw [view.races]
  · show Stores.ScopeLive m'.state sc
    rw [view.state]
    exact h

/-- The walk over the targets: `I` kept on the queue that follows, the collected commands
evaluations, the fibers the old ones up to interrupts, each pending record kept or dropped. -/
theorem configTyped_interruptEach (root : ProgramSource) (rootTy : EffTy) {w : World}
    {q : List RCmd} (who : FiberId) (extra : ReasonAnnotations Ann) :
    ∀ (targets : List FiberId) (m : RState) (acc : List RCmd),
      ConfigTyped root rootTy w m q → (∀ c ∈ acc, ∃ t, c = .evaluate t) →
      ConfigTyped root rootTy w
          (interruptEach (interpR root.program) who extra targets (m, acc)).1 q ∧
        (∀ c ∈ (interruptEach (interpR root.program) who extra targets (m, acc)).2,
          ∃ t, c = .evaluate t) ∧
        InterruptView m (interruptEach (interpR root.program) who extra targets (m, acc)).1 ∧
        (∀ id x', (interruptEach (interpR root.program) who extra targets (m, acc)).1.fiber? id =
          some x' → ∀ x, m.fiber? id = some x → PendingWeaker x.pending x'.pending) := by
  intro targets
  induction targets with
  | nil =>
    intro m acc typed evals
    refine ⟨typed, evals, InterruptView.refl m, fun id x' h x h0 => ?_⟩
    change m.fiber? id = some x' at h
    rw [h0] at h
    cases h
    exact PendingWeaker.refl _
  | cons t ts ih =>
    intro m acc typed evals
    cases ht : m.fiber? t with
    | none =>
      have e : interruptEach (interpR root.program) who extra (t :: ts) (m, acc) =
          interruptEach (interpR root.program) who extra ts (m, acc) := by
        unfold interruptEach
        rw [List.foldl_cons]
        simp only [ht]
      rw [e]
      exact ih m acc typed evals
    | some g =>
      have recorded := configTyped_interruptRecord typed ht (some who) extra
      have fields := interruptRecord_fields root (some who) extra g
      rcases hrec : interruptRecord (interpR root.program) (some who) extra g with ⟨g', applyNow⟩
      rw [hrec] at recorded fields
      dsimp only at fields
      have e : interruptEach (interpR root.program) who extra (t :: ts) (m, acc) =
          interruptEach (interpR root.program) who extra ts
            ((m.update g').emit [RunEvent.interruptRecorded (some who) t],
              acc ++ (if applyNow then [Cmd.evaluate t] else [])) := by
        unfold interruptEach
        rw [List.foldl_cons]
        simp only [ht, hrec]
      rw [e]
      have dropped : ConfigTyped root rootTy w (m.update g') q := by
        dsimp only at recorded
        split at recorded
        · exact configTyped_tail recorded
        · exact recorded
      have m1 := configTyped_emit dropped [RunEvent.interruptRecorded (some who) t]
      have evals' : ∀ c ∈ acc ++ (if applyNow then [Cmd.evaluate t] else []),
          ∃ t, c = .evaluate t := by
        intro c hc
        rcases List.mem_append.mp hc with old | new
        · exact evals c old
        · split at new
          · exact ⟨t, List.mem_singleton.mp new⟩
          · cases new
      obtain ⟨typed', evals'', view', pending'⟩ := ih _ _ m1 evals'
      have gid : g.id = t := rfiber?_id ht
      have hf : m.fiber? g.id = some g := by rw [gid]; exact ht
      have step : InterruptView m ((m.update g').emit [RunEvent.interruptRecorded (some who) t]) :=
        (interruptView_rupdate hf fields).emit _
      refine ⟨typed', evals'', step.trans view', fun id x'' h x h0 => ?_⟩
      obtain ⟨x', h', _⟩ := view'.lookup id x'' h
      have weak' := pending' id x'' h x' h'
      have h1 : (m.update g').fiber? id = some x' := h'
      rw [rfiber?_update, h0, Option.map_some] at h1
      by_cases hx : x.id = g'.id
      · rw [if_pos hx] at h1
        cases h1
        have same : x = g := rfiber?_same hf h0 (hx.trans fields.1)
        subst same
        refine fun token p hp => ?_
        have hp' := weak' token p hp
        have shape : g'.pending = x.pending ∨ g'.pending = [] := by
          have e2 : g' = (interruptRecord (interpR root.program) (some who) extra x).1 := by
            rw [hrec]
          rw [e2]
          unfold interruptRecord
          by_cases hxe : x.exit.isSome = true
          · rw [if_pos hxe]
            exact Or.inl rfl
          · rw [if_neg hxe]
            dsimp only
            split
            · split
              · split
                · exact Or.inl rfl
                · exact Or.inr rfl
              · exact Or.inl rfl
            · split
              · split
                · exact Or.inl rfl
                · exact Or.inr rfl
              · exact Or.inl rfl
        rcases shape with same | empty
        · rw [← same]
          exact hp'
        · rw [empty] at hp'
          cases hp'
      · rw [if_neg hx] at h1
        cases h1
        exact weak'

/-- A request on the walked machine was one on the old machine: an interrupt keeps a park's
current code or unparks. -/
theorem InterruptView.requests {m m' : RState} (v : InterruptView m m') {id : FiberId}
    {tok : Nat} {r : NativeOp × Val} (h : requestOfR m' id tok = some r) :
    requestOfR m id tok = some r := by
  cases h' : m'.fiber? id with
  | none =>
    have none' : requestOfR m' id tok = none := by
      unfold requestOfR
      rw [h']
      rfl
    rw [none'] at h
    cases h
  | some x' =>
    obtain ⟨x, hx, kept⟩ := v.lookup id x' h'
    by_cases hp : x'.parked = .withGuard tok
    · rw [requestOfR_of_parked h' hp] at h
      rcases kept.2.2.2.2.2 with ⟨pk, ck⟩ | np
      · rw [requestOfR_of_parked hx (pk ▸ hp), ← ck]
        exact h
      · rw [np] at hp
        cases hp
    · rw [requestOfR_of_not_parked h' hp] at h
      cases h

/-- The await-all walk reads only lookups and exits, which an interrupt view keeps. -/
theorem countdownWalk_view {m m' : RState} (v : InterruptView m m') :
    ∀ (l : List FiberId) (exits : List ExitV), countdownWalk m' l exits = countdownWalk m l exits
  | [], _ => rfl
  | t :: rest, exits => by
    simp only [countdownWalk]
    cases h' : m'.fiber? t with
    | none =>
      have h0 : m.fiber? t = none := by
        cases h0 : m.fiber? t with
        | none => rfl
        | some x =>
          obtain ⟨x', hx', _⟩ := v.lookupFwd t x h0
          rw [h'] at hx'
          cases hx'
      rw [h0]
      exact countdownWalk_view v rest exits
    | some x' =>
      obtain ⟨x, h0, kept⟩ := v.lookup t x' h'
      rw [h0]
      dsimp only
      rw [kept.2.1]
      cases x.exit with
      | none => rfl
      | some ex => exact countdownWalk_view v rest (exits ++ [ex])

/-- What the await-all walk returns: the collected exits followed by those of exited targets, and
the first live target with the targets after it. -/
theorem countdownWalk_spec (m : RState) : ∀ (l : List FiberId) (collected : List ExitV),
    (∃ extra, (countdownWalk m l collected).1 = collected ++ extra ∧
      ∀ e ∈ extra, ∃ t ∈ l, ∃ g, m.fiber? t = some g ∧ g.exit = some e) ∧
    (∀ next rest', (countdownWalk m l collected).2 = some (next, rest') →
      next ∈ l ∧ (∃ g, m.fiber? next = some g ∧ g.exit = none) ∧ ∀ x ∈ rest', x ∈ l)
  | [], collected => ⟨⟨[], (List.append_nil collected).symm, fun _ h => nomatch h⟩,
      fun _ _ h => nomatch h⟩
  | t :: rest, collected => by
    simp only [countdownWalk]
    cases ht : m.fiber? t with
    | none =>
      obtain ⟨⟨extra, hex, hextra⟩, hnext⟩ := countdownWalk_spec m rest collected
      refine ⟨⟨extra, hex, fun e he => ?_⟩, fun next rest' h => ?_⟩
      · obtain ⟨t', ht', g, hg, ge⟩ := hextra e he
        exact ⟨t', List.mem_cons_of_mem _ ht', g, hg, ge⟩
      · obtain ⟨hn, live, sub⟩ := hnext next rest' h
        exact ⟨List.mem_cons_of_mem _ hn, live, fun x hx => List.mem_cons_of_mem _ (sub x hx)⟩
    | some g =>
      dsimp only
      cases hg : g.exit with
      | none =>
        refine ⟨⟨[], (List.append_nil collected).symm, fun _ h => nomatch h⟩,
          fun next rest' h => ?_⟩
        dsimp only at h
        cases h
        exact ⟨List.mem_cons_self, ⟨g, ht, hg⟩, fun x hx => List.mem_cons_of_mem _ hx⟩
      | some ex =>
        dsimp only
        obtain ⟨⟨extra, hex, hextra⟩, hnext⟩ := countdownWalk_spec m rest (collected ++ [ex])
        refine ⟨⟨ex :: extra, by rw [hex, List.append_assoc, List.singleton_append], fun e he => ?_⟩,
          fun next rest' h => ?_⟩
        · rcases List.mem_cons.mp he with rfl | he
          · exact ⟨t, List.mem_cons_self, g, ht, hg⟩
          · obtain ⟨t', ht', g', hg', ge⟩ := hextra e he
            exact ⟨t', List.mem_cons_of_mem _ ht', g', hg', ge⟩
        · obtain ⟨hn, live, sub⟩ := hnext next rest' h
          exact ⟨List.mem_cons_of_mem _ hn, live, fun x hx => List.mem_cons_of_mem _ (sub x hx)⟩

/-! ## The countdown's record, before and after -/

/-- A countdown correlation, read at a found record. -/
theorem countdownAt_found {w : World} {m : RState} {waiter : FiberId} {token : Nat}
    {incoming : Ty → Ty → Prop} {wf : RFiber} {p : RPending}
    (h : CountdownAt w m waiter token incoming) (hw : m.fiber? waiter = some wf)
    (hp : wf.pending.find? (fun q => q.token = token) = some p) :
    ∃ a e tt, CountdownPayload w m waiter p a e tt ∧ incoming a e := by
  unfold CountdownAt at h
  rw [hw] at h
  dsimp only at h
  rw [hp] at h
  exact h

/-- A countdown correlation, given at a found record. -/
theorem countdownAt_of_found {w : World} {m : RState} {waiter : FiberId} {token : Nat}
    {incoming : Ty → Ty → Prop} {g : RFiber} {p : RPending} (hw : m.fiber? waiter = some g)
    (hp : g.pending.find? (fun q => q.token = token) = some p)
    (h : ∃ a e tt, CountdownPayload w m waiter p a e tt ∧ incoming a e) :
    CountdownAt w m waiter token incoming := by
  unfold CountdownAt
  rw [hw]
  dsimp only
  rw [hp]
  exact h

/-- The new record keeps the old one's payload at the same columns: the same token and resume,
its collected exits typed there, its targets among the old ones. -/
theorem countdownPayload_advance {w : World} {m m' : RState} {waiter : FiberId}
    {p p' : RPending} {a e : Ty} {tt : EffTy} (old : CountdownPayload w m waiter p a e tt)
    (token : p'.token = p.token) (resume : p'.resumeWith = p.resumeWith)
    (collected : ∀ ex ∈ p'.collected, ExitOk w ⟨a, e, Env.Requirement.empty⟩ ex)
    (targets : ∀ id ∈ p'.waitingOn.toList ++ p'.remaining, id ∈ p.waitingOn.toList ++ p.remaining)
    (lookup : ∀ id f', m'.fiber? id = some f' → ∃ f, m.fiber? id = some f ∧ f'.id = f.id) :
    CountdownPayload w m' waiter p' a e tt := by
  refine ⟨by rw [token]; exact old.token, collected, fun id hid fiber hf => ?_, ?_⟩
  · obtain ⟨f, h0, hid'⟩ := lookup id fiber hf
    rw [hid']
    exact old.targets id (targets id hid) f h0
  · have r := old.resume
    rw [resume]
    exact r

/-- Off the exits-value resume no clause reads the columns: the payload holds at `unknown`. -/
theorem countdownPayload_unknown {w : World} {m : RState} {waiter : FiberId} {p : RPending}
    {a e : Ty} {tt : EffTy} (h : CountdownPayload w m waiter p a e tt)
    (notValue : p.resumeWith ≠ .exitsValue) :
    CountdownPayload w m waiter p .unknown .unknown tt := by
  refine ⟨h.token, fun ex hex => exitOk_subN (h.collected ex hex) (subN_unknown _) (subN_unknown _),
    fun id hid fiber hf => ?_, ?_⟩
  · obtain ⟨ty, declared, _, _⟩ := h.targets id hid fiber hf
    exact ⟨ty, declared, subN_unknown _, subN_unknown _⟩
  · have r := h.resume
    cases hr : p.resumeWith with
    | exitsValue => exact absurd hr notValue
    | void =>
      rw [hr] at r
      exact r
    | continueWith name =>
      rw [hr] at r
      cases name with
      | restore saved => exact r
      | _ => exact r

/-- At the exits-value resume the token pins the columns. -/
theorem countdownPayload_pinned {w : World} {m : RState} {waiter : FiberId} {p : RPending}
    {a e a' e' : Ty} {tt tt' : EffTy} (h1 : CountdownPayload w m waiter p a e tt)
    (h2 : CountdownPayload w m waiter p a' e' tt') (value : p.resumeWith = .exitsValue) :
    a' = a ∧ e' = e := by
  have t1 := h1.token
  have t2 := h2.token
  rw [t1] at t2
  cases t2
  have r1 := h1.resume
  have r2 := h2.resume
  rw [value] at r1 r2
  rw [r1] at r2
  unfold EffTy.pure at r2
  injection r2 with r2
  injection r2 with r2
  injection r2 with ha he
  exact ⟨ha.symm, he.symm⟩

/-- **A countdown correlation at the advanced record.** The old record's payload at any columns
gives the new record's: at the head's columns when the record resumes with the exits (the token
pins them), at `unknown` otherwise; the correlation's own condition follows by `widen`. -/
theorem countdownAt_advance {w : World} {m m' : RState} {waiter : FiberId} {token : Nat}
    {incoming : Ty → Ty → Prop} {p p' : RPending} {g' : RFiber} {a e : Ty} {tt : EffTy}
    (head : CountdownPayload w m waiter p a e tt)
    (other : ∃ a e tt, CountdownPayload w m waiter p a e tt ∧ incoming a e)
    (widen : ∀ a e, incoming a e → incoming .unknown .unknown)
    (lookupNew : m'.fiber? waiter = some g')
    (findNew : g'.pending.find? (fun q => q.token = token) = some p')
    (ptoken : p'.token = p.token) (presume : p'.resumeWith = p.resumeWith)
    (collected : ∀ ex ∈ p'.collected, ExitOk w ⟨a, e, Env.Requirement.empty⟩ ex)
    (targets : ∀ id ∈ p'.waitingOn.toList ++ p'.remaining, id ∈ p.waitingOn.toList ++ p.remaining)
    (lookup : ∀ id f', m'.fiber? id = some f' → ∃ f, m.fiber? id = some f ∧ f'.id = f.id) :
    CountdownAt w m' waiter token incoming := by
  obtain ⟨ax, ex', ttx, payx, incx⟩ := other
  refine countdownAt_of_found lookupNew findNew ?_
  by_cases value : p.resumeWith = .exitsValue
  · obtain ⟨ha, he⟩ := countdownPayload_pinned head payx value
    subst ha
    subst he
    exact ⟨ax, ex', ttx, countdownPayload_advance payx ptoken presume collected targets lookup, incx⟩
  · refine ⟨.unknown, .unknown, ttx, countdownPayload_advance (countdownPayload_unknown payx value)
      ptoken presume (fun x hx => exitOk_subN (collected x hx) (subN_unknown _) (subN_unknown _))
      targets lookup, widen ax ex' incx⟩

/-- **A finished countdown's continuation is typed at its token's declaration** (`resumePrim`,
`Machine/Fibers.lean:881-886`): the exits as a value at the pinned list of exits, `void`, or the
restoring continuation's saved exit. -/
theorem resumePrim_typed (root : ProgramSource) {w : World} {m : RState} {waiter : FiberId}
    {p : RPending} {a e : Ty} {tt : EffTy} (payload : CountdownPayload w m waiter p a e tt)
    (exits : List ExitV) (typedExits : ∀ ex ∈ exits, ExitOk w ⟨a, e, Env.Requirement.empty⟩ ex) :
    TypedProg root w tt (countdownPark.resumePrim (interpR root.program) p.resumeWith exits) := by
  have r := payload.resume
  cases hr : p.resumeWith with
  | exitsValue =>
    rw [hr] at r
    subst r
    exact TypedProg.pure ⟨awaitAll_delivered (targets := []) fun ex hex => (typedExits ex hex).1,
      trivial⟩
  | void =>
    rw [hr] at r
    subst r
    exact TypedProg.pure ⟨trivial, trivial⟩
  | continueWith name =>
    rw [hr] at r
    show TypedProg root w tt (restoreR (.pure (.success (exitsVal exits))) name)
    cases name with
    | restore saved =>
      refine seq_typed_clean root (mid := EffTy.pure (.list (.exitOf .unknown .unknown)))
        (TypedProg.pure ⟨awaitAll_delivered (targets := []) fun ex hex =>
          fitsExit_subN (subN_unknown _) (subN_unknown _) (typedExits ex hex).1, trivial⟩)
        (fun w' o _ _ => TypedProg.pure (strongExit_mono _ _ _ _ o r)) rfl
    | _ => exact TypedProg.pure r

/-- Evaluations queued in front of a typed configuration keep it typed. -/
theorem configTyped_evaluates {root : ProgramSource} {rootTy : EffTy} {w : World} {m : RState}
    {q : List RCmd} (typed : ConfigTyped root rootTy w m q) :
    ∀ (es : List RCmd), (∀ c ∈ es, ∃ t, c = .evaluate t) → ConfigTyped root rootTy w m (es ++ q)
  | [], _ => typed
  | c :: es, h => by
    obtain ⟨t, rfl⟩ := h c List.mem_cons_self
    exact configTyped_cons_evaluate
      (configTyped_evaluates typed es fun c hc => h c (List.mem_cons_of_mem _ hc)) t

/-- The waiter's record with its countdown record advanced keeps its clauses on the new machine;
its own observers at the countdown's key are re-proved by the caller. -/
theorem fiberTyped_repend {root : ProgramSource} {w : World} {m M' : RState} {wf : RFiber}
    {p' : RPending} {token : Nat} (old : FiberTyped root w m wf)
    (view : ExceptView m M' (wf.id, token)) (nextId : m.nextId ≤ M'.nextId)
    (nextToken : m.nextToken ≤ M'.nextToken) (parked : wf.parked = .withGuard token)
    (ptok : p'.token = token)
    (keyed : ∀ o ∈ wf.observers, ¬ OffKey (wf.id, token) o → StoredObserverOk root w M' wf.id o)
    (targets : ∀ id ∈ p'.waitingOn.toList ++ p'.remaining, id.value < m.nextId) :
    FiberTyped root w M' { wf with pending := [p'] } := by
  have declared : (w.Θ wf.id token).isSome = true := old.tokens token parked
  refine ⟨⟨old.ok.c0, fun q hq => ?_, old.ok.c2, old.ok.c3, old.ok.c4, old.ok.c5⟩,
    old.delivery_races (racesKept_of_eq view.races),
    Nat.lt_of_lt_of_le old.below nextId, ?_, old.parkedIdle,
    fun t hp => Nat.lt_of_lt_of_le (old.parkedBelow t hp) nextToken, old.exited,
    old.exitedStack, old.deferredCause, fun q hq => ?_, fun o ho => ?_, fun raceId marker => ?_,
    old.code_races (racesKept_of_eq view.races),
    old.tokens, fun r race hr o ho => old.raceObservers r race ((view.races r).symm.trans hr) o ho,
    fun q hq id hid => by
      rw [List.mem_singleton.mp hq] at hid
      exact Nat.lt_of_lt_of_le (targets id hid) nextId,
    fun o ho k hk => Nat.lt_of_lt_of_le (old.observersBelow o ho k hk) nextId⟩
  · rw [List.mem_singleton.mp hq, ptok]
    exact ⟨wf.id, declared⟩
  · show Guard.PendingShape { wf with pending := [p'] }
    unfold Guard.PendingShape
    rw [show ({ wf with pending := [p'] } : RFiber).parked = wf.parked from rfl, parked]
    exact ⟨p', rfl, ptok⟩
  · rw [List.mem_singleton.mp hq, ptok]
    exact declared
  · by_cases off : OffKey (wf.id, token) o
    · exact storedObserverOk_except view o off (old.observers o ho)
    · exact keyed o ho off
  · obtain ⟨race, resultTy, found, host, token', reply⟩ := old.registration raceId marker
    exact ⟨race, resultTy, (view.races raceId).trans found, host, token',
      stackReply_races (racesKept_of_eq view.races) reply⟩

/-! ## The countdown arm -/

theorem rfiber?_emit (m : RState)
    (events : List (RunEvent EffName EffThunk Val Err Defect FiberId Ann Ctx RProgram Unit))
    (id : FiberId) : (m.emit events).fiber? id = m.fiber? id := rfl

/-- A found countdown record is the waiter's whole park: parked on the token, one record. -/
theorem countdown_parked {root : ProgramSource} {w : World} {m : RState} {wf : RFiber}
    {p : RPending} {token : Nat} (old : FiberTyped root w m wf)
    (hp : wf.pending.find? (fun q => decide (q.token = token)) = some p) :
    wf.parked = .withGuard token ∧ wf.pending = [p] ∧ p.token = token := by
  have found := List.find?_some hp
  have ptok : p.token = token := of_decide_eq_true found
  have shape := old.pendingShape
  unfold Guard.PendingShape at shape
  cases hpk : wf.parked with
  | notParked =>
    rw [hpk] at shape
    rw [shape] at hp
    cases hp
  | withGuard t =>
    rw [hpk] at shape
    obtain ⟨p0, single, ht⟩ := shape
    rw [single] at hp
    rw [List.find?_cons] at hp
    by_cases h0 : p0.token = token
    · rw [decide_eq_true h0] at hp
      cases hp
      exact ⟨by rw [← ht, h0], single, ptok⟩
    · rw [decide_eq_false h0] at hp
      cases hp

/-- Lookups on an updated machine come back to an older machine's, through the replaced
record. -/
theorem lookupBack_update {m M : RState} {y g : RFiber}
    (back : ∀ id f', M.fiber? id = some f' → ∃ f, m.fiber? id = some f ∧ f'.id = f.id)
    (hy : M.fiber? y.id = some y) (hid : g.id = y.id) :
    ∀ id f', (M.update g).fiber? id = some f' → ∃ f, m.fiber? id = some f ∧ f'.id = f.id := by
  intro id f' h
  rw [rfiber?_update] at h
  cases h2 : M.fiber? id with
  | none =>
    rw [h2] at h
    cases h
  | some x =>
    rw [h2, Option.map_some] at h
    cases h
    obtain ⟨x0, hx0, k⟩ := back id x h2
    by_cases hx : x.id = g.id
    · rw [if_pos hx]
      have same : x = y := rfiber?_same hy h2 (hx.trans hid)
      subst same
      exact ⟨x0, hx0, hid.trans k⟩
    · rw [if_neg hx]
      exact ⟨x0, hx0, k⟩

/-- An observer at the key is the countdown at the key. -/
theorem countdown_of_not_offKey {key : FiberId × Nat} {o : Observer} (h : ¬ OffKey key o) :
    o = .countdown key.1 key.2 := by
  cases o with
  | countdown waiter token =>
    by_cases same : (waiter, token) = key
    · rw [← same]
    · exact absurd (fun w t ho => by cases ho; exact same) h
  | resumeAwait _ _ _ => exact absurd (fun _ _ ho => nomatch ho) h
  | raceCallback _ => exact absurd (fun _ _ ho => nomatch ho) h
  | dropScopeFinalizer _ _ => exact absurd (fun _ _ ho => nomatch ho) h
  | untrackChild _ => exact absurd (fun _ _ ho => nomatch ho) h
  | callback _ => exact absurd (fun _ _ ho => nomatch ho) h

/-- **`observe` keeps `I` at a countdown observer.** -/
theorem observe_countdown (root : ProgramSource) (rootTy : EffTy) {w : World} {m : RState}
    {rest : List RCmd} {source : FiberId} {exit : ExitV} {waiter : FiberId} {token : Nat}
    (typed : ConfigTyped root rootTy w m (.observe source exit (.countdown waiter token) :: rest)) :
    ConfigTyped root rootTy w
      (fireObserver (interpR root.program) source exit (m, []) (.countdown waiter token)).1
      ((fireObserver (interpR root.program) source exit (m, []) (.countdown waiter token)).2 ++
        rest) := by
  have tail := configTyped_tail typed
  have t1 := configTyped_emit tail [RunEvent.observerFired source (.countdown waiter token)]
  have obsOk : ObserverCommandOk root w m source exit (.countdown waiter token) :=
    (typed.queue.observer source exit _ List.mem_cons_self).2
  have keyMem : (waiter, token) ∈
      (Cmd.observe source exit (.countdown waiter token) :: rest).flatMap Guard.commandKeys :=
    List.mem_flatMap.mpr ⟨_, List.mem_cons_self, List.mem_singleton_self _⟩
  have keyBelow : token < m.nextToken := typed.queue.keys.below _ keyMem
  have keyFree : requestOfR m waiter token = none := by
    cases h : requestOfR m waiter token with
    | none => rfl
    | some r => exact absurd keyMem (typed.queue.keys.disjoint waiter token r h)
  unfold fireObserver
  dsimp only
  rw [rfiber?_emit]
  cases hw : m.fiber? waiter with
  | none => exact t1
  | some wf =>
    dsimp only
    cases hp : wf.pending.find? (fun p => decide (p.token = token)) with
    | none => exact t1
    | some p =>
      dsimp only
      obtain ⟨a, e, tt, payload, incomingOk⟩ := countdownAt_found obsOk hw hp
      have wid : wf.id = waiter := rfiber?_id hw
      have hwf : m.fiber? wf.id = some wf := by rw [wid]; exact hw
      have hmem : wf ∈ m.fibers := rfiber?_mem hwf
      have old := typed.machine.fiber hmem
      obtain ⟨parked, single, ptok⟩ := countdown_parked old hp
      have idle : wf.running = false := old.parkedIdle (by rw [parked]; exact fun h => nomatch h)
      have live : wf.exit = none := by
        cases hx : wf.exit with
        | none => rfl
        | some _ =>
          have notParked := (old.exited (by rw [hx]; rfl)).1
          rw [parked] at notParked
          cases notParked
      generalize hpair : (if (p.failFast && !Exit.isSuccess exit &&
            p.collected.all Exit.isSuccess) = true then
          interruptEach (interpR root.program) waiter ((interpR root.program).stackAnnotations waiter)
            p.remaining (m.emit [RunEvent.observerFired source (.countdown waiter token)], [])
        else (m.emit [RunEvent.observerFired source (.countdown waiter token)], [])) = pr
      obtain ⟨t2, evals, iview, pweak⟩ : ConfigTyped root rootTy w pr.1 rest ∧
          (∀ c ∈ pr.2, ∃ t, c = .evaluate t) ∧
          InterruptView (m.emit [RunEvent.observerFired source (.countdown waiter token)]) pr.1 ∧
          (∀ id x', pr.1.fiber? id = some x' → ∀ x,
            (m.emit [RunEvent.observerFired source (.countdown waiter token)]).fiber? id = some x →
              PendingWeaker x.pending x'.pending) := by
        rw [← hpair]
        split
        · exact configTyped_interruptEach root rootTy waiter _ p.remaining _ [] t1
            (fun _ h => nomatch h)
        · refine ⟨t1, (fun _ h => nomatch h), InterruptView.refl _, fun id x' h x h0 => ?_⟩
          rw [h0] at h
          cases h
          exact PendingWeaker.refl _
      obtain ⟨m2, nested⟩ := pr
      dsimp only at t2 evals iview pweak ⊢
      have view2 : InterruptView m m2 := ((InterruptView.refl m).emit _).trans iview
      have obs2 : ObsView m m2 := obsView_of_pending view2 fun id x' h x h0 => pweak id x' h x h0
      obtain ⟨y, hy, ykept⟩ := view2.lookupFwd waiter wf hw
      have yid : y.id = waiter := ykept.1.trans wid
      have hy' : m2.fiber? y.id = some y := by rw [yid]; exact hy
      have ymem : y ∈ m2.fibers := rfiber?_mem hy'
      have wfNone : externalRequestR wf.frame.current = none := by
        rw [← requestOfR_of_parked hw parked]
        exact keyFree
      have walk := countdownWalk_spec m2 p.remaining (p.collected ++ [exit])
      have typedExtra : ∀ x, (∃ t ∈ p.remaining, ∃ g, m2.fiber? t = some g ∧ g.exit = some x) →
          ExitOk w ⟨a, e, Env.Requirement.empty⟩ x := by
        rintro x ⟨t, ht, g, hg, gx⟩
        obtain ⟨g0, hg0, kept⟩ := view2.lookup t g hg
        have g0x : g0.exit = some x := kept.2.1.symm.trans gx
        obtain ⟨ty, declared, sa, se⟩ :=
          payload.targets t (List.mem_append_right _ ht) g0 hg0
        exact exitOk_subN ((typed.machine.fiber (rfiber?_mem hg0)).ok.c3 x g0x ty declared) sa se
      have lookupBack : ∀ (g : RFiber), g.id = waiter → ∀ id f',
          (m2.update g).fiber? id = some f' → ∃ f, m.fiber? id = some f ∧ f'.id = f.id := by
        intro g gid id f' h
        rw [rfiber?_update] at h
        cases h2 : m2.fiber? id with
        | none =>
          rw [h2] at h
          cases h
        | some x =>
          rw [h2, Option.map_some] at h
          cases h
          obtain ⟨x0, hx0, kept⟩ := view2.lookup id x h2
          by_cases hx : x.id = g.id
          · rw [if_pos hx]
            exact ⟨x0, hx0, gid.trans ((hx.trans gid).symm.trans kept.1)⟩
          · rw [if_neg hx]
            exact ⟨x0, hx0, kept.1⟩
      have typedWalk : ∀ x ∈ (countdownWalk m2 p.remaining (p.collected ++ [exit])).1,
          ExitOk w ⟨a, e, Env.Requirement.empty⟩ x := by
        obtain ⟨⟨extra, hexits, hextra⟩, _⟩ := walk
        intro x hx
        rw [hexits] at hx
        rcases List.mem_append.mp hx with hx | hx
        · rcases List.mem_append.mp hx with hx | hx
          · exact payload.collected x hx
          · rw [List.mem_singleton.mp hx]
            exact incomingOk
        · exact typedExtra x (hextra x hx)
      have nextWalk := walk.2
      rcases hwalk : countdownWalk m2 p.remaining (p.collected ++ [exit]) with
        ⟨exits, _ | ⟨next, rest'⟩⟩
      · rw [hwalk] at typedWalk
        dsimp only
        rw [single, List.map_cons, List.map_nil, if_pos ptok]
        let p' : RPending := { p with waitingOn := none, remaining := [], collected := exits }
        let g : RFiber := { wf with pending := [p'] }
        show ConfigTyped root rootTy w (m2.update g)
          ((([] ++ nested) ++
            [Cmd.resume waiter token (countdownPark.resumePrim (interpR root.program) p.resumeWith
              exits)]) ++ rest)
        have gid : g.id = waiter := wid
        have hid : g.id = y.id := gid.trans yid.symm
        have look : (m2.update g).fiber? waiter = some g := by
          rw [← gid]
          exact rfiber?_update_self hy' hid
        have find' : g.pending.find? (fun q => decide (q.token = token)) = some p' := by
          show ([p'] : List RPending).find? (fun q => decide (q.token = token)) = some p'
          rw [List.find?_cons, decide_eq_true (show p'.token = token from ptok)]
        have gNone : ∀ tok r, requestOfR (m2.update g) waiter tok = some r → False := by
          intro tok r hr
          by_cases hpk : g.parked = .withGuard tok
          · rw [requestOfR_of_parked look hpk] at hr
            have current : g.frame.current = wf.frame.current := rfl
            rw [current, wfNone] at hr
            cases hr
          · rw [requestOfR_of_not_parked look hpk] at hr
            cases hr
        have agree : PendingExcept y.pending g.pending (fun tok => (y.id, tok) = (waiter, token)) := by
          intro tok q skip hq
          have hq' : ([p'] : List RPending).find? (fun x => decide (x.token = tok)) = some q := hq
          rw [List.find?_cons] at hq'
          by_cases same : p'.token = tok
          · exact absurd (by rw [yid, ← same]; exact congrArg _ ptok) skip
          · rw [decide_eq_false same] at hq'
            cases hq'
        have keysG : ∀ k ∈ Guard.fiberKeys g, k ∈ Guard.internalKeys m2 ∨
            (k.2 < m2.nextToken ∧ requestOfR m2 k.1 k.2 = none) := by
          intro k hk
          refine Or.inl (fiberKeys_internal ymem ?_)
          unfold Guard.fiberKeys at hk ⊢
          rw [ykept.2.2.2.1, ykept.2.2.2.2.1]
          exact hk
        have lookupNew := lookupBack g gid
        have advance : ∀ (incoming : Ty → Ty → Prop),
            (∀ a e, incoming a e → incoming .unknown .unknown) →
            CountdownAt w m waiter token incoming → CountdownAt w (m2.update g) waiter token incoming := by
          intro incoming widen h
          exact countdownAt_advance payload (countdownAt_found h hw hp) widen look find' rfl rfl
            typedWalk (fun _ h => nomatch h) lookupNew
        have widenCols : ∀ (s : FiberId) (a e : Ty), FiberColumnsBelow w s a e →
            FiberColumnsBelow w s .unknown .unknown := by
          rintro s a e ⟨ty, d, _, _⟩
          exact ⟨ty, d, subN_unknown _, subN_unknown _⟩
        have storedNew : ∀ x ∈ m.fibers, ∀ o ∈ x.observers, ¬ OffKey (waiter, token) o →
            StoredObserverOk root w (m2.update g) x.id o := by
          intro x hx o ho off
          have ho' := countdown_of_not_offKey off
          dsimp only at ho'
          have stored := (typed.machine.fiber hx).observers o ho
          rw [ho'] at stored ⊢
          exact advance _ (widenCols x.id) stored
        have fresh : FiberTyped root w (m2.update g) g := by
          have view' : ExceptView m (m2.update g) (wf.id, token) := by
            rw [wid]
            exact ExceptView.obs_trans obs2 (exceptView_rupdate hy' hid agree)
          exact fiberTyped_repend old view' (Nat.le_of_eq view2.nextId.symm)
            (Nat.le_of_eq view2.nextToken.symm) parked ptok
            (fun o ho off => storedNew wf hmem o ho (by rw [← wid]; exact off))
            (fun _ h => nomatch h)
        have replaced := configTyped_replace t2 hy' hid (ykept.2.2.1.trans idle)
          (ykept.2.1.trans live) idle (key := (waiter, token)) agree keysG
          (fun tok r hr => absurd hr (fun h => gNone tok r (by rw [← gid]; exact h)))
          (fun x hx _ o ho off => by
            obtain ⟨x0, hx0, kept⟩ := view2.member x hx
            rw [kept.1]
            exact storedNew x0 hx0 o (by rw [← kept.2.2.2.1]; exact ho) off)
          (fun src ex o ho off => by
            have ho' := countdown_of_not_offKey off
            dsimp only at ho'
            have queued := (typed.queue.observer src ex o (List.mem_cons_of_mem _ ho)).2
            rw [ho'] at queued ⊢
            exact advance _ (fun a e h => exitOk_subN h (subN_unknown _) (subN_unknown _)) queued)
          fresh
        have resumeOk : Contracts.ResumeOk (TypedProg root) w waiter token
            (countdownPark.resumePrim (interpR root.program) p.resumeWith exits) := by
          intro ty declared
          have pt := payload.token
          rw [ptok, declared] at pt
          cases pt
          exact resumePrim_typed root payload exits typedWalk
        have free : requestOfR (m2.update g) waiter token = none := by
          cases h : requestOfR (m2.update g) waiter token with
          | none => rfl
          | some r => exact (gNone token r h).elim
        have consed := configTyped_cons_resume replaced resumeOk
          (by rw [show (m2.update g).nextToken = m.nextToken from view2.nextToken]; exact keyBelow)
          free
        have all := configTyped_evaluates consed nested evals
        rw [List.nil_append, List.append_assoc, List.singleton_append]
        exact all
      · rw [hwalk] at typedWalk nextWalk
        dsimp only
        rw [single, List.map_cons, List.map_nil, if_pos ptok]
        obtain ⟨nextMem, ⟨gn, hgn, _⟩, restSub⟩ := nextWalk next rest' rfl
        let p' : RPending :=
          { p with waitingOn := some next, remaining := rest', collected := exits }
        let g : RFiber := { wf with pending := [p'] }
        let obs : RFiber → RFiber := fun x =>
          { x with observers := x.observers ++ [Observer.countdown waiter token] }
        have gnid : gn.id = next := rfiber?_id hgn
        have hgn' : m2.fiber? gn.id = some gn := by rw [gnid]; exact hgn
        have modified : m2.modify next obs = m2.update (obs gn) := by
          unfold RunMachine.modify
          rw [hgn]
        show ConfigTyped root rootTy w ((m2.modify next obs).update g) (([] ++ nested) ++ rest)
        rw [modified]
        -- the next target's record and the head's columns at it
        obtain ⟨gn0, hgn0, gnkept⟩ := view2.lookup next gn hgn
        have nextCols : FiberColumnsBelow w gn.id a e := by
          rw [gnkept.1]
          exact payload.targets next (List.mem_append_right _ nextMem) gn0 hgn0
        have widenCols : ∀ (s : FiberId) (a e : Ty), FiberColumnsBelow w s a e →
            FiberColumnsBelow w s .unknown .unknown := by
          rintro s a e ⟨ty, d, _, _⟩
          exact ⟨ty, d, subN_unknown _, subN_unknown _⟩
        have m2NoReq : requestOfR m2 waiter token = none := by
          cases h : requestOfR m2 waiter token with
          | none => rfl
          | some r =>
            have back := view2.requests h
            rw [keyFree] at back
            cases back
        -- step 1: the next target stores the countdown observer
        have obs2' : ObsView m2 (m2.update (obs gn)) :=
          obsView_rupdate hgn' rfl (PendingWeaker.refl _)
        have t3 : ConfigTyped root rootTy w (m2.update (obs gn)) rest := by
          refine configTyped_rupdate t2 hgn' rfl (PendingWeaker.refl _) rfl rfl rfl rfl rfl
            (fun p => p) (fun k hk => ?_) ?_
          · unfold Guard.fiberKeys at hk
            rw [show (obs gn).observers = gn.observers ++ [Observer.countdown waiter token] from rfl,
              List.flatMap_append] at hk
            rcases List.mem_append.mp hk with hk | hk
            · rcases List.mem_append.mp hk with hk | hk
              · exact Or.inl (fiberKeys_internal (rfiber?_mem hgn')
                  (List.mem_append_left _ hk))
              · rw [List.flatMap_cons, List.flatMap_nil, List.append_nil] at hk
                rw [List.mem_singleton.mp hk]
                exact Or.inr ⟨by rw [view2.nextToken]; exact keyBelow, m2NoReq⟩
            · exact Or.inl (fiberKeys_internal (rfiber?_mem hgn') (List.mem_append_right _ hk))
          · have moved := fiberTyped_transport (t2.machine.fiber (rfiber?_mem hgn')) obs2'
              (Nat.le_refl _) (Nat.le_refl _)
            refine ⟨runFiberOk_congr moved.ok rfl rfl rfl rfl rfl rfl rfl, moved.delivery,
              moved.below, moved.pendingShape, moved.parkedIdle,
              moved.parkedBelow, moved.exited, moved.exitedStack, moved.deferredCause,
              moved.pendingOwner, fun o ho => ?_, moved.registration, moved.code, moved.tokens,
              fun r race hr o ho => by
                rcases mem_append_observer ho with old' | rfl
                · exact moved.raceObservers r race hr o old'
                · have hr2 : m2.race? r = some race := (obs2'.races r).symm.trans hr
                  have hr0 : m.race? r = some race := by
                    unfold RunMachine.race? at hr2 ⊢
                    rw [view2.races] at hr2
                    exact hr2
                  exact typed.queue.raceObservers source exit (.countdown waiter token)
                    List.mem_cons_self r race hr0,
              moved.targetsBelow,
              fun o ho k hk => by
                rcases mem_append_observer ho with old' | rfl
                · exact moved.observersBelow o old' k hk
                · rw [show Guard.observerKeys (.countdown waiter token) = [(waiter, token)] from rfl,
                    List.mem_singleton] at hk
                  subst hk
                  show waiter.value < m2.nextId
                  rw [view2.nextId, ← wid]
                  exact old.below⟩
            rcases mem_append_observer ho with old' | rfl
            · exact moved.observers o old'
            · show CountdownAt w (m2.update (obs gn)) waiter token (FiberColumnsBelow w gn.id)
              unfold CountdownAt
              cases hz : (m2.update (obs gn)).fiber? waiter with
              | none => trivial
              | some z =>
                dsimp only
                cases hzp : z.pending.find? (fun q => decide (q.token = token)) with
                | none => trivial
                | some q =>
                  dsimp only
                  obtain ⟨z1, hz1, _, weakz⟩ := obs2'.fibers waiter z hz
                  obtain ⟨z0, hz0, _, weak0⟩ := obs2.fibers waiter z1 hz1
                  rw [hw] at hz0
                  cases hz0
                  have found := weak0 token q (weakz token q hzp)
                  rw [hp] at found
                  cases found
                  exact ⟨a, e, tt, ⟨payload.token, payload.collected, fun id hid f hf => by
                    obtain ⟨f1, hf1, hid1, _⟩ := obs2'.fibers id f hf
                    obtain ⟨f0, hf0, hid0, _⟩ := obs2.fibers id f1 hf1
                    rw [hid1, hid0]
                    exact payload.targets id hid f0 hf0, payload.resume⟩, nextCols⟩
        -- step 2: the waiter's record advances
        obtain ⟨y3, hy3, y3facts⟩ : ∃ y3, (m2.update (obs gn)).fiber? waiter = some y3 ∧
            y3.id = waiter ∧ y3.running = false ∧ y3.exit = none ∧
            (∀ k, k ∈ Guard.fiberKeys g → k ∈ Guard.fiberKeys y3) := by
          by_cases same : next = waiter
          · refine ⟨obs gn, ?_, by rw [show (obs gn).id = gn.id from rfl, gnid, same], ?_, ?_, ?_⟩
            · rw [← same, ← gnid]
              exact rfiber?_update_self hgn' rfl
            · have gy : gn = y := by
                rw [same] at hgn
                rw [hy] at hgn
                exact (Option.some.inj hgn).symm
              rw [show (obs gn).running = gn.running from rfl, gy]
              exact ykept.2.2.1.trans idle
            · have gy : gn = y := by
                rw [same] at hgn
                rw [hy] at hgn
                exact (Option.some.inj hgn).symm
              rw [show (obs gn).exit = gn.exit from rfl, gy]
              exact ykept.2.1.trans live
            · have gy : gn = y := by
                rw [same] at hgn
                rw [hy] at hgn
                exact (Option.some.inj hgn).symm
              intro k hk
              unfold Guard.fiberKeys at hk ⊢
              rw [show (obs gn).observers = gn.observers ++ [Observer.countdown waiter token] from rfl,
                show (obs gn).dispatcher = gn.dispatcher from rfl, gy, ykept.2.2.2.1,
                ykept.2.2.2.2.1, List.flatMap_append]
              rcases List.mem_append.mp hk with hk | hk
              · exact List.mem_append_left _ (List.mem_append_left _ hk)
              · exact List.mem_append_right _ hk
          · refine ⟨y, ?_, yid, ykept.2.2.1.trans idle, ykept.2.1.trans live, ?_⟩
            · rw [rfiber?_update_other (show waiter ≠ (obs gn).id by
                rw [show (obs gn).id = gn.id from rfl, gnid]
                exact fun h => same h.symm)]
              exact hy
            · intro k hk
              unfold Guard.fiberKeys at hk ⊢
              rw [ykept.2.2.2.1, ykept.2.2.2.2.1]
              exact hk
        obtain ⟨y3id, y3idle, y3live, y3keys⟩ := y3facts
        have hy3' : (m2.update (obs gn)).fiber? y3.id = some y3 := by rw [y3id]; exact hy3
        have gid : g.id = waiter := wid
        have hid : g.id = y3.id := gid.trans y3id.symm
        have look : ((m2.update (obs gn)).update g).fiber? waiter = some g := by
          rw [← gid]
          exact rfiber?_update_self hy3' hid
        have find' : g.pending.find? (fun q => decide (q.token = token)) = some p' := by
          show ([p'] : List RPending).find? (fun q => decide (q.token = token)) = some p'
          rw [List.find?_cons, decide_eq_true (show p'.token = token from ptok)]
        have gNone : ∀ tok r, requestOfR ((m2.update (obs gn)).update g) waiter tok = some r →
            False := by
          intro tok r hr
          by_cases hpk : g.parked = .withGuard tok
          · rw [requestOfR_of_parked look hpk] at hr
            have current : g.frame.current = wf.frame.current := rfl
            rw [current, wfNone] at hr
            cases hr
          · rw [requestOfR_of_not_parked look hpk] at hr
            cases hr
        have agree : PendingExcept y3.pending g.pending
            (fun tok => (y3.id, tok) = (waiter, token)) := by
          intro tok q skip hq
          have hq' : ([p'] : List RPending).find? (fun x => decide (x.token = tok)) = some q := hq
          rw [List.find?_cons] at hq'
          by_cases same : p'.token = tok
          · exact absurd (by rw [y3id, ← same]; exact congrArg _ ptok) skip
          · rw [decide_eq_false same] at hq'
            cases hq'
        have back3 : ∀ id f', (m2.update (obs gn)).fiber? id = some f' →
            ∃ f, m.fiber? id = some f ∧ f'.id = f.id :=
          lookupBack_update (fun id f' h => by
            obtain ⟨f, hf, k⟩ := view2.lookup id f' h
            exact ⟨f, hf, k.1⟩) hgn' rfl
        have lookupNew := lookupBack_update back3 hy3' hid
        have targets' : ∀ id ∈ p'.waitingOn.toList ++ p'.remaining,
            id ∈ p.waitingOn.toList ++ p.remaining := by
          intro id hid'
          rcases List.mem_append.mp hid' with h | h
          · have hn : id = next := by
              change id ∈ [next] at h
              exact List.mem_singleton.mp h
            rw [hn]
            exact List.mem_append_right _ nextMem
          · exact List.mem_append_right _ (restSub id h)
        have advance : ∀ (incoming : Ty → Ty → Prop),
            (∀ a e, incoming a e → incoming .unknown .unknown) →
            (∃ a e tt, CountdownPayload w m waiter p a e tt ∧ incoming a e) →
            CountdownAt w ((m2.update (obs gn)).update g) waiter token incoming := by
          intro incoming widen other
          exact countdownAt_advance payload other widen look find' rfl rfl typedWalk targets'
            lookupNew
        have storedNew : ∀ x ∈ m.fibers, ∀ o ∈ x.observers, ¬ OffKey (waiter, token) o →
            StoredObserverOk root w ((m2.update (obs gn)).update g) x.id o := by
          intro x hx o ho off
          have ho' := countdown_of_not_offKey off
          dsimp only at ho'
          have stored := (typed.machine.fiber hx).observers o ho
          rw [ho'] at stored ⊢
          exact advance _ (widenCols x.id) (countdownAt_found stored hw hp)
        have obs3 : ObsView m (m2.update (obs gn)) := obs2.trans obs2'
        have fresh : FiberTyped root w ((m2.update (obs gn)).update g) g := by
          have view' : ExceptView m ((m2.update (obs gn)).update g) (wf.id, token) := by
            rw [wid]
            exact ExceptView.obs_trans obs3 (exceptView_rupdate hy3' hid agree)
          exact fiberTyped_repend old view' (Nat.le_of_eq view2.nextId.symm)
            (Nat.le_of_eq view2.nextToken.symm) parked ptok
            (fun o ho off => storedNew wf hmem o ho (by rw [← wid]; exact off))
            (fun id hid => by
              have pmem : p ∈ wf.pending := List.mem_of_find?_eq_some hp
              rcases List.mem_append.mp hid with h | h
              · rw [List.mem_singleton.mp h]
                exact old.targetsBelow p pmem next (List.mem_append_right _ nextMem)
              · exact old.targetsBelow p pmem id (List.mem_append_right _ (restSub id h)))
        have replaced := configTyped_replace t3 hy3' hid y3idle y3live idle
          (key := (waiter, token)) agree
          (fun k hk => Or.inl (fiberKeys_internal (rfiber?_mem hy3') (y3keys k hk)))
          (fun tok r hr => absurd hr (fun h => gNone tok r (by rw [← gid]; exact h)))
          (fun x hx _ o ho off => by
            rcases mem_rupdate hx with rfl | ⟨hold, _⟩
            · rcases mem_append_observer ho with old' | rfl
              · obtain ⟨x0, hx0, kept⟩ := view2.member gn (rfiber?_mem hgn')
                rw [show (obs gn).id = gn.id from rfl, kept.1]
                exact storedNew x0 hx0 o (by rw [← kept.2.2.2.1]; exact old') off
              · show CountdownAt w ((m2.update (obs gn)).update g) waiter token
                  (FiberColumnsBelow w gn.id)
                exact advance _ (widenCols gn.id) ⟨a, e, tt, payload, nextCols⟩
            · obtain ⟨x0, hx0, kept⟩ := view2.member x hold
              rw [kept.1]
              exact storedNew x0 hx0 o (by rw [← kept.2.2.2.1]; exact ho) off)
          (fun src ex o ho off => by
            have ho' := countdown_of_not_offKey off
            dsimp only at ho'
            have queued := (typed.queue.observer src ex o (List.mem_cons_of_mem _ ho)).2
            rw [ho'] at queued ⊢
            exact advance _ (fun a e h => exitOk_subN h (subN_unknown _) (subN_unknown _))
              (countdownAt_found queued hw hp))
          fresh
        have all := configTyped_evaluates replaced nested evals
        rw [List.nil_append]
        exact all

/-! ## `observe` -/

/-- **`observe` keeps `I`**: at the same world for every observer but a scope-finalizer drop,
which removes the finalizer from a scope the store holds (`ObserverCommandOk`'s
`Stores.ScopeLive` excludes the halting arm) at the world over the edited store. -/
theorem observe_preserves (root : ProgramSource) (rootTy : EffTy) (source : FiberId)
    (exit : ExitV) (observer : Observer) :
    StepPreserves root rootTy (.observe source exit observer) := by
  intro w m rest _ typed
  have tail := configTyped_tail typed
  have wide := typed.machine.wide
  have obsOk : ObserverCommandOk root w m source exit observer :=
    (typed.queue.observer source exit observer List.mem_cons_self).2
  cases observer with
  | countdown waiter token => exact ⟨w, leHost_refl w, observe_countdown root rootTy typed⟩
  | raceCallback raceId =>
    exact ⟨w, leHost_refl w, observe_raceCallback root rootTy tail source exit raceId obsOk⟩
  | resumeAwait waiter token mode =>
    refine ⟨w, leHost_refl w, ?_⟩
    have keyMem : (waiter, token) ∈
        (Cmd.observe source exit (.resumeAwait waiter token mode) :: rest).flatMap
          Guard.commandKeys :=
      List.mem_flatMap.mpr ⟨_, List.mem_cons_self, List.mem_singleton_self _⟩
    have free : requestOfR m waiter token = none := by
      cases h : requestOfR m waiter token with
      | none => rfl
      | some r => exact absurd keyMem (typed.queue.keys.disjoint waiter token r h)
    exact configTyped_cons_resume
      (configTyped_emit tail [RunEvent.observerFired source (.resumeAwait waiter token mode)])
      (observerCommand_resume_typed root w m source waiter token mode exit obsOk)
      (typed.queue.keys.below _ keyMem) free
  | untrackChild parent =>
    exact ⟨w, leHost_refl w, configTyped_modify_quiet
      (configTyped_emit tail [RunEvent.observerFired source (.untrackChild parent)]) parent
      (quiet_untrack source) (fun _ _ o ho => Or.inl ho)⟩
  | callback key =>
    exact ⟨w, leHost_refl w, configTyped_emit
      (configTyped_emit tail [RunEvent.observerFired source (.callback key)]) _⟩
  | dropScopeFinalizer scope key =>
    have live : m.state.ScopeLive scope := obsOk
    obtain ⟨entry, hentry⟩ := Option.isSome_iff_exists.mp live
    let s : Stores := { m.state with scopes := m.state.scopes.removeFinalizer scope key }
    have hdrop : (interpR root.program).dropFinalizer scope key m.state = some s :=
      dropFinalizer_live root hentry
    have step : syncOpStep (.scopeRemove scope key) m.state = some (s, Val.unit) := rfl
    have le : m.state.le s := syncOpStep_le _ _ _ _ step
    have wf : s.WF := syncOpStep_wf (.scopeRemove scope key) m.state s Val.unit wide.wf live step
    have ord : w.leHost { w with state := s } := by
      apply leHost_restate
      · rw [wide.state]
        exact le
      · rw [wide.state]
      · rw [wide.state]
      · rw [wide.state]
    have stores : StoresOk (preds root) { w with state := s } Expect.root s := by
      obtain ⟨c0, c1, c2, c3, c4, c5⟩ := storesOk_world ord rfl rfl rfl wide.stores
      exact ⟨c0, c1, ⟨c2.c0⟩, scopeStoreOk_removeFinalizer c3 scope key, c4, c5⟩
    have t1 := configTyped_emit tail [RunEvent.observerFired source (.dropScopeFinalizer scope key)]
    obtain ⟨_, restated⟩ := configTyped_restate t1 le rfl rfl rfl wf stores (fun _ h => h)
      wide.live.dueOwners (fun _ h => h)
    refine ⟨_, ord, ?_⟩
    show ConfigTyped root rootTy { w with state := s }
      (fireObserver (interpR root.program) source exit (m, []) (.dropScopeFinalizer scope key)).1
      ((fireObserver (interpR root.program) source exit (m, []) (.dropScopeFinalizer scope key)).2
        ++ rest)
    unfold fireObserver
    dsimp only
    rw [show (m.emit [RunEvent.observerFired source (.dropScopeFinalizer scope key)]).state =
      m.state from rfl, hdrop]
    exact restated

end Effect4.Program.Typed

#obligation_proved Effect4.Program.Typed.M6Ledger.step_observe :=
  @Effect4.Program.Typed.observe_preserves
-- `M6Ledger`'s report runs at the foot of the last command module, which sees every proof.
#typed_state_obligations Effect4.Program.Typed.M6Ledger ceiling 4
  using aesop (rule_sets := [Effect4.TypedState])
