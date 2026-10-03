import Effect4.Laws.Program.Typed.Assembly
import Effect4.Laws.Program.Typed.Seq

/-!
# Laws.Program.Typed.Commands.Bookkeeping — the bookkeeping commands keep the typed configuration

Wave 2's first command group (seat D3): the commands that read no fiber's code and edit only the
bookkeeping a fiber or the store carries. Each obligation is `StepPreserves`
(`Typed/Assembly.lean`): a dispatched command keeps `I` (`ConfigTyped`) at some later world, and
every halting arm of the command is shown unreachable from `I` (decisions row 139's census).

Proved here: `trackChild` (no halting arm), `drainDue` (`postTask` on an unknown owner, excluded by
`MachineLive.dueOwners`), `link` (an unknown scope or target, excluded by `QueueOk.links`).
`observe` is proved in `Commands/Observe.lean` over this module's transports (its race-callback arm,
`observe_raceCallback`, is here). Not provable as stated (seat D3's receipt, with checked
refutations, `docs/research/2026-10-01-landing/seat-D3/probes/`): `exitDone` (an exited fiber whose
current code is a race registration marker keeps `RegistrationState` only through its stack, which
`exitDone` clears) and `wake` (a batch wake owes a resume to a waiter whose token no clause relates
to the completion it is owed).

The first part is shared by every command group: `J` (`MachineTyped`) split into its machine-wide
clauses (`MachineWide`) and the clauses read at one fiber (`FiberTyped`), the lookups of the
reference machine after a fiber, race or store edit, and the transports of the observer
correlations, the authority, the delivery and the queue facts between two machines whose views
agree. A command proof then states only what the command changes.
-/

set_option autoImplicit false
namespace Effect4.Program.Typed
open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Sched Effect4.Program.Denote
open Contracts

/-! ## Lookups on the reference machine -/

theorem rfiber?_id {m : RState} {id : FiberId} {f : RFiber} (h : m.fiber? id = some f) :
    f.id = id :=
  of_decide_eq_true (List.find?_some (p := fun g : RFiber => decide (g.id = id)) h)

theorem rfiber?_mem {m : RState} {id : FiberId} {f : RFiber} (h : m.fiber? id = some f) :
    f ∈ m.fibers :=
  List.mem_of_find?_eq_some h

/-- With distinct ids, a member is what its id looks up. -/
theorem rfiber?_of_mem {m : RState} (nodup : (m.fibers.map RunFiber.id).Nodup) {f : RFiber}
    (hf : f ∈ m.fibers) : m.fiber? f.id = some f := by
  unfold RunMachine.fiber?
  generalize m.fibers = fibers at nodup hf
  induction fibers with
  | nil => cases hf
  | cons x rest ih =>
    rw [List.map_cons, List.nodup_cons] at nodup
    rw [List.find?_cons]
    rcases List.mem_cons.mp hf with rfl | there
    · rw [decide_eq_true rfl]
    · have hne : x.id ≠ f.id := fun h => nodup.1 (h ▸ List.mem_map_of_mem there)
      rw [decide_eq_false hne]
      exact ih nodup.2 there

theorem rfiber?_update (m : RState) (g : RFiber) (id : FiberId) :
    (m.update g).fiber? id = (m.fiber? id).map (fun x => if x.id = g.id then g else x) := by
  unfold RunMachine.update RunMachine.fiber?
  rw [List.find?_map]
  have hp : ((fun x : RFiber => decide (x.id = id)) ∘ fun x => if x.id = g.id then g else x) =
      fun x : RFiber => decide (x.id = id) := by
    funext x
    by_cases hx : x.id = g.id
    · rw [Function.comp_apply, if_pos hx, hx]
    · rw [Function.comp_apply, if_neg hx]
  rw [hp]

theorem rfiber?_update_self {m : RState} {f g : RFiber} (hf : m.fiber? f.id = some f)
    (hid : g.id = f.id) : (m.update g).fiber? g.id = some g := by
  rw [rfiber?_update, hid, hf, Option.map_some, if_pos rfl]

theorem rfiber?_update_other {m : RState} {g : RFiber} {id : FiberId} (hne : id ≠ g.id) :
    (m.update g).fiber? id = m.fiber? id := by
  rw [rfiber?_update]
  cases h : m.fiber? id with
  | none => rfl
  | some x =>
    have hx : x.id = id := rfiber?_id h
    rw [Option.map_some, hx, if_neg hne]

theorem mem_rupdate {m : RState} {g x : RFiber} (hx : x ∈ (m.update g).fibers) :
    x = g ∨ (x ∈ m.fibers ∧ x.id ≠ g.id) := by
  obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
  by_cases h : y.id = g.id
  · rw [if_pos h]
    exact Or.inl rfl
  · rw [if_neg h]
    exact Or.inr ⟨hy, h⟩

theorem mem_rupdate_of_ne {m : RState} {g x : RFiber} (hx : x ∈ m.fibers) (hne : x.id ≠ g.id) :
    x ∈ (m.update g).fibers :=
  List.mem_map.mpr ⟨x, hx, if_neg hne⟩

theorem mem_rupdate_self {m : RState} {f g : RFiber} (hf : f ∈ m.fibers) (hid : f.id = g.id) :
    g ∈ (m.update g).fibers :=
  List.mem_map.mpr ⟨f, hf, if_pos hid⟩

theorem rupdate_ids (m : RState) (g : RFiber) :
    (m.update g).fibers.map RunFiber.id = m.fibers.map RunFiber.id := by
  unfold RunMachine.update
  rw [List.map_map]
  apply List.map_congr_left
  intro x _
  by_cases h : x.id = g.id
  · rw [Function.comp_apply, if_pos h, h]
  · rw [Function.comp_apply, if_neg h]

/-- A fiber's keys are its observers' and its dispatcher's (`Guard.fiberKeys`); the machine's
internal keys are the store's, the races' and every fiber's. -/
theorem internalKeys_fibers (m : RState) :
    Guard.internalKeys m = (Guard.wakeKeys m.state.timers.wake ++
      m.state.deferreds.cells.flatMap (fun c => Guard.wakeKeys c.wake) ++
      m.state.deferreds.due.map (fun d => (d.waiter, d.token)) ++
      m.races.map (fun r => (r.host, r.token))) ++ m.fibers.flatMap Guard.fiberKeys := rfl

theorem fiberKeys_internal {m : RState} {f : RFiber} (hf : f ∈ m.fibers) :
    Guard.fiberKeys f ⊆ Guard.internalKeys m := by
  intro key hk
  rw [internalKeys_fibers]
  exact List.mem_append_right _ (List.mem_flatMap.mpr ⟨f, hf, hk⟩)

/-- After a fiber edit, every internal key is an old one or a key of the edited fiber. -/
theorem internalKeys_rupdate (m : RState) (g : RFiber) :
    Guard.internalKeys (m.update g) ⊆ Guard.internalKeys m ++ Guard.fiberKeys g := by
  intro key hk
  rw [internalKeys_fibers] at hk
  rcases List.mem_append.mp hk with hstore | hfs
  · exact List.mem_append_left _ (by rw [internalKeys_fibers]; exact List.mem_append_left _ hstore)
  · obtain ⟨z, hz, hkz⟩ := List.mem_flatMap.mp hfs
    rcases mem_rupdate hz with rfl | ⟨hold, _⟩
    · exact List.mem_append_right _ hkz
    · exact List.mem_append_left _ (fiberKeys_internal hold hkz)

/-- After a fiber edit, every old key not carried by the replaced fiber is still a key. -/
theorem internalKeys_rupdate_old {m : RState} {f g : RFiber} (hf : f ∈ m.fibers)
    (nodup : (m.fibers.map RunFiber.id).Nodup) (hid : g.id = f.id) :
    Guard.internalKeys m ⊆ Guard.internalKeys (m.update g) ++ Guard.fiberKeys f := by
  intro key hk
  rw [internalKeys_fibers] at hk
  rcases List.mem_append.mp hk with hstore | hfs
  · apply List.mem_append_left
    rw [internalKeys_fibers]
    exact List.mem_append_left _ hstore
  · obtain ⟨z, hz, hkz⟩ := List.mem_flatMap.mp hfs
    by_cases hzid : z.id = g.id
    · have same : z = f := by
        have hz' := rfiber?_of_mem nodup hz
        have hf' := rfiber?_of_mem nodup hf
        rw [hzid, hid] at hz'
        exact Option.some.inj (hz'.symm.trans hf')
      subst same
      exact List.mem_append_right _ hkz
    · apply List.mem_append_left
      rw [internalKeys_fibers]
      exact List.mem_append_right _ (List.mem_flatMap.mpr ⟨z, mem_rupdate_of_ne hz hzid, hkz⟩)

/-! ## `J` split at the fibers

`J` is a conjunction of machine-wide clauses and clauses read at one fiber. A command edits one
fiber, the store or the races; the split lets its proof re-establish only what it touched. -/

/-- The clauses of `J` read at one fiber `f` of machine `m` (the per-fiber parts of
`WorldValid`, the generated bundle, `ActiveDelivery`, `SchedulerState`, `ObserverState`,
`RegistrationState` and `LiveCode`). -/
structure FiberTyped (root : ProgramSource) (w : World) (m : RState) (f : RFiber) : Prop where
  ok : RunFiberOk (preds root) w Expect.root f
  delivery : ∀ token, f.parked = .withGuard token →
    ∃ tin final, w.Θ f.id token = some tin ∧ w.Γ f.id = some final ∧
      HostStack root w m f.id tin final f.frame.stack ∧ InterruptProvenance f.frame
  below : f.id.value < m.nextId
  pendingShape : Guard.PendingShape f
  parkedIdle : f.parked ≠ .notParked → f.running = false
  parkedBelow : ∀ token, f.parked = .withGuard token → token < m.nextToken
  exited : f.exit.isSome = true → f.parked = .notParked ∧ f.running = false
  exitedStack : f.exit.isSome = true → f.frame.stack = []
  deferredCause : f.frame.deferredInterrupt = true → f.frame.interruptedCause.isSome = true
  pendingOwner : ∀ pending ∈ f.pending, (w.Θ f.id pending.token).isSome = true
  observers : ∀ o ∈ f.observers, StoredObserverOk root w m f.id o
  registration : ∀ raceId, raceRegistrationR f.frame.current = some raceId →
    ∃ race resultTy, m.race? raceId = some race ∧ race.host = f.id ∧
      w.Θ race.host race.token = some resultTy ∧ StackReply root w m f resultTy
  /-- An idle fiber's code is typed at its declaration; a parked one is typed by `delivery` (its
  current is the operation it parked on, which nothing reads: `resume` and an applied interrupt
  overwrite it, `evaluate` skips it; seat M6B's finding). -/
  code : f.exit = none → f.running = false → raceRegistrationR f.frame.current = none →
    f.parked = .notParked → ∀ ty, w.Γ f.id = some ty → CodeOk root w m f.id ty f.frame
  tokens : ∀ token, f.parked = .withGuard token → (w.Θ f.id token).isSome = true
  /-- Decisions row 134 (d), at this fiber: none of its stored observers holds a race's key. -/
  raceObservers : ∀ raceId race, m.race? raceId = some race → ∀ o ∈ f.observers,
    (race.host, race.token) ∉ Guard.observerKeys o
  /-- Decisions row 134 (e), at this fiber: its countdowns' targets and its stored observers' keys
  name fibers below `nextId`. -/
  targetsBelow : ∀ p ∈ f.pending, ∀ id ∈ p.waitingOn.toList ++ p.remaining, id.value < m.nextId
  observersBelow : ∀ o ∈ f.observers, ∀ k ∈ Guard.observerKeys o, k.1.value < m.nextId
  /-- Its tracked children are declared (`WorldValid.children`). -/
  children : ∀ c ∈ f.children, (w.Γ c).isSome = true

/-- A fiber's delivery clause moves to a machine whose races keep their host and token (row 188
(b)'s alternative reads them). -/
theorem FiberTyped.delivery_races {root : ProgramSource} {w : World} {m m' : RState} {x : RFiber}
    (h : FiberTyped root w m x) (kept : RacesKept m m') :
    ∀ token, x.parked = .withGuard token →
      ∃ tin final, w.Θ x.id token = some tin ∧ w.Γ x.id = some final ∧
        HostStack root w m' x.id tin final x.frame.stack ∧ InterruptProvenance x.frame := by
  intro token hp
  obtain ⟨tin, final, declared, final', stack, provenance⟩ := h.delivery token hp
  exact ⟨tin, final, declared, final', hostStack_races kept stack, provenance⟩

/-- A fiber's code clause moves likewise. -/
theorem FiberTyped.code_races {root : ProgramSource} {w : World} {m m' : RState} {x : RFiber}
    (h : FiberTyped root w m x) (kept : RacesKept m m') :
    x.exit = none → x.running = false → raceRegistrationR x.frame.current = none →
      x.parked = .notParked → ∀ ty, w.Γ x.id = some ty → CodeOk root w m' x.id ty x.frame :=
  fun hx hr hm hp ty declared => codeOk_races kept (h.code hx hr hm hp ty declared)

/-- The machine-wide clauses of `J`. -/
structure MachineWide (root : ProgramSource) (rootTy : EffTy) (w : World) (m : RState) : Prop where
  ids : w.ids = m.fibers.map (·.id)
  fibers : ∀ id, (w.Γ id).isSome = true ↔ id ∈ m.fibers.map (·.id)
  heap : ∀ key, (w.Ρ key).isSome = true ↔ key.index < m.state.refs.length
  promises : ∀ key, (w.«Π» key).isSome = true ↔ key.index < m.state.deferreds.cells.length
  tokenBound : ∀ id token ty, w.Θ id token = some ty → token < m.nextToken
  tokenTargets : ∀ id token ty, w.Θ id token = some ty → (w.Γ id).isSome = true
  state : w.state = m.state
  wf : m.state.WF
  cells : HeapTable w ∧ PromiseTable w
  rootDeclared : w.Γ Api.root = some rootTy
  races : (preds root).RaceOk w Expect.root m.races
  stores : StoresOk (preds root) w Expect.root m.state
  fiberIds : (m.fibers.map RunFiber.id).Nodup
  raceIds : (m.races.map Race.id).Nodup
  racesBelow : ∀ race ∈ m.races, race.id < m.nextRace
  raceHosts : ∀ race ∈ m.races, ∃ fiber, m.fiber? race.host = some fiber
  keysBelow : Guard.InternalKeysBelow m
  requestsBelow : ∀ fiber token request, requestOfR m fiber token = some request →
    token < m.nextToken
  requestsOwned : ∀ fiber token request, requestOfR m fiber token = some request →
    (fiber, token) ∉ Guard.internalKeys m
  services : w.serviceTy = root.sig.serviceTy
  live : MachineLive m
  /-- Decisions row 134 (a): the timer store's sleepers are declared at a type `void` fits. -/
  timers : WakeTyped w SleepDemand m.state.timers.wake
  /-- Decisions row 134 (b): a Deferred cell's waiters are declared above the cell's columns. -/
  waiters : ∀ key cell, m.state.deferreds.cellAt key = some cell → ∀ a e, w.«Π» key = some (a, e) →
    WakeTyped w (AwaitDemand a e) cell.wake
  /-- Decisions row 134 (e): every race's live set names fibers below `nextId`. -/
  liveBelow : ∀ raceId race, m.race? raceId = some race → ∀ id ∈ race.state.live,
    id.value < m.nextId
  /-- The source's layer references are well formed (decisions row 170; `MachineTyped.sourceWF`). -/
  sourceWF : root.program.layerRefsWF = true

theorem MachineTyped.wide {root : ProgramSource} {rootTy : EffTy} {w : World} {m : RState}
    (typed : MachineTyped root rootTy w m) : MachineWide root rootTy w m := by
  obtain ⟨⟨valid, ok, _, sched, _, _⟩, services, _, live, sourceWF⟩ := typed
  exact ⟨valid.ids, valid.fibers, valid.heap, valid.promises, valid.tokenBound, valid.tokenTargets,
    valid.state, valid.wf, valid.cells, valid.root, ok.c1, ok.c2, sched.fiberIds, sched.raceIds, sched.racesBelow,
    sched.raceHosts, sched.keysBelow, sched.requestsBelow, sched.requestsOwned, services, live,
    valid.timers, valid.waiters, sched.liveBelow, sourceWF⟩

theorem MachineTyped.fiber {root : ProgramSource} {rootTy : EffTy} {w : World} {m : RState}
    (typed : MachineTyped root rootTy w m) {f : RFiber} (hf : f ∈ m.fibers) :
    FiberTyped root w m f := by
  obtain ⟨⟨valid, ok, deliv, sched, obsv, reg⟩, _, code, _⟩ := typed
  exact ⟨ok.c0 f hf, deliv f hf, sched.fibersBelow f hf, sched.pendingShape f hf,
    sched.parkedIdle f hf, sched.parkedBelow f hf, sched.exited f hf, sched.exitedStack f hf,
    sched.deferredCause f hf,
    obsv.pendingOwner f hf, obsv.observers f hf, reg f hf, code f hf, valid.tokens f hf,
    fun r race hr o ho => sched.raceObservers r race hr f hf o ho, sched.targetsBelow f hf,
    sched.observersBelow f hf, valid.children f hf⟩

/-- `J` from its machine-wide clauses and its clauses at every fiber. -/
theorem machineTyped_of {root : ProgramSource} {rootTy : EffTy} {w : World} {m : RState}
    (wide : MachineWide root rootTy w m) (fibers : ∀ f ∈ m.fibers, FiberTyped root w m f) :
    MachineTyped root rootTy w m :=
  ⟨⟨⟨wide.ids, wide.fibers, wide.heap, wide.promises, fun f hf => (fibers f hf).tokens,
      wide.tokenBound, wide.tokenTargets, wide.state, wide.wf, wide.cells, wide.rootDeclared, wide.timers,
      wide.waiters, fun f hf => (fibers f hf).children⟩,
    ⟨fun f hf => (fibers f hf).ok, wide.races, wide.stores⟩,
    fun f hf => (fibers f hf).delivery,
    ⟨wide.fiberIds, fun f hf => (fibers f hf).below, wide.raceIds, wide.racesBelow,
      wide.raceHosts, wide.keysBelow, wide.requestsBelow, wide.requestsOwned,
      fun f hf => (fibers f hf).pendingShape, fun f hf => (fibers f hf).parkedIdle,
      fun f hf => (fibers f hf).parkedBelow, fun f hf => (fibers f hf).exited,
      fun f hf => (fibers f hf).exitedStack, fun f hf => (fibers f hf).deferredCause,
      fun r race hr f hf o ho => (fibers f hf).raceObservers r race hr o ho, wide.liveBelow,
      fun f hf => (fibers f hf).targetsBelow, fun f hf => (fibers f hf).observersBelow⟩,
    ⟨fun f hf => (fibers f hf).pendingOwner, fun f hf => (fibers f hf).observers⟩,
    fun f hf => (fibers f hf).registration⟩,
    wide.services, fun f hf => (fibers f hf).code, wide.live, wide.sourceWF⟩

/-! ## The observer correlations and the queue between two machines -/

/-- A fiber's pending parks after an edit find no park the old ones did not: a park found by
token is the old park (`resume` filters the resumed one out, an applied interrupt clears them). -/
def PendingWeaker (old new : List RPending) : Prop :=
  ∀ token p, new.find? (fun q => q.token = token) = some p →
    old.find? (fun q => q.token = token) = some p

theorem PendingWeaker.refl (l : List RPending) : PendingWeaker l l := fun _ _ h => h

/-- Two machines whose fiber lookups agree on ids, find no new pending park, and keep every fiber;
whose races agree; and whose second store holds every scope the first holds: the observer and
enrollment correlations read the same facts on both, or weaker ones. -/
structure ObsView (m m' : RState) : Prop where
  fibers : ∀ id f', m'.fiber? id = some f' →
    ∃ f, m.fiber? id = some f ∧ f'.id = f.id ∧ PendingWeaker f.pending f'.pending
  exists_ : ∀ id, (m.fiber? id).isSome = true → (m'.fiber? id).isSome = true
  races : ∀ race, m'.race? race = m.race? race
  scopes : ∀ sc, m.state.ScopeLive sc → m'.state.ScopeLive sc

theorem ObsView.refl (m : RState) : ObsView m m :=
  ⟨fun _ f' h => ⟨f', h, rfl, PendingWeaker.refl _⟩, fun _ h => h, fun _ => rfl, fun _ h => h⟩

theorem ObsView.trans {m m' m'' : RState} (a : ObsView m m') (b : ObsView m' m'') :
    ObsView m m'' := by
  refine ⟨fun id f'' h'' => ?_, fun id h => b.exists_ id (a.exists_ id h),
    fun r => (b.races r).trans (a.races r), fun sc h => b.scopes sc (a.scopes sc h)⟩
  obtain ⟨f', h', hid', weak'⟩ := b.fibers id f'' h''
  obtain ⟨f, h, hid, weak⟩ := a.fibers id f' h'
  exact ⟨f, h, hid'.trans hid, fun token p hp => weak token p (weak' token p hp)⟩

/-- Machines with the same fibers agree on every lookup. -/
theorem ObsView.ofLookup {m m' : RState} (lookup : ∀ id, m'.fiber? id = m.fiber? id)
    (races : ∀ r, m'.race? r = m.race? r) (scopes : ∀ sc, m.state.ScopeLive sc → m'.state.ScopeLive sc) :
    ObsView m m' :=
  ⟨fun id f' h' => ⟨f', (lookup id).symm.trans h', rfl, PendingWeaker.refl _⟩,
    fun id h => by rw [lookup]; exact h, races, scopes⟩

theorem countdownAt_view {w : World} {m m' : RState}
    (fibers : ∀ id f', m'.fiber? id = some f' →
      ∃ f, m.fiber? id = some f ∧ f'.id = f.id ∧ PendingWeaker f.pending f'.pending)
    {waiter : FiberId} {token : Nat} {incoming : Ty → Ty → Prop}
    (h : CountdownAt w m waiter token incoming) : CountdownAt w m' waiter token incoming := by
  unfold CountdownAt at h ⊢
  cases h' : m'.fiber? waiter with
  | none => trivial
  | some f' =>
    obtain ⟨f, h0, _, weak⟩ := fibers waiter f' h'
    rw [h0] at h
    dsimp only at h ⊢
    cases hfind : f'.pending.find? (fun pending => pending.token = token) with
    | none => trivial
    | some pending =>
      rw [weak token pending hfind] at h
      dsimp only at h ⊢
      obtain ⟨answer, error, tokenTy, payload, incomingOk⟩ := h
      refine ⟨answer, error, tokenTy, ⟨payload.token, payload.collected, ?_, payload.resume⟩,
        incomingOk⟩
      intro id member target lookup
      obtain ⟨old, hold, hid, _⟩ := fibers id target lookup
      rw [hid]
      exact payload.targets id member old hold

theorem storedObserverOk_view {root : ProgramSource} {w : World} {m m' : RState}
    (view : ObsView m m') {source : FiberId} (o : Observer)
    (h : StoredObserverOk root w m source o) : StoredObserverOk root w m' source o := by
  cases o with
  | resumeAwait waiter token mode => exact h
  | countdown waiter token => exact countdownAt_view view.fibers h
  | raceCallback raceId =>
    unfold StoredObserverOk at h ⊢
    dsimp only at h ⊢
    rw [view.races]
    exact h
  | dropScopeFinalizer scope key => exact view.scopes scope h
  | untrackChild parent => trivial
  | callback key => trivial

theorem observerCommandOk_view {root : ProgramSource} {w : World} {m m' : RState}
    (view : ObsView m m') {source : FiberId} {exit : ExitV} (o : Observer)
    (h : ObserverCommandOk root w m source exit o) : ObserverCommandOk root w m' source exit o := by
  cases o with
  | resumeAwait waiter token mode => exact h
  | countdown waiter token => exact countdownAt_view view.fibers h
  | raceCallback raceId =>
    unfold ObserverCommandOk at h ⊢
    dsimp only at h ⊢
    rw [view.races]
    exact h
  | dropScopeFinalizer scope key => exact view.scopes scope h
  | untrackChild parent => trivial
  | callback key => trivial

theorem enrollRaceOk_view {root : ProgramSource} {w : World} {m m' : RState}
    (view : ObsView m m') (ids : m.nextId ≤ m'.nextId) {raceId : Nat} {child : FiberId}
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

/-- The queue facts move to a machine whose lookups agree, given the commands' authority and
delivery there, no new external request and no smaller fiber-id or token supply. -/
theorem queueOk_transport {root : ProgramSource} {w : World} {m m' : RState} {q : List RCmd}
    (queue : QueueOk root w m q) (view : ObsView m m') (ids : m.nextId ≤ m'.nextId)
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
    ⟨fun key hk => Nat.lt_of_lt_of_le (queue.keys.below key hk) tokens,
      fun fiber token r hr hk => queue.keys.disjoint fiber token r (requests fiber token r hr) hk⟩,
    fun s e o ho => ⟨Nat.lt_of_lt_of_le (queue.observer s e o ho).1 ids,
      observerCommandOk_view view o (queue.observer s e o ho).2⟩,
    fun r c hc => enrollRaceOk_view view ids (queue.enroll r c hc), queue.noRaceAfterInterrupt,
    fun md sc tg ir ex hl => ?_,
    fun s e o ho r race hr => queue.raceObservers s e o ho r race ((view.races r).symm.trans hr)⟩
  obtain ⟨live, present⟩ := queue.links md sc tg ir ex hl
  exact ⟨view.scopes sc live, view.exists_ tg present⟩

/-- Dropping the head of the queue keeps `I` on the same machine: every fact of the tail is a fact
of the whole queue. -/
theorem configTyped_tail {root : ProgramSource} {rootTy : EffTy} {w : World} {m : RState}
    {c : RCmd} {rest : List RCmd} (typed : ConfigTyped root rootTy w m (c :: rest)) :
    ConfigTyped root rootTy w m rest := by
  obtain ⟨machine, code, queue⟩ := typed
  refine ⟨machine, fun f hf hr ⟨y, reads⟩ => code f hf hr ⟨y, ?_⟩, ?_⟩
  · rcases reads with r | r
    · exact Or.inl (List.mem_cons_of_mem _ r)
    · exact Or.inr (List.mem_cons_of_mem _ r)
  · refine ⟨fun x hx => queue.payload x (List.mem_cons_of_mem _ hx),
      fun x hx => queue.authority x (List.mem_cons_of_mem _ hx),
      fun x hx => queue.delivery x (List.mem_cons_of_mem _ hx), ?_, queue.registration.2,
      ⟨fun key hk => queue.keys.below key (List.mem_flatMap.mpr ?_),
        fun fiber token r hr hk => queue.keys.disjoint fiber token r hr (List.mem_flatMap.mpr ?_)⟩,
      fun s e o ho => queue.observer s e o (List.mem_cons_of_mem _ ho),
      fun r ch hc => queue.enroll r ch (List.mem_cons_of_mem _ hc),
      fun h y r hr => queue.noRaceAfterInterrupt h y r (List.mem_cons_of_mem _ hr),
      fun md sc tg ir ex hl => queue.links md sc tg ir ex (List.mem_cons_of_mem _ hl),
      fun s e o ho => queue.raceObservers s e o (List.mem_cons_of_mem _ ho)⟩
    · have nodup := queue.owners
      rw [List.filterMap_cons] at nodup
      cases hc : Guard.commandOwner m c with
      | none =>
        rw [hc] at nodup
        exact nodup
      | some owner =>
        rw [hc] at nodup
        exact (List.nodup_cons.mp nodup).2
    · obtain ⟨x, hx, hkx⟩ := List.mem_flatMap.mp hk
      exact ⟨x, List.mem_cons_of_mem _ hx, hkx⟩
    · obtain ⟨x, hx, hkx⟩ := List.mem_flatMap.mp hk
      exact ⟨x, List.mem_cons_of_mem _ hx, hkx⟩

/-! ## What authority and delivery read

A queued command's authority reads the flags of the fiber it names (`running`, `parked`, `exit`,
its current code for a registration marker); its delivery reads that fiber's saved stack. Two
machines whose lookups agree on these move both. -/

/-- What a command's authority and delivery read of a fiber. -/
def ctlView (f : RFiber) : FiberId × Bool × Parked × Option ExitV × RSaved :=
  (f.id, f.running, f.parked, f.exit, f.frame)

theorem ctlView_lookup {m m' : RState}
    (ctl : ∀ id, (m'.fiber? id).map ctlView = (m.fiber? id).map ctlView)
    {id : FiberId} {f : RFiber} (h : m.fiber? id = some f) :
    ∃ f', m'.fiber? id = some f' ∧ f'.id = f.id ∧ f'.running = f.running ∧
      f'.parked = f.parked ∧ f'.exit = f.exit ∧ f'.frame = f.frame := by
  have hv := ctl id
  rw [h] at hv
  cases h' : m'.fiber? id with
  | none =>
    rw [h'] at hv
    cases hv
  | some f' =>
    rw [h'] at hv
    simp only [ctlView, Option.map_some, Option.some.injEq, Prod.mk.injEq] at hv
    exact ⟨f', rfl, hv.1, hv.2.1, hv.2.2.1, hv.2.2.2.1, hv.2.2.2.2⟩

theorem ctlView_lookup_back {m m' : RState}
    (ctl : ∀ id, (m'.fiber? id).map ctlView = (m.fiber? id).map ctlView)
    {id : FiberId} {f' : RFiber} (h' : m'.fiber? id = some f') :
    ∃ f, m.fiber? id = some f ∧ f'.id = f.id ∧ f'.running = f.running ∧
      f'.parked = f.parked ∧ f'.exit = f.exit ∧ f'.frame = f.frame := by
  have hv := ctl id
  rw [h'] at hv
  cases h : m.fiber? id with
  | none =>
    rw [h] at hv
    cases hv
  | some f =>
    rw [h] at hv
    simp only [ctlView, Option.map_some, Option.some.injEq, Prod.mk.injEq] at hv
    exact ⟨f, rfl, hv.1, hv.2.1, hv.2.2.1, hv.2.2.2.1, hv.2.2.2.2⟩

theorem activeAt_view {m m' : RState}
    (ctl : ∀ id, (m'.fiber? id).map ctlView = (m.fiber? id).map ctlView)
    {id : FiberId} (h : Guard.ActiveAt m id) : Guard.ActiveAt m' id := by
  obtain ⟨f, hf, running, parked⟩ := h
  obtain ⟨f', hf', _, hr, hp, _, _⟩ := ctlView_lookup ctl hf
  exact ⟨f', hf', hr.trans running, hp.trans parked⟩

theorem commandAuthority_view {m m' : RState}
    (ctl : ∀ id, (m'.fiber? id).map ctlView = (m.fiber? id).map ctlView)
    (races : ∀ r, m'.race? r = m.race? r) (c : RCmd) (h : CommandAuthorityR m c) :
    CommandAuthorityR m' c := by
  cases c with
  | loop fiber _ => exact activeAt_view ctl h
  | deliver fiber _ => exact activeAt_view ctl h
  | finish fiber _ => exact activeAt_view ctl h
  | afterInterrupt fiber _ _ => exact activeAt_view ctl h
  | closeParAwait fiber _ _ => exact activeAt_view ctl h
  | raceCancel _ fiber _ _ _ => exact activeAt_view ctl h
  | registrationDone raceId _ =>
    obtain ⟨race, f, found, hf, running, parked, marker⟩ := h
    obtain ⟨f', hf', _, hr, hp, _, hframe⟩ := ctlView_lookup ctl hf
    refine ⟨race, f', (races raceId).trans found, hf', hr.trans running, hp.trans parked, ?_⟩
    rw [hframe]
    exact marker
  | launch raceId =>
    obtain ⟨race, found, active⟩ := h
    exact ⟨race, (races raceId).trans found, activeAt_view ctl active⟩
  | enrollRace raceId _ =>
    obtain ⟨race, found, active⟩ := h
    exact ⟨race, (races raceId).trans found, activeAt_view ctl active⟩
  | exitDone fiber =>
    obtain ⟨f, hf, exited⟩ := h
    obtain ⟨f', hf', _, _, _, hx, _⟩ := ctlView_lookup ctl hf
    exact ⟨f', hf', by rw [hx]; exact exited⟩
  | evaluate _ => trivial
  | resume _ _ _ => trivial
  | interruptTarget _ _ _ => trivial
  | trackChild _ _ => trivial
  | observe _ _ _ => trivial
  | link _ _ _ _ _ => trivial
  | drainDue => trivial
  | wake _ _ => trivial

theorem stackReply_congr {root : ProgramSource} {w : World} {m m' : RState} {f f' : RFiber}
    {ty : EffTy} (kept : RacesKept m m') (id : f'.id = f.id) (frame : f'.frame = f.frame)
    (h : StackReply root w m f ty) : StackReply root w m' f' ty := by
  have moved := stackReply_races kept h
  unfold StackReply at moved ⊢
  rw [id, frame]
  exact moved

theorem commandDelivery_view {root : ProgramSource} {w : World} {m m' : RState}
    (ctl : ∀ id, (m'.fiber? id).map ctlView = (m.fiber? id).map ctlView) (kept : RacesKept m m')
    (c : RCmd)
    (h : CommandDeliveryOk root w m c) : CommandDeliveryOk root w m' c := by
  cases c with
  | afterInterrupt host _ kind =>
    intro f' hf'
    obtain ⟨f, hf, hid, _, _, _, hframe⟩ := ctlView_lookup_back ctl hf'
    obtain ⟨replyTy, reply, stack⟩ := h f hf
    exact ⟨replyTy, reply, stackReply_congr kept hid hframe stack⟩
  | raceCancel _ host _ remaining visited =>
    intro f' hf'
    obtain ⟨f, hf, hid, _, _, _, hframe⟩ := ctlView_lookup_back ctl hf'
    obtain ⟨answer, error, cols, stack⟩ := h f hf
    exact ⟨answer, error, cols, stackReply_congr kept hid hframe stack⟩
  | closeParAwait host _ targets =>
    intro f' hf'
    obtain ⟨f, hf, hid, _, _, _, hframe⟩ := ctlView_lookup_back ctl hf'
    obtain ⟨answer, error, cols, protocol, stack⟩ := h f hf
    exact ⟨answer, error, cols, protocol, stackReply_congr kept hid hframe stack⟩
  | finish host _ =>
    intro f' hf'
    obtain ⟨f, hf, _, _, _, _, hframe⟩ := ctlView_lookup_back ctl hf'
    rw [hframe]
    exact h f hf
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

/-- What a command's authority reads of a fiber: its flags and its current code. -/
def authView (f : RFiber) : FiberId × Bool × Parked × Option ExitV × RProgram :=
  (f.id, f.running, f.parked, f.exit, f.frame.current)

theorem authView_lookup {m m' : RState}
    (auth : ∀ id, (m'.fiber? id).map authView = (m.fiber? id).map authView)
    {id : FiberId} {f : RFiber} (h : m.fiber? id = some f) :
    ∃ f', m'.fiber? id = some f' ∧ f'.id = f.id ∧ f'.running = f.running ∧
      f'.parked = f.parked ∧ f'.exit = f.exit ∧ f'.frame.current = f.frame.current := by
  have hv := auth id
  rw [h] at hv
  cases h' : m'.fiber? id with
  | none =>
    rw [h'] at hv
    cases hv
  | some f' =>
    rw [h'] at hv
    simp only [authView, Option.map_some, Option.some.injEq, Prod.mk.injEq] at hv
    exact ⟨f', rfl, hv.1, hv.2.1, hv.2.2.1, hv.2.2.2.1, hv.2.2.2.2⟩

theorem commandAuthority_auth {m m' : RState}
    (auth : ∀ id, (m'.fiber? id).map authView = (m.fiber? id).map authView)
    (races : ∀ r, m'.race? r = m.race? r) (c : RCmd) (h : CommandAuthorityR m c) :
    CommandAuthorityR m' c := by
  have active : ∀ {id}, Guard.ActiveAt m id → Guard.ActiveAt m' id := fun {id} h => by
    obtain ⟨f, hf, running, parked⟩ := h
    obtain ⟨f', hf', _, hr, hp, _, _⟩ := authView_lookup auth hf
    exact ⟨f', hf', hr.trans running, hp.trans parked⟩
  cases c with
  | loop fiber _ => exact active h
  | deliver fiber _ => exact active h
  | finish fiber _ => exact active h
  | afterInterrupt fiber _ _ => exact active h
  | closeParAwait fiber _ _ => exact active h
  | raceCancel _ fiber _ _ _ => exact active h
  | registrationDone raceId _ =>
    obtain ⟨race, f, found, hf, running, parked, marker⟩ := h
    obtain ⟨f', hf', _, hr, hp, _, hcur⟩ := authView_lookup auth hf
    refine ⟨race, f', (races raceId).trans found, hf', hr.trans running, hp.trans parked, ?_⟩
    rw [hcur]
    exact marker
  | launch raceId =>
    obtain ⟨race, found, act⟩ := h
    exact ⟨race, (races raceId).trans found, active act⟩
  | enrollRace raceId _ =>
    obtain ⟨race, found, act⟩ := h
    exact ⟨race, (races raceId).trans found, active act⟩
  | exitDone fiber =>
    obtain ⟨f, hf, exited⟩ := h
    obtain ⟨f', hf', _, _, _, hx, _⟩ := authView_lookup auth hf
    exact ⟨f', hf', by rw [hx]; exact exited⟩
  | evaluate _ => trivial
  | resume _ _ _ => trivial
  | interruptTarget _ _ _ => trivial
  | trackChild _ _ => trivial
  | observe _ _ _ => trivial
  | link _ _ _ _ _ => trivial
  | drainDue => trivial
  | wake _ _ => trivial

/-- What a command's delivery reads of the fiber it finds: its id and saved stack, with the
provenance of its saved state. -/
def StackView (m m' : RState) : Prop :=
  ∀ id f', m'.fiber? id = some f' → ∃ f, m.fiber? id = some f ∧ f'.id = f.id ∧
    f'.frame.stack = f.frame.stack ∧ (InterruptProvenance f.frame → InterruptProvenance f'.frame)

theorem stackReply_view {root : ProgramSource} {w : World} {m m' : RState} {f f' : RFiber}
    {ty : EffTy} (kept : RacesKept m m') (hid : f'.id = f.id)
    (hstack : f'.frame.stack = f.frame.stack)
    (hprov : InterruptProvenance f.frame → InterruptProvenance f'.frame)
    (h : StackReply root w m f ty) : StackReply root w m' f' ty := by
  obtain ⟨final, declared, stack, provenance⟩ := stackReply_races kept h
  refine ⟨final, ?_, ?_, hprov provenance⟩
  · rw [hid]
    exact declared
  · rw [hstack, hid]
    exact stack

theorem commandDelivery_stack {root : ProgramSource} {w : World} {m m' : RState}
    (view : StackView m m') (kept : RacesKept m m') (c : RCmd) (h : CommandDeliveryOk root w m c) :
    CommandDeliveryOk root w m' c := by
  cases c with
  | afterInterrupt host _ kind =>
    intro f' hf'
    obtain ⟨f, hf, hid, hstack, hprov⟩ := view host f' hf'
    obtain ⟨replyTy, ok, stack⟩ := h f hf
    exact ⟨replyTy, ok, stackReply_view kept hid hstack hprov stack⟩
  | raceCancel _ host _ remaining visited =>
    intro f' hf'
    obtain ⟨f, hf, hid, hstack, hprov⟩ := view host f' hf'
    obtain ⟨answer, error, cols, stack⟩ := h f hf
    exact ⟨answer, error, cols, stackReply_view kept hid hstack hprov stack⟩
  | closeParAwait host _ targets =>
    intro f' hf'
    obtain ⟨f, hf, hid, hstack, hprov⟩ := view host f' hf'
    obtain ⟨answer, error, cols, protocol, stack⟩ := h f hf
    exact ⟨answer, error, cols, protocol, stackReply_view kept hid hstack hprov stack⟩
  | finish host _ =>
    intro f' hf'
    obtain ⟨f, hf, _, hstack, _⟩ := view host f' hf'
    rw [hstack]
    exact h f hf
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

theorem requestOfR_congr {m m' : RState} {fiber : FiberId} (h : m'.fiber? fiber = m.fiber? fiber)
    (token : Nat) : requestOfR m' fiber token = requestOfR m fiber token := by
  unfold requestOfR
  rw [h]

/-- The external request of a fiber parked on `token` is its current code's. -/
theorem requestOfR_of_parked {m : RState} {fiber : FiberId} {f : RFiber}
    (h : m.fiber? fiber = some f) {token : Nat} (hp : f.parked = .withGuard token) :
    requestOfR m fiber token = externalRequestR f.frame.current := by
  unfold requestOfR
  rw [h]
  show (guard (f.parked = .withGuard token) >>= fun _ => externalRequestR f.frame.current) = _
  unfold guard
  rw [if_pos hp]
  rfl

/-- A fiber not parked on `token` has no external request at it. -/
theorem requestOfR_of_not_parked {m : RState} {fiber : FiberId} {f : RFiber}
    (h : m.fiber? fiber = some f) {token : Nat} (hp : f.parked ≠ .withGuard token) :
    requestOfR m fiber token = none := by
  unfold requestOfR
  rw [h]
  show (guard (f.parked = .withGuard token) >>= fun _ => externalRequestR f.frame.current) = _
  unfold guard
  rw [if_neg hp]
  rfl

/-! ## One fiber edited

`m.update g` replaces the fiber `f` the id finds by `g`. The other fibers keep their clauses on
the edited machine (`fiberTyped_transport`); the machine-wide clauses need only that `g` keeps the
id, carries internal keys the machine already holds, and has no external request `f` did not
have (`machineWide_rupdate`). -/

/-- The unchanged fibers keep their clauses on a machine whose observer view agrees and whose
counters did not shrink. -/
theorem fiberTyped_transport {root : ProgramSource} {w : World} {m m' : RState} {x : RFiber}
    (h : FiberTyped root w m x) (view : ObsView m m') (nextId : m.nextId ≤ m'.nextId)
    (nextToken : m.nextToken ≤ m'.nextToken) : FiberTyped root w m' x := by
  refine ⟨h.ok, h.delivery_races (racesKept_of_eq view.races), Nat.lt_of_lt_of_le h.below nextId,
    h.pendingShape, h.parkedIdle,
    fun token hp => Nat.lt_of_lt_of_le (h.parkedBelow token hp) nextToken, h.exited,
    h.exitedStack, h.deferredCause, h.pendingOwner, fun o ho => storedObserverOk_view view o (h.observers o ho),
    fun raceId marker => ?_, h.code_races (racesKept_of_eq view.races), h.tokens,
    fun r race hr o ho => h.raceObservers r race ((view.races r).symm.trans hr) o ho,
    fun p hp id hid => Nat.lt_of_lt_of_le (h.targetsBelow p hp id hid) nextId,
    fun o ho k hk => Nat.lt_of_lt_of_le (h.observersBelow o ho k hk) nextId, h.children⟩
  obtain ⟨race, resultTy, found, host, token, reply⟩ := h.registration raceId marker
  exact ⟨race, resultTy, (view.races raceId).trans found, host, token,
    stackReply_races (racesKept_of_eq view.races) reply⟩

/-- The fiber a lookup finds by the edited fiber's id is the replaced one. -/
theorem rfiber?_same {m : RState} {f x : RFiber} {id : FiberId} (hf : m.fiber? f.id = some f)
    (hx : m.fiber? id = some x) (same : x.id = f.id) : x = f := by
  have hid : x.id = id := rfiber?_id hx
  rw [← hid, same, hf] at hx
  exact (Option.some.inj hx).symm

/-- The observer view after an edit that keeps the edited fiber's id and finds no new pending
park on it. -/
theorem obsView_rupdate {m : RState} {f g : RFiber} (hf : m.fiber? f.id = some f)
    (hid : g.id = f.id) (pending : PendingWeaker f.pending g.pending) : ObsView m (m.update g) := by
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
        exact ⟨x, rfl, hid, pending⟩
      · rw [if_neg hx]
        exact ⟨x, rfl, rfl, PendingWeaker.refl _⟩
  · rw [rfiber?_update, Option.isSome_map]
    exact h

/-- The control view after an edit that keeps the edited fiber's id, flags and saved state. -/
theorem ctlView_rupdate {m : RState} {f g : RFiber} (hf : m.fiber? f.id = some f)
    (hid : g.id = f.id) (running : g.running = f.running) (parked : g.parked = f.parked)
    (exit : g.exit = f.exit) (frame : g.frame = f.frame) :
    ∀ id, ((m.update g).fiber? id).map ctlView = (m.fiber? id).map ctlView := by
  intro id
  rw [rfiber?_update]
  cases h : m.fiber? id with
  | none => rfl
  | some x =>
    by_cases hx : x.id = g.id
    · rw [Option.map_some, if_pos hx]
      have same : x = f := rfiber?_same hf h (hx.trans hid)
      subst same
      simp only [ctlView, hid, running, parked, exit, frame, Option.map_some]
    · rw [Option.map_some, if_neg hx]

/-- `J`'s machine-wide clauses after one fiber is edited. -/
theorem machineWide_rupdate {root : ProgramSource} {rootTy : EffTy} {w : World} {m : RState}
    {f g : RFiber} (wide : MachineWide root rootTy w m)
    (hid : g.id = f.id)
    (keys : ∀ k ∈ Guard.fiberKeys g, k ∈ Guard.internalKeys m ∨
      (k.2 < m.nextToken ∧ requestOfR m k.1 k.2 = none))
    (request : ∀ token r, requestOfR (m.update g) g.id token = some r →
      requestOfR m f.id token = some r) :
    MachineWide root rootTy w (m.update g) := by
  have ids : (m.update g).fibers.map (·.id) = m.fibers.map (·.id) := rupdate_ids m g
  have requests : ∀ fiber token r, requestOfR (m.update g) fiber token = some r →
      requestOfR m fiber token = some r := by
    intro fiber token r hr
    by_cases same : fiber = g.id
    · subst same
      rw [hid]
      exact request token r hr
    · rw [requestOfR_congr (rfiber?_update_other same)] at hr
      exact hr
  refine ⟨wide.ids.trans ids.symm, fun id => by rw [ids]; exact wide.fibers id, wide.heap,
    wide.promises, wide.tokenBound, wide.tokenTargets, wide.state, wide.wf, wide.cells,
    wide.rootDeclared,
    wide.races, wide.stores, by rw [rupdate_ids]; exact wide.fiberIds, wide.raceIds,
    wide.racesBelow, fun race hr => ?_, fun key hk => ?_,
    fun fiber token r hr => wide.requestsBelow fiber token r (requests fiber token r hr),
    fun fiber token r hr hk => ?_, wide.services,
    ⟨wide.live.running, fun o ho owner priority mode => ?_⟩, wide.timers, wide.waiters,
    wide.liveBelow, wide.sourceWF⟩
  · obtain ⟨x, hx⟩ := wide.raceHosts race hr
    rw [rfiber?_update, hx, Option.map_some]
    exact ⟨_, rfl⟩
  · rcases List.mem_append.mp (internalKeys_rupdate m g hk) with old | new
    · exact wide.keysBelow key old
    · rcases keys key new with old | ⟨below, _⟩
      · exact wide.keysBelow key old
      · exact below
  · have before := requests fiber token r hr
    rcases List.mem_append.mp (internalKeys_rupdate m g hk) with old | new
    · exact wide.requestsOwned fiber token r before old
    · rcases keys (fiber, token) new with old | ⟨_, none⟩
      · exact wide.requestsOwned fiber token r before old
      · rw [none] at before
        cases before
  · have before := wide.live.dueOwners o ho owner priority mode
    rw [rfiber?_update, Option.isSome_map]
    exact before

theorem runFiberOk_congr {P : Preds World} {w : World} {e : Expect} {f g : RFiber}
    (h : RunFiberOk P w e f) (id : g.id = f.id) (frame : g.frame = f.frame)
    (pending : g.pending = f.pending) (finalizing : g.finalizing = f.finalizing)
    (exit : g.exit = f.exit) (dispatcher : g.dispatcher = f.dispatcher)
    (context : g.context = f.context) : RunFiberOk P w e g := by
  obtain ⟨c0, c1, c2, c3, c4, c5⟩ := h
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [id, frame]
    exact c0
  · rw [pending]
    exact c1
  · rw [finalizing, id]
    exact c2
  · rw [exit, id]
    exact c3
  · rw [dispatcher]
    exact c4
  · rw [context]
    exact c5

/-- A fiber edit that keeps every field a typed clause reads; it may append observers that carry
no key, and change the fields no clause reads (children, the op counter, the budget fields, the
yield override). -/
structure QuietEdit (k : RFiber → RFiber) : Prop where
  id : ∀ f, (k f).id = f.id
  frame : ∀ f, (k f).frame = f.frame
  running : ∀ f, (k f).running = f.running
  parked : ∀ f, (k f).parked = f.parked
  pending : ∀ f, (k f).pending = f.pending
  finalizing : ∀ f, (k f).finalizing = f.finalizing
  exit : ∀ f, (k f).exit = f.exit
  dispatcher : ∀ f, (k f).dispatcher = f.dispatcher
  context : ∀ f, (k f).context = f.context
  observers : ∀ f, ∃ extra, (k f).observers = f.observers ++ extra ∧
    ∀ o ∈ extra, Guard.observerKeys o = []

theorem QuietEdit.keys {k : RFiber → RFiber} (quiet : QuietEdit k) (f : RFiber) :
    Guard.fiberKeys (k f) ⊆ Guard.fiberKeys f := by
  obtain ⟨extra, hobs, nokeys⟩ := quiet.observers f
  intro key hk
  unfold Guard.fiberKeys at hk ⊢
  rw [hobs, quiet.dispatcher f, List.flatMap_append] at hk
  rcases List.mem_append.mp hk with hk | hk
  · rcases List.mem_append.mp hk with hk | hk
    · exact List.mem_append_left _ hk
    · obtain ⟨o, ho, hko⟩ := List.mem_flatMap.mp hk
      rw [nokeys o ho] at hko
      cases hko
  · exact List.mem_append_right _ hk

/-- **A quiet fiber edit keeps `I`**, given that every observer it appends is typed on the edited
machine (`trackChild`'s untrack observer, `link`'s drop, `enrollRace`'s race callback, the yield
override). An appended observer holds no key (`QuietEdit.observers`), so decisions row 134 (d)
and (e) hold of it vacuously. -/
theorem configTyped_modify_quiet {root : ProgramSource} {rootTy : EffTy} {w : World} {m : RState}
    {q : List RCmd} (typed : ConfigTyped root rootTy w m q) (target : FiberId)
    {k : RFiber → RFiber} (quiet : QuietEdit k)
    (added : ∀ f, m.fiber? target = some f → ∀ o ∈ (k f).observers,
      o ∈ f.observers ∨ StoredObserverOk root w (m.modify target k) f.id o)
    (children : ∀ f, ∀ c ∈ (k f).children, c ∈ f.children ∨ (w.Γ c).isSome = true) :
    ConfigTyped root rootTy w (m.modify target k) q := by
  unfold RunMachine.modify
  cases hfound : m.fiber? target with
  | none => exact typed
  | some f =>
    show ConfigTyped root rootTy w (m.update (k f)) q
    have fid : f.id = target := rfiber?_id hfound
    have hf : m.fiber? f.id = some f := by rw [fid]; exact hfound
    have hmem : f ∈ m.fibers := rfiber?_mem hf
    have look : (m.update (k f)).fiber? (k f).id = some (k f) := rfiber?_update_self hf (quiet.id f)
    have view : ObsView m (m.update (k f)) :=
      obsView_rupdate hf (quiet.id f) (by rw [quiet.pending f]; exact PendingWeaker.refl _)
    have ctl := ctlView_rupdate hf (quiet.id f) (quiet.running f) (quiet.parked f) (quiet.exit f)
      (quiet.frame f)
    obtain ⟨machine, code, queue⟩ := typed
    have old : FiberTyped root w m f := machine.fiber hmem
    have fresh : FiberTyped root w (m.update (k f)) (k f) := by
      have hpending : Guard.PendingShape (k f) := by
        have shape := old.pendingShape
        unfold Guard.PendingShape at shape ⊢
        rw [quiet.parked f, quiet.pending f]
        exact shape
      refine ⟨runFiberOk_congr old.ok (quiet.id f) (quiet.frame f) (quiet.pending f)
          (quiet.finalizing f) (quiet.exit f) (quiet.dispatcher f) (quiet.context f),
        ?_, ?_, hpending, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · rw [quiet.parked f, quiet.id f, quiet.frame f]
        exact old.delivery_races (racesKept_of_eq view.races)
      · rw [quiet.id f]
        exact old.below
      · rw [quiet.parked f, quiet.running f]
        exact old.parkedIdle
      · rw [quiet.parked f]
        exact old.parkedBelow
      · rw [quiet.exit f, quiet.parked f, quiet.running f]
        exact old.exited
      · rw [quiet.exit f, quiet.frame f]
        exact old.exitedStack
      · rw [quiet.frame f]
        exact old.deferredCause
      · rw [quiet.pending f, quiet.id f]
        exact old.pendingOwner
      · intro o ho
        rw [quiet.id f]
        rcases added f hfound o ho with stored | typed'
        · exact storedObserverOk_view view o (old.observers o stored)
        · unfold RunMachine.modify at typed'
          rw [hfound] at typed'
          exact typed'
      · intro raceId marker
        rw [quiet.frame f] at marker
        obtain ⟨race, resultTy, found, host, token, reply⟩ := old.registration raceId marker
        exact ⟨race, resultTy, found, host.trans (quiet.id f).symm, token,
          stackReply_congr (racesKept_of_eq view.races) (quiet.id f) (quiet.frame f) reply⟩
      · rw [quiet.exit f, quiet.running f, quiet.frame f, quiet.id f, quiet.parked f]
        exact old.code_races (racesKept_of_eq view.races)
      · rw [quiet.parked f, quiet.id f]
        exact old.tokens
      · intro r race hr o ho
        obtain ⟨extra, hobs, nokeys⟩ := quiet.observers f
        rw [hobs] at ho
        rcases List.mem_append.mp ho with stored | new
        · exact old.raceObservers r race hr o stored
        · rw [nokeys o new]
          exact List.not_mem_nil
      · rw [quiet.pending f]
        exact old.targetsBelow
      · intro o ho key hk
        obtain ⟨extra, hobs, nokeys⟩ := quiet.observers f
        rw [hobs] at ho
        rcases List.mem_append.mp ho with stored | new
        · exact old.observersBelow o stored key hk
        · rw [nokeys o new] at hk
          cases hk
      · intro c hc
        rcases children f c hc with kept | declared
        · exact old.children c kept
        · exact declared
    refine ⟨machineTyped_of (machineWide_rupdate machine.wide (quiet.id f)
        (fun key hk => Or.inl (fiberKeys_internal hmem (quiet.keys f hk))) ?_) (fun x hx => ?_), ?_,
      queueOk_transport queue view (Nat.le_refl _)
        (fun c _ h => commandAuthority_view ctl view.races c h)
        (fun c _ h => commandDelivery_view ctl (racesKept_of_eq view.races) c h) ?_ (Nat.le_refl _)⟩
    · intro token r hr
      by_cases hp : (k f).parked = .withGuard token
      · rw [requestOfR_of_parked look hp] at hr
        rw [quiet.parked f] at hp
        rw [requestOfR_of_parked hf hp, ← quiet.frame f]
        exact hr
      · rw [requestOfR_of_not_parked look hp] at hr
        cases hr
    · rcases mem_rupdate hx with rfl | ⟨hold, _⟩
      · exact fresh
      · exact fiberTyped_transport (machine.fiber hold) view (Nat.le_refl _) (Nat.le_refl _)
    · intro x hx running reads marker ty declared
      rcases mem_rupdate hx with rfl | ⟨hold, _⟩
      · rw [quiet.frame f, quiet.id f]
        rw [quiet.running f] at running
        rw [quiet.id f] at reads declared
        rw [quiet.frame f] at marker
        exact codeOk_races (racesKept_of_eq view.races) (code f hmem running reads marker ty declared)
      · exact codeOk_races (racesKept_of_eq view.races) (code x hold running reads marker ty declared)
    · intro fiber token r hr
      by_cases same : fiber = (k f).id
      · subst same
        by_cases hp : (k f).parked = .withGuard token
        · rw [requestOfR_of_parked look hp] at hr
          rw [quiet.parked f] at hp
          rw [quiet.id f, requestOfR_of_parked hf hp, ← quiet.frame f]
          exact hr
        · rw [requestOfR_of_not_parked look hp] at hr
          cases hr
      · rw [requestOfR_congr (rfiber?_update_other same)] at hr
        exact hr

/-! ## A later world with the same declarations

A store edit outside the store rows (a drained due list, a scope's finalizer, the clock) moves the
world's store and keeps every declaration table. Every clause of `J` and `I` that reads the world
reads it through the tables, membership and the program judgment, all monotone along the host
order (`fits_mono`, `strongExit_mono`, `typedProg_mono`, `stackAccepts_mono`); with the fiber and
token tables unchanged, the antitone readings (`∀ ty, Γ id = some ty → …`) are unchanged too. -/

section World
variable {w w' : World} (ord : w.leHost w') (hΓ : w'.Γ = w.Γ) (hΘ : w'.Θ = w.Θ)
include ord

-- `servicesFit_mono` (a context's services fit at every later world) is `Typed/Denotation.lean`'s.

omit ord in
include hΓ in
theorem fiberColumnsBelow_world {id : FiberId} {a e : Ty} (h : FiberColumnsBelow w id a e) :
    FiberColumnsBelow w' id a e := by
  unfold FiberColumnsBelow at h ⊢
  rw [hΓ]
  exact h

include hΓ hΘ in
theorem racePayload_world {root : ProgramSource} {race : RRace} {ty : EffTy}
    (h : RacePayload root w race ty) : RacePayload root w' race ty := by
  refine ⟨by rw [hΘ]; exact h.token, strongExit_mono _ _ _ _ ord h.failures,
    fun pair hp => fits_mono ord (h.winner pair hp),
    fun ex hx => strongExit_mono _ _ _ _ ord (h.accepted ex hx),
    fun wait hw => strongExit_mono _ _ _ _ ord (h.cleanup wait hw),
    fun id hid => by
      obtain ⟨t, hd, ha, he⟩ := h.live id hid
      exact ⟨t, by rw [hΓ]; exact hd, ha, he⟩,
    fun code hc => ?_⟩
  obtain ⟨cty, typed, ha, he⟩ := h.programs code hc
  exact ⟨cty, typedProg_mono root w w' cty code ord typed, ha, he⟩

include hΓ hΘ in
theorem countdownAt_world {m : RState} {waiter : FiberId} {token : Nat}
    {incoming incoming' : Ty → Ty → Prop} (hin : ∀ a e, incoming a e → incoming' a e)
    (h : CountdownAt w m waiter token incoming) : CountdownAt w' m waiter token incoming' := by
  unfold CountdownAt at h ⊢
  cases hf : m.fiber? waiter with
  | none => trivial
  | some fiber =>
    rw [hf] at h
    dsimp only at h ⊢
    cases hp : fiber.pending.find? (fun pending => pending.token = token) with
    | none => trivial
    | some pending =>
      rw [hp] at h
      dsimp only at h ⊢
      obtain ⟨answer, error, tokenTy, payload, incomingOk⟩ := h
      refine ⟨answer, error, tokenTy, ⟨by rw [hΘ]; exact payload.token,
        fun ex hx => strongExit_mono _ _ _ _ ord (payload.collected ex hx),
        fun id hid target ht => fiberColumnsBelow_world hΓ (payload.targets id hid target ht),
        ?_⟩, hin answer error incomingOk⟩
      have resume := payload.resume
      split at resume
      · exact resume
      · exact resume
      · exact strongExit_mono _ _ _ _ ord resume
      · exact strongExit_mono _ _ _ _ ord resume

include hΓ hΘ in
theorem storedObserverOk_world {root : ProgramSource} {m : RState} {source : FiberId} (o : Observer)
    (h : StoredObserverOk root w m source o) : StoredObserverOk root w' m source o := by
  cases o with
  | resumeAwait waiter token mode =>
    obtain ⟨sourceTy, declared, token'⟩ := h
    exact ⟨sourceTy, by rw [hΓ]; exact declared, by rw [hΘ]; exact token'⟩
  | countdown waiter token =>
    exact countdownAt_world ord hΓ hΘ (fun a e hc => fiberColumnsBelow_world hΓ hc) h
  | raceCallback raceId =>
    unfold StoredObserverOk at h ⊢
    dsimp only at h ⊢
    split at h
    · trivial
    · obtain ⟨resultTy, payload, live⟩ := h
      exact ⟨resultTy, racePayload_world ord hΓ hΘ payload,
        fun hl => fiberColumnsBelow_world hΓ (live hl)⟩
  | dropScopeFinalizer scope key => exact h
  | untrackChild parent => trivial
  | callback key => trivial

include hΓ hΘ in
theorem observerCommandOk_world {root : ProgramSource} {m : RState} {source : FiberId}
    {exit : ExitV} (o : Observer) (h : ObserverCommandOk root w m source exit o) :
    ObserverCommandOk root w' m source exit o := by
  cases o with
  | resumeAwait waiter token mode =>
    obtain ⟨sourceTy, declared, token', typed⟩ := h
    exact ⟨sourceTy, by rw [hΓ]; exact declared, by rw [hΘ]; exact token',
      strongExit_mono _ _ _ _ ord typed⟩
  | countdown waiter token =>
    exact countdownAt_world ord hΓ hΘ (fun a e hc => strongExit_mono _ _ _ _ ord hc) h
  | raceCallback raceId =>
    unfold ObserverCommandOk at h ⊢
    dsimp only at h ⊢
    split at h
    · trivial
    · obtain ⟨resultTy, payload, live⟩ := h
      exact ⟨resultTy, racePayload_world ord hΓ hΘ payload,
        fun hl => strongExit_mono _ _ _ _ ord (live hl)⟩
  | dropScopeFinalizer scope key => exact h
  | untrackChild parent => trivial
  | callback key => trivial

include hΓ hΘ in
theorem enrollRaceOk_world {root : ProgramSource} {m : RState} {raceId : Nat} {child : FiberId}
    (h : EnrollRaceOk root w m raceId child) : EnrollRaceOk root w' m raceId child := by
  unfold EnrollRaceOk at h ⊢
  obtain ⟨below, h⟩ := h
  refine ⟨below, ?_⟩
  split at h
  · obtain ⟨resultTy, payload, cols⟩ := h
    exact ⟨resultTy, racePayload_world ord hΓ hΘ payload, fiberColumnsBelow_world hΓ cols⟩
  · trivial

include hΓ in
theorem stackReply_world {root : ProgramSource} {m : RState} {f : RFiber} {ty : EffTy}
    (h : StackReply root w m f ty) : StackReply root w' m f ty := by
  obtain ⟨final, declared, stack, provenance⟩ := h
  exact ⟨final, by rw [hΓ]; exact declared, hostStack_mono ord stack, provenance⟩

include hΘ in
/-- A resume's code is typed at the same token declaration at the later world. -/
theorem resumeOk_world {root : ProgramSource} {target : FiberId} {token : Nat} {code : RProgram}
    (h : Contracts.ResumeOk (TypedProg root) w target token code) :
    Contracts.ResumeOk (TypedProg root) w' target token code := by
  intro ty declared
  rw [hΘ] at declared
  exact typedProg_mono root w w' ty code ord (h ty declared)

include hΓ hΘ in
theorem rcmdOk_world {root : ProgramSource} (c : RCmd) (h : RCmdOk (preds root) w c) :
    RCmdOk (preds root) w' c := by
  cases c with
  | finish fiber exit =>
    intro ty declared
    change w'.Γ fiber = some ty at declared
    rw [hΓ] at declared
    exact strongExit_mono _ _ _ _ ord (h ty declared)
  | observe fiber exit observer =>
    intro ty declared
    change w'.Γ fiber = some ty at declared
    rw [hΓ] at declared
    exact strongExit_mono _ _ _ _ ord (h ty declared)
  | resume target token code => exact resumeOk_world ord hΘ h
  | evaluate _ => trivial
  | loop _ _ => trivial
  | deliver _ _ => trivial
  | launch _ => trivial
  | enrollRace _ _ => trivial
  | registrationDone _ _ => trivial
  | interruptTarget _ _ _ => trivial
  | afterInterrupt _ _ _ => trivial
  | raceCancel _ _ _ _ _ => trivial
  | trackChild _ _ => trivial
  | exitDone _ => trivial
  | closeParAwait _ _ _ => trivial
  | link _ _ _ _ _ => trivial
  | drainDue => trivial
  | wake _ _ => trivial

include hΓ hΘ in
theorem queueOk_world {root : ProgramSource} {m : RState} {q : List RCmd}
    (queue : QueueOk root w m q) : QueueOk root w' m q :=
  ⟨fun c hc => rcmdOk_world ord hΓ hΘ c (queue.payload c hc), queue.authority,
    fun c hc => commandDelivery_mono ord (fun _ _ h => by rw [hΓ]; exact h)
      (racesKept_of_eq fun _ => rfl) (fun _ _ => rfl) (queue.delivery c hc), queue.owners,
    queue.registration, queue.keys,
    fun s e o ho => ⟨(queue.observer s e o ho).1,
      observerCommandOk_world ord hΓ hΘ o (queue.observer s e o ho).2⟩,
    fun r c hc => enrollRaceOk_world ord hΓ hΘ (queue.enroll r c hc),
    queue.noRaceAfterInterrupt, queue.links, queue.raceObservers⟩

include hΓ in
theorem readCode_world {root : ProgramSource} {m : RState} {q : List RCmd}
    (code : ReadCode root w m q) : ReadCode root w' m q := by
  intro f hf running reads marker ty declared
  rw [hΓ] at declared
  exact codeOk_mono ord (code f hf running reads marker ty declared)

include hΓ hΘ in
theorem runFiberOk_world {root : ProgramSource} {f : RFiber}
    (h : RunFiberOk (preds root) w Expect.root f) : RunFiberOk (preds root) w' Expect.root f := by
  obtain ⟨⟨c0⟩, c1, c2, c3, ⟨c4⟩, c5⟩ := h
  refine ⟨⟨fun ty declared => ?_⟩, fun p hp => ?_, fun v hv ty declared => ?_,
    fun v hv ty declared => ?_, ⟨fun b hb => ⟨fun t ht => ?_⟩⟩, servicesFit_mono ord c5⟩
  · change w'.Γ f.id = some ty at declared
    rw [hΓ] at declared
    obtain ⟨tin, stack, provenance⟩ := c0 ty declared
    exact ⟨tin, positionStack_mono ord stack, provenance⟩
  · obtain ⟨id, isSome⟩ := c1 p hp
    exact ⟨id, by rw [hΘ]; exact isSome⟩
  · change w'.Γ f.id = some ty at declared
    rw [hΓ] at declared
    exact strongExit_mono _ _ _ _ ord (c2 v hv ty declared)
  · change w'.Γ f.id = some ty at declared
    rw [hΓ] at declared
    exact strongExit_mono _ _ _ _ ord (c3 v hv ty declared)
  · have task := (c4 b hb).c0 t ht
    cases t with
    | resume target token code => exact resumeOk_world ord hΘ task
    | start _ => trivial
    | wake _ _ => trivial

include hΓ hΘ in
/-- The clauses at one fiber move to a later world with the same fiber and token tables. -/
theorem fiberTyped_world {root : ProgramSource} {m : RState} {x : RFiber}
    (h : FiberTyped root w m x) : FiberTyped root w' m x := by
  refine ⟨runFiberOk_world ord hΓ hΘ h.ok, fun token hp => ?_, h.below, h.pendingShape,
    h.parkedIdle, h.parkedBelow, h.exited, h.exitedStack, h.deferredCause, fun p hp => ?_,
    fun o ho => storedObserverOk_world ord hΓ hΘ o (h.observers o ho), fun raceId marker => ?_,
    fun hx hr hm hp ty declared => ?_, fun token hp => ?_, h.raceObservers, h.targetsBelow,
    h.observersBelow, fun c hc => by rw [hΓ]; exact h.children c hc⟩
  · obtain ⟨tin, final, declared, final', stack, provenance⟩ := h.delivery token hp
    exact ⟨tin, final, by rw [hΘ]; exact declared, by rw [hΓ]; exact final',
      hostStack_mono ord stack, provenance⟩
  · rw [hΘ]
    exact h.pendingOwner p hp
  · obtain ⟨race, resultTy, found, host, token, reply⟩ := h.registration raceId marker
    exact ⟨race, resultTy, found, host, by rw [hΘ]; exact token, stackReply_world ord hΓ reply⟩
  · rw [hΓ] at declared
    exact codeOk_mono ord (h.code hx hr hm hp ty declared)
  · rw [hΘ]
    exact h.tokens token hp

end World

/-! ## `trackChild` (no halting arm)

`forkUnsafe`'s tracking (`Machine/Fibers.lean:1956-1963`): a child that has not exited joins its
parent's children and gets the untrack observer. Neither field is read by a typed clause, and the
untrack observer is typed (`StoredObserverOk`'s `untrackChild` arm is `True`) and carries no key. -/

/-- The edit `trackChild` makes to the parent. -/
theorem quiet_children (child : FiberId) :
    QuietEdit (fun p : RFiber => { p with children := p.children ++ [child] }) :=
  ⟨fun _ => rfl, fun _ => rfl, fun _ => rfl, fun _ => rfl, fun _ => rfl, fun _ => rfl,
    fun _ => rfl, fun _ => rfl, fun _ => rfl,
    fun f => ⟨[], (List.append_nil f.observers).symm, fun _ h => nomatch h⟩⟩

/-- Appending one keyless observer. -/
theorem quiet_observe (o : Observer) (nokey : Guard.observerKeys o = []) :
    QuietEdit (fun c : RFiber => { c with observers := c.observers ++ [o] }) :=
  ⟨fun _ => rfl, fun _ => rfl, fun _ => rfl, fun _ => rfl, fun _ => rfl, fun _ => rfl,
    fun _ => rfl, fun _ => rfl, fun _ => rfl,
    fun _ => ⟨[o], rfl, fun x hx => by rw [List.mem_singleton.mp hx]; exact nokey⟩⟩

/-- An appended observer is the new one or an old one. -/
theorem mem_append_observer {f : RFiber} {o x : Observer}
    (hx : x ∈ ({ f with observers := f.observers ++ [o] } : RFiber).observers) :
    x ∈ f.observers ∨ x = o := by
  rcases List.mem_append.mp hx with old | new
  · exact Or.inl old
  · exact Or.inr (List.mem_singleton.mp new)

/-- **`trackChild` keeps `I`** (no halting arm; the world is unchanged). -/
theorem trackChild_preserves (root : ProgramSource) (rootTy : EffTy) (parent child : FiberId) :
    StepPreserves root rootTy (.trackChild parent child) := by
  intro w m rest _ typed
  refine ⟨w, leHost_refl w, ?_⟩
  have tail := configTyped_tail typed
  simp only [driveStep]
  split
  · exact tail
  · rename_i c hc
    have hc' : m.fiber? c.id = some c := by rw [rfiber?_id hc]; exact hc
    have declared : (w.Γ child).isSome = true :=
      (tail.machine.wide.fibers child).mpr (List.mem_map.mpr ⟨c, rfiber?_mem hc', rfiber?_id hc⟩)
    split
    · exact tail
    · refine configTyped_modify_quiet ?_ child (quiet_observe (.untrackChild parent) rfl) ?_
        (fun _ _ kept => Or.inl kept)
      · exact configTyped_modify_quiet tail parent (quiet_children child)
          (fun _ _ o ho => Or.inl ho) (fun _ c' hc' => (List.mem_append.mp hc').imp id
            (fun new => by rw [List.mem_singleton.mp new]; exact declared))
      · intro c _ o ho
        rcases mem_append_observer ho with old | rfl
        · exact Or.inl old
        · exact Or.inr trivial

/-! ## Queue heads, congruent machines and a general fiber edit -/

/-- The queue facts of one command placed at the head of a queue. -/
structure HeadOk (root : ProgramSource) (w : World) (m : RState) (c : RCmd) (q : List RCmd) :
    Prop where
  payload : RCmdOk (preds root) w c
  authority : CommandAuthorityR m c
  delivery : CommandDeliveryOk root w m c
  owner : ∀ o, Guard.commandOwner m c = some o → o ∉ q.filterMap (Guard.commandOwner m)
  tail : Guard.RegistrationQueue.RegistrationTail c q
  keysBelow : ∀ key ∈ Guard.commandKeys c, key.2 < m.nextToken
  keysFree : ∀ fiber token r, requestOfR m fiber token = some r → (fiber, token) ∉ Guard.commandKeys c
  observer : ∀ source exit observer, c = .observe source exit observer →
    source.value < m.nextId ∧ ObserverCommandOk root w m source exit observer
  enroll : ∀ race child, c = .enrollRace race child → EnrollRaceOk root w m race child
  noRace : ∀ host yielding race, c ≠ .afterInterrupt host yielding (.race race)
  link : ∀ mode scope target interruptor extra, c = .link mode scope target interruptor extra →
    m.state.ScopeLive scope ∧ (m.fiber? target).isSome = true
  /-- Decisions row 134 (d) at the head: a queued observer holds no race's key. -/
  raceObservers : ∀ source exit o, c = .observe source exit o → ∀ raceId race,
    m.race? raceId = some race → (race.host, race.token) ∉ Guard.observerKeys o

theorem queueOk_cons {root : ProgramSource} {w : World} {m : RState} {c : RCmd} {q : List RCmd}
    (head : HeadOk root w m c q) (queue : QueueOk root w m q) : QueueOk root w m (c :: q) := by
  refine ⟨fun x hx => ?_, fun x hx => ?_, fun x hx => ?_, ?_, ⟨head.tail, queue.registration⟩,
    ⟨fun key hk => ?_, fun fiber token r hr hk => ?_⟩, fun src e o ho => ?_, fun r ch hc => ?_,
    fun host y r hr => ?_, fun md sc tg ir ex hl => ?_, fun src e o ho => ?_⟩
  · rcases List.mem_cons.mp hx with rfl | hx
    · exact head.payload
    · exact queue.payload x hx
  · rcases List.mem_cons.mp hx with rfl | hx
    · exact head.authority
    · exact queue.authority x hx
  · rcases List.mem_cons.mp hx with rfl | hx
    · exact head.delivery
    · exact queue.delivery x hx
  · rw [List.filterMap_cons]
    cases hc : Guard.commandOwner m c with
    | none => exact queue.owners
    | some o => exact List.nodup_cons.mpr ⟨head.owner o hc, queue.owners⟩
  · rw [List.flatMap_cons] at hk
    rcases List.mem_append.mp hk with hk | hk
    · exact head.keysBelow key hk
    · exact queue.keys.below key hk
  · rw [List.flatMap_cons] at hk
    rcases List.mem_append.mp hk with hk | hk
    · exact head.keysFree fiber token r hr hk
    · exact queue.keys.disjoint fiber token r hr hk
  · rcases List.mem_cons.mp ho with h | ho
    · exact head.observer src e o h.symm
    · exact queue.observer src e o ho
  · rcases List.mem_cons.mp hc with h | hc
    · exact head.enroll r ch h.symm
    · exact queue.enroll r ch hc
  · rcases List.mem_cons.mp hr with heq | hr
    · exact head.noRace host y r heq.symm
    · exact queue.noRaceAfterInterrupt host y r hr
  · rcases List.mem_cons.mp hl with h | hl
    · exact head.link md sc tg ir ex h.symm
    · exact queue.links md sc tg ir ex hl
  · rcases List.mem_cons.mp ho with h | ho
    · exact head.raceObservers src e o h.symm
    · exact queue.raceObservers src e o ho

/-- A command that is neither `loop` nor `deliver` reads no code: `ReadCode` ignores it. -/
theorem readCode_cons {root : ProgramSource} {w : World} {m : RState} {c : RCmd} {q : List RCmd}
    (noLoop : ∀ id y, c ≠ .loop id y) (noDeliver : ∀ id y, c ≠ .deliver id y)
    (code : ReadCode root w m q) : ReadCode root w m (c :: q) := by
  intro f hf running reads marker ty declared
  obtain ⟨y, r⟩ := reads
  refine code f hf running ⟨y, ?_⟩ marker ty declared
  rcases r with r | r
  · rcases List.mem_cons.mp r with h | h
    · exact absurd h.symm (noLoop f.id y)
    · exact Or.inl h
  · rcases List.mem_cons.mp r with h | h
    · exact absurd h.symm (noDeliver f.id y)
    · exact Or.inr h

/-- **A typed resume command joins the queue**: its code is typed at its token's declaration, its
key is below the token supply, and no external request waits at it. -/
theorem configTyped_cons_resume {root : ProgramSource} {rootTy : EffTy} {w : World} {m : RState}
    {q : List RCmd} {target : FiberId} {token : Nat} {code : RProgram}
    (typed : ConfigTyped root rootTy w m q)
    (resume : Contracts.ResumeOk (TypedProg root) w target token code)
    (below : token < m.nextToken) (free : requestOfR m target token = none) :
    ConfigTyped root rootTy w m (.resume target token code :: q) := by
  refine ⟨typed.machine, readCode_cons (fun _ _ h => nomatch h) (fun _ _ h => nomatch h)
      typed.code,
    queueOk_cons ⟨resume, trivial, trivial, (fun _ h => nomatch h), trivial, fun key hk => ?_,
      fun fiber tok r hr hk => ?_, (fun _ _ _ h => nomatch h), (fun _ _ h => nomatch h),
      (fun _ _ _ h => nomatch h), (fun _ _ _ _ _ h => nomatch h), (fun _ _ _ h => nomatch h)⟩
      typed.queue⟩
  · rw [List.mem_singleton.mp hk]
    exact below
  · obtain ⟨rfl, rfl⟩ := Prod.mk.inj (List.mem_singleton.mp hk)
    rw [free] at hr
    cases hr

/-- Machines with the same fibers, races, store, counters and halt marker satisfy the same `I`:
`arm`, `emit` and `disarm` change none of them. -/
theorem configTyped_congr {root : ProgramSource} {rootTy : EffTy} {w : World} {m m' : RState}
    {q : List RCmd} (fibers : m'.fibers = m.fibers) (races : m'.races = m.races)
    (state : m'.state = m.state) (nextId : m'.nextId = m.nextId)
    (nextToken : m'.nextToken = m.nextToken) (nextRace : m'.nextRace = m.nextRace)
    (stuck : m'.stuck = m.stuck) (typed : ConfigTyped root rootTy w m q) :
    ConfigTyped root rootTy w m' q := by
  have lookup : ∀ id, m'.fiber? id = m.fiber? id := fun id => by
    unfold RunMachine.fiber?
    rw [fibers]
  have raceLookup : ∀ r, m'.race? r = m.race? r := fun r => by
    unfold RunMachine.race?
    rw [races]
  have view : ObsView m m' :=
    ObsView.ofLookup lookup raceLookup (fun sc h => by rw [state]; exact h)
  have ctl : ∀ id, (m'.fiber? id).map ctlView = (m.fiber? id).map ctlView := fun id => by
    rw [lookup]
  refine ⟨machineTyped_congr fibers races state nextId nextToken nextRace stuck typed.machine,
    readCode_races fibers (racesKept_of_eq raceLookup) typed.code,
    queueOk_transport typed.queue view (Nat.le_of_eq nextId.symm)
      (fun c _ h => commandAuthority_view ctl view.races c h)
      (fun c _ h => commandDelivery_view ctl (racesKept_of_eq view.races) c h)
      (fun fiber token r hr => by rw [requestOfR_congr (lookup fiber)] at hr; exact hr)
      (Nat.le_of_eq nextToken.symm)⟩

/-- The authority view after an edit that keeps the edited fiber's id, flags and current code. -/
theorem authView_rupdate {m : RState} {f g : RFiber} (hf : m.fiber? f.id = some f)
    (hid : g.id = f.id) (running : g.running = f.running) (parked : g.parked = f.parked)
    (exit : g.exit = f.exit) (current : g.frame.current = f.frame.current) :
    ∀ id, ((m.update g).fiber? id).map authView = (m.fiber? id).map authView := by
  intro id
  rw [rfiber?_update]
  cases h : m.fiber? id with
  | none => rfl
  | some x =>
    by_cases hx : x.id = g.id
    · rw [Option.map_some, if_pos hx]
      have same : x = f := rfiber?_same hf h (hx.trans hid)
      subst same
      simp only [authView, hid, running, parked, exit, current, Option.map_some]
    · rw [Option.map_some, if_neg hx]

/-- The delivery view after an edit that keeps the edited fiber's id and saved stack. -/
theorem stackView_rupdate {m : RState} {f g : RFiber} (hf : m.fiber? f.id = some f)
    (hid : g.id = f.id) (stack : g.frame.stack = f.frame.stack)
    (prov : InterruptProvenance f.frame → InterruptProvenance g.frame) :
    StackView m (m.update g) := by
  intro id f' hf'
  rw [rfiber?_update] at hf'
  cases h : m.fiber? id with
  | none =>
    rw [h] at hf'
    cases hf'
  | some x =>
    rw [h, Option.map_some] at hf'
    cases hf'
    by_cases hx : x.id = g.id
    · rw [if_pos hx]
      have same : x = f := rfiber?_same hf h (hx.trans hid)
      subst same
      exact ⟨x, rfl, hid, stack, prov⟩
    · rw [if_neg hx]
      exact ⟨x, rfl, rfl, rfl, fun p => p⟩

/-- The trace is no clause's: an `emit` keeps `I`. -/
theorem configTyped_emit {root : ProgramSource} {rootTy : EffTy} {w : World} {m : RState}
    {q : List RCmd} (typed : ConfigTyped root rootTy w m q)
    (events : List (RunEvent EffName EffThunk Val Err Defect FiberId Ann Ctx RProgram Unit)) :
    ConfigTyped root rootTy w (m.emit events) q :=
  configTyped_congr (m := m) (m' := m.emit events) rfl rfl rfl rfl rfl rfl rfl typed

/-- **A fiber edit keeps `I`**, in its general form: the edited fiber keeps its id and saved
stack, finds no new pending park, keeps its provenance, carries only keys the machine holds or
fresh unrequested ones, has no external request it did not have, keeps every queued command's
authority, has its code typed if a queued `loop` or `deliver` reads it, and is typed on the edited
machine. -/
theorem configTyped_rupdate_code {root : ProgramSource} {rootTy : EffTy} {w : World} {m : RState}
    {q : List RCmd} {f g : RFiber} (typed : ConfigTyped root rootTy w m q)
    (hf : m.fiber? f.id = some f) (hid : g.id = f.id) (pending : PendingWeaker f.pending g.pending)
    (stack : g.frame.stack = f.frame.stack)
    (prov : InterruptProvenance f.frame → InterruptProvenance g.frame)
    (keys : ∀ k ∈ Guard.fiberKeys g, k ∈ Guard.internalKeys m ∨
      (k.2 < m.nextToken ∧ requestOfR m k.1 k.2 = none))
    (request : ∀ token r, requestOfR (m.update g) g.id token = some r →
      requestOfR m f.id token = some r)
    (auth : ∀ c ∈ q, CommandAuthorityR m c → CommandAuthorityR (m.update g) c)
    (readG : g.running = true → ReadsCode g.id q → raceRegistrationR g.frame.current = none →
      ∀ ty, w.Γ g.id = some ty → CodeOk root w (m.update g) g.id ty g.frame)
    (fresh : FiberTyped root w (m.update g) g) : ConfigTyped root rootTy w (m.update g) q := by
  have view : ObsView m (m.update g) := obsView_rupdate hf hid pending
  have sview := stackView_rupdate hf hid stack prov
  obtain ⟨machine, code, queue⟩ := typed
  refine ⟨machineTyped_of (machineWide_rupdate machine.wide hid keys request) (fun x hx => ?_),
    ?_, queueOk_transport queue view (Nat.le_refl _) auth
      (fun c _ h => commandDelivery_stack sview (racesKept_of_eq view.races) c h) ?_ (Nat.le_refl _)⟩
  · rcases mem_rupdate hx with rfl | ⟨hold, _⟩
    · exact fresh
    · exact fiberTyped_transport (machine.fiber hold) view (Nat.le_refl _) (Nat.le_refl _)
  · intro x hx hrun reads marker ty declared
    rcases mem_rupdate hx with rfl | ⟨hold, _⟩
    · exact readG hrun reads marker ty declared
    · exact codeOk_races (racesKept_of_eq view.races) (code x hold hrun reads marker ty declared)
  · intro fiber token r hr
    by_cases same : fiber = g.id
    · subst same
      rw [hid]
      exact request token r hr
    · rw [requestOfR_congr (rfiber?_update_other same)] at hr
      exact hr

/-- `configTyped_rupdate_code` for an edited fiber whose read code is `SavedOk` (no injected
registration callback in its stack, decisions row 188 (b)). -/
theorem configTyped_rupdate_gen {root : ProgramSource} {rootTy : EffTy} {w : World} {m : RState}
    {q : List RCmd} {f g : RFiber} (typed : ConfigTyped root rootTy w m q)
    (hf : m.fiber? f.id = some f) (hid : g.id = f.id) (pending : PendingWeaker f.pending g.pending)
    (stack : g.frame.stack = f.frame.stack)
    (prov : InterruptProvenance f.frame → InterruptProvenance g.frame)
    (keys : ∀ k ∈ Guard.fiberKeys g, k ∈ Guard.internalKeys m ∨
      (k.2 < m.nextToken ∧ requestOfR m k.1 k.2 = none))
    (request : ∀ token r, requestOfR (m.update g) g.id token = some r →
      requestOfR m f.id token = some r)
    (auth : ∀ c ∈ q, CommandAuthorityR m c → CommandAuthorityR (m.update g) c)
    (readG : g.running = true → ReadsCode g.id q → raceRegistrationR g.frame.current = none →
      ∀ ty, w.Γ g.id = some ty → SavedOk (TypedProg root) ExitOk (frameProtocols root) w ty g.frame)
    (fresh : FiberTyped root w (m.update g) g) : ConfigTyped root rootTy w (m.update g) q :=
  configTyped_rupdate_code typed hf hid pending stack prov keys request auth
    (fun hrun reads marker ty declared => codeOk_of_saved (readG hrun reads marker ty declared)) fresh

/-- **A fiber edit that keeps the fiber's flags keeps `I`**: the edited fiber keeps its id, flags,
current code and saved stack, finds no new pending park, keeps its provenance, carries only keys
the machine holds or fresh unrequested ones, and is typed on the edited machine. -/
theorem configTyped_rupdate {root : ProgramSource} {rootTy : EffTy} {w : World} {m : RState}
    {q : List RCmd} {f g : RFiber} (typed : ConfigTyped root rootTy w m q)
    (hf : m.fiber? f.id = some f) (hid : g.id = f.id) (pending : PendingWeaker f.pending g.pending)
    (running : g.running = f.running) (parked : g.parked = f.parked) (exit : g.exit = f.exit)
    (current : g.frame.current = f.frame.current) (stack : g.frame.stack = f.frame.stack)
    (prov : InterruptProvenance f.frame → InterruptProvenance g.frame)
    (keys : ∀ k ∈ Guard.fiberKeys g, k ∈ Guard.internalKeys m ∨
      (k.2 < m.nextToken ∧ requestOfR m k.1 k.2 = none))
    (fresh : FiberTyped root w (m.update g) g) : ConfigTyped root rootTy w (m.update g) q := by
  have hmem : f ∈ m.fibers := rfiber?_mem hf
  have look : (m.update g).fiber? g.id = some g := rfiber?_update_self hf hid
  have auth := authView_rupdate hf hid running parked exit current
  refine configTyped_rupdate_code typed hf hid pending stack prov keys ?_
    (fun c _ h => commandAuthority_auth auth (fun _ => rfl) c h) ?_ fresh
  · intro token r hr
    by_cases hp : g.parked = .withGuard token
    · rw [requestOfR_of_parked look hp] at hr
      rw [parked] at hp
      rw [requestOfR_of_parked hf hp, ← current]
      exact hr
    · rw [requestOfR_of_not_parked look hp] at hr
      cases hr
  · intro hrun reads marker ty declared
    rw [running] at hrun
    rw [hid] at reads declared
    rw [current] at marker
    obtain ⟨tin, typedCode, stackOk, provenance⟩ := typed.code f hmem hrun reads marker ty declared
    exact ⟨tin, by rw [current]; exact typedCode,
      by rw [stack, hid]; exact hostStack_races (racesKept_of_eq (m := m) fun _ => rfl) stackOk,
      prov provenance⟩

/-! ## A store edit outside the store rows

The store moves while the declarations stay: `drainDue` empties the due list, `link` adds a scope
finalizer, a scope-finalizer drop removes one, the clock moves its timers. The world moves with
the store (`{ w with state := s }`), later in the host order when the store grew and kept its
heap, its Deferred cells and its external spellings. -/

/-- **The host order along a store edit** that keeps the heap, every Deferred cell's completion
and the external spellings, and only grows (a cell's wake list may change). -/
theorem leHost_cells {w : World} {s : Stores} (le : w.state.le s) (refs : s.refs = w.state.refs)
    (cells : ∀ key c', s.deferreds.cellAt key = some c' →
      ∃ c, w.state.deferreds.cellAt key = some c ∧ c'.completion = c.completion)
    (externals : s.externals = w.state.externals) :
    w.leHost { w with state := s } := by
  have ext : Extends w.state.externals.allocated s.externals.allocated := by
    rw [externals]
    exact fun _ _ h => h
  refine ⟨⟨⟨fun _ h => h, le⟩, fun _ _ h => h, fun _ _ h => h, fun _ _ h => h, ⟨?_, ?_⟩,
    fun _ _ _ h => h, rfl⟩, ext⟩
  · intro key ty h
    refine ⟨h.1, fun value hv => ?_⟩
    have hv' : refPeek w.state.refs key = some value := by
      change refPeek s.refs key = some value at hv
      rw [refs] at hv
      exact hv
    exact value_transport w { w with state := s } ty value ext (h.2 value hv')
  · intro key types h
    refine ⟨h.1, fun cell hc completion hcomp => ?_⟩
    obtain ⟨c, hc0, same⟩ := cells key cell hc
    rw [same] at hcomp
    exact completion_transport w { w with state := s } types (fun _ _ h => h) ext completion
      (h.2 c hc0 completion hcomp)

/-- Cells unchanged keep every completion. -/
theorem cells_kept {s t : Stores} (cells : s.deferreds.cells = t.deferreds.cells) :
    ∀ key c', s.deferreds.cellAt key = some c' →
      ∃ c, t.deferreds.cellAt key = some c ∧ c'.completion = c.completion ∧
        Guard.wakeKeys c'.wake ⊆ Guard.wakeKeys c.wake := by
  intro key c' h
  refine ⟨c', ?_, rfl, List.Subset.refl _⟩
  unfold DeferredStore.cellAt at h ⊢
  rw [← cells]
  exact h

theorem leHost_restate {w : World} {s : Stores} (le : w.state.le s) (refs : s.refs = w.state.refs)
    (cells : s.deferreds.cells = w.state.deferreds.cells) (externals : s.externals = w.state.externals) :
    w.leHost { w with state := s } :=
  leHost_cells le refs (fun key c' h =>
    let ⟨c, hc, same, _⟩ := cells_kept cells key c' h
    ⟨c, hc, same⟩) externals

/-- **The waiter → due transfer** (`note.md` §3): a waiter declared at a type that accepts its
cell's columns accepts any completion the cell holds, the cell's completion moving along both
columns (`fitsExit_sub`; a delayed read along the checker's order, `Ty.sub_le_subN`). -/
theorem completionStrong_await {w : World} {a e : Ty} {ty : EffTy}
    {c : Completion Val Err Defect FiberId Ann} (demand : AwaitDemand a e ty)
    (h : CompletionStrong w ⟨a, e, Env.Requirement.empty⟩ c) : CompletionStrong w ty c := by
  cases c with
  | ofExit ex => exact ⟨fitsExit_sub demand.1 demand.2 h.1, h.2⟩
  | ofRefGet cell =>
    obtain ⟨t, declared, sub⟩ := h
    exact ⟨t, declared, Ty.subN_trans sub (Ty.sub_le_subN demand.1)⟩

theorem completionStrong_mono {w w' : World} (ord : w.leHost w') {ty : EffTy}
    {c : Completion Val Err Defect FiberId Ann} (h : CompletionStrong w ty c) :
    CompletionStrong w' ty c := by
  cases c with
  | ofExit ex => exact strongExit_mono _ _ _ _ ord h
  | ofRefGet cell =>
    obtain ⟨t, ht, sub⟩ := h
    exact ⟨t, ord.1.2.2.2.1 _ _ ht, sub⟩

theorem captureTyped_mono {root : ProgramSource} {w w' : World} (ord : w.leHost w') {c : Capture}
    (h : CaptureTyped root w c) : CaptureTyped root w' c := by
  obtain ⟨acquire, release, env, t, a, hnode, hcheck, hacq, henv, hsvc⟩ := h
  exact ⟨acquire, release, env, t, a, hnode, hcheck, hacq, envTyped_mono ord henv,
    servicesFit_mono ord hsvc⟩

theorem finNameOk_world {root : ProgramSource} {w w' : World} (ord : w.leHost w') {e : Expect}
    {fin : FinName} (h : FinNameOk (preds root) w e fin) : FinNameOk (preds root) w' e fin := by
  cases fin with
  | foreign c => exact ⟨captureTyped_mono ord h.c0⟩
  | interruptFiber _ _ => trivial
  | closeChildScope _ => trivial
  | detachFromParent _ _ => trivial
  | release _ _ => trivial
  | awaitNewChildren _ => trivial
  | parkThen _ => trivial
  | closeChildOnFailure _ => trivial
  | memoEntry _ _ => trivial
  | memoDone _ _ => trivial

theorem scopeStateOk_world {root : ProgramSource} {w w' : World} (ord : w.leHost w') {e : Expect}
    {st : ScopeState Nat FinName Val Err Defect FiberId Ann}
    (h : ScopeStateOk (preds root) w e st) : ScopeStateOk (preds root) w' e st := by
  cases st with
  | empty => trivial
  | openEmpty => trivial
  | openInline key fin => exact ⟨finalizerTyped_mono root w w' fin ord h.1, finNameOk_world ord h.2⟩
  | openMap entries =>
    exact ⟨fun v0 hv => finalizerTyped_mono root w w' v0.2 ord (h.1 v0 hv),
      fun v0 hv => finNameOk_world ord (h.2 v0 hv)⟩
  | closed exit => exact fits_mono ord h

/-- The store clauses move to a later world with the same declaration tables. -/
theorem storesOk_world {root : ProgramSource} {w w' : World} (ord : w.leHost w')
    (hΘ : w'.Θ = w.Θ) (hΡ : w'.Ρ = w.Ρ) (hPi : w'.«Π» = w.«Π») {e : Expect} {s : Stores}
    (h : StoresOk (preds root) w e s) : StoresOk (preds root) w' e s := by
  obtain ⟨c0, c1, ⟨c2⟩, ⟨c3⟩, c4, c5⟩ := h
  refine ⟨⟨fun o ho ty declared => ?_, MemoTableTyped.mono ord (PromiseTableOk.memo c0)⟩,
    fun i v hv ty declared => ?_,
    ⟨fun i cell hc a e' declared c hcomp => ?_⟩, ⟨fun entry he => ?_⟩, fun mm hm => ?_, c5⟩
  · rw [hΘ] at declared
    exact completionStrong_mono ord (PromiseTableOk.due c0 o ho ty declared)
  · rw [hΡ] at declared
    exact fits_mono ord (c1 i v hv ty declared)
  · rw [hPi] at declared
    exact completionStrong_mono ord (c2 i cell hc a e' declared c hcomp)
  · exact ⟨⟨scopeStateOk_world ord (c3 entry he).c0.c0⟩⟩
  · exact ⟨fun v0 hv => ⟨finNameOk_world ord ((c4 mm hm).c0 v0 hv).c0⟩⟩

/-- A store with the same heap, scopes, memo world, timers and Deferred cells as a well-formed
one it grew from is well-formed. -/
theorem wf_cells {t s : Stores} (wf : t.WF) (le : t.le s) (refs : s.refs = t.refs)
    (scopes : s.scopes = t.scopes) (memo : s.memo = t.memo) (timers : s.timers = t.timers)
    (cellCount : s.deferreds.cells.length = t.deferreds.cells.length) : s.WF := by
  obtain ⟨hrefs, hscopes, hmemo, htimers⟩ := wf
  refine ⟨fun v hv => ?_, fun e he => ?_, fun mm hm entry he => ?_, ?_⟩
  · rw [refs] at hv
    exact Val.validIn_mono le v (hrefs v hv)
  · rw [scopes] at he
    have old := hscopes e he
    cases hc : e.scope.closingExit? with
    | none => rfl
    | some ex =>
      rw [hc] at old
      exact Val.validIn_mono le _ old
  · rw [memo] at hm
    have old := hmemo mm hm entry he
    rw [cellCount, scopes]
    exact old
  · rw [timers]
    exact htimers

theorem wf_restate {t s : Stores} (wf : t.WF) (le : t.le s) (refs : s.refs = t.refs)
    (scopes : s.scopes = t.scopes) (memo : s.memo = t.memo) (timers : s.timers = t.timers)
    (cells : s.deferreds.cells = t.deferreds.cells) : s.WF :=
  wf_cells wf le refs scopes memo timers (by rw [cells])

/-- **How a store edit moves the views `J` reads** (`docs/research/2026-10-02-proof-structure/
note.md` §4): it grows, keeps the heap and the external spellings, keeps the cell count and every
cell's completion, and only shrinks each cell's and the timers' wake keys (the waiter and timer
columns, decisions row 134 (a), (b)). The new store's generated typing, its well-formedness, the
internal keys and the owners of scheduled due work are separate premises of `configTyped_frame`:
an edit of the due list, the scopes or the memo world states them. -/
structure StoreFrame (s s' : Stores) : Prop where
  le : s.le s'
  refs : s'.refs = s.refs
  cellCount : s'.deferreds.cells.length = s.deferreds.cells.length
  cells : ∀ key c', s'.deferreds.cellAt key = some c' →
    ∃ c, s.deferreds.cellAt key = some c ∧ c'.completion = c.completion ∧
      Guard.wakeKeys c'.wake ⊆ Guard.wakeKeys c.wake
  externals : s'.externals = s.externals
  timers : Guard.wakeKeys s'.timers.wake ⊆ Guard.wakeKeys s.timers.wake

/-- A store whose Deferred cells are unchanged moves no cell view. -/
theorem StoreFrame.ofCells {s s' : Stores} (le : s.le s') (refs : s'.refs = s.refs)
    (cells : s'.deferreds.cells = s.deferreds.cells) (externals : s'.externals = s.externals)
    (timers : Guard.wakeKeys s'.timers.wake ⊆ Guard.wakeKeys s.timers.wake) : StoreFrame s s' :=
  ⟨le, refs, by rw [cells], cells_kept cells, externals, timers⟩

/-- The world over a store frame is later in the host order. -/
theorem leHost_frame {w : World} {m : RState} (state : w.state = m.state) {s : Stores}
    (frame : StoreFrame m.state s) : w.leHost { w with state := s } :=
  leHost_cells (by rw [state]; exact frame.le) (by rw [frame.refs, state])
    (fun key c' h => by
      obtain ⟨c, hc, same, _⟩ := frame.cells key c' h
      exact ⟨c, by rw [state]; exact hc, same⟩)
    (by rw [frame.externals, state])

/-- `J`'s machine-wide clauses over a store frame. -/
theorem machineWide_frame {root : ProgramSource} {rootTy : EffTy} {w : World} {m : RState}
    (wide : MachineWide root rootTy w m) {s : Stores} (frame : StoreFrame m.state s) (wf : s.WF)
    (stores : StoresOk (preds root) { w with state := s } Expect.root s)
    (keys : Guard.internalKeys { m with state := s } ⊆ Guard.internalKeys m)
    (due : ∀ o ∈ s.deferreds.due, ∀ owner priority, o.mode = .scheduled owner priority →
      (m.fiber? owner).isSome = true) :
    MachineWide root rootTy { w with state := s } { m with state := s } := by
  have kept : ∀ key c', s.deferreds.cellAt key = some c' →
      ∃ c, w.state.deferreds.cellAt key = some c ∧ c'.completion = c.completion := by
    intro key c' h
    obtain ⟨c, hc, same, _⟩ := frame.cells key c' h
    exact ⟨c, by rw [wide.state]; exact hc, same⟩
  have ord : w.leHost { w with state := s } := leHost_frame wide.state frame
  have ext : Extends w.state.externals.allocated s.externals.allocated := by
    rw [frame.externals, wide.state]
    exact fun _ _ h => h
  refine ⟨wide.ids, wide.fibers, fun key => ?_, fun key => ?_, wide.tokenBound, wide.tokenTargets,
    rfl, wf, ⟨fun i v hv ty hty => ?_, fun i cell hc types hty c hcomp => ?_⟩, wide.rootDeclared,
    fun r hr => ?_, stores, wide.fiberIds, wide.raceIds, wide.racesBelow, wide.raceHosts,
    fun key hk => wide.keysBelow key (keys hk), wide.requestsBelow,
    fun fiber token r hr hk => wide.requestsOwned fiber token r hr (keys hk), wide.services,
    ⟨wide.live.running, due⟩, WakeTyped.of_subset frame.timers wide.timers,
    fun key cell hc a e declared => ?_, wide.liveBelow, wide.sourceWF⟩
  · show (w.Ρ key).isSome = true ↔ key.index < s.refs.length
    rw [frame.refs]
    exact wide.heap key
  · show (w.«Π» key).isSome = true ↔ key.index < s.deferreds.cells.length
    rw [frame.cellCount]
    exact wide.promises key
  · have hv' : w.state.refs[i]? = some v := by
      change s.refs[i]? = some v at hv
      rw [wide.state, ← frame.refs]
      exact hv
    exact value_transport w { w with state := s } ty v ext (wide.cells.1 i v hv' ty hty)
  · obtain ⟨c0, hc0, same⟩ := kept ⟨i⟩ cell hc
    rw [same] at hcomp
    exact completion_transport w { w with state := s } types (fun _ _ h => h) ext c
      (wide.cells.2 i c0 hc0 types hty c hcomp)
  · obtain ⟨resultTy, payload⟩ := wide.races r hr
    exact ⟨resultTy, racePayload_world ord rfl rfl payload⟩
  · obtain ⟨c0, hc0, _, sub⟩ := frame.cells key cell hc
    exact WakeTyped.of_subset sub (wide.waiters key c0 hc0 a e declared)

/-- **A store edit keeps `I`** at the world over the edited store (`note.md` §4): the views
`J` reads move as the frame says, and the new store states its own clauses (well-formedness, the
generated store typing, no new internal key, owners for its scheduled due entries). -/
theorem configTyped_frame {root : ProgramSource} {rootTy : EffTy} {w : World} {m : RState}
    {q : List RCmd} (typed : ConfigTyped root rootTy w m q) {s : Stores}
    (frame : StoreFrame m.state s) (wf : s.WF)
    (stores : StoresOk (preds root) { w with state := s } Expect.root s)
    (keys : Guard.internalKeys { m with state := s } ⊆ Guard.internalKeys m)
    (due : ∀ o ∈ s.deferreds.due, ∀ owner priority, o.mode = .scheduled owner priority →
      (m.fiber? owner).isSome = true) :
    w.leHost { w with state := s } ∧
      ConfigTyped root rootTy { w with state := s } { m with state := s } q := by
  obtain ⟨machine, code, queue⟩ := typed
  have wide := machine.wide
  have ord : w.leHost { w with state := s } := leHost_frame wide.state frame
  have view : ObsView m { m with state := s } :=
    ObsView.ofLookup (fun _ => rfl) (fun _ => rfl) (fun sc h => frame.le.2.2.1 sc h)
  have ctl : ∀ id, (({ m with state := s } : RState).fiber? id).map ctlView =
      (m.fiber? id).map ctlView := fun _ => rfl
  refine ⟨ord, machineTyped_of (machineWide_frame wide frame wf stores keys due)
    (fun x hx => fiberTyped_transport (fiberTyped_world ord rfl rfl (machine.fiber hx)) view
      (Nat.le_refl _) (Nat.le_refl _)),
    readCode_world ord rfl (readCode_races (m := m) rfl (racesKept_of_eq fun _ => rfl) code),
    queueOk_transport (queueOk_world ord rfl rfl queue) view (Nat.le_refl _)
      (fun c _ h => commandAuthority_view ctl view.races c h)
      (fun c _ h => commandDelivery_view ctl (racesKept_of_eq view.races) c h) (fun _ _ _ hr => hr) (Nat.le_refl _)⟩

/-- A store edit that keeps every Deferred cell (`configTyped_frame` at `StoreFrame.ofCells`). -/
theorem configTyped_restate {root : ProgramSource} {rootTy : EffTy} {w : World} {m : RState}
    {q : List RCmd} (typed : ConfigTyped root rootTy w m q) {s : Stores} (le : m.state.le s)
    (refs : s.refs = m.state.refs) (cells : s.deferreds.cells = m.state.deferreds.cells)
    (externals : s.externals = m.state.externals) (wf : s.WF)
    (stores : StoresOk (preds root) { w with state := s } Expect.root s)
    (keys : Guard.internalKeys { m with state := s } ⊆ Guard.internalKeys m)
    (due : ∀ o ∈ s.deferreds.due, ∀ owner priority, o.mode = .scheduled owner priority →
      (m.fiber? owner).isSome = true)
    (timerKeys : Guard.wakeKeys s.timers.wake ⊆ Guard.wakeKeys m.state.timers.wake) :
    w.leHost { w with state := s } ∧
      ConfigTyped root rootTy { w with state := s } { m with state := s } q :=
  configTyped_frame typed (StoreFrame.ofCells le refs cells externals timerKeys) wf stores keys due


/-! ## `wake` (`E4-TYPED-CE-026` repaired)

A scheduled wake runs one Deferred cell's batch (`Stores.wakeList`, `DeferredStore.wakeBatch`,
`Machine/Stores.lean:1163-1175`): a completed cell owes each batched waiter its completion now, an
uncompleted one returns the batch to its pending list. The edit is a store frame (completions kept,
keys shrink: `Guard.wakeBatch_cellAt`), and each new due entry is a transfer from the cell's waiter
column (`docs/research/2026-10-02-proof-structure/note.md` §3, `completionStrong_await`). -/

/-- **`wake` keeps `I`** at the world over the woken store. -/
theorem wake_preserves (root : ProgramSource) (rootTy : EffTy) (list : WakeKey) (phase : WakePhase) :
    StepPreserves root rootTy (.wake list phase) := by
  intro w m rest _ typed
  have tail := configTyped_tail typed
  have wide := typed.machine.wide
  show ∃ w', w.leHost w' ∧
    ConfigTyped root rootTy w' { m with state := Stores.wakeList list phase m.state } rest
  unfold Stores.wakeList
  split
  · let cell : DeferredKey := ⟨list.index⟩
    let s : Stores := { m.state with deferreds := m.state.deferreds.wakeBatch cell }
    have count : s.deferreds.cells.length = m.state.deferreds.cells.length :=
      Guard.wakeBatch_cells_length _ _
    have frame : StoreFrame m.state s :=
      ⟨⟨Nat.le_refl _, Nat.le_of_eq count.symm, fun _ h => h, Nat.le_refl _, fun _ h => h,
        Nat.le_refl _⟩, rfl, count, fun _ _ h => Guard.wakeBatch_cellAt h, rfl,
        List.Subset.refl _⟩
    have ord : w.leHost { w with state := s } := leHost_frame wide.state frame
    -- a new due entry: one of the cell's batched waiters, typed by the waiter column
    have transfer : ∀ o ∈ s.deferreds.due, o ∉ m.state.deferreds.due → ∀ ty,
        w.Θ o.waiter o.token = some ty → CompletionStrong w ty o.code := by
      intro o ho fresh ty declared
      rcases Guard.wakeBatch_due ho with old | ⟨c, effect, hcell, hcomp, key, code, _⟩
      · exact absurd old fresh
      · have hcell' : m.state.deferreds.cells[cell.index]? = some c := hcell
        obtain ⟨live, _⟩ := List.getElem?_eq_some_iff.mp hcell'
        obtain ⟨⟨a, e⟩, declaredCell⟩ := Option.isSome_iff_exists.mp ((wide.promises cell).mpr live)
        obtain ⟨ty0, declared0, demand⟩ := wide.waiters cell c hcell a e declaredCell _ key
        have same : ty0 = ty := Option.some.inj (declared0.symm.trans declared)
        subst same
        rw [code]
        exact completionStrong_await demand
          (wide.stores.c2.c0 cell.index c hcell' a e declaredCell effect hcomp)
    have stores : StoresOk (preds root) { w with state := s } Expect.root s := by
      obtain ⟨c0, c1, ⟨c2⟩, c3, c4, c5⟩ := storesOk_world ord rfl rfl rfl wide.stores
      refine ⟨⟨fun o ho ty declared => ?_, PromiseTableOk.memo c0⟩, c1,
        ⟨fun i c' hc a e declaredCell x hx => ?_⟩, c3, c4, c5⟩
      · by_cases old : o ∈ m.state.deferreds.due
        · exact PromiseTableOk.due c0 o old ty declared
        · exact completionStrong_mono ord (transfer o ho old ty declared)
      · obtain ⟨c0', hc0, same, _⟩ := Guard.wakeBatch_cellAt (key := ⟨i⟩) hc
        rw [same] at hx
        exact c2 i c0' hc0 a e declaredCell x hx
    have owners : ∀ o ∈ s.deferreds.due, ∀ owner priority, o.mode = .scheduled owner priority →
        (m.fiber? owner).isSome = true := by
      intro o ho owner priority mode
      rcases Guard.wakeBatch_due ho with old | ⟨_, _, _, _, _, _, now⟩
      · exact wide.live.dueOwners o old owner priority mode
      · rw [now] at mode
        cases mode
    obtain ⟨ord', config⟩ := configTyped_frame tail frame
      (wf_cells wide.wf frame.le rfl rfl rfl rfl count) stores
      (Guard.internalKeys_state_subset m s (Guard.storeKeys_mono (List.Subset.refl _)
        (Guard.deferredKeys_wakeBatch_subset _ _)))
      owners
    exact ⟨_, ord', config⟩
  · exact ⟨w, leHost_refl w, tail⟩

/-! ## `drainDue` (one halting arm: `postTask` on an unknown owner, `Machine/Fibers.lean:709-716`,
excluded by `MachineLive.dueOwners`)

The due list leaves the store; a `now` entry becomes a `resume` command and a `scheduled` entry a
resume task on its owner's dispatcher (`drainOwed`, `:1831-1840`). Each is typed by the store's
generated due column (`preds`' `PromiseTable`) at its token's declaration. -/

abbrev RBucket := Bucket EffName EffThunk Val Err Defect FiberId Ann RProgram

/-- A task of a bucket list after an insertion is the inserted task or an old one. -/
theorem mem_insert_tasks {priority : Nat} {task t : RTask} :
    ∀ {buckets : List RBucket} {b : RBucket}, b ∈ Dispatcher.insert priority task buckets →
      t ∈ b.tasks → t = task ∨ ∃ b' ∈ buckets, t ∈ b'.tasks
  | [], b, hb, ht => by
    rw [Dispatcher.insert, List.mem_singleton] at hb
    subst hb
    exact Or.inl (List.mem_singleton.mp ht)
  | bucket :: rest, b, hb, ht => by
    rw [Dispatcher.insert] at hb
    split at hb
    · rcases List.mem_cons.mp hb with rfl | hb
      · rcases List.mem_append.mp ht with ht | ht
        · exact Or.inr ⟨bucket, List.mem_cons_self, ht⟩
        · exact Or.inl (List.mem_singleton.mp ht)
      · exact Or.inr ⟨b, List.mem_cons_of_mem _ hb, ht⟩
    · split at hb
      · rcases List.mem_cons.mp hb with rfl | hb
        · exact Or.inl (List.mem_singleton.mp ht)
        · exact Or.inr ⟨b, hb, ht⟩
      · rcases List.mem_cons.mp hb with rfl | hb
        · exact Or.inr ⟨b, List.mem_cons_self, ht⟩
        · rcases mem_insert_tasks hb ht with new | ⟨b', hb', ht'⟩
          · exact Or.inl new
          · exact Or.inr ⟨b', List.mem_cons_of_mem _ hb', ht'⟩

/-- The keys of a bucket list after an insertion are the inserted task's and the old ones. -/
theorem bucketKeys_insert {priority : Nat} {task : RTask} {buckets : List RBucket} :
    Guard.bucketKeys (Dispatcher.insert priority task buckets) ⊆
      Guard.bucketKeys buckets ++ Guard.taskKeys task := by
  intro key hk
  unfold Guard.bucketKeys at hk ⊢
  obtain ⟨b, hb, hkb⟩ := List.mem_flatMap.mp hk
  obtain ⟨t, ht, hkt⟩ := List.mem_flatMap.mp hkb
  rcases mem_insert_tasks hb ht with rfl | ⟨b', hb', ht'⟩
  · exact List.mem_append_right _ hkt
  · exact List.mem_append_left _ (List.mem_flatMap.mpr ⟨b', hb', List.mem_flatMap.mpr ⟨t, ht', hkt⟩⟩)

/-- What an owed resume needs to be delivered or posted. -/
structure OwedOk (root : ProgramSource) (w : World) (m : RState) (o : Owed RProgram) : Prop where
  typed : Contracts.ResumeOk (TypedProg root) w o.waiter o.token o.code
  below : o.token < m.nextToken
  free : requestOfR m o.waiter o.token = none
  owner : ∀ owner priority, o.mode = .scheduled owner priority → (m.fiber? owner).isSome = true

/-- Posting a typed resume task on an existing owner's dispatcher keeps `I`. -/
theorem configTyped_postTask {root : ProgramSource} {rootTy : EffTy} {w : World} {m : RState}
    {q : List RCmd} (typed : ConfigTyped root rootTy w m q) {owner : FiberId} {priority : Nat}
    {waiter : FiberId} {token : Nat} {code : RProgram}
    (resume : Contracts.ResumeOk (TypedProg root) w waiter token code)
    (below : token < m.nextToken) (free : requestOfR m waiter token = none)
    (exists_ : (m.fiber? owner).isSome = true) :
    ConfigTyped root rootTy w (m.postTask owner priority (.resume waiter token code)) q := by
  unfold RunMachine.postTask
  cases hfound : m.fiber? owner with
  | none =>
    rw [hfound] at exists_
    cases exists_
  | some o =>
    let g : RFiber :=
      { o with dispatcher := o.dispatcher.enqueue priority (.resume waiter token code) }
    show ConfigTyped root rootTy w (((m.update g).arm owner).emit
      [RunEvent.scheduledTask owner priority (.resume waiter token code)]) q
    have oid : o.id = owner := rfiber?_id hfound
    have hf : m.fiber? o.id = some o := by rw [oid]; exact hfound
    have hmem : o ∈ m.fibers := rfiber?_mem hf
    have view : ObsView m (m.update g) := obsView_rupdate hf rfl (PendingWeaker.refl _)
    have old := typed.machine.fiber hmem
    have fresh : FiberTyped root w (m.update g) g := by
      have moved := fiberTyped_transport old view (Nat.le_refl _) (Nat.le_refl _)
      refine ⟨⟨moved.ok.c0, moved.ok.c1, moved.ok.c2, moved.ok.c3, ⟨fun b hb => ⟨fun t ht => ?_⟩⟩,
        moved.ok.c5⟩, moved.delivery, moved.below, moved.pendingShape, moved.parkedIdle,
        moved.parkedBelow, moved.exited, moved.exitedStack, moved.deferredCause, moved.pendingOwner,
        moved.observers, moved.registration, moved.code, moved.tokens, moved.raceObservers,
        moved.targetsBelow, moved.observersBelow, moved.children⟩
      rcases mem_insert_tasks hb ht with rfl | ⟨b', hb', ht'⟩
      · exact resume
      · exact (old.ok.c4.c0 b' hb').c0 t ht'
    have keys : ∀ k ∈ Guard.fiberKeys g, k ∈ Guard.internalKeys m ∨
        (k.2 < m.nextToken ∧ requestOfR m k.1 k.2 = none) := by
      intro k hk
      unfold Guard.fiberKeys at hk
      rcases List.mem_append.mp hk with hk | hk
      · exact Or.inl (fiberKeys_internal hmem (List.mem_append_left _ hk))
      · rcases List.mem_append.mp (bucketKeys_insert hk) with hk | hk
        · exact Or.inl (fiberKeys_internal hmem (List.mem_append_right _ hk))
        · rw [List.mem_singleton.mp hk]
          exact Or.inr ⟨below, free⟩
    have edited := configTyped_rupdate (g := g) typed hf rfl (PendingWeaker.refl _) rfl rfl rfl rfl rfl
      (fun p => p) keys fresh
    exact configTyped_congr rfl rfl rfl rfl rfl rfl rfl
      (configTyped_congr (m := m.update g) rfl rfl rfl rfl rfl rfl rfl edited)

/-- `postTask` keeps the token supply and every external request. -/
theorem postTask_request (m : RState) (owner : FiberId) (priority : Nat) (task : RTask)
    (fiber : FiberId) (token : Nat) :
    requestOfR (m.postTask owner priority task) fiber token = requestOfR m fiber token ∧
      (m.postTask owner priority task).nextToken = m.nextToken := by
  unfold RunMachine.postTask
  cases hfound : m.fiber? owner with
  | none => exact ⟨rfl, rfl⟩
  | some o =>
    have hf : m.fiber? o.id = some o := by rw [rfiber?_id hfound]; exact hfound
    refine ⟨?_, rfl⟩
    show requestOfR (m.update { o with dispatcher := o.dispatcher.enqueue priority task }) fiber token = _
    by_cases same : fiber = o.id
    · subst same
      have look := rfiber?_update_self hf (g := { o with dispatcher := o.dispatcher.enqueue priority task }) rfl
      by_cases hp : o.parked = .withGuard token
      · rw [requestOfR_of_parked look hp, requestOfR_of_parked hf hp]
      · rw [requestOfR_of_not_parked look hp, requestOfR_of_not_parked hf hp]
    · exact requestOfR_congr
        (rfiber?_update_other (g := { o with dispatcher := o.dispatcher.enqueue priority task }) same)
        token

/-- `postTask` keeps every fiber's existence. -/
theorem postTask_isSome (m : RState) (owner : FiberId) (priority : Nat) (task : RTask)
    (id : FiberId) : ((m.postTask owner priority task).fiber? id).isSome = (m.fiber? id).isSome := by
  unfold RunMachine.postTask
  cases hfound : m.fiber? owner with
  | none => rfl
  | some o =>
    show ((m.update { o with dispatcher := o.dispatcher.enqueue priority task }).fiber? id).isSome = _
    rw [rfiber?_update, Option.isSome_map]

theorem owedOk_postTask {root : ProgramSource} {w : World} {m : RState} {owner : FiberId}
    {priority : Nat} {task : RTask} {o : Owed RProgram} (h : OwedOk root w m o) :
    OwedOk root w (m.postTask owner priority task) o := by
  refine ⟨h.typed, ?_, ?_, fun owner' priority' mode => ?_⟩
  · rw [(postTask_request m owner priority task o.waiter o.token).2]
    exact h.below
  · rw [(postTask_request m owner priority task o.waiter o.token).1]
    exact h.free
  · rw [postTask_isSome]
    exact h.owner owner' priority' mode

/-- `drainOwed` keeps the token supply and every external request. -/
theorem drainOwed_request : ∀ (ds : List (Owed RProgram)) (m : RState) (fiber : FiberId) (token : Nat),
    requestOfR (drainOwed m ds).1 fiber token = requestOfR m fiber token ∧
      (drainOwed m ds).1.nextToken = m.nextToken
  | [], _, _, _ => ⟨rfl, rfl⟩
  | d :: rest, m, fiber, token => by
    cases hmode : d.mode with
    | now =>
      simp only [drainOwed, hmode]
      exact drainOwed_request rest m fiber token
    | scheduled owner priority =>
      simp only [drainOwed, hmode]
      obtain ⟨r1, t1⟩ := drainOwed_request rest
        (m.postTask owner priority (.resume d.waiter d.token d.code)) fiber token
      obtain ⟨r2, t2⟩ := postTask_request m owner priority (.resume d.waiter d.token d.code) fiber token
      exact ⟨r1.trans r2, t1.trans t2⟩

/-- **The owed resumes keep `I`** (`drainOwed`): each `now` entry is a typed resume command at the
head of the residue, each `scheduled` one a typed task on its existing owner's dispatcher. -/
theorem configTyped_drainOwed {root : ProgramSource} {rootTy : EffTy} {w : World} :
    ∀ (ds : List (Owed RProgram)) (m : RState) (q : List RCmd),
      ConfigTyped root rootTy w m q → (∀ o ∈ ds, OwedOk root w m o) →
        ConfigTyped root rootTy w (drainOwed m ds).1 ((drainOwed m ds).2 ++ q)
  | [], _, _, typed, _ => typed
  | d :: rest, m, q, typed, owed => by
    have here := owed d List.mem_cons_self
    have later : ∀ o ∈ rest, OwedOk root w m o := fun o ho => owed o (List.mem_cons_of_mem _ ho)
    cases hmode : d.mode with
    | now =>
      simp only [drainOwed, hmode]
      have ih := configTyped_drainOwed rest m q typed later
      obtain ⟨sameRequest, sameToken⟩ := drainOwed_request rest m d.waiter d.token
      rw [List.cons_append]
      exact configTyped_cons_resume ih here.typed (by rw [sameToken]; exact here.below)
        (by rw [sameRequest]; exact here.free)
    | scheduled owner priority =>
      simp only [drainOwed, hmode]
      exact configTyped_drainOwed rest _ q
        (configTyped_postTask typed here.typed here.below here.free (here.owner owner priority hmode))
        (fun o ho => owedOk_postTask (later o ho))

/-- A stored completion's program is typed at every type the completion is strong at. -/
theorem denoteCompletion_typed (root : ProgramSource) {w : World} {ty : EffTy}
    {c : Completion Val Err Defect FiberId Ann} (h : CompletionStrong w ty c) :
    TypedProg root w ty (denoteCompletion c) := by
  cases c with
  | ofExit ex => exact TypedProg.pure h
  | ofRefGet cell =>
    obtain ⟨t, declared, sub⟩ := h
    refine TypedProg.store (cert := ()) ⟨t, declared⟩ fun w' ord ans post => ?_
    obtain ⟨t', declared', fits⟩ := post
    rw [ord.1.2.2.2.1 _ _ declared] at declared'
    cases declared'
    exact TypedProg.pure (strongExit_success w' ty ans (fits_subN w' sub ans fits))

/-- The internal keys of a machine whose store lost its due list are among the old ones. -/
theorem internalKeys_dueless (m : RState) :
    Guard.internalKeys { m with state := { m.state with deferreds :=
      { m.state.deferreds with due := [] } } } ⊆ Guard.internalKeys m := by
  intro key hk
  rw [internalKeys_fibers] at hk ⊢
  simp only [List.map_nil, List.append_nil, List.mem_append] at hk ⊢
  rcases hk with ((hk | hk) | hk) | hk
  · exact Or.inl (Or.inl (Or.inl (Or.inl hk)))
  · exact Or.inl (Or.inl (Or.inl (Or.inr hk)))
  · exact Or.inl (Or.inr hk)
  · exact Or.inr hk

/-- **`drainDue` keeps `I`** at the world over the drained store. Its one halting arm, `postTask`
on an unknown owner, is excluded by `MachineLive.dueOwners`. -/
theorem drainDue_preserves (root : ProgramSource) (rootTy : EffTy) :
    StepPreserves root rootTy .drainDue := by
  intro w m rest _ typed
  have tail := configTyped_tail typed
  have wide := typed.machine.wide
  let s : Stores := { m.state with deferreds := { m.state.deferreds with due := [] } }
  have le : m.state.le s := Stores.le_refl m.state
  have stores : StoresOk (preds root) { w with state := s } Expect.root s := by
    have ord : w.leHost { w with state := s } := by
      apply leHost_restate
      · rw [wide.state]
        exact le
      · rw [wide.state]
      · rw [wide.state]
      · rw [wide.state]
    obtain ⟨c0, c1, c2, c3, c4, c5⟩ := storesOk_world ord rfl rfl rfl wide.stores
    exact ⟨⟨(fun o ho => nomatch ho), PromiseTableOk.memo c0⟩, c1, ⟨c2.c0⟩, c3, c4, c5⟩
  obtain ⟨ord, restated⟩ := configTyped_restate tail le rfl rfl rfl
    (wf_restate wide.wf le rfl rfl rfl rfl rfl) stores (internalKeys_dueless m)
    (fun o ho => nomatch ho) (fun _ h => h)
  refine ⟨{ w with state := s }, ord, ?_⟩
  show ConfigTyped root rootTy { w with state := s }
    (drainOwed { m with state := s } (m.state.deferreds.due.map (Owed.mapCode denoteCompletion))).1
    ((drainOwed { m with state := s } (m.state.deferreds.due.map (Owed.mapCode denoteCompletion))).2
      ++ rest)
  apply configTyped_drainOwed _ _ _ restated
  intro o ho
  obtain ⟨d, hd, rfl⟩ := List.mem_map.mp ho
  have key : (d.waiter, d.token) ∈ Guard.internalKeys m := by
    rw [internalKeys_fibers]
    exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _
      (List.mem_map.mpr ⟨d, hd, rfl⟩)))
  refine ⟨fun ty declared => ?_, wide.keysBelow _ key, ?_, fun owner priority mode => ?_⟩
  · have strong := PromiseTableOk.due wide.stores.c0 d hd ty declared
    exact typedProg_mono root w _ ty _ ord (denoteCompletion_typed root strong)
  · cases hr : requestOfR m d.waiter d.token with
    | none => exact hr
    | some r => exact absurd key (wide.requestsOwned _ _ r hr)
  · exact wide.live.dueOwners d hd owner priority mode

/-! ## An interrupt recorded on one fiber (`interruptRecord`, `Machine/Fibers.lean:803-824`)

Shared by `link` on a closed scope, `interruptTarget`, the interrupt decision and the fail-fast
countdown: the cause is recorded (interrupts only), a running interruptible fiber defers it, an
idle interruptible fiber is unparked with the failure as its current code and evaluated now. -/

/-- A fiber's saved position and provenance at its declared type (`preds`' `SavedOk` column). -/
theorem FiberTyped.position {root : ProgramSource} {w : World} {m : RState} {f : RFiber}
    (h : FiberTyped root w m f) {ty : EffTy} (declared : w.Γ f.id = some ty) :
    ∃ tin, PositionStack root w tin ty f.frame.stack ∧ InterruptProvenance f.frame :=
  h.ok.c0.c0 ty declared

theorem MachineWide.declared {root : ProgramSource} {rootTy : EffTy} {w : World} {m : RState}
    (wide : MachineWide root rootTy w m) {f : RFiber} (hf : f ∈ m.fibers) :
    ∃ ty, w.Γ f.id = some ty :=
  Option.isSome_iff_exists.mp ((wide.fibers f.id).mpr (List.mem_map_of_mem hf))

/-- The cause an interrupt records has only interrupt reasons. -/
theorem interruptCause_interrupts (root : ProgramSource) (who : Option FiberId)
    (extra : ReasonAnnotations Ann) (id : FiberId) :
    ∀ r ∈ (Cause.annotate (Supervision.interruptCause (interpR root.program).encodeFiber who
      ((interpR root.program).stackAnnotations id)) extra false : CauseV).reasons,
      r.tag = .interrupt := by
  intro r hr
  rw [Cause.annotate_reasons, Supervision.interruptCause_eq, Cause.annotate_reasons,
    Cause.interrupt_reasons] at hr
  simp only [List.map_cons, List.map_nil, List.mem_singleton] at hr
  subst hr
  rfl

/-- An interrupt failure is typed at every effect type. -/
theorem exitOk_interrupts (w : World) (ty : EffTy) {c : CauseV}
    (interrupts : ∀ r ∈ c.reasons, r.tag = .interrupt) : ExitOk w ty (.failure c) :=
  strongExit_of_clean w ty c (cleanExit_of_interrupts c interrupts)
    (noShapeDefect_of_interrupts ty c interrupts)

/-- The fiber an uninterruptible fiber becomes: the cause recorded. -/
def recordedFiber (t : RFiber) (acc : CauseV) : RFiber :=
  { t with frame := { t.frame with interruptedCause := some acc } }

/-- The fiber a running interruptible fiber becomes: the cause recorded and deferred. -/
def deferredFiber (t : RFiber) (acc : CauseV) : RFiber :=
  { t with
    frame := { t.frame with interruptedCause := some acc, deferredInterrupt := true } }

/-- The fiber an idle interruptible fiber becomes: unparked, its failure the current code. -/
def appliedFiber (t : RFiber) (acc : CauseV) : RFiber :=
  { t with
    parked := .notParked
    pending := []
    frame := { t.frame with interruptedCause := some acc, current := .pure (.failure acc) } }

/-- The three outcomes of `interruptRecord` on the term machine, with the recorded cause. -/
theorem interruptRecord_shape (root : ProgramSource) (who : Option FiberId)
    (extra : ReasonAnnotations Ann) (t : RFiber) (prov : InterruptProvenance t.frame) :
    (t.exit.isSome = true ∧ interruptRecord (interpR root.program) who extra t = (t, false)) ∨
    (t.exit.isSome = false ∧ ∃ acc : CauseV, (∀ x ∈ acc.reasons, x.tag = .interrupt) ∧
      ((t.frame.interruptible = false ∧
          interruptRecord (interpR root.program) who extra t = (recordedFiber t acc, false)) ∨
       (t.frame.interruptible = true ∧ t.running = true ∧
          interruptRecord (interpR root.program) who extra t = (deferredFiber t acc, false)) ∨
       (t.frame.interruptible = true ∧ t.running = false ∧
          interruptRecord (interpR root.program) who extra t = (appliedFiber t acc, true)))) := by
  have cause := interruptCause_interrupts root who extra t.id
  unfold interruptRecord
  by_cases hx : t.exit.isSome = true
  · exact Or.inl ⟨hx, if_pos hx⟩
  · rw [if_neg hx]
    have hint : ∀ c : CauseV,
        termCore.interruptible (termCore.recordCause t.frame c) = t.frame.interruptible :=
      fun _ => rfl
    dsimp only
    rw [hint]
    refine Or.inr ⟨Bool.eq_false_iff.mpr hx, ?_⟩
    by_cases hi : t.frame.interruptible = true
    · rw [if_pos hi]
      by_cases hr : t.running = true
      · rw [if_pos hr]
        refine ⟨_, ?_, Or.inr (Or.inl ⟨hi, hr, rfl⟩)⟩
        intro x hx'
        split at hx'
        · exact cause x hx'
        · rename_i previous hprev
          rcases (Cause.mem_combine x previous _).mp hx' with old | new
          · exact prov.recorded previous hprev x old
          · exact cause x new
      · rw [if_neg hr]
        refine ⟨_, ?_, Or.inr (Or.inr ⟨hi, Bool.eq_false_iff.mpr hr, rfl⟩)⟩
        intro x hx'
        split at hx'
        · exact cause x hx'
        · rename_i previous hprev
          rcases (Cause.mem_combine x previous _).mp hx' with old | new
          · exact prov.recorded previous hprev x old
          · exact cause x new
    · rw [if_neg hi]
      refine ⟨_, ?_, Or.inl ⟨Bool.eq_false_iff.mpr hi, rfl⟩⟩
      intro x hx'
      split at hx'
      · exact cause x hx'
      · rename_i previous hprev
        rcases (Cause.mem_combine x previous _).mp hx' with old | new
        · exact prov.recorded previous hprev x old
        · exact cause x new

/-- A lookup that finds a fiber other than the replaced one finds it after the edit. -/
theorem rfiber?_update_keep {m : RState} {t g x : RFiber} {id : FiberId}
    (ht : m.fiber? t.id = some t) (hid : g.id = t.id) (hx : m.fiber? id = some x) (hne : x ≠ t) :
    (m.update g).fiber? id = some x := by
  by_cases same : id = g.id
  · rw [same, hid] at hx
    exact absurd (Option.some.inj (hx.symm.trans ht)).symm hne.symm
  · rw [rfiber?_update_other same]
    exact hx

/-- Editing a fiber that is neither running nor exited keeps every queued command's authority:
none reads it (an active owner runs; `exitDone` names an exited fiber). -/
theorem commandAuthority_idle {m : RState} {t g : RFiber} (ht : m.fiber? t.id = some t)
    (hid : g.id = t.id) (idle : t.running = false) (live : t.exit = none) (c : RCmd)
    (h : CommandAuthorityR m c) : CommandAuthorityR (m.update g) c := by
  have active : ∀ {id}, Guard.ActiveAt m id → Guard.ActiveAt (m.update g) id := fun {id} h => by
    obtain ⟨f, hf, running, parked⟩ := h
    have hne : f ≠ t := fun same => by
      rw [same, idle] at running
      cases running
    exact ⟨f, rfiber?_update_keep ht hid hf hne, running, parked⟩
  cases c with
  | loop fiber _ => exact active h
  | deliver fiber _ => exact active h
  | finish fiber _ => exact active h
  | afterInterrupt fiber _ _ => exact active h
  | closeParAwait fiber _ _ => exact active h
  | raceCancel _ fiber _ _ _ => exact active h
  | registrationDone raceId _ =>
    obtain ⟨race, f, found, hf, running, parked, marker⟩ := h
    have hne : f ≠ t := fun same => by
      rw [same, idle] at running
      cases running
    exact ⟨race, f, found, rfiber?_update_keep ht hid hf hne, running, parked, marker⟩
  | launch raceId =>
    obtain ⟨race, found, act⟩ := h
    exact ⟨race, found, active act⟩
  | enrollRace raceId _ =>
    obtain ⟨race, found, act⟩ := h
    exact ⟨race, found, active act⟩
  | exitDone fiber =>
    obtain ⟨f, hf, exited⟩ := h
    have hne : f ≠ t := fun same => by
      rw [same, live] at exited
      cases exited
    exact ⟨f, rfiber?_update_keep ht hid hf hne, exited⟩
  | evaluate _ => trivial
  | resume _ _ _ => trivial
  | interruptTarget _ _ _ => trivial
  | trackChild _ _ => trivial
  | observe _ _ _ => trivial
  | link _ _ _ _ _ => trivial
  | drainDue => trivial
  | wake _ _ => trivial

/-- A fiber whose saved state changed only in its interrupt bookkeeping keeps its clauses: the
current code and the stack are the old ones, and the new provenance holds. -/
theorem fiberTyped_reframe {root : ProgramSource} {w : World} {m m' : RState} {t : RFiber}
    (h : FiberTyped root w m t) (view : ObsView m m') (nextId : m.nextId ≤ m'.nextId)
    (nextToken : m.nextToken ≤ m'.nextToken) (fr : RSaved) (current : fr.current = t.frame.current)
    (stack : fr.stack = t.frame.stack) (prov : InterruptProvenance fr) :
    FiberTyped root w m' { t with frame := fr } := by
  have moved := fiberTyped_transport h view nextId nextToken
  refine ⟨⟨⟨fun ty declared => ?_⟩, moved.ok.c1, moved.ok.c2, moved.ok.c3, moved.ok.c4,
      moved.ok.c5⟩, fun token hp => ?_, moved.below, moved.pendingShape, moved.parkedIdle,
    moved.parkedBelow, moved.exited, fun hx => stack.trans (moved.exitedStack hx), fun _ => ?_,
    moved.pendingOwner, moved.observers,
    fun raceId marker => ?_, fun hx hr hm hp ty declared => ?_, moved.tokens, moved.raceObservers,
    moved.targetsBelow, moved.observersBelow, moved.children⟩
  · obtain ⟨tin, stackOk, _⟩ := h.position declared
    exact ⟨tin, by rw [stack]; exact stackOk, prov⟩
  · obtain ⟨tin, final, token', final', stackOk, _⟩ := h.delivery token hp
    exact ⟨tin, final, token', final',
      by rw [stack]; exact hostStack_races (racesKept_of_eq view.races) stackOk, prov⟩
  · exact prov.deferred (by assumption)
  · rw [current] at marker
    obtain ⟨race, resultTy, found, host, token, reply⟩ := moved.registration raceId marker
    exact ⟨race, resultTy, found, host, token,
      stackReply_view (f := t) (racesKept_of_eq (m := m') fun _ => rfl) rfl (by rw [stack])
        (fun _ => prov) reply⟩
  · rw [current] at hm
    obtain ⟨tin, code, stackOk, _⟩ := h.code hx hr hm hp ty declared
    exact ⟨tin, by rw [current]; exact code,
      by rw [stack]; exact hostStack_races (racesKept_of_eq view.races) stackOk, prov⟩

/-- The head facts of an `evaluate`: it reads nothing, owns nothing, carries no key. -/
theorem headOk_evaluate (root : ProgramSource) (w : World) (m : RState) (id : FiberId)
    (q : List RCmd) : HeadOk root w m (.evaluate id) q :=
  ⟨trivial, trivial, trivial, (fun _ h => nomatch h), trivial, (fun _ h => nomatch h),
    (fun _ _ _ _ h => nomatch h), (fun _ _ _ h => nomatch h), (fun _ _ h => nomatch h),
    (fun _ _ _ h => nomatch h), (fun _ _ _ _ _ h => nomatch h), (fun _ _ _ h => nomatch h)⟩

theorem configTyped_cons_evaluate {root : ProgramSource} {rootTy : EffTy} {w : World}
    {m : RState} {q : List RCmd} (typed : ConfigTyped root rootTy w m q) (id : FiberId) :
    ConfigTyped root rootTy w m (.evaluate id :: q) :=
  ⟨typed.machine, readCode_cons (fun _ _ h => nomatch h) (fun _ _ h => nomatch h) typed.code,
    queueOk_cons (headOk_evaluate root w m id q) typed.queue⟩

/-- **An interrupt recorded on one fiber keeps `I`** (`interruptRecord`), with the evaluation an
idle interruptible fiber owes queued first. -/
theorem configTyped_interruptRecord {root : ProgramSource} {rootTy : EffTy} {w : World}
    {m : RState} {q : List RCmd} (typed : ConfigTyped root rootTy w m q) {target : FiberId}
    {t : RFiber} (ht : m.fiber? target = some t) (who : Option FiberId)
    (extra : ReasonAnnotations Ann) :
    ConfigTyped root rootTy w (m.update (interruptRecord (interpR root.program) who extra t).1)
      ((if (interruptRecord (interpR root.program) who extra t).2 then [Cmd.evaluate target]
        else []) ++ q) := by
  have tid : t.id = target := rfiber?_id ht
  have hf : m.fiber? t.id = some t := by rw [tid]; exact ht
  have hmem : t ∈ m.fibers := rfiber?_mem hf
  have wide := typed.machine.wide
  have old := typed.machine.fiber hmem
  obtain ⟨ty, declared⟩ := wide.declared hmem
  obtain ⟨tin, _, prov⟩ := old.position declared
  have sameKeys : ∀ (g : RFiber), g.observers = t.observers → g.dispatcher = t.dispatcher →
      ∀ k ∈ Guard.fiberKeys g, k ∈ Guard.internalKeys m ∨
        (k.2 < m.nextToken ∧ requestOfR m k.1 k.2 = none) := by
    intro g hobs hdisp k hk
    unfold Guard.fiberKeys at hk
    rw [hobs, hdisp] at hk
    exact Or.inl (fiberKeys_internal hmem hk)
  rcases interruptRecord_shape root who extra t prov with
    ⟨_, hr⟩ | ⟨hx, acc, hacc, ⟨_, hr⟩ | ⟨_, _, hr⟩ | ⟨_, hidle, hr⟩⟩
  · rw [hr]
    exact configTyped_rupdate (g := t) typed hf rfl (PendingWeaker.refl _) rfl rfl rfl rfl rfl
      (fun p => p) (sameKeys t rfl rfl)
      (fiberTyped_transport old (obsView_rupdate hf rfl (PendingWeaker.refl _)) (Nat.le_refl _)
        (Nat.le_refl _))
  · rw [hr]
    have newProv : InterruptProvenance (recordedFiber t acc).frame :=
      ⟨fun c hc => by cases hc; exact hacc, fun _ => rfl⟩
    exact configTyped_rupdate (g := recordedFiber t acc) typed hf rfl (PendingWeaker.refl _) rfl
      rfl rfl rfl rfl (fun _ => newProv) (sameKeys _ rfl rfl)
      (fiberTyped_reframe old (obsView_rupdate (g := recordedFiber t acc) hf rfl
        (PendingWeaker.refl _)) (Nat.le_refl _) (Nat.le_refl _) (recordedFiber t acc).frame rfl rfl
        newProv)
  · rw [hr]
    have newProv : InterruptProvenance (deferredFiber t acc).frame :=
      ⟨fun c hc => by cases hc; exact hacc, fun _ => rfl⟩
    exact configTyped_rupdate (g := deferredFiber t acc) typed hf rfl (PendingWeaker.refl _) rfl
      rfl rfl rfl rfl (fun _ => newProv) (sameKeys _ rfl rfl)
      (fiberTyped_reframe old (obsView_rupdate (g := deferredFiber t acc) hf rfl
        (PendingWeaker.refl _)) (Nat.le_refl _) (Nat.le_refl _) (deferredFiber t acc).frame rfl rfl
        newProv)
  · rw [hr]
    show ConfigTyped root rootTy w (m.update (appliedFiber t acc)) (.evaluate target :: q)
    let g := appliedFiber t acc
    have live : t.exit = none := by
      cases h : t.exit with
      | none => rfl
      | some _ =>
        rw [h] at hx
        cases hx
    have newProv : InterruptProvenance g.frame := ⟨fun c hc => by cases hc; exact hacc, fun _ => rfl⟩
    have view : ObsView m (m.update g) := obsView_rupdate (g := g) hf rfl (fun _ _ h => nomatch h)
    have look : (m.update g).fiber? g.id = some g := rfiber?_update_self hf rfl
    have fresh : FiberTyped root w (m.update g) g := by
      have moved := fiberTyped_transport old view (Nat.le_refl _) (Nat.le_refl _)
      refine ⟨⟨⟨fun ty' declared' => ?_⟩, (fun _ hp => nomatch hp), moved.ok.c2, moved.ok.c3,
          moved.ok.c4, moved.ok.c5⟩, (fun _ hp => nomatch hp), moved.below, rfl,
        (fun h => absurd rfl h), (fun _ hp => nomatch hp), (fun hx' => ?_), (fun hx' => ?_),
        (fun _ => rfl), (fun _ hp => nomatch hp), moved.observers, (fun _ hm => nomatch hm),
        (fun _ _ _ _ ty' declared' => ?_), (fun _ hp => nomatch hp), moved.raceObservers,
        (fun _ hp => nomatch hp), moved.observersBelow, moved.children⟩
      · obtain ⟨tin', stackOk, _⟩ := old.position declared'
        exact ⟨tin', stackOk, newProv⟩
      · rw [show g.exit = t.exit from rfl, live] at hx'
        cases hx'
      · rw [show g.exit = t.exit from rfl, live] at hx'
        cases hx'
      · -- the failure is installed over the stack the old fiber's correlated clauses type: its
        -- code clause, or its registration's reply stack (row 188 (b))
        cases hm : raceRegistrationR t.frame.current with
        | none =>
          -- an idle fiber's stack by its code clause, a parked one's by its delivery clause
          cases hp : t.parked with
          | notParked =>
            obtain ⟨tin', _, stackOk, _⟩ := old.code live hidle hm hp ty' declared'
            exact ⟨tin', TypedProg.pure (exitOk_interrupts w tin' hacc),
              hostStack_races (racesKept_of_eq view.races) stackOk, newProv⟩
          | withGuard token =>
            obtain ⟨tin', final, _, declaredF, stackOk, _⟩ := old.delivery token hp
            have same : final = ty' := by
              have both : w.Γ t.id = some ty' := declared'
              rw [declaredF] at both
              exact Option.some.inj both
            subst same
            exact ⟨tin', TypedProg.pure (exitOk_interrupts w tin' hacc),
              hostStack_races (racesKept_of_eq view.races) stackOk, newProv⟩
        | some r =>
          obtain ⟨_, resultTy, _, _, _, final, declaredF, stackOk, _⟩ := old.registration r hm
          have same : final = ty' := by
            have both : w.Γ t.id = some ty' := declared'
            rw [declaredF] at both
            exact Option.some.inj both
          subst same
          exact ⟨resultTy, TypedProg.pure (exitOk_interrupts w resultTy hacc),
            hostStack_races (racesKept_of_eq view.races) stackOk, newProv⟩
    have edited := configTyped_rupdate_gen (g := g) typed hf rfl (fun _ _ h => nomatch h) rfl
      (fun _ => newProv) (sameKeys g rfl rfl)
      (fun token r hr' => by
        rw [requestOfR_of_not_parked look (fun h => nomatch h)] at hr'
        cases hr')
      (fun c _ h => commandAuthority_idle (g := g) hf rfl hidle live c h)
      (fun hrun => by
        change t.running = true at hrun
        rw [hidle] at hrun
        cases hrun)
      fresh
    exact configTyped_cons_evaluate edited target

/-! ## Scope finalizers: the store edits of `link` and of a scope-finalizer drop

`link` on an open scope registers the target's interrupt finalizer under a fresh key: the store
`syncOpStep (.scopeAdd scope fin)` reaches on an open scope (`syncOpStep_scopeAdd_open`); the
drop observer removes it: the store `.scopeRemove` reaches (`syncOpStep_scopeRemove`). Their
growth and well-formedness are the store's own laws (`syncOpStep_le`, `syncOpStep_wf`); what is
left is the generated scope column (`ScopeStateOk`), read through a state's registrations and its
closing exit. -/

theorem scopeStateOk_of {root : ProgramSource} {w : World} {e : Expect}
    {st : ScopeState Nat FinName Val Err Defect FiberId Ann}
    (typed : ∀ v ∈ st.entries, FinalizerTyped root w v.2)
    (fins : ∀ v ∈ st.entries, FinNameOk (preds root) w e v.2)
    (closed : ∀ ex, st.closingExit? = some ex → (preds root).ScopeExitOk w e ex) :
    ScopeStateOk (preds root) w e st := by
  cases st with
  | empty => trivial
  | openEmpty => trivial
  | openInline key fin =>
    exact ⟨typed (key, fin) (List.mem_singleton_self _), fins (key, fin) (List.mem_singleton_self _)⟩
  | openMap entries => exact ⟨fun v hv => typed v hv, fun v hv => fins v hv⟩
  | closed exit => exact closed exit rfl

theorem scopeStateOk_entries {root : ProgramSource} {w : World} {e : Expect}
    {st : ScopeState Nat FinName Val Err Defect FiberId Ann}
    (h : ScopeStateOk (preds root) w e st) : ∀ v ∈ st.entries, FinNameOk (preds root) w e v.2 := by
  cases st with
  | empty => exact fun _ hv => nomatch hv
  | openEmpty => exact fun _ hv => nomatch hv
  | openInline key fin =>
    intro v hv
    rw [ScopeState.entries_openInline, List.mem_singleton] at hv
    subst hv
    exact h.2
  | openMap entries => exact h.2
  | closed exit => exact fun _ hv => nomatch hv

/-- The typed half of the scope clause at every registered finalizer (seat D4's `FinalizerOk`,
decisions row 151 (a″)): the sibling of `scopeStateOk_entries`. -/
theorem scopeStateOk_typed {root : ProgramSource} {w : World} {e : Expect}
    {st : ScopeState Nat FinName Val Err Defect FiberId Ann}
    (h : ScopeStateOk (preds root) w e st) : ∀ v ∈ st.entries, FinalizerTyped root w v.2 := by
  cases st with
  | empty => exact fun _ hv => nomatch hv
  | openEmpty => exact fun _ hv => nomatch hv
  | openInline key fin =>
    intro v hv
    rw [ScopeState.entries_openInline, List.mem_singleton] at hv
    subst hv
    exact h.1
  | openMap entries => exact h.1
  | closed exit => exact fun _ hv => nomatch hv

theorem scopeStateOk_closed {root : ProgramSource} {w : World} {e : Expect}
    {st : ScopeState Nat FinName Val Err Defect FiberId Ann}
    (h : ScopeStateOk (preds root) w e st) :
    ∀ ex, st.closingExit? = some ex → (preds root).ScopeExitOk w e ex := by
  cases st with
  | closed exit =>
    intro ex hex
    cases hex
    exact h
  | empty => exact fun _ hex => nomatch hex
  | openEmpty => exact fun _ hex => nomatch hex
  | openInline _ _ => exact fun _ hex => nomatch hex
  | openMap _ => exact fun _ hex => nomatch hex

theorem mem_tableInsert {table : List (Nat × FinName)} {key : Nat} {fin : FinName}
    {v : Nat × FinName} (hv : v ∈ Effect4.Scope.tableInsert table key fin) :
    v ∈ table ∨ v = (key, fin) := by
  by_cases hmem : key ∈ table.map Prod.fst
  · rw [Effect4.Scope.tableInsert_existing table key fin hmem] at hv
    obtain ⟨old, hold, rfl⟩ := List.mem_map.mp hv
    by_cases hk : old.fst = key
    · rw [if_pos hk]
      exact Or.inr rfl
    · rw [if_neg hk]
      exact Or.inl hold
  · rw [Effect4.Scope.tableInsert_new table key fin hmem] at hv
    rcases List.mem_append.mp hv with old | new
    · exact Or.inl old
    · exact Or.inr (List.mem_singleton.mp new)

/-- A registration's state holds the old registrations and the new one. -/
theorem entries_addUnsafe (sc : ScopeV) (key : Nat) (fin : FinName) :
    ∀ v ∈ (sc.addUnsafe key fin).state.entries, v ∈ sc.state.entries ∨ v = (key, fin) := by
  intro v hv
  cases hs : sc.state with
  | empty =>
    rw [Effect4.Scope.addUnsafe_empty sc key fin hs, ScopeState.entries_openInline,
      List.mem_singleton] at hv
    exact Or.inr hv
  | openEmpty =>
    rw [Effect4.Scope.addUnsafe_openEmpty sc key fin hs, ScopeState.entries_openInline,
      List.mem_singleton] at hv
    exact Or.inr hv
  | openInline k f =>
    rw [Effect4.Scope.addUnsafe_openInline sc k key f fin hs, ScopeState.entries_openMap] at hv
    rcases mem_tableInsert hv with old | new
    · rw [ScopeState.entries_openInline]
      exact Or.inl old
    · exact Or.inr new
  | openMap table =>
    rw [Effect4.Scope.addUnsafe_openMap sc table key fin hs, ScopeState.entries_openMap] at hv
    rcases mem_tableInsert hv with old | new
    · rw [ScopeState.entries_openMap]
      exact Or.inl old
    · exact Or.inr new
  | closed exit =>
    have closed : sc.isClosed = true := by
      show sc.state.isClosed = true
      rw [hs]
      rfl
    rw [Effect4.Scope.addUnsafe_closed sc key fin closed, hs] at hv
    exact Or.inl hv

theorem scopeStoreOk_setEntry {root : ProgramSource} {w : World} {e : Expect} {st : ScopeStore}
    (h : ScopeStoreOk (preds root) w e st) {entry : ScopeEntry}
    (ok : ScopeEntryOk (preds root) w e entry) : ScopeStoreOk (preds root) w e (st.setEntry entry) :=
  ⟨fun x hx => by
    rcases ScopeStore.mem_setEntry hx with rfl | old
    · exact ok
    · exact h.c0 x old⟩

/-- The scope column after a registration of a typed finalizer on an open scope. -/
theorem scopeStoreOk_addUnsafe {root : ProgramSource} {w : World} {e : Expect} {st : ScopeStore}
    (h : ScopeStoreOk (preds root) w e st) {scope : Nat} {entry : ScopeEntry}
    (hentry : st.entryAt scope = some entry) (key : Nat) {fin : FinName}
    (finOk : FinNameOk (preds root) w e fin) (finTyped : FinalizerTyped root w fin) :
    ScopeStoreOk (preds root) w e (st.setEntry { entry with scope := entry.scope.addUnsafe key fin }) := by
  have old := (h.c0 entry (List.mem_of_find?_eq_some hentry)).c0.c0
  refine scopeStoreOk_setEntry h
    ⟨⟨scopeStateOk_of (fun v hv => ?_) (fun v hv => ?_) (fun ex hex => ?_)⟩⟩
  · rcases entries_addUnsafe entry.scope key fin v hv with oldv | rfl
    · exact scopeStateOk_typed old v oldv
    · exact finTyped
  · rcases entries_addUnsafe entry.scope key fin v hv with oldv | rfl
    · exact scopeStateOk_entries old v oldv
    · exact finOk
  · change (entry.scope.addUnsafe key fin).closingExit? = some ex at hex
    rw [Effect4.Scope.closingExit_addUnsafe entry.scope key fin] at hex
    exact scopeStateOk_closed old ex hex

/-- The scope column after a registration is removed. -/
theorem scopeStoreOk_removeFinalizer {root : ProgramSource} {w : World} {e : Expect}
    {st : ScopeStore} (h : ScopeStoreOk (preds root) w e st) (scope key : Nat) :
    ScopeStoreOk (preds root) w e (st.removeFinalizer scope key) := by
  unfold ScopeStore.removeFinalizer
  split
  · exact h
  · rename_i entry hentry
    have old := (h.c0 entry (List.mem_of_find?_eq_some hentry)).c0.c0
    refine scopeStoreOk_setEntry h
      ⟨⟨scopeStateOk_of (fun v hv => ?_) (fun v hv => ?_) (fun ex hex => ?_)⟩⟩
    · exact scopeStateOk_typed old v
        ((Effect4.Scope.removeUnsafe_finalizers_sublist entry.scope key).subset hv)
    · exact scopeStateOk_entries old v
        ((Effect4.Scope.removeUnsafe_finalizers_sublist entry.scope key).subset hv)
    · change (entry.scope.removeUnsafe key).closingExit? = some ex at hex
      rw [Effect4.Scope.closingExit_removeUnsafe entry.scope key] at hex
      exact scopeStateOk_closed old ex hex

/-- The scope column after a close (`ScopeStore.closeState`, the state half of `scopeCloseUnsafe`,
`internal/effect.ts:3778-3798`): the closed entry holds no registrations, and its exit is the one
it already held or the closing exit, which the column types (finding F-CLOSE). -/
theorem scopeStoreOk_closeState {root : ProgramSource} {w : World} {e : Expect} {st : ScopeStore}
    (h : ScopeStoreOk (preds root) w e st) (scope : Nat) {ex : ExitV}
    (hex : (preds root).ScopeExitOk w e ex) :
    ScopeStoreOk (preds root) w e (st.closeState scope ex) := by
  unfold ScopeStore.closeState
  split
  · exact h
  · rename_i entry hentry
    have old := (h.c0 entry (List.mem_of_find?_eq_some hentry)).c0.c0
    have none : (entry.scope.closeState ex).finalizers = [] := Effect4.Scope.closeState_finalizers _ _
    refine scopeStoreOk_setEntry h
      ⟨⟨scopeStateOk_of (fun v hv => ?_) (fun v hv => ?_) (fun ex' hex' => ?_)⟩⟩
    · change v ∈ (entry.scope.closeState ex).finalizers at hv
      rw [none] at hv
      cases hv
    · change v ∈ (entry.scope.closeState ex).finalizers at hv
      rw [none] at hv
      cases hv
    · change (entry.scope.closeState ex).closingExit? = some ex' at hex'
      cases hcl : entry.scope.isClosed with
      | true =>
        rw [Effect4.Scope.closeState_idempotent _ _ hcl] at hex'
        exact scopeStateOk_closed old ex' hex'
      | false =>
        rw [Effect4.Scope.close_closingExit _ _ hcl] at hex'
        cases hex'
        exact hex

/-- The internal keys do not read the scope store. -/
theorem internalKeys_scopes (m : RState) (scopes : ScopeStore) (nextName : Nat) :
    Guard.internalKeys { m with state := { m.state with scopes := scopes, nextName := nextName } } =
      Guard.internalKeys m := rfl

theorem internalKeys_scopes' (m : RState) (scopes : ScopeStore) :
    Guard.internalKeys { m with state := { m.state with scopes := scopes } } =
      Guard.internalKeys m := rfl

/-- On an open scope, a registration is `setEntry` of the scope with the finalizer added. -/
theorem addFinalizer_open_eq {st : ScopeStore} {scope key : Nat} {fin : FinName}
    {entry : ScopeEntry} (hentry : st.entryAt scope = some entry)
    (hopen : entry.scope.closingExit? = none) :
    (st.addFinalizer scope key fin).1 = st.setEntry { entry with scope := entry.scope.addUnsafe key fin } := by
  unfold ScopeStore.addFinalizer
  rw [hentry]
  dsimp only
  unfold Effect4.Scope.addExit
  rw [hopen]

/-- A fiber edit keeps the store. -/
theorem rmodify_state (m : RState) (id : FiberId) (k : RFiber → RFiber) :
    (m.modify id k).state = m.state := by
  unfold RunMachine.modify
  split
  · rfl
  · rfl

/-- The registration `link` makes on an open scope: an interrupt finalizer of the target, under
the supply's fresh key. -/
theorem scopeLinkFiber_open (root : ProgramSource) (mode : Supervision.ScopeMode) (scope : Nat)
    (fiber : FiberId) (st : Stores) {entry : ScopeEntry} (hentry : st.scopes.entryAt scope = some entry) :
    ∃ skip : Bool, (interpR root.program).scopeLinkFiber mode scope fiber st =
      some ({ st with
        scopes := (st.scopes.addFinalizer scope st.nextName (.interruptFiber fiber skip)).1
        nextName := st.nextName + 1 }, st.nextName) := by
  cases mode with
  | forkIn => exact ⟨true, by simp only [interpR, interpOf, hentry]⟩
  | fiberRunIn => exact ⟨false, by simp only [interpR, interpOf, hentry]⟩

/-! ## `link` (three halting arms: an unknown scope at the status read or at the registration,
an unknown target; `Machine/Fibers.lean:1005-1036`, excluded by `QueueOk.links`)

On a closed scope the target is interrupted (`interruptRecord`); on an open one an exited target
is not linked, and a live one gets the interrupt finalizer under a fresh key and the observer that
drops exactly that key. -/

/-- **`link` keeps `I`**: at the same world on a closed scope or an exited target, at the world
over the store with the new registration otherwise. -/
theorem link_preserves (root : ProgramSource) (rootTy : EffTy) (mode : Supervision.ScopeMode)
    (scope : Nat) (target : FiberId) (interruptor : Option FiberId)
    (extra : ReasonAnnotations Ann) :
    StepPreserves root rootTy (.link mode scope target interruptor extra) := by
  intro w m rest _ typed
  have tail := configTyped_tail typed
  have wide := typed.machine.wide
  obtain ⟨live, present⟩ := typed.queue.links mode scope target interruptor extra List.mem_cons_self
  obtain ⟨entry, hentry⟩ := Option.isSome_iff_exists.mp live
  obtain ⟨t, ht⟩ := Option.isSome_iff_exists.mp present
  have hstatus : (interpR root.program).scopeStatus scope m.state =
      some entry.scope.closingExit? := by
    show (m.state.scopes.entryAt scope).map (fun e => e.scope.closingExit?) = _
    rw [hentry]
    rfl
  simp only [driveStep]
  unfold linkScope
  rw [hstatus]
  cases hc : entry.scope.closingExit? with
  | some ex =>
    simp only [ht]
    exact ⟨w, leHost_refl w, configTyped_emit (configTyped_interruptRecord tail ht interruptor extra) _⟩
  | none =>
    simp only [ht]
    by_cases hx : t.exit.isSome = true
    · rw [if_pos hx]
      exact ⟨w, leHost_refl w, tail⟩
    · rw [if_neg hx]
      obtain ⟨skip, hlink⟩ := scopeLinkFiber_open root mode scope target m.state hentry
      rw [hlink, addFinalizer_open_eq hentry hc]
      dsimp only
      let fin : FinName := .interruptFiber target skip
      let s : Stores := { m.state with
        scopes := m.state.scopes.setEntry
          { entry with scope := entry.scope.addUnsafe m.state.nextName fin }
        nextName := m.state.nextName + 1 }
      have step : syncOpStep (.scopeAdd scope fin) m.state = some (s, Val.unit) :=
        syncOpStep_scopeAdd_open m.state scope fin hentry hc
      have le : m.state.le s := syncOpStep_le _ _ _ _ step
      have wf : s.WF := syncOpStep_wf (.scopeAdd scope fin) m.state s Val.unit wide.wf live step
      have ord : w.leHost { w with state := s } := by
        apply leHost_restate
        · rw [wide.state]
          exact le
        · rw [wide.state]
        · rw [wide.state]
        · rw [wide.state]
      have stores : StoresOk (preds root) { w with state := s } Expect.root s := by
        obtain ⟨c0, c1, c2, c3, c4, c5⟩ := storesOk_world ord rfl rfl rfl wide.stores
        exact ⟨c0, c1, ⟨c2.c0⟩, scopeStoreOk_addUnsafe c3 hentry m.state.nextName trivial
          (finalizerTyped_of_admitted root _ _ trivial), c4, c5⟩
      obtain ⟨_, restated⟩ := configTyped_restate tail le rfl rfl rfl wf stores
        (fun _ h => h) wide.live.dueOwners (fun _ h => h)
      have modified := configTyped_modify_quiet restated target
        (quiet_observe (.dropScopeFinalizer scope m.state.nextName) rfl) (by
          intro c _ o ho
          rcases mem_append_observer ho with old | rfl
          · exact Or.inl old
          · refine Or.inr ?_
            show Stores.ScopeLive (RunMachine.modify _ target _).state scope
            rw [rmodify_state]
            exact ScopeStore.entryAt_setEntry_isSome _ _ scope live)
        (fun _ _ kept => Or.inl kept)
      exact ⟨{ w with state := s }, ord, configTyped_emit modified _⟩

/-! ## `observe` (one halting arm: a scope-finalizer drop on an absent scope,
`Machine/Fibers.lean:1669-1671`, excluded by `ObserverCommandOk`'s `Stores.ScopeLive`) -/

/-- The edit `untrackChild` makes to the parent. -/
theorem quiet_untrack (child : FiberId) :
    QuietEdit (fun p : RFiber => { p with children := p.children.filter fun c => c ≠ child }) :=
  ⟨fun _ => rfl, fun _ => rfl, fun _ => rfl, fun _ => rfl, fun _ => rfl, fun _ => rfl,
    fun _ => rfl, fun _ => rfl, fun _ => rfl,
    fun f => ⟨[], (List.append_nil f.observers).symm, fun _ h => nomatch h⟩⟩

/-- The removal the drop observer makes, at the interpreter. -/
theorem dropFinalizer_live (root : ProgramSource) {st : Stores} {scope key : Nat}
    {entry : ScopeEntry} (hentry : st.scopes.entryAt scope = some entry) :
    (interpR root.program).dropFinalizer scope key st =
      some { st with scopes := st.scopes.removeFinalizer scope key } := by
  simp only [interpR, interpOf, hentry]

/-! ## Exits and races

A race's bookkeeping is updated by its callbacks (`raceComplete`, the settle flag, the live set),
never its host or token. The race column (`RacePayload`) reads the bookkeeping at the race's one
result type, pinned by its token's declaration. -/

theorem subN_unknown (t : Ty) : Ty.subN t .unknown = true := Ty.sub_unknown _

/-- Exit subsumption in the checker's order, column by column. -/
theorem exitOk_subN {w : World} {ty ty' : EffTy} {ex : ExitV} (h : ExitOk w ty ex)
    (ha : Ty.subN ty.answer ty'.answer = true) (he : Ty.subN ty.error ty'.error = true) :
    ExitOk w ty' ex :=
  ⟨fitsExit_subN ha he h.1, h.2⟩

/-- The error-column half of a failed exit's membership: this seat's one reading of
`fitsExit_failure_iff`. Seat D1's decisions row 152 adds `∧ ShapeFree c` to that lemma's right
side; this proof then takes the first half (`((fitsExit_failure_iff w ty c).mp h).1`), and no
caller changes. -/
theorem failureFits_cause {w : World} {ty : EffTy} {c : CauseV} (h : FitsExit w ty (.failure c)) :
    FitsCause w ty.error c :=
  ((fitsExit_failure_iff w ty c).mp h).1

/-- A failed exit's membership from its error-column half and part one's exclusion: this seat's
one construction through `fitsExit_failure_iff`. Under row 152 the proof passes the exclusion
too (`.mpr ⟨h, _shape⟩`, `NoShapeDefect`'s failure arm being `ShapeFree` by `Iff.rfl`), and no
caller changes. -/
theorem failureFits_of_cause {w : World} {ty : EffTy} {c : CauseV} (h : FitsCause w ty.error c)
    (_shape : NoShapeDefect ty (.failure c)) : FitsExit w ty (.failure c) :=
  (fitsExit_failure_iff w ty c).mpr ⟨h, _shape⟩

/-- A failure built from two typed failures' reasons is typed. -/
theorem exitOk_failure_append {w : World} {ty : EffTy} {a b : List (Reason Err Defect FiberId Ann)}
    (ha : ExitOk w ty (.failure ⟨a⟩)) (hb : ExitOk w ty (.failure ⟨b⟩)) :
    ExitOk w ty (.failure ⟨a ++ b⟩) := by
  have fa := failureFits_cause ha.1
  have fb := failureFits_cause hb.1
  have shape : NoShapeDefect ty (.failure ⟨a ++ b⟩) := fun r hr => by
    rcases List.mem_append.mp hr with hr | hr
    · exact ha.2 r hr
    · exact hb.2 r hr
  refine ⟨failureFits_of_cause (fun r hr => ?_) shape, shape⟩
  rcases List.mem_append.mp hr with hr | hr
  · exact fa r hr
  · exact fb r hr

/-- An exit's own reasons, as a failure, are typed where the exit is. -/
theorem exitOk_causeReasons {w : World} {ty : EffTy} {ex : ExitV} (h : ExitOk w ty ex) :
    ExitOk w ty (.failure ⟨ex.causeReasons⟩) := by
  cases ex with
  | success v =>
    exact ⟨failureFits_of_cause (fun r hr => nomatch hr) (fun r hr => nomatch hr),
      (fun r hr => nomatch hr)⟩
  | failure c => exact h

theorem rrace?_id {m : RState} {id : Nat} {r : RRace} (h : m.race? id = some r) : r.id = id :=
  of_decide_eq_true (List.find?_some (p := fun s : RRace => decide (s.id = id)) h)

theorem rrace?_updateRace (m : RState) (r : RRace) (id : Nat) :
    (m.updateRace r).race? id = (m.race? id).map (fun s => if s.id = r.id then r else s) := by
  unfold RunMachine.updateRace RunMachine.race?
  rw [List.find?_map]
  have hp : ((fun s : RRace => decide (s.id = id)) ∘ fun s => if s.id = r.id then r else s) =
      fun s : RRace => decide (s.id = id) := by
    funext s
    by_cases hs : s.id = r.id
    · rw [Function.comp_apply, if_pos hs, hs]
    · rw [Function.comp_apply, if_neg hs]
  rw [hp]

/-- The race column after a callback: the exit of a live entrant is typed at the race's type. -/
theorem racePayload_complete {root : ProgramSource} {w : World} {race : RRace} {resultTy : EffTy}
    (h : RacePayload root w race resultTy) (id : FiberId) (exit : ExitV)
    (typed : id ∈ race.state.live → ExitOk w resultTy exit) :
    RacePayload root w { race with state := Supervision.raceComplete race.state id exit } resultTy := by
  unfold Supervision.raceComplete
  by_cases hl : id ∈ race.state.live
  · rw [if_pos hl]
    have ex := typed hl
    have liveSub : ∀ x ∈ race.state.live.filter (fun x => decide (x ≠ id)),
        x ∈ race.state.live := fun x hx => (List.mem_filter.mp hx).1
    split
    · refine ⟨h.token, exitOk_failure_append h.failures (exitOk_causeReasons ex), h.winner,
        h.accepted, fun wait hw => ?_, fun x hx => h.live x (liveSub x hx), h.programs⟩
      cases hc : race.state.cleanup with
      | none =>
        rw [hc] at hw
        cases hw
      | some old =>
        rw [hc] at hw
        cases hw
        dsimp only
        split
        · exact h.cleanup old hc
        · exact h.cleanup old hc
    · split
      · exact ⟨h.token, h.failures, fun pair hp => by cases hp; exact ex.1,
          fun e he => by cases he; exact ex, (fun _ hw => nomatch hw),
          fun x hx => h.live x (liveSub x hx), h.programs⟩
      · split
        · have both := exitOk_failure_append h.failures ex
          exact ⟨h.token, both, h.winner, fun e he => by cases he; exact both,
            (fun _ hw => nomatch hw), fun x hx => h.live x (liveSub x hx), h.programs⟩
        · exact ⟨h.token, exitOk_failure_append h.failures ex, h.winner, h.accepted, h.cleanup,
            fun x hx => h.live x (liveSub x hx), h.programs⟩
  · rw [if_neg hl]
    exact h

/-- A race's type is pinned by its token's declaration. -/
theorem racePayload_unique {root : ProgramSource} {w : World} {r r' : RRace} {ty ty' : EffTy}
    (h : RacePayload root w r ty) (h' : RacePayload root w r' ty') (host : r'.host = r.host)
    (token : r'.token = r.token) : ty' = ty := by
  have a := h.token
  have b := h'.token
  rw [host, token, a] at b
  exact (Option.some.inj b).symm

/-- After a race edit that keeps its id, host and token, a race lookup finds the edited race or
the old one. -/
theorem rrace?_updateRace_cases {m : RState} {old new : RRace} (hr : m.race? old.id = some old)
    (hid : new.id = old.id) (raceId : Nat) :
    ((m.updateRace new).race? raceId = m.race? raceId ∧ raceId ≠ old.id) ∨
      (raceId = old.id ∧ (m.updateRace new).race? raceId = some new) := by
  by_cases same : raceId = old.id
  · subst same
    refine Or.inr ⟨rfl, ?_⟩
    rw [rrace?_updateRace, hr, Option.map_some, if_pos hid.symm]
  · refine Or.inl ⟨?_, same⟩
    rw [rrace?_updateRace]
    cases h : m.race? raceId with
    | none => rfl
    | some x =>
      have hx : x.id = raceId := rrace?_id h
      rw [Option.map_some, if_neg (by rw [hx, hid]; exact same)]

/-- With distinct race ids, a member race is what its id looks up. -/
theorem rrace?_of_mem {m : RState} (nodup : (m.races.map Race.id).Nodup) {r : RRace}
    (hr : r ∈ m.races) : m.race? r.id = some r := by
  unfold RunMachine.race?
  generalize m.races = races at nodup hr
  induction races with
  | nil => cases hr
  | cons x rest ih =>
    rw [List.map_cons, List.nodup_cons] at nodup
    rw [List.find?_cons]
    rcases List.mem_cons.mp hr with rfl | there
    · rw [decide_eq_true rfl]
    · have hne : x.id ≠ r.id := fun h => nodup.1 (h ▸ List.mem_map_of_mem there)
      rw [decide_eq_false hne]
      exact ih nodup.2 there

theorem internalKeys_updateRace {m : RState} (nodup : (m.races.map Race.id).Nodup) {old new : RRace}
    (hr : m.race? old.id = some old) (hid : new.id = old.id) (host : new.host = old.host)
    (token : new.token = old.token) :
    Guard.internalKeys (m.updateRace new) = Guard.internalKeys m := by
  have races : (m.updateRace new).races.map (fun r => (r.host, r.token)) =
      m.races.map (fun r => (r.host, r.token)) := by
    show (m.races.map fun s => if s.id = new.id then new else s).map (fun r => (r.host, r.token)) = _
    rw [List.map_map]
    apply List.map_congr_left
    intro s hs
    by_cases h : s.id = new.id
    · rw [Function.comp_apply, if_pos h]
      have found := rrace?_of_mem nodup hs
      rw [h, hid, hr] at found
      rw [host, token, Option.some.inj found]
    · rw [Function.comp_apply, if_neg h]
  rw [internalKeys_fibers, internalKeys_fibers, races]
  rfl

/-- A race edit keeps every fiber lookup. -/
theorem sameFibers_updateRace (m : RState) (r : RRace) : ∀ id f', (m.updateRace r).fiber? id = some f' →
    ∃ f, m.fiber? id = some f ∧ f'.id = f.id ∧ PendingWeaker f.pending f'.pending :=
  fun _ f' h => ⟨f', h, rfl, PendingWeaker.refl _⟩

section RaceEdit
variable {root : ProgramSource} {w : World} {m : RState} {old new : RRace} {resultTy : EffTy}
  (hr : m.race? old.id = some old) (hid : new.id = old.id) (hhost : new.host = old.host)
  (htoken : new.token = old.token) (payload : RacePayload root w new resultTy)
  (live : ∀ src ∈ new.state.live, src ∈ old.state.live ∨
    FiberColumnsBelow w src resultTy.answer resultTy.error)
include hr hid hhost htoken payload live

theorem storedObserverOk_updateRace {source : FiberId} (o : Observer)
    (h : StoredObserverOk root w m source o) : StoredObserverOk root w (m.updateRace new) source o := by
  cases o with
  | raceCallback raceId =>
    unfold StoredObserverOk at h ⊢
    dsimp only at h ⊢
    rcases rrace?_updateRace_cases hr hid raceId with ⟨same, _⟩ | ⟨rfl, found⟩
    · rw [same]
      exact h
    · rw [found]
      rw [hr] at h
      obtain ⟨r', oldPayload, oldLive⟩ := h
      have eq := racePayload_unique payload oldPayload hhost.symm htoken.symm
      subst eq
      refine ⟨r', payload, fun hl => ?_⟩
      rcases live source hl with o | cols
      · exact oldLive o
      · exact cols
  | resumeAwait _ _ _ => exact h
  | countdown _ _ => exact countdownAt_view (sameFibers_updateRace m new) h
  | dropScopeFinalizer _ _ => exact h
  | untrackChild _ => trivial
  | callback _ => trivial

theorem observerCommandOk_updateRace {source : FiberId} {exit : ExitV}
    (typed : ∀ ty, w.Γ source = some ty → ExitOk w ty exit) (o : Observer)
    (h : ObserverCommandOk root w m source exit o) :
    ObserverCommandOk root w (m.updateRace new) source exit o := by
  cases o with
  | raceCallback raceId =>
    unfold ObserverCommandOk at h ⊢
    dsimp only at h ⊢
    rcases rrace?_updateRace_cases hr hid raceId with ⟨same, _⟩ | ⟨rfl, found⟩
    · rw [same]
      exact h
    · rw [found]
      rw [hr] at h
      obtain ⟨r', oldPayload, oldLive⟩ := h
      have eq := racePayload_unique payload oldPayload hhost.symm htoken.symm
      subst eq
      refine ⟨r', payload, fun hl => ?_⟩
      rcases live source hl with o | cols
      · exact oldLive o
      · obtain ⟨ty, declared, ha, he⟩ := cols
        exact exitOk_subN (typed ty declared) ha he
  | resumeAwait _ _ _ => exact h
  | countdown _ _ => exact countdownAt_view (sameFibers_updateRace m new) h
  | dropScopeFinalizer _ _ => exact h
  | untrackChild _ => trivial
  | callback _ => trivial

theorem enrollRaceOk_updateRace {raceId : Nat} {child : FiberId}
    (h : EnrollRaceOk root w m raceId child) : EnrollRaceOk root w (m.updateRace new) raceId child := by
  unfold EnrollRaceOk at h ⊢
  obtain ⟨below, h⟩ := h
  refine ⟨below, ?_⟩
  rcases rrace?_updateRace_cases hr hid raceId with ⟨same, _⟩ | ⟨rfl, found⟩
  · rw [same]
    exact h
  · rw [found]
    rw [hr] at h
    show match some new, m.fiber? child with
      | some race, some fiber => ∃ resultTy, RacePayload root w race resultTy ∧
          FiberColumnsBelow w fiber.id resultTy.answer resultTy.error
      | _, _ => True
    cases hc : m.fiber? child with
    | none => trivial
    | some c =>
      rw [hc] at h
      obtain ⟨r', oldPayload, cols⟩ := h
      have eq := racePayload_unique payload oldPayload hhost.symm htoken.symm
      subst eq
      exact ⟨r', payload, cols⟩

end RaceEdit

/-- **A race edit that keeps the race's id, host and token keeps `I`**, given the edited race's
column at its type and a live set that only gains entrants whose columns are below it and whose
ids are below `nextId` (decisions row 134 (e)). -/
theorem configTyped_updateRace {root : ProgramSource} {rootTy : EffTy} {w : World} {m : RState}
    {q : List RCmd} (typed : ConfigTyped root rootTy w m q) {old new : RRace}
    (hr : m.race? old.id = some old) (hid : new.id = old.id) (hhost : new.host = old.host)
    (htoken : new.token = old.token) {resultTy : EffTy} (payload : RacePayload root w new resultTy)
    (live : ∀ src ∈ new.state.live, src ∈ old.state.live ∨
      (FiberColumnsBelow w src resultTy.answer resultTy.error ∧ src.value < m.nextId)) :
    ConfigTyped root rootTy w (m.updateRace new) q := by
  obtain ⟨machine, code, queue⟩ := typed
  have wide := machine.wide
  have liveCols : ∀ src ∈ new.state.live, src ∈ old.state.live ∨
      FiberColumnsBelow w src resultTy.answer resultTy.error :=
    fun src h => (live src h).imp id And.left
  have hold : old ∈ m.races := List.mem_of_find?_eq_some hr
  have keys := internalKeys_updateRace wide.raceIds hr hid hhost htoken
  have lookHost : ∀ raceId r', (m.updateRace new).race? raceId = some r' →
      ∃ r, m.race? raceId = some r ∧ r'.host = r.host ∧ r'.token = r.token := by
    intro raceId r' h'
    rcases rrace?_updateRace_cases hr hid raceId with ⟨same, _⟩ | ⟨rfl, found⟩
    · rw [same] at h'
      exact ⟨r', h', rfl, rfl⟩
    · rw [found] at h'
      cases h'
      exact ⟨old, hr, hhost, htoken⟩
  have lookFwd : ∀ raceId r, m.race? raceId = some r →
      ∃ r', (m.updateRace new).race? raceId = some r' ∧ r'.host = r.host ∧ r'.token = r.token := by
    intro raceId r h
    rcases rrace?_updateRace_cases hr hid raceId with ⟨same, _⟩ | ⟨rfl, found⟩
    · exact ⟨r, by rw [same]; exact h, rfl, rfl⟩
    · rw [hr] at h
      cases h
      exact ⟨new, found, hhost, htoken⟩
  have raceIds : (m.updateRace new).races.map Race.id = m.races.map Race.id := by
    show (m.races.map fun s => if s.id = new.id then new else s).map Race.id = _
    rw [List.map_map]
    apply List.map_congr_left
    intro s _
    by_cases h : s.id = new.id
    · rw [Function.comp_apply, if_pos h, h]
    · rw [Function.comp_apply, if_neg h]
  refine ⟨machineTyped_of ⟨wide.ids, wide.fibers, wide.heap, wide.promises, wide.tokenBound,
      wide.tokenTargets, wide.state, wide.wf, wide.cells, wide.rootDeclared, fun r hr' => ?_, wide.stores,
      wide.fiberIds, by rw [raceIds]; exact wide.raceIds, fun r hr' => ?_, fun r hr' => ?_,
      fun key hk => wide.keysBelow key (by rw [← keys]; exact hk), wide.requestsBelow,
      fun fiber token r' hr'' hk => wide.requestsOwned fiber token r' hr'' (by rw [← keys]; exact hk),
      wide.services, ⟨wide.live.running, wide.live.dueOwners⟩, wide.timers, wide.waiters,
      fun r race hr' id hid' => ?_, wide.sourceWF⟩ (fun x hx => ?_), readCode_races (m := m) rfl lookFwd code,
      ⟨queue.payload, fun c hc => ?_,
      fun c hc => commandDelivery_view (m := m) (m' := m.updateRace new) (fun _ => rfl) lookFwd c
        (queue.delivery c hc), ?_,
      queue.registration, ⟨queue.keys.below, queue.keys.disjoint⟩, fun src e o ho => ?_,
      fun r c hc => enrollRaceOk_updateRace hr hid hhost htoken payload liveCols
        (queue.enroll r c hc),
      queue.noRaceAfterInterrupt, queue.links, fun s e o ho r race hr' => by
        obtain ⟨r0, found, hh, ht⟩ := lookHost r race hr'
        rw [hh, ht]
        exact queue.raceObservers s e o ho r r0 found⟩⟩
  · obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hr'
    by_cases h : s.id = new.id
    · rw [if_pos h]
      exact ⟨resultTy, payload⟩
    · rw [if_neg h]
      exact wide.races s hs
  · obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hr'
    by_cases h : s.id = new.id
    · rw [if_pos h, hid]
      exact wide.racesBelow old hold
    · rw [if_neg h]
      exact wide.racesBelow s hs
  · obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hr'
    by_cases h : s.id = new.id
    · rw [if_pos h, hhost]
      exact wide.raceHosts old hold
    · rw [if_neg h]
      exact wide.raceHosts s hs
  · rcases rrace?_updateRace_cases hr hid r with ⟨same, _⟩ | ⟨rfl, found⟩
    · rw [same] at hr'
      exact wide.liveBelow r race hr' id hid'
    · rw [found] at hr'
      cases hr'
      rcases live id hid' with inOld | ⟨_, fresh⟩
      · exact wide.liveBelow old.id old hr id inOld
      · exact fresh
  · have hx' : x ∈ m.fibers := hx
    have old' := machine.fiber hx'
    refine ⟨old'.ok, old'.delivery_races lookFwd, old'.below, old'.pendingShape, old'.parkedIdle,
      old'.parkedBelow, old'.exited, old'.exitedStack, old'.deferredCause, old'.pendingOwner,
      fun o ho => storedObserverOk_updateRace hr hid hhost htoken payload liveCols o
        (old'.observers o ho), fun raceId marker => ?_, old'.code_races lookFwd, old'.tokens,
      fun r race hr' o ho => ?_, old'.targetsBelow, old'.observersBelow, old'.children⟩
    · obtain ⟨race, rty, found, host, token, reply⟩ := old'.registration raceId marker
      obtain ⟨r', found', host', token'⟩ := lookFwd raceId race found
      exact ⟨r', rty, found', host'.trans host, by rw [host', token']; exact token,
        stackReply_races lookFwd reply⟩
    · obtain ⟨r0, found, hh, ht⟩ := lookHost r race hr'
      rw [hh, ht]
      exact old'.raceObservers r r0 found o ho
  · have before := queue.authority c hc
    cases c with
    | registrationDone raceId _ =>
      obtain ⟨race, f, found, rest⟩ := before
      obtain ⟨r', found', host', _⟩ := lookFwd raceId race found
      exact ⟨r', f, found', by rw [host']; exact rest.1, rest.2⟩
    | launch raceId =>
      obtain ⟨race, found, act⟩ := before
      obtain ⟨r', found', host', _⟩ := lookFwd raceId race found
      exact ⟨r', found', by rw [host']; exact act⟩
    | enrollRace raceId _ =>
      obtain ⟨race, found, act⟩ := before
      obtain ⟨r', found', host', _⟩ := lookFwd raceId race found
      exact ⟨r', found', by rw [host']; exact act⟩
    | _ => exact before
  · have same : Guard.commandOwner (Code := RProgram) (m.updateRace new) = Guard.commandOwner m := by
      funext c
      cases c with
      | registrationDone raceId yielding =>
        simp only [Guard.commandOwner]
        cases h : m.race? raceId with
        | none =>
          rcases rrace?_updateRace_cases hr hid raceId with ⟨same, _⟩ | ⟨rfl, _⟩
          · rw [same, h]
          · rw [hr] at h
            cases h
        | some race =>
          obtain ⟨r', found', host', _⟩ := lookFwd raceId race h
          rw [found', Option.map_some, Option.map_some, host']
      | _ => rfl
    rw [same]
    exact queue.owners
  · have typedExit : ∀ ty, w.Γ src = some ty → ExitOk w ty e := by
      have pay := queue.payload (.observe src e o) ho
      intro ty declared
      exact pay ty declared
    exact ⟨(queue.observer src e o ho).1,
      observerCommandOk_updateRace hr hid hhost htoken payload liveCols typedExit o
        (queue.observer src e o ho).2⟩

/-- **Sequencing after a program that never fails with a typed error**: its failures are clean
(interrupts and defects), so they fit every error column; the continuation types the successes. -/
theorem seq_typed_clean (root : ProgramSource) {w : World} {mid ty : EffTy} {a : RProgram}
    {k : Val → RProgram} (ha : TypedProg root w mid a)
    (hk : ∀ w', w.leHost w' → ∀ v, Fits w' v mid.answer → TypedProg root w' ty (k v))
    (never : mid.error = .never) :
    TypedProg root w ty ((guardR .onSuccess a).bind (seqR k)) := by
  show TypedProg root w ty (.vis (.inr (.guard_ .onSuccess)) _)
  refine TypedProg.guard mid ?_ ?_ ?_
  · show TypedProg root w mid
      ((a.bind fun ex => .vis (.inr (.unguard ex)) Effects.Program.pure).bind (seqR k))
    rw [Effects.Program.bind_assoc]
    exact close_typed root ha (seqR k)
  · intro w' o ex hpost
    obtain ⟨harm, hfit⟩ := hpost
    cases ex with
    | success v =>
      have hf := hfit.1
      rw [fitsExit_success_iff] at hf
      exact hk w' o v hf
    | failure c => exact Bool.noConfusion harm
  · intro w' _ ex hfit hmiss
    cases ex with
    | success v => exact Bool.noConfusion hmiss
    | failure c =>
      exact strongExit_of_clean w' ty c (cleanExit_of_never_fits w' mid c never hfit.1) hfit.2

/-- A settled race's program is typed at the race's type (`denoteRaceSettle`, D6a): the accepted
exit, after the masked cleanup when the winning callback saw a live entrant. -/
theorem raceSettle_typed (root : ProgramSource) {w : World} {ty : EffTy} (race : Nat)
    (cleanup : Bool) {ex : ExitV} (typed : ExitOk w ty ex) :
    TypedProg root w ty ((interpR root.program).raceSettle race cleanup ex) := by
  show TypedProg root w ty (denoteRaceSettle race cleanup ex)
  unfold denoteRaceSettle
  split
  · refine seq_typed_clean root (mid := EffTy.pure .unit) ?_
      (fun w' o _ _ => TypedProg.pure (strongExit_mono _ _ _ _ o typed)) rfl
    refine TypedProg.fiber (fun _ h => nomatch h) (fun _ h => nomatch h) (fun _ h => nomatch h)
      (fun _ _ _ h => nomatch h) (EffTy.pure .unit) (BodyTyped.raceCleanup race) ?_
    intro w' _ ans post
    exact TypedProg.pure post
  · exact TypedProg.pure typed

/-- The internal keys contain every race's host and token. -/
theorem raceKey_internal {m : RState} {race : RRace} (hr : race ∈ m.races) :
    (race.host, race.token) ∈ Guard.internalKeys m := by
  rw [internalKeys_fibers]
  exact List.mem_append_left _ (List.mem_append_right _ (List.mem_map.mpr ⟨race, hr, rfl⟩))

/-- The race column does not read the settled flag. -/
theorem racePayload_settled {root : ProgramSource} {w : World} {r : RRace} {ty : EffTy}
    (h : RacePayload root w r ty) (b : Bool) : RacePayload root w { r with settled := b } ty :=
  ⟨h.token, h.failures, h.winner, h.accepted, h.cleanup, h.live, h.programs⟩

/-- A callback only removes entrants from the live set. -/
theorem raceComplete_live (s : Supervision.RaceAllState Val Err Defect FiberId Ann) (id : FiberId)
    (exit : ExitV) : ∀ x ∈ (Supervision.raceComplete s id exit).live, x ∈ s.live := by
  intro x hx
  unfold Supervision.raceComplete at hx
  split at hx
  · have sub : ∀ y ∈ s.live.filter (fun y => decide (y ≠ id)), y ∈ s.live :=
      fun y hy => (List.mem_filter.mp hy).1
    split at hx
    · exact sub x hx
    · split at hx
      · exact sub x hx
      · split at hx
        · exact sub x hx
        · exact sub x hx
  · exact hx

/-- The race callback arm of `observe`: the callback's exit updates the race's bookkeeping, and a
first accepted answer settles the race and, unless its registration is still running, resumes
the host with the settle program. -/
theorem observe_raceCallback (root : ProgramSource) (rootTy : EffTy) {w : World} {m : RState}
    {rest : List RCmd} (tail : ConfigTyped root rootTy w m rest) (id : FiberId) (exit : ExitV)
    (raceId : Nat) (obs : ObserverCommandOk root w m id exit (.raceCallback raceId)) :
    ConfigTyped root rootTy w
      (fireObserver (interpR root.program) id exit (m, []) (.raceCallback raceId)).1
      ((fireObserver (interpR root.program) id exit (m, []) (.raceCallback raceId)).2 ++ rest) := by
  have wide := tail.machine.wide
  have tail1 := configTyped_emit tail [RunEvent.observerFired id (.raceCallback raceId)]
  unfold fireObserver
  dsimp only
  rw [show (m.emit [RunEvent.observerFired id (.raceCallback raceId)]).race? raceId =
    m.race? raceId from rfl]
  cases hr : m.race? raceId with
  | none => exact tail1
  | some race =>
    dsimp only
    have hrid : race.id = raceId := rrace?_id hr
    have hmem : race ∈ m.races := List.mem_of_find?_eq_some hr
    have obs' : ∃ resultTy, RacePayload root w race resultTy ∧
        (id ∈ race.state.live → ExitOk w resultTy exit) := by
      unfold ObserverCommandOk at obs
      dsimp only at obs
      rw [hr] at obs
      exact obs
    obtain ⟨resultTy, payload, liveTyped⟩ := obs'
    have payload1 := racePayload_complete payload id exit liveTyped
    have hr1 : (m.emit [RunEvent.observerFired id (.raceCallback raceId)]).race? race.id =
        some race := by
      rw [hrid]
      exact hr
    have m2 := configTyped_updateRace tail1 hr1 rfl rfl rfl
      (new := { race with state := Supervision.raceComplete race.state id exit }) payload1
      (fun src h => Or.inl (raceComplete_live race.state id exit src h))
    split
    · rename_i accepted hacc _
      have hr2 : ((m.emit [RunEvent.observerFired id (.raceCallback raceId)]).updateRace
          { race with state := Supervision.raceComplete race.state id exit }).race?
            race.id = some { race with state := Supervision.raceComplete race.state id exit } := by
        rw [rrace?_updateRace, hr1, Option.map_some, if_pos rfl]
      have m3 := configTyped_updateRace m2 hr2 rfl rfl rfl
        (old := { race with state := Supervision.raceComplete race.state id exit })
        (new := { race with state := Supervision.raceComplete race.state id exit, settled := true })
        (racePayload_settled payload1 true) (fun src h => Or.inl h)
      have m4 := configTyped_emit m3 [RunEvent.raceSettled raceId accepted]
      split
      · exact m4
      · have acceptedTyped : ExitOk w resultTy accepted := payload1.accepted accepted hacc
        have code := raceSettle_typed root (w := w) raceId
          (Supervision.raceComplete race.state id exit).cleanupNeeded acceptedTyped
        have resumeOk : Contracts.ResumeOk (TypedProg root) w race.host race.token
            ((interpR root.program).raceSettle raceId
              (Supervision.raceComplete race.state id exit).cleanupNeeded accepted) := by
          intro ty declared
          rw [payload.token] at declared
          cases declared
          exact code
        have key := raceKey_internal hmem
        have free : requestOfR m race.host race.token = none := by
          cases hreq : requestOfR m race.host race.token with
          | none => rfl
          | some r => exact absurd key (wide.requestsOwned _ _ r hreq)
        exact configTyped_cons_resume m4 resumeOk (wide.keysBelow _ key) free
    · exact m2

end Effect4.Program.Typed

#obligation_proved Effect4.Program.Typed.M6Ledger.step_trackChild :=
  @Effect4.Program.Typed.trackChild_preserves
#obligation_proved Effect4.Program.Typed.M6Ledger.step_drainDue :=
  @Effect4.Program.Typed.drainDue_preserves
#obligation_proved Effect4.Program.Typed.M6Ledger.step_link :=
  @Effect4.Program.Typed.link_preserves
#obligation_proved Effect4.Program.Typed.M6Ledger.step_wake :=
  @Effect4.Program.Typed.wake_preserves
-- `M6Ledger`'s report runs at the foot of the last command module, which sees every proof.

/-!
## Completing a Deferred preserves the due-typing column

The four corresponding isolated declarations were checked on Lean v4.33.1 over
actual Bookkeeping imports, using at most [propext, Quot.sound]. This local
connection retains the strong completion input before coarse store typing hides it.

Placement:
1. Concept4, typed scheduler/store invariant preservation.
2. Existing M6Ledger.step_loop store arm, consumed by PromiseTableOk.due and
   then drainDue_preserves; no new ledger target.
3. Actual DeferredStore.complete, current MachineWide, row134(b)'s declared
   waiter columns and CompletionStrong. Later-world transfer requires leHost
   and unchanged token declarations, as the explicit complete_world witness has.
4. No whole store/loop step, new invariant, progress, host safety or backend claim.
5. Supplies one R4/R9 preservation conjunct on the existing M5 -> M6 -> M7 spine.

The structural lemmas use the actual Deferred operations and the existing Guard
wake-key view. The typed lemmas use only MachineWide's stores, promises and waiters
projections; they retain the entire current MachineWide premise.
-/
namespace Effect4.Program.Typed.CompletionDue
open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Sched Effect4.Program.Denote
open Effect4.Program.Typed Effect4.Program.Guard

/-- Completion provenance for M6.step_loop: retain the cell, pending waiter and entire output.
An old entry and a newly appended equal entry need not be disjoint alternatives. -/
theorem complete_due_origin {κ : Type} {store : DeferredStore κ} {cell : DeferredKey}
    {effect : κ} {o : Owed κ} (h : o ∈ (store.complete cell effect).1.due) :
    o ∈ store.due ∨ ∃ c w, store.cellAt cell = some c ∧ c.completion = none ∧
      w ∈ c.wake.waiters ∧ o = ⟨w.fiber, w.token, effect, .now⟩ := by
  unfold DeferredStore.complete at h
  cases hc : store.cellAt cell with
  | none =>
    simp only [hc] at h
    exact Or.inl h
  | some c =>
    cases hd : c.completion with
    | some previous =>
      simp only [hc, hd] at h
      exact Or.inl h
    | none =>
      simp only [hc, hd, WakeList.wakeAll] at h
      rcases List.mem_append.mp h with old | new
      · exact Or.inl old
      · obtain ⟨w, hw, rfl⟩ := List.mem_map.mp new
        exact Or.inr ⟨c, w, rfl, hd, hw, rfl⟩

/-- The wake-key view used by the typed due transfer below.
Only the forward implication uses wakeKeys: the view also contains captured batches. -/
theorem complete_due {κ : Type} {store : DeferredStore κ} {cell : DeferredKey}
    {effect : κ} {o : Owed κ} (h : o ∈ (store.complete cell effect).1.due) :
    o ∈ store.due ∨ ∃ c, store.cellAt cell = some c ∧ c.completion = none ∧
      (o.waiter, o.token) ∈ wakeKeys c.wake ∧ o.code = effect ∧ o.mode = .now := by
  rcases complete_due_origin h with old | ⟨c, w, hc, hd, hw, rfl⟩
  · exact Or.inl old
  · exact Or.inr ⟨c, hc, hd, wakeKeys_waiter_mem hw, rfl, rfl⟩


theorem completion_due_typed {root : ProgramSource} {rootTy : EffTy}
    {w : Effect4.Program.Typed.World} {m : RState} (wide : MachineWide root rootTy w m)
    (cell : DeferredKey) (completion : Completion Val Err Defect FiberId Ann)
    (strong : ∀ a e, w.«Π» cell = some (a, e) →
      CompletionStrong w ⟨a, e, Env.Requirement.empty⟩ completion) :
    ∀ o ∈ (m.state.deferreds.complete cell completion).1.due, ∀ ty,
      w.Θ o.waiter o.token = some ty → CompletionStrong w ty o.code := by
  intro o ho ty declared
  rcases complete_due ho with old | ⟨c, hcell, _, key, code, _⟩
  · exact PromiseTableOk.due wide.stores.c0 o old ty declared
  · have hcell' : m.state.deferreds.cells[cell.index]? = some c := hcell
    obtain ⟨live, _⟩ := List.getElem?_eq_some_iff.mp hcell'
    obtain ⟨⟨a, e⟩, declaredCell⟩ :=
      Option.isSome_iff_exists.mp ((wide.promises cell).mpr live)
    obtain ⟨ty0, declared0, demand⟩ :=
      wide.waiters cell c hcell a e declaredCell _ key
    have same : ty0 = ty := Option.some.inj (declared0.symm.trans declared)
    subst same
    rw [code]
    exact completionStrong_await demand (strong a e declaredCell)

/-- The same due typing at an explicitly related world with unchanged token declarations.
This is a small transport used after the concrete complete_world witness. -/
theorem completion_due_typed_later {root : ProgramSource} {rootTy : EffTy}
    {w newer : Effect4.Program.Typed.World} {m : RState} (wide : MachineWide root rootTy w m)
    (cell : DeferredKey) (completion : Completion Val Err Defect FiberId Ann)
    (strong : ∀ a e, w.«Π» cell = some (a, e) →
      CompletionStrong w ⟨a, e, Env.Requirement.empty⟩ completion)
    (ord : w.leHost newer) (tokens : newer.Θ = w.Θ) :
    ∀ o ∈ (m.state.deferreds.complete cell completion).1.due, ∀ ty,
      newer.Θ o.waiter o.token = some ty → CompletionStrong newer ty o.code := by
  intro o ho ty declared
  rw [tokens] at declared
  exact completionStrong_mono ord (completion_due_typed wide cell completion strong o ho ty declared)

end Effect4.Program.Typed.CompletionDue
