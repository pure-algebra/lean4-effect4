import Effect4.Laws.Program.Typed.Commands.Registration

/-!
# Laws.Program.Typed.Commands.Launch — allocation and a race entrant's launch

Concept 4 (the configuration invariant `I`); question `M6Ledger.step_launch`, and through the
allocation transport every allocating evaluator arm (`fork`, `forkIn`, `forkScoped`, the parallel
close). The actual allocation (`spawn`, `Machine/Fibers.lean:948-966`) appends one fresh fiber at
the old `nextId` and increments the counter; the world declares it (`World.addFiber`).

What allocation needs of the invariant. Every clause reading the fiber table positively (a
declaration exists, `FiberColumnsBelow`, a reply stack's final type) is kept by the extension.
A clause reading it negatively (`∀ ty, Γ id = some ty → …`) is kept only where the destination's
declaration reflects back, so each such read site needs its id distinct from the fresh one: the
clause's own fibers (below `nextId`), live sets and countdown targets (row 134 (e)), queued
enrollments (row 134 (e)), queued observe sources (row 189), a finish's active owner. The fresh
fiber's own lookups are a separate case: it has no pending record, observer, park or key. Θ, the
store and the races are untouched (Codex's command-polarity review, 2026-10-02, isolates exactly
these reads). Not established here: progress, or that the launched entrant's evaluation is typed
beyond its typed code (that is `evaluate` and the evaluator's goals).
-/

set_option autoImplicit false
namespace Effect4.Program.Typed
open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Sched Effect4.Program.Denote
open Effect4.Laws.Effects Contracts

/-! ## The allocated machine and the extended world -/

/-- The machine `spawn` builds before its trace event: one fiber appended at the old `nextId`. -/
def allocR (m : RState) (child : RFiber) (record : ForkRecord) : RState :=
  { m with fibers := m.fibers ++ [child], nextId := m.nextId + 1, forks := m.forks ++ [record] }

private theorem find?_append_single_miss {α : Type _} (p : α → Bool) (xs : List α) (x : α)
    (hx : p x = false) : (xs ++ [x]).find? p = xs.find? p := by
  have hs : [x].find? p = none := by
    rw [List.find?_cons, hx]
    rfl
  rw [List.find?_append, hs, Option.or_none]

private theorem find?_append_single_hit {α : Type _} (p : α → Bool) (xs : List α) (x : α)
    (hn : xs.find? p = none) (hx : p x = true) : (xs ++ [x]).find? p = some x := by
  have hs : [x].find? p = some x := by rw [List.find?_cons, hx]
  rw [List.find?_append, hn, Option.none_or, hs]

section Alloc
variable {m : RState} {child : RFiber} {record : ForkRecord}

theorem allocR_fiber_other {id : FiberId} (ne : child.id ≠ id) :
    (allocR m child record).fiber? id = m.fiber? id :=
  find?_append_single_miss _ _ _ (decide_eq_false ne)

theorem allocR_fiber_self (fresh : m.fiber? child.id = none) :
    (allocR m child record).fiber? child.id = some child :=
  find?_append_single_hit _ _ _ fresh (decide_eq_true rfl)

theorem allocR_race (r : Nat) : (allocR m child record).race? r = m.race? r := rfl

theorem allocR_requestOfR (parked : child.parked = .notParked) (fresh : m.fiber? child.id = none)
    (fiber : FiberId) (token : Nat) :
    requestOfR (allocR m child record) fiber token = requestOfR m fiber token := by
  by_cases same : child.id = fiber
  · subst same
    have off : child.parked ≠ .withGuard token := by
      rw [parked]
      exact fun h => nomatch h
    rw [requestOfR_of_not_parked (allocR_fiber_self fresh) off]
    unfold requestOfR
    rw [fresh]
    rfl
  · rw [requestOfR_congr (allocR_fiber_other same)]

end Alloc

section World
variable {w : World} {n : FiberId} {ty : EffTy}

theorem addFiber_Γ_other {id : FiberId} (ne : n ≠ id) : (w.addFiber n ty).Γ id = w.Γ id := by
  show tableInsert w.Γ n ty id = w.Γ id
  unfold tableInsert
  rw [if_neg (fun h => ne h.symm)]

theorem addFiber_Γ_self : (w.addFiber n ty).Γ n = some ty := by
  show tableInsert w.Γ n ty n = some ty
  unfold tableInsert
  rw [if_pos rfl]

theorem addFiber_extends (fresh : w.Γ n = none) {id : FiberId} {t : EffTy}
    (h : w.Γ id = some t) : (w.addFiber n ty).Γ id = some t := by
  have ne : n ≠ id := fun same => by rw [same, h] at fresh; cases fresh
  rw [addFiber_Γ_other ne]
  exact h

theorem addFiber_leHost (fresh : w.Γ n = none) : w.leHost (w.addFiber n ty) :=
  ⟨(fork_extension w n ty fresh).1, fun _ _ h => h⟩

end World

/-- The typed state's freshness of the next fiber id: no fiber has it, the world declares none. -/
theorem fresh_of_typed {root : ProgramSource} {rootTy : EffTy} {w : World} {m : RState}
    (typed : MachineTyped root rootTy w m) :
    m.fiber? ⟨m.nextId⟩ = none ∧ w.Γ ⟨m.nextId⟩ = none := by
  have sched := typed.typed.2.2.2.1
  have wide := typed.wide
  have absent : ⟨m.nextId⟩ ∉ m.fibers.map (·.id) := by
    intro h
    obtain ⟨f, hf, hid⟩ := List.mem_map.mp h
    have below := sched.fibersBelow f hf
    rw [hid] at below
    exact Nat.lt_irrefl _ below
  refine ⟨?_, ?_⟩
  · cases hf : m.fiber? ⟨m.nextId⟩ with
    | none => rfl
    | some f =>
      exact absurd (List.mem_map.mpr ⟨f, rfiber?_mem hf, rfiber?_id hf⟩) absent
  · cases hd : w.Γ ⟨m.nextId⟩ with
    | none => rfl
    | some t => exact absurd ((wide.fibers _).mp (by rw [hd]; rfl)) absent

/-! ## Transports of the clauses across one allocation -/

section Transport
variable {root : ProgramSource} {w w' : World} {m m' : RState} {n : FiberId}
  (ord : w.leHost w') (ext : ∀ id t, w.Γ id = some t → w'.Γ id = some t)
  (back : ∀ id t, w'.Γ id = some t → id ≠ n → w.Γ id = some t) (hΘ : w'.Θ = w.Θ)

omit ord back hΘ in
include ext in
theorem fiberColumnsBelow_ext {id : FiberId} {a e : Ty} (h : FiberColumnsBelow w id a e) :
    FiberColumnsBelow w' id a e := by
  obtain ⟨t, declared, ha, he⟩ := h
  exact ⟨t, ext _ _ declared, ha, he⟩

omit ext back in
include ord hΘ in
theorem racePayload_alloc {race : RRace} {resultTy : EffTy} (h : RacePayload root w race resultTy) :
    RacePayload root w' race resultTy := by
  refine ⟨by rw [hΘ]; exact h.token, strongExit_mono _ _ _ _ ord h.failures,
    fun pair hp => fits_mono ord (h.winner pair hp),
    fun ex hx => strongExit_mono _ _ _ _ ord (h.accepted ex hx),
    fun wait hw => strongExit_mono _ _ _ _ ord (h.cleanup wait hw),
    fun id hid => by
      obtain ⟨t, declared, ha, he⟩ := h.live id hid
      exact ⟨t, ord.1.2.1 _ _ declared, ha, he⟩,
    fun code hc => ?_⟩
  obtain ⟨cty, typed, ha, he⟩ := h.programs code hc
  exact ⟨cty, typedProg_mono root w w' cty code ord typed, ha, he⟩

omit back in
include ord ext hΘ in
/-- A countdown at a waiter whose lookup is unchanged and whose pending targets avoid the fresh
id, or at the fresh fiber, which has no pending record. -/
theorem countdownAt_alloc {waiter : FiberId} {token : Nat} {incoming incoming' : Ty → Ty → Prop}
    (hin : ∀ a e, incoming a e → incoming' a e)
    (lookup : m'.fiber? waiter = m.fiber? waiter ∨
      (m.fiber? waiter = none ∧ ∀ f, m'.fiber? waiter = some f → f.pending = []))
    (fibers : ∀ id, id ≠ n → m'.fiber? id = m.fiber? id)
    (targets : ∀ f, m.fiber? waiter = some f → ∀ p ∈ f.pending,
      ∀ id ∈ p.waitingOn.toList ++ p.remaining, id ≠ n)
    (h : CountdownAt w m waiter token incoming) : CountdownAt w' m' waiter token incoming' := by
  rcases lookup with same | ⟨absent, empty⟩
  · unfold CountdownAt at h ⊢
    rw [same]
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
        have member : pending ∈ fiber.pending := List.mem_of_find?_eq_some hp
        refine ⟨answer, error, tokenTy, ⟨by rw [hΘ]; exact payload.token,
          fun ex hx => strongExit_mono _ _ _ _ ord (payload.collected ex hx), ?_, ?_⟩,
          hin answer error incomingOk⟩
        · intro id hid target hlook
          have ne := targets fiber hf pending member id hid
          rw [fibers id ne] at hlook
          exact fiberColumnsBelow_ext ext (payload.targets id hid target hlook)
        · have resume := payload.resume
          split at resume
          · exact resume
          · exact resume
          · exact strongExit_mono _ _ _ _ ord resume
          · exact strongExit_mono _ _ _ _ ord resume
  · unfold CountdownAt
    cases hf : m'.fiber? waiter with
    | none => trivial
    | some fiber =>
      dsimp only
      rw [empty fiber hf]
      trivial

end Transport

/-! ## The allocation of one spawned child -/

section Spawn
variable {root : ProgramSource} {rootTy : EffTy} {w : World} {m : RState} {record : ForkRecord}
  {program : RProgram} {flag : Bool} {budget : Nat × Bool} {ctx : Ctx} {ty : EffTy} {q : List RCmd}

/-- The fiber `spawn` appends (`Machine/Fibers.lean:958-959`). -/
abbrev spawnChild (m : RState) (program : RProgram) (flag : Bool) (budget : Nat × Bool)
    (ctx : Ctx) : RFiber :=
  RunFiber.make ⟨m.nextId⟩ program flag budget ctx

theorem ne_next {id : FiberId} (below : id.value < m.nextId) : id ≠ ⟨m.nextId⟩ := fun same => by
  rw [same] at below
  exact Nat.lt_irrefl _ below

theorem storedObserverOk_alloc (typed : MachineTyped root rootTy w m) {x : RFiber}
    (hx : x ∈ m.fibers) {o : Observer} (ho : o ∈ x.observers)
    (h : StoredObserverOk root w m x.id o) :
    StoredObserverOk root (w.addFiber ⟨m.nextId⟩ ty)
      (allocR m (spawnChild m program flag budget ctx) record) x.id o := by
  have sched := typed.typed.2.2.2.1
  have freshΓ := (fresh_of_typed typed).2
  have ord : w.leHost (w.addFiber ⟨m.nextId⟩ ty) := addFiber_leHost freshΓ
  have ext : ∀ id t, w.Γ id = some t → (w.addFiber ⟨m.nextId⟩ ty).Γ id = some t :=
    fun _ _ h => addFiber_extends freshΓ h
  have back : ∀ id t, (w.addFiber ⟨m.nextId⟩ ty).Γ id = some t → id ≠ ⟨m.nextId⟩ →
      w.Γ id = some t := fun _ _ h ne => by rwa [addFiber_Γ_other (Ne.symm ne)] at h
  have fibers : ∀ id, id ≠ ⟨m.nextId⟩ →
      (allocR m (spawnChild m program flag budget ctx) record).fiber? id = m.fiber? id :=
    fun _ ne => allocR_fiber_other (Ne.symm ne)
  cases o with
  | resumeAwait waiter token mode =>
    obtain ⟨sourceTy, declared, token'⟩ := h
    exact ⟨sourceTy, ext _ _ declared, token'⟩
  | countdown waiter token =>
    have below := sched.observersBelow x hx _ ho (waiter, token) (List.mem_singleton_self _)
    exact countdownAt_alloc ord ext rfl (fun _ _ hc => fiberColumnsBelow_ext ext hc)
      (.inl (fibers waiter (ne_next below))) fibers
      (fun f hf p hp id hid => ne_next (sched.targetsBelow f (rfiber?_mem hf) p hp id hid)) h
  | raceCallback raceId =>
    unfold StoredObserverOk at h ⊢
    dsimp only at h ⊢
    rw [allocR_race]
    split at h
    · trivial
    · rename_i race found
      obtain ⟨resultTy, payload, live⟩ := h
      exact ⟨resultTy, racePayload_alloc ord rfl payload,
        fun hl => fiberColumnsBelow_ext ext (live hl)⟩
  | dropScopeFinalizer scope key => exact h
  | untrackChild parent => trivial
  | callback key => trivial

theorem observerCommandOk_alloc (typed : MachineTyped root rootTy w m) {source : FiberId}
    {exit : ExitV} {o : Observer} (h : ObserverCommandOk root w m source exit o) :
    ObserverCommandOk root (w.addFiber ⟨m.nextId⟩ ty)
      (allocR m (spawnChild m program flag budget ctx) record) source exit o := by
  have sched := typed.typed.2.2.2.1
  have fresh := fresh_of_typed typed
  have ord : w.leHost (w.addFiber ⟨m.nextId⟩ ty) := addFiber_leHost fresh.2
  have ext : ∀ id t, w.Γ id = some t → (w.addFiber ⟨m.nextId⟩ ty).Γ id = some t :=
    fun _ _ h => addFiber_extends fresh.2 h
  have back : ∀ id t, (w.addFiber ⟨m.nextId⟩ ty).Γ id = some t → id ≠ ⟨m.nextId⟩ →
      w.Γ id = some t := fun _ _ h ne => by rwa [addFiber_Γ_other (Ne.symm ne)] at h
  have fibers : ∀ id, id ≠ ⟨m.nextId⟩ →
      (allocR m (spawnChild m program flag budget ctx) record).fiber? id = m.fiber? id :=
    fun _ ne => allocR_fiber_other (Ne.symm ne)
  cases o with
  | resumeAwait waiter token mode =>
    obtain ⟨sourceTy, declared, token', typedExit⟩ := h
    exact ⟨sourceTy, ext _ _ declared, token', strongExit_mono _ _ _ _ ord typedExit⟩
  | countdown waiter token =>
    have lookup : (allocR m (spawnChild m program flag budget ctx) record).fiber? waiter =
          m.fiber? waiter ∨
        (m.fiber? waiter = none ∧ ∀ f, (allocR m (spawnChild m program flag budget ctx)
          record).fiber? waiter = some f → f.pending = []) := by
      by_cases same : waiter = ⟨m.nextId⟩
      · subst same
        refine .inr ⟨fresh.1, fun f hf => ?_⟩
        have self : (allocR m (spawnChild m program flag budget ctx) record).fiber? ⟨m.nextId⟩ =
            some (spawnChild m program flag budget ctx) := allocR_fiber_self fresh.1
        rw [self] at hf
        cases hf
        rfl
      · exact .inl (fibers waiter same)
    exact countdownAt_alloc ord ext rfl (fun _ _ hc => strongExit_mono _ _ _ _ ord hc) lookup
      fibers
      (fun f hf p hp id hid => ne_next (sched.targetsBelow f (rfiber?_mem hf) p hp id hid)) h
  | raceCallback raceId =>
    unfold ObserverCommandOk at h ⊢
    dsimp only at h ⊢
    rw [allocR_race]
    split at h
    · trivial
    · rename_i race found
      obtain ⟨resultTy, payload, live⟩ := h
      exact ⟨resultTy, racePayload_alloc ord rfl payload,
        fun hl => strongExit_mono _ _ _ _ ord (live hl)⟩
  | dropScopeFinalizer scope key => exact h
  | untrackChild parent => trivial
  | callback key => trivial

theorem enrollRaceOk_alloc (typed : MachineTyped root rootTy w m) {raceId : Nat}
    {c : FiberId} (h : EnrollRaceOk root w m raceId c) :
    EnrollRaceOk root (w.addFiber ⟨m.nextId⟩ ty)
      (allocR m (spawnChild m program flag budget ctx) record) raceId c := by
  have sched := typed.typed.2.2.2.1
  have fresh := fresh_of_typed typed
  obtain ⟨below, h⟩ := h
  refine ⟨Nat.lt_succ_of_lt below, ?_⟩
  rw [allocR_race, allocR_fiber_other (Ne.symm (ne_next below))]
  split at h
  · rename_i race fiber found _
    obtain ⟨resultTy, payload, cols⟩ := h
    exact ⟨resultTy, racePayload_alloc (addFiber_leHost fresh.2) rfl payload,
      fiberColumnsBelow_ext (fun _ _ h => addFiber_extends fresh.2 h) cols⟩
  · trivial

theorem internalKeys_allocR :
    Guard.internalKeys (allocR m (spawnChild m program flag budget ctx) record) =
      Guard.internalKeys m := by
  have child : List.flatMap Guard.observerKeys (spawnChild m program flag budget ctx).observers ++
      List.flatMap (fun b => List.flatMap Guard.taskKeys b.tasks)
        (spawnChild m program flag budget ctx).dispatcher.buckets = [] := rfl
  simp only [Guard.internalKeys, allocR, List.flatMap_append, List.flatMap_cons, List.flatMap_nil,
    List.append_nil, child]

theorem machineWide_alloc (typed : MachineTyped root rootTy w m) :
    MachineWide root rootTy (w.addFiber ⟨m.nextId⟩ ty)
      (allocR m (spawnChild m program flag budget ctx) record) := by
  have wide := typed.wide
  have sched := typed.typed.2.2.2.1
  have fresh := fresh_of_typed typed
  have ord : w.leHost (w.addFiber ⟨m.nextId⟩ ty) := addFiber_leHost fresh.2
  have back : ∀ id t, (w.addFiber ⟨m.nextId⟩ ty).Γ id = some t → id ≠ ⟨m.nextId⟩ →
      w.Γ id = some t := fun _ _ h ne => by rwa [addFiber_Γ_other (Ne.symm ne)] at h
  have exists_below : ∀ id f, m.fiber? id = some f → id.value < m.nextId := fun id f hf => by
    rw [← rfiber?_id hf]
    exact sched.fibersBelow f (rfiber?_mem hf)
  have absent : ⟨m.nextId⟩ ∉ m.fibers.map (·.id) := by
    intro h
    obtain ⟨f, hf, hid⟩ := List.mem_map.mp h
    have below := sched.fibersBelow f hf
    rw [hid] at below
    exact Nat.lt_irrefl _ below
  refine ⟨?_, ?_, wide.heap, wide.promises, wide.tokenBound, ?_, wide.state, wide.wf, ?_,
    addFiber_extends fresh.2 wide.rootDeclared,
    ?_, storesOk_world ord rfl rfl rfl wide.stores, ?_, wide.raceIds, wide.racesBelow, ?_, ?_, ?_, ?_,
    wide.services, ⟨wide.live.running, ?_⟩, wide.timers, wide.waiters,
    fun r race h id hid => Nat.lt_succ_of_lt (wide.liveBelow r race h id hid), wide.sourceWF⟩
  · show w.ids ++ [⟨m.nextId⟩] = (m.fibers ++ [spawnChild m program flag budget ctx]).map (·.id)
    rw [List.map_append, ← wide.ids]
    rfl
  · intro id
    show ((w.addFiber ⟨m.nextId⟩ ty).Γ id).isSome = true ↔
      id ∈ (m.fibers ++ [spawnChild m program flag budget ctx]).map (·.id)
    rw [List.map_append, List.mem_append]
    by_cases same : id = ⟨m.nextId⟩
    · subst same
      rw [addFiber_Γ_self]
      exact ⟨fun _ => .inr (List.mem_singleton_self _), fun _ => rfl⟩
    · rw [addFiber_Γ_other (Ne.symm same), wide.fibers id]
      refine ⟨.inl, fun h => h.elim (fun x => x) fun h' => absurd (List.mem_singleton.mp h') same⟩
  · intro id token t h
    obtain ⟨t', ht'⟩ := Option.isSome_iff_exists.mp (wide.tokenTargets id token t h)
    rw [addFiber_extends fresh.2 ht']
    rfl
  · exact ⟨(fork_extension w _ ty fresh.2).2.2.1 wide.cells.1,
      (fork_extension w _ ty fresh.2).2.2.2.1 wide.cells.2⟩
  · intro r hr
    obtain ⟨resultTy, payload⟩ := wide.races r hr
    exact ⟨resultTy, racePayload_alloc ord rfl payload⟩
  · show ((m.fibers ++ [spawnChild m program flag budget ctx]).map RunFiber.id).Nodup
    rw [List.map_append]
    refine List.nodup_append.mpr ⟨wide.fiberIds, List.nodup_cons.mpr ⟨List.not_mem_nil, List.nodup_nil⟩,
      fun a ha b hb same => absent ?_⟩
    change b ∈ [(spawnChild m program flag budget ctx).id] at hb
    rw [List.mem_singleton] at hb
    subst hb
    subst same
    exact ha
  · intro r hr
    obtain ⟨f, hf⟩ := wide.raceHosts r hr
    exact ⟨f, by rw [allocR_fiber_other (Ne.symm (ne_next (exists_below _ _ hf)))]; exact hf⟩
  · intro k hk
    rw [internalKeys_allocR] at hk
    exact wide.keysBelow k hk
  · intro fiber token r hr
    rw [allocR_requestOfR rfl fresh.1] at hr
    exact wide.requestsBelow fiber token r hr
  · intro fiber token r hr
    rw [allocR_requestOfR rfl fresh.1] at hr
    rw [internalKeys_allocR]
    exact wide.requestsOwned fiber token r hr
  · intro o ho owner priority mode
    obtain ⟨f, hf⟩ := Option.isSome_iff_exists.mp (wide.live.dueOwners o ho owner priority mode)
    rw [allocR_fiber_other (Ne.symm (ne_next (exists_below _ _ hf))), hf]
    rfl

/-- An old fiber keeps its per-fiber clauses across the allocation: its own declaration reflects
back (its id is below `nextId`), and its observers' read sites avoid the fresh id. -/
theorem fiberTyped_alloc (typed : MachineTyped root rootTy w m) {x : RFiber} (hx : x ∈ m.fibers) :
    FiberTyped root (w.addFiber ⟨m.nextId⟩ ty)
      (allocR m (spawnChild m program flag budget ctx) record) x := by
  have old := typed.fiber hx
  have fresh := fresh_of_typed typed
  have ord : w.leHost (w.addFiber ⟨m.nextId⟩ ty) := addFiber_leHost fresh.2
  have ne : (⟨m.nextId⟩ : FiberId) ≠ x.id := Ne.symm (ne_next old.below)
  have kept : RacesKept m (allocR m (spawnChild m program flag budget ctx) record) :=
    racesKept_of_eq fun r => allocR_race r
  obtain ⟨⟨c0⟩, c1, c2, c3, ⟨c4⟩, c5⟩ := old.ok
  refine ⟨⟨⟨fun ty' declared => ?_⟩, c1, fun v hv ty' declared => ?_, fun v hv ty' declared => ?_,
      ⟨fun b hb => ⟨fun t ht => ?_⟩⟩, servicesFit_mono ord c5⟩,
    fun token hp => ?_, Nat.lt_succ_of_lt old.below, old.pendingShape, old.parkedIdle,
    old.parkedBelow, old.exited, old.exitedStack, old.deferredCause, old.pendingOwner,
    fun o ho => storedObserverOk_alloc typed hx ho (old.observers o ho),
    fun raceId marker => ?_, fun hx' hr hm hp ty' declared => ?_, old.tokens, old.raceObservers,
    fun p hp id hid => Nat.lt_succ_of_lt (old.targetsBelow p hp id hid),
    fun o ho k hk => Nat.lt_succ_of_lt (old.observersBelow o ho k hk),
    fun c hc => let ⟨t, ht⟩ := Option.isSome_iff_exists.mp (old.children c hc)
      Option.isSome_iff_exists.mpr ⟨t, addFiber_extends fresh.2 ht⟩⟩
  · change (w.addFiber ⟨m.nextId⟩ ty).Γ x.id = some ty' at declared
    rw [addFiber_Γ_other ne] at declared
    obtain ⟨tin, stack, provenance⟩ := c0 ty' declared
    exact ⟨tin, positionStack_mono ord stack, provenance⟩
  · change (w.addFiber ⟨m.nextId⟩ ty).Γ x.id = some ty' at declared
    rw [addFiber_Γ_other ne] at declared
    exact strongExit_mono _ _ _ _ ord (c2 v hv ty' declared)
  · change (w.addFiber ⟨m.nextId⟩ ty).Γ x.id = some ty' at declared
    rw [addFiber_Γ_other ne] at declared
    exact strongExit_mono _ _ _ _ ord (c3 v hv ty' declared)
  · have task := (c4 b hb).c0 t ht
    cases t with
    | resume target token code => exact resumeOk_world ord rfl task
    | start _ => trivial
    | wake _ _ => trivial
  · obtain ⟨tin, final, declared, final', stack, provenance⟩ := old.delivery token hp
    exact ⟨tin, final, declared, addFiber_extends fresh.2 final',
      hostStack_mono ord (hostStack_races kept stack), provenance⟩
  · obtain ⟨race, resultTy, found, host, token, final, declared, stack, provenance⟩ :=
      old.registration raceId marker
    exact ⟨race, resultTy, found, host, token, final, addFiber_extends fresh.2 declared,
      hostStack_mono ord (hostStack_races kept stack), provenance⟩
  · rw [addFiber_Γ_other ne] at declared
    exact codeOk_mono ord (codeOk_races kept (old.code hx' hr hm hp ty' declared))

/-- The spawned child's per-fiber clauses: idle, unparked, no pending record, observer or exit,
an empty stack, its typed code at its declaration. -/
theorem fiberTyped_child (typed : MachineTyped root rootTy w m) (code : TypedProg root w ty program)
    (services : ServicesFit w ctx.services) :
    FiberTyped root (w.addFiber ⟨m.nextId⟩ ty)
      (allocR m (spawnChild m program flag budget ctx) record) (spawnChild m program flag budget ctx) := by
  have fresh := fresh_of_typed typed
  have ord : w.leHost (w.addFiber ⟨m.nextId⟩ ty) := addFiber_leHost fresh.2
  have prov : InterruptProvenance (spawnChild m program flag budget ctx).frame :=
    ⟨(fun _ h => nomatch h), (fun h => nomatch h)⟩
  have declaredOnly : ∀ ty', (w.addFiber ⟨m.nextId⟩ ty).Γ ⟨m.nextId⟩ = some ty' → ty' = ty :=
    fun ty' h => by
      rw [addFiber_Γ_self] at h
      cases h
      rfl
  refine ⟨⟨⟨fun ty' d => ?_⟩, (fun _ h => nomatch h), (fun _ h => nomatch h),
      (fun _ h => nomatch h), ⟨fun _ h => nomatch h⟩, servicesFit_mono ord services⟩,
    (fun _ h => nomatch h), Nat.lt_succ_self _, rfl, (fun h => absurd rfl h), (fun _ h => nomatch h),
    (fun h => nomatch h), (fun h => nomatch h), (fun h => nomatch h), (fun _ h => nomatch h),
    (fun _ h => nomatch h), (fun _ marker => ?_), (fun _ _ _ _ ty' d => ?_), (fun _ h => nomatch h),
    (fun _ _ _ _ h => nomatch h), (fun _ h => nomatch h), (fun _ h => nomatch h),
    (fun _ h => nomatch h)⟩
  · rw [declaredOnly ty' d]
    exact ⟨ty, .nil ty, prov⟩
  · rw [show (spawnChild m program flag budget ctx).frame.current = program from rfl,
      raceRegistrationR_typed code] at marker
    cases marker
  · rw [declaredOnly ty' d]
    exact ⟨ty, typedProg_mono root w _ ty program ord code, .nil ty, prov⟩

theorem readCode_alloc (typed : ConfigTyped root rootTy w m q) :
    ReadCode root (w.addFiber ⟨m.nextId⟩ ty)
      (allocR m (spawnChild m program flag budget ctx) record) q := by
  have fresh := fresh_of_typed typed.machine
  have ord : w.leHost (w.addFiber ⟨m.nextId⟩ ty) := addFiber_leHost fresh.2
  have kept : RacesKept m (allocR m (spawnChild m program flag budget ctx) record) :=
    racesKept_of_eq fun r => allocR_race r
  intro f hf running reads marker ty' declared
  rcases List.mem_append.mp hf with hold | hnew
  · have ne : (⟨m.nextId⟩ : FiberId) ≠ f.id :=
      Ne.symm (ne_next ((typed.machine.fiber hold).below))
    rw [addFiber_Γ_other ne] at declared
    exact codeOk_mono ord (codeOk_races kept (typed.code f hold running reads marker ty' declared))
  · rw [List.mem_singleton] at hnew
    subst hnew
    cases running

/-- A fiber the typed machine finds has an id below `nextId`. -/
theorem below_of_lookup (typed : MachineTyped root rootTy w m) {id : FiberId} {f : RFiber}
    (h : m.fiber? id = some f) : id.value < m.nextId := by
  have below := typed.typed.2.2.2.1.fibersBelow f (rfiber?_mem h)
  rwa [rfiber?_id h] at below

/-- An old fiber's lookup survives the allocation. -/
theorem allocR_fiber_old (typed : MachineTyped root rootTy w m) {id : FiberId} {f : RFiber}
    (h : m.fiber? id = some f) :
    (allocR m (spawnChild m program flag budget ctx) record).fiber? id = some f := by
  rw [allocR_fiber_other (Ne.symm (ne_next (below_of_lookup typed h)))]
  exact h

theorem commandAuthority_alloc (typed : MachineTyped root rootTy w m) {c : RCmd}
    (h : CommandAuthorityR m c) :
    CommandAuthorityR (allocR m (spawnChild m program flag budget ctx) record) c :=
  commandAuthority_mono (fun _ _ hf => allocR_fiber_old typed hf) (fun _ => rfl) h

/-- A command's payload at the extended world: the two antitone reads (a queued `finish`'s fiber,
a queued observer's source) name ids below `nextId`, whose declarations the allocation leaves
unchanged. -/
theorem rcmdOk_alloc (typed : MachineTyped root rootTy w m) {c : RCmd}
    (authority : CommandAuthorityR m c)
    (source : ∀ s e o, c = .observe s e o → s.value < m.nextId) (h : RCmdOk (preds root) w c) :
    RCmdOk (preds root) (w.addFiber ⟨m.nextId⟩ ty) c := by
  have ord : w.leHost (w.addFiber ⟨m.nextId⟩ ty) := addFiber_leHost (fresh_of_typed typed).2
  cases c with
  | finish fiber exit =>
    obtain ⟨f, hf, _, _⟩ := authority
    intro ty' declared
    change (w.addFiber ⟨m.nextId⟩ ty).Γ fiber = some ty' at declared
    rw [addFiber_Γ_other (Ne.symm (ne_next (below_of_lookup typed hf)))] at declared
    exact strongExit_mono _ _ _ _ ord (h ty' declared)
  | observe fiber exit observer =>
    intro ty' declared
    change (w.addFiber ⟨m.nextId⟩ ty).Γ fiber = some ty' at declared
    rw [addFiber_Γ_other (Ne.symm (ne_next (source fiber exit observer rfl)))] at declared
    exact strongExit_mono _ _ _ _ ord (h ty' declared)
  | resume target token code => exact resumeOk_world ord rfl h
  | _ => trivial

/-- A command's delivery facts across the allocation: its owner is found, so old
(`commandDelivery_mono`). -/
theorem commandDelivery_alloc (typed : MachineTyped root rootTy w m) {c : RCmd}
    (authority : CommandAuthorityR m c) (h : CommandDeliveryOk root w m c) :
    CommandDeliveryOk root (w.addFiber ⟨m.nextId⟩ ty)
      (allocR m (spawnChild m program flag budget ctx) record) c := by
  have fresh := fresh_of_typed typed
  refine commandDelivery_mono (addFiber_leHost fresh.2) (fun _ _ h => addFiber_extends fresh.2 h)
    (racesKept_of_eq fun r => allocR_race r) (fun o ho => ?_) h
  obtain ⟨_, hf⟩ := commandOwner_found authority ho
  exact allocR_fiber_other (Ne.symm (ne_next (below_of_lookup typed hf)))

theorem queueOk_alloc (typed : ConfigTyped root rootTy w m q) :
    QueueOk root (w.addFiber ⟨m.nextId⟩ ty)
      (allocR m (spawnChild m program flag budget ctx) record) q := by
  have machine := typed.machine
  have queue := typed.queue
  have fresh := fresh_of_typed machine
  refine ⟨fun c hc => rcmdOk_alloc machine (queue.authority c hc)
      (fun s e o h => (queue.observer s e o (h ▸ hc)).1) (queue.payload c hc),
    fun c hc => commandAuthority_alloc machine (queue.authority c hc),
    fun c hc => commandDelivery_alloc machine (queue.authority c hc) (queue.delivery c hc),
    queue.owners, queue.registration,
    ⟨queue.keys.below, fun fiber token r hr hk => queue.keys.disjoint fiber token r
      (by rw [allocR_requestOfR rfl fresh.1] at hr; exact hr) hk⟩,
    fun s e o ho => ⟨Nat.lt_succ_of_lt (queue.observer s e o ho).1,
      observerCommandOk_alloc machine (queue.observer s e o ho).2⟩,
    fun r c hc => enrollRaceOk_alloc machine (queue.enroll r c hc), queue.noRaceAfterInterrupt,
    fun md sc tg ir ex hl => ?_, queue.raceObservers⟩
  obtain ⟨live, present⟩ := queue.links md sc tg ir ex hl
  refine ⟨live, ?_⟩
  cases hf : m.fiber? tg with
  | none => rw [hf] at present; cases present
  | some f => rw [allocR_fiber_old machine hf]; rfl

/-- **The allocation keeps `I`**: the queue unchanged, the world extended by the child's
declaration at a closed type its code is typed at. -/
theorem configTyped_alloc (typed : ConfigTyped root rootTy w m q)
    (code : TypedProg root w ty program) (services : ServicesFit w ctx.services) :
    ConfigTyped root rootTy (w.addFiber ⟨m.nextId⟩ ty)
      (allocR m (spawnChild m program flag budget ctx) record) q := by
  refine ⟨machineTyped_of (machineWide_alloc typed.machine) fun f hf => ?_,
    readCode_alloc typed, queueOk_alloc typed⟩
  rcases List.mem_append.mp hf with hold | hnew
  · exact fiberTyped_alloc typed.machine hold
  · rw [List.mem_singleton] at hnew
    subst hnew
    exact fiberTyped_child typed.machine code services

end Spawn

/-! ## The launch step -/

section Step
variable {root : ProgramSource} {rootTy : EffTy} {w : World} {m : RState} {q : List RCmd}

/-- **An entrant's enrollment joins the queue**: the race exists with an active host, the child is
below `nextId` with its columns below the race's result type, and the race's registration
completion is still queued. -/
theorem configTyped_cons_enroll (typed : ConfigTyped root rootTy w m q) {raceId : Nat}
    {race : RRace} {child : FiberId} {c : RFiber} {resultTy : EffTy}
    (hr : m.race? raceId = some race) (hc : m.fiber? child = some c)
    (active : Guard.ActiveAt m race.host) (below : child.value < m.nextId)
    (payload : RacePayload root w race resultTy)
    (cols : FiberColumnsBelow w c.id resultTy.answer resultTy.error)
    (registration : ∃ yielding, .registrationDone raceId yielding ∈ q) :
    ConfigTyped root rootTy w m (.enrollRace raceId child :: q) := by
  refine ⟨typed.machine, readCode_cons (fun _ _ h => nomatch h) (fun _ _ h => nomatch h) typed.code,
    queueOk_cons ⟨trivial, ⟨race, hr, active⟩, trivial, (fun _ h => nomatch h), registration,
      (fun _ h => nomatch h), (fun _ _ _ _ h => nomatch h), (fun _ _ _ h => nomatch h),
      (fun r ch h => ?_), (fun _ _ _ h => nomatch h), (fun _ _ _ _ _ h => nomatch h),
      (fun _ _ _ h => nomatch h)⟩ typed.queue⟩
  cases h
  unfold EnrollRaceOk
  rw [hr, hc]
  exact ⟨below, resultTy, payload, cols⟩

/-- The launch arm's machine edits after the allocation (a trace event, the race edit, a trace
event) leave every fiber lookup alone. -/
theorem fiber?_launched (m : RState) (new : RRace)
    (e₁ e₂ : List (RunEvent EffName EffThunk Val Err Defect FiberId Ann Ctx RProgram Unit))
    (id : FiberId) : (((m.emit e₁).updateRace new).emit e₂).fiber? id = m.fiber? id := rfl

/-- …and find the edited race at its id. -/
theorem race?_launched {m : RState} {raceId : Nat} {race new : RRace}
    (hr : m.race? raceId = some race) (hid : new.id = race.id)
    (e₁ e₂ : List (RunEvent EffName EffThunk Val Err Defect FiberId Ann Ctx RProgram Unit)) :
    (((m.emit e₁).updateRace new).emit e₂).race? raceId = some new := by
  show (m.updateRace new).race? raceId = some new
  rw [rrace?_updateRace, hr, Option.map_some, if_pos hid.symm]

end Step

/-- **`launch` keeps `I`** (`Machine/Fibers.lean:1879-1896`, rc.112 `:1520-1528`): the entrant is
allocated at the old `nextId` and declared at the race's result type (its program, typed at a
type whose columns are below it, widened there; closed because the race token's declaration is),
the race loses that program, and the entrant's evaluation and enrollment are queued ahead of the
next launch. Every other arm leaves the machine and drops the head. -/
theorem launch_preserves (root : ProgramSource) (rootTy : EffTy) (raceId : Nat) :
    StepPreserves root rootTy (.launch raceId) := by
  intro w m rest _ typed
  have tail := configTyped_tail typed
  simp only [driveStep]
  cases hr : m.race? raceId with
  | none => exact ⟨w, leHost_refl w, tail⟩
  | some race =>
    dsimp only
    cases hp : race.programs with
    | nil => exact ⟨w, leHost_refl w, tail⟩
    | cons program more =>
      dsimp only
      cases ha : race.state.accepted.isSome with
      | true => exact ⟨w, leHost_refl w, tail⟩
      | false =>
        simp only [Bool.false_eq_true, ↓reduceIte]
        cases hh : m.fiber? race.host with
        | none => exact ⟨w, leHost_refl w, tail⟩
        | some host =>
          dsimp only [launchEntrant, spawn]
          have machine := typed.machine
          have wide := machine.wide
          have fresh := fresh_of_typed machine
          obtain ⟨race₀, hr₀, active⟩ := typed.queue.authority _ List.mem_cons_self
          rw [hr] at hr₀
          cases hr₀
          obtain ⟨resultTy, payload⟩ := wide.races race (List.mem_of_find?_eq_some hr)
          obtain ⟨childTy, code, subA, subE⟩ :=
            payload.programs program (by rw [hp]; exact List.mem_cons_self)
          obtain ⟨_, _, _, _, _, services⟩ := (machine.fiber (rfiber?_mem hh)).ok
          have ord : w.leHost (w.addFiber ⟨m.nextId⟩ resultTy) := addFiber_leHost fresh.2
          have payload' : RacePayload root (w.addFiber ⟨m.nextId⟩ resultTy) race resultTy :=
            racePayload_alloc ord rfl payload
          let new : RRace :=
            { race with programs := more, nextSite := race.nextSite.map (fun site => site ++ [1]) }
          have payloadNew : RacePayload root (w.addFiber ⟨m.nextId⟩ resultTy) new resultTy :=
            ⟨payload'.token, payload'.failures, payload'.winner, payload'.accepted, payload'.cleanup,
              payload'.live,
              fun code hc => payload'.programs code (by rw [hp]; exact List.mem_cons_of_mem _ hc)⟩
          let child := spawnChild m program true ((interpR root.program).budgetOf host.context)
            host.context
          let record : ForkRecord := ⟨⟨m.nextId⟩, host.id, true, race.nextSite.getD []⟩
          have allocated := configTyped_alloc (record := record) (flag := true)
            (budget := (interpR root.program).budgetOf host.context) typed
            (typedProg_widen root subA subE code) services
          have edited := configTyped_emit (configTyped_updateRace
            (configTyped_emit allocated [RunEvent.forked host.id ⟨m.nextId⟩ true]) (old := race)
            (new := new) (by rw [rrace?_id hr]; exact hr) rfl rfl rfl payloadNew
            (fun _ h => .inl h)) [RunEvent.raceLaunched raceId ⟨m.nextId⟩]
          obtain ⟨yielding, queued⟩ := typed.queue.registration.1
          refine ⟨w.addFiber ⟨m.nextId⟩ resultTy, ord,
            configTyped_cons_evaluate (configTyped_cons_enroll edited
              (race?_launched (m := allocR m child record) (new := new) hr rfl _ _)
              ((fiber?_launched _ new _ _ _).trans (allocR_fiber_self fresh.1))
              (by
                obtain ⟨f, hf, running, parked⟩ := active
                exact ⟨f, allocR_fiber_old (record := record) machine hf, running, parked⟩)
              (Nat.lt_succ_self _) payloadNew
              ⟨resultTy, addFiber_Γ_self, Ty.subN_refl _, Ty.subN_refl _⟩
              ⟨yielding, List.mem_cons_of_mem _ queued⟩) _⟩

end Effect4.Program.Typed

#obligation_proved Effect4.Program.Typed.M6Ledger.step_launch :=
  @Effect4.Program.Typed.launch_preserves
