import Effect4.Laws.Program.Typed.Commands.Observe
import Effect4.Laws.Program.Typed.Body

/-!
# Laws.Program.Typed.Commands.Evaluate — the evaluation step as handler soundness

Concept 4 (the configuration invariant `I`); questions `M6Ledger.step_deliver` and
`M6Ledger.step_loop`. `deliver` settles one evaluation of the fiber's current code
(`Machine/Fibers.lean:1861-1864`) and `loop` settles one after the loop top, the op counter and the
yield injection (`iteration`, `:1650-1656`). The evaluation (`evaluateR`, `Laws/Program/EvaluateR.lean`)
is a handler of the fiber and store signatures `TypedProg` types each operation by: a certificate,
the operation's pre (`fiberPre`, the store row's pre) and a continuation typed at every answer its
post admits at every later world. So preservation is handler soundness (Plotkin–Pretnar): each
operation clause meets its contract, and the step is the clauses' case split plus `settle`. This
module proves it in that shape, one clause at a time; the stack walk is `HostWalk`'s
(`deliverR_hostTyped` over `popR_typed`), the store clauses are seat B's `StoreImplements`.

This file's first layer: a running fiber's frame may move under the queued `loop` or `deliver` that
owns it, because the only queued commands whose delivery reads a fiber's stack own that fiber, and
the queue holds one owner per fiber (`QueueOk.owners`).

Not established here: the clauses the receipt lists open (`scoped`, the generator and loop
entries, the race registration, the fiber actions, the store rows, the walk), `loop`'s prefix,
progress.
-/

set_option autoImplicit false
namespace Effect4.Program.Typed
open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Sched Effect4.Program.Denote
open Contracts

/-! ## The frame of the fiber a queued `loop` or `deliver` owns -/

/-- Every fiber but `id` keeps its stack and provenance from `m` to `m'`. -/
def StackViewExcept (m m' : RState) (id : FiberId) : Prop :=
  ∀ i f', i ≠ id → m'.fiber? i = some f' → ∃ f, m.fiber? i = some f ∧ f'.id = f.id ∧
    f'.frame.stack = f.frame.stack ∧ (InterruptProvenance f.frame → InterruptProvenance f'.frame)

/-- Editing fiber `g` keeps every other fiber's stack. -/
theorem stackViewExcept_rupdate {m : RState} {f g : RFiber} (hid : g.id = f.id) :
    StackViewExcept m (m.update g) f.id := by
  intro i f' hi hf'
  rw [rfiber?_update_other (fun h => hi (h.trans hid))] at hf'
  exact ⟨f', hf', rfl, rfl, id⟩

/-- **A queued command not owned by `id` keeps its delivery judgment when only fiber `id`'s stack
moves**: the four deliveries that read a stack (`afterInterrupt`, `raceCancel`, `closeParAwait`,
`finish`) read their owner's. -/
theorem commandDelivery_stack_except {root : ProgramSource} {w : World} {m m' : RState} {id : FiberId}
    (view : StackViewExcept m m' id) (kept : RacesKept m m') (c : RCmd)
    (owner : Guard.commandOwner m c ≠ some id) (h : CommandDeliveryOk root w m c) :
    CommandDeliveryOk root w m' c := by
  cases c with
  | afterInterrupt host _ kind =>
    intro f' hf'
    obtain ⟨f, hf, hid, hstack, hprov⟩ := view host f' (fun e => owner (by rw [e]; rfl)) hf'
    obtain ⟨replyTy, ok, stack⟩ := h f hf
    exact ⟨replyTy, ok, stackReply_view kept hid hstack hprov stack⟩
  | raceCancel _ host _ remaining visited =>
    intro f' hf'
    obtain ⟨f, hf, hid, hstack, hprov⟩ := view host f' (fun e => owner (by rw [e]; rfl)) hf'
    obtain ⟨answer, error, cols, stack⟩ := h f hf
    exact ⟨answer, error, cols, stackReply_view kept hid hstack hprov stack⟩
  | closeParAwait host _ targets =>
    intro f' hf'
    obtain ⟨f, hf, hid, hstack, hprov⟩ := view host f' (fun e => owner (by rw [e]; rfl)) hf'
    obtain ⟨answer, error, cols, protocol, stack⟩ := h f hf
    exact ⟨answer, error, cols, protocol, stackReply_view kept hid hstack hprov stack⟩
  | finish host _ =>
    intro f' hf'
    obtain ⟨f, hf, _, hstack, _⟩ := view host f' (fun e => owner (by rw [e]; rfl)) hf'
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

/-- **A fiber edit that may move the fiber's frame keeps `I`** when no queued command owns the
fiber: `configTyped_rupdate_code` without its stack premise, the queue's deliveries transported by
`commandDelivery_stack_except`. -/
theorem configTyped_rupdate_frame {root : ProgramSource} {rootTy : EffTy} {w : World} {m : RState}
    {q : List RCmd} {f g : RFiber} (typed : ConfigTyped root rootTy w m q)
    (hf : m.fiber? f.id = some f) (hid : g.id = f.id) (pending : PendingWeaker f.pending g.pending)
    (free : ∀ c ∈ q, Guard.commandOwner m c ≠ some f.id)
    (keys : ∀ k ∈ Guard.fiberKeys g, k ∈ Guard.internalKeys m ∨
      (k.2 < m.nextToken ∧ requestOfR m k.1 k.2 = none))
    (request : ∀ token r, requestOfR (m.update g) g.id token = some r →
      requestOfR m f.id token = some r)
    (auth : ∀ c ∈ q, CommandAuthorityR m c → CommandAuthorityR (m.update g) c)
    (readG : g.running = true → ReadsCode g.id q → raceRegistrationR g.frame.current = none →
      ∀ ty, w.Γ g.id = some ty → CodeOk root w (m.update g) g.id ty g.frame)
    (fresh : FiberTyped root w (m.update g) g) : ConfigTyped root rootTy w (m.update g) q := by
  have view : ObsView m (m.update g) := obsView_rupdate hf hid pending
  obtain ⟨machine, code, queue⟩ := typed
  refine ⟨machineTyped_of (machineWide_rupdate machine.wide hid keys request) (fun x hx => ?_),
    ?_, queueOk_transport queue view (Nat.le_refl _) auth
      (fun c hc h => commandDelivery_stack_except (stackViewExcept_rupdate hid)
        (racesKept_of_eq view.races) c (free c hc) h) ?_ (Nat.le_refl _)⟩
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

/-- The fiber the head `loop` or `deliver` owns is owned by no command of the rest. -/
theorem owner_free_rest {root : ProgramSource} {w : World} {m : RState} {c : RCmd} {rest : List RCmd}
    (queue : QueueOk root w m (c :: rest)) {o : FiberId} (owner : Guard.commandOwner m c = some o) :
    ∀ d ∈ rest, Guard.commandOwner m d ≠ some o := by
  intro d hd same
  exact owner_free queue owner (List.mem_filterMap.mpr ⟨d, hd, same⟩)

/-- `configTyped_cons_loop`'s twin for a queued `deliver`, the other command that reads code. -/
theorem configTyped_cons_deliver {root : ProgramSource} {rootTy : EffTy} {w : World} {m : RState}
    {q : List RCmd} (typed : ConfigTyped root rootTy w m q) {f : RFiber}
    (hf : m.fiber? f.id = some f) (running : f.running = true) (parked : f.parked = .notParked)
    (free : f.id ∉ q.filterMap (Guard.commandOwner m)) (yielding : Bool)
    (code : raceRegistrationR f.frame.current = none → ∀ ty, w.Γ f.id = some ty →
      CodeOk root w m f.id ty f.frame) :
    ConfigTyped root rootTy w m (.deliver f.id yielding :: q) := by
  have wide := typed.machine.wide
  refine ⟨typed.machine, ?_, queueOk_cons ?_ typed.queue⟩
  · intro x hx run reads marker ty declared
    by_cases same : x.id = f.id
    · have xf : x = f := rfiber?_same hf (rfiber?_of_mem wide.fiberIds hx) same
      rw [xf] at marker declared ⊢
      exact code marker ty declared
    · obtain ⟨y, r⟩ := reads
      refine typed.code x hx run ⟨y, ?_⟩ marker ty declared
      rcases r with r | r
      · rcases List.mem_cons.mp r with h | h
        · cases h
        · exact Or.inl h
      · rcases List.mem_cons.mp r with h | h
        · injection h with hid _
          exact absurd hid same
        · exact Or.inr h
  · refine ⟨trivial, ⟨f, hf, running, parked⟩, trivial, ?_, trivial, (fun _ h => nomatch h),
      (fun _ _ _ _ h => nomatch h), (fun _ _ _ h => nomatch h), (fun _ _ h => nomatch h),
      (fun _ _ _ h => nomatch h), (fun _ _ _ _ _ h => nomatch h), (fun _ _ _ h => nomatch h)⟩
    intro o owner
    cases owner
    exact free

/-- An edit that keeps a fiber's flags keeps every fiber active that was. -/
theorem activeAt_frame {m : RState} {f g : RFiber} (hf : m.fiber? f.id = some f) (hid : g.id = f.id)
    (running : g.running = f.running) (parked : g.parked = f.parked) {id : FiberId}
    (h : Guard.ActiveAt m id) : Guard.ActiveAt (m.update g) id := by
  obtain ⟨x, hx, xr, xp⟩ := h
  by_cases same : id = g.id
  · subst same
    rw [hid] at hx
    have xf : x = f := Option.some.inj (hx.symm.trans hf)
    subst xf
    exact ⟨g, rfiber?_update_self hf hid, running.trans xr, parked.trans xp⟩
  · exact ⟨x, by rw [rfiber?_update_other same]; exact hx, xr, xp⟩

/-- **A frame edit keeps the authority of every queued command it does not own**: the authorities
read flags, which the edit keeps, and `registrationDone` reads its owner's current code. -/
theorem commandAuthority_frame {m : RState} {f g : RFiber} (hf : m.fiber? f.id = some f)
    (hid : g.id = f.id) (running : g.running = f.running) (parked : g.parked = f.parked)
    (exit : g.exit = f.exit) (c : RCmd) (owner : Guard.commandOwner m c ≠ some f.id)
    (h : CommandAuthorityR m c) : CommandAuthorityR (m.update g) c := by
  have act : ∀ {id}, Guard.ActiveAt m id → Guard.ActiveAt (m.update g) id :=
    fun h => activeAt_frame hf hid running parked h
  cases c with
  | loop fiber _ => exact act h
  | deliver fiber _ => exact act h
  | finish fiber _ => exact act h
  | afterInterrupt fiber _ _ => exact act h
  | closeParAwait fiber _ _ => exact act h
  | raceCancel _ fiber _ _ _ => exact act h
  | registrationDone raceId _ =>
    obtain ⟨race, fiber, found, host, fr, fp, marker⟩ := h
    have other : race.host ≠ g.id := by
      intro same
      apply owner
      rw [show Guard.commandOwner m (.registrationDone raceId _) = (m.race? raceId).map Race.host
        from rfl, found, Option.map_some, same, hid]
    exact ⟨race, fiber, found, by rw [rfiber?_update_other other]; exact host, fr, fp, marker⟩
  | launch raceId =>
    obtain ⟨race, found, active⟩ := h
    exact ⟨race, found, act active⟩
  | enrollRace raceId _ =>
    obtain ⟨race, found, active⟩ := h
    exact ⟨race, found, act active⟩
  | exitDone fiber =>
    obtain ⟨x, hx, xe⟩ := h
    by_cases same : fiber = g.id
    · subst same
      rw [hid] at hx
      have xf : x = f := Option.some.inj (hx.symm.trans hf)
      subst xf
      exact ⟨g, rfiber?_update_self hf hid, by rw [exit]; exact xe⟩
    · exact ⟨x, by rw [rfiber?_update_other same]; exact hx, xe⟩
  | evaluate _ => trivial
  | resume _ _ _ => trivial
  | interruptTarget _ _ _ => trivial
  | trackChild _ _ => trivial
  | observe _ _ _ => trivial
  | link _ _ _ _ _ => trivial
  | drainDue => trivial
  | wake _ _ => trivial

/-- **A running fiber whose frame moves stays typed**: every clause but the position reads fields
the edit keeps, or is vacuous at a running fiber (not parked, not exited, and its typed code is no
race registration marker). -/
theorem fiberTyped_frame {root : ProgramSource} {w : World} {m : RState} {f : RFiber}
    (old : FiberTyped root w m f) (hf : m.fiber? f.id = some f) (running : f.running = true)
    (fr : RSaved)
    (position : ∀ ty, w.Γ f.id = some ty → ∃ tin, PositionStack root w tin ty fr.stack)
    (prov : InterruptProvenance fr) (marker : raceRegistrationR fr.current = none) :
    FiberTyped root w (m.update { f with frame := fr }) { f with frame := fr } := by
  have view : ObsView m (m.update { f with frame := fr }) :=
    obsView_rupdate hf rfl (PendingWeaker.refl f.pending)
  have moved := fiberTyped_transport old view (Nat.le_refl _) (Nat.le_refl _)
  have notParked : f.parked = .notParked := by
    cases hp : f.parked with
    | notParked => rfl
    | withGuard _ =>
      have idle := old.parkedIdle (by rw [hp]; exact fun h => nomatch h)
      rw [running] at idle
      cases idle
  have live : f.exit = none := by
    cases hx : f.exit with
    | none => rfl
    | some _ =>
      have stopped := (old.exited (by rw [hx]; rfl)).2
      rw [running] at stopped
      cases stopped
  exact
    { ok := ⟨⟨fun ty declared => by
          obtain ⟨tin, stack⟩ := position ty declared
          exact ⟨tin, stack, prov⟩⟩, moved.ok.c1, moved.ok.c2, moved.ok.c3, moved.ok.c4, moved.ok.c5⟩
      delivery := fun token hp => by
        change f.parked = .withGuard token at hp
        rw [notParked] at hp
        cases hp
      below := moved.below
      pendingShape := moved.pendingShape
      parkedIdle := moved.parkedIdle
      parkedBelow := moved.parkedBelow
      exited := moved.exited
      exitedStack := fun hx => by
        change f.exit.isSome = true at hx
        rw [live] at hx
        cases hx
      deferredCause := prov.deferred
      pendingOwner := moved.pendingOwner
      observers := moved.observers
      registration := fun raceId hm => by
        change raceRegistrationR fr.current = some raceId at hm
        rw [marker] at hm
        cases hm
      code := fun _ hr => by
        change f.running = false at hr
        rw [running] at hr
        cases hr
      tokens := moved.tokens
      raceObservers := moved.raceObservers
      targetsBelow := moved.targetsBelow
      observersBelow := moved.observersBelow }

/-- A command's owner does not read the fibers: editing one keeps every owner. -/
theorem commandOwner_rupdate (m : RState) (g : RFiber) :
    Guard.commandOwner (Code := RProgram) (m.update g) = Guard.commandOwner m := rfl

/-- **The frame step**: from a typed configuration headed by the `loop` or `deliver` that owns the
running fiber `f`, a new frame for `f` typed at its declared type (its current code no race
registration marker) gives the configuration with that frame installed, under either head. The
step's frame-only clauses all end here. -/
theorem configTyped_frame_step {root : ProgramSource} {rootTy : EffTy} {w : World} {m : RState}
    {c : RCmd} {rest : List RCmd} {f : RFiber} (typed : ConfigTyped root rootTy w m (c :: rest))
    (owner : Guard.commandOwner m c = some f.id) (hf : m.fiber? f.id = some f)
    (running : f.running = true) (fr : RSaved)
    (code : ∀ ty, w.Γ f.id = some ty → CodeOk root w m f.id ty fr)
    (marker : raceRegistrationR fr.current = none) :
    (∀ y, ConfigTyped root rootTy w (m.update { f with frame := fr }) (.loop f.id y :: rest)) ∧
    (∀ y, ConfigTyped root rootTy w (m.update { f with frame := fr }) (.deliver f.id y :: rest)) := by
  let g : RFiber := { f with frame := fr }
  have hmem : f ∈ m.fibers := rfiber?_mem hf
  have old := typed.machine.fiber hmem
  have free := owner_free_rest typed.queue owner
  have notParked : f.parked = .notParked := by
    cases hp : f.parked with
    | notParked => rfl
    | withGuard _ =>
      have idle := old.parkedIdle (by rw [hp]; exact fun h => nomatch h)
      rw [running] at idle
      cases idle
  obtain ⟨ty, declared⟩ : ∃ ty, w.Γ f.id = some ty :=
    Option.isSome_iff_exists.mp ((typed.machine.wide.fibers f.id).mpr
      (List.mem_map.mpr ⟨f, hmem, rfl⟩))
  have prov : InterruptProvenance fr := by
    obtain ⟨_, _, _, p⟩ := code ty declared
    exact p
  have look : (m.update g).fiber? g.id = some g := rfiber?_update_self hf rfl
  have fresh : FiberTyped root w (m.update g) g :=
    fiberTyped_frame old hf running fr
      (fun ty' declared' => by
        obtain ⟨tin, _, stack, _⟩ := code ty' declared'
        exact ⟨tin, positionStack_of_host stack⟩) prov marker
  have edited : ConfigTyped root rootTy w (m.update g) rest := by
    refine configTyped_rupdate_frame (configTyped_tail typed) hf rfl (PendingWeaker.refl f.pending)
      free (fun k hk => Or.inl (fiberKeys_internal hmem hk)) ?_
      (fun d hd h => commandAuthority_frame (g := g) hf rfl rfl rfl rfl d (free d hd) h) ?_ fresh
    · intro token r hr
      have off : g.parked ≠ .withGuard token := by
        show f.parked ≠ _
        rw [notParked]
        exact fun h => nomatch h
      rw [requestOfR_of_not_parked look off] at hr
      cases hr
    · intro _ reads
      obtain ⟨y, r⟩ := reads
      rcases r with r | r
      · exact absurd rfl (free _ r)
      · exact absurd rfl (free _ r)
  have freeG : g.id ∉ rest.filterMap (Guard.commandOwner (m.update g)) := by
    rw [commandOwner_rupdate]
    exact owner_free typed.queue owner
  have codeG : raceRegistrationR g.frame.current = none → ∀ ty, w.Γ g.id = some ty →
      CodeOk root w (m.update g) g.id ty g.frame :=
    fun _ ty' declared' =>
      codeOk_races (m := m) (m' := m.update g) (racesKept_of_eq fun _ => rfl) (code ty' declared')
  exact ⟨fun y => configTyped_cons_loop edited look running notParked freeG y codeG,
    fun y => configTyped_cons_deliver edited look running notParked freeG y codeG⟩

/-! ## Construction glue (`prepareR`) at the completed view -/

/-- **The completed view is typed at `J`'s world** (row 175): each listed exit is an exited fiber's,
typed at its declaration by `RunFiberOk`'s exit clause; every fiber is declared (`WorldValid`). -/
theorem viewTyped_completed {root : ProgramSource} {rootTy : EffTy} {w : World} {m : RState}
    (typed : MachineTyped root rootTy w m) : ViewTyped w m.completedExits := by
  intro q hq
  obtain ⟨f, hf, hx⟩ := List.mem_filterMap.mp hq
  obtain ⟨ex, fx, rfl⟩ := Option.map_eq_some_iff.mp hx
  obtain ⟨ty, declared⟩ : ∃ ty, w.Γ f.id = some ty :=
    Option.isSome_iff_exists.mp ((typed.wide.fibers f.id).mpr (List.mem_map.mpr ⟨f, hf, rfl⟩))
  exact ⟨ty, declared, (typed.fiber hf).ok.c3 ex fx ty declared⟩

/-- **Construction glue keeps typing** (`prepareR`, `Laws/Program/DenoteR.lean`): a `construction`
operation answers the completed view, which is exactly its post when the view is typed; a guard
prepares its body, its run and skip arms untouched; nothing else moves. -/
theorem prepareR_typed {root : ProgramSource} (C : List (FiberId × ExitV)) (c : RProgram) :
    ∀ {w : World} {ty : EffTy}, ViewTyped w C → TypedProg root w ty c →
      TypedProg root w ty (prepareR C c) := by
  fun_induction prepareR C c with
  | case1 ex => exact fun _ h => h
  | case2 k ih =>
    intro w ty view h
    obtain ⟨cert, _, next⟩ := TypedProg.fiber_inv h (fun _ h => nomatch h) (fun _ h => nomatch h)
      (fun _ h => nomatch h) (fun _ _ _ h => nomatch h)
    exact ih view (next w (leHost_refl w) C view)
  | case3 kind k ih =>
    intro w ty view h
    cases h with
    | fiber notGuard _ _ _ _ _ _ => exact absurd rfl (notGuard kind)
    | guard mid body run skip => exact TypedProg.guard mid (ih view body) run skip
    | scopedGuard mid prev sc body callback live services widen =>
      exact TypedProg.scopedGuard mid prev sc (ih view body) callback live services widen
  | case4 op k _ _ => exact fun _ h => h

/-! ## Settling a frame-only clause -/

/-- Two edits of one fiber collapse to the second. -/
theorem rupdate_rupdate (m : RState) {f g : RFiber} (hid : g.id = f.id) :
    (m.update f).update g = m.update g := by
  unfold RunMachine.update
  have fibers : (m.fibers.map fun x => if x.id = f.id then f else x).map
      (fun x => if x.id = g.id then g else x) = m.fibers.map fun x => if x.id = g.id then g else x := by
    rw [List.map_map]
    apply List.map_congr_left
    intro x _
    show (if (if x.id = f.id then f else x).id = g.id then g else (if x.id = f.id then f else x)) =
      (if x.id = g.id then g else x)
    by_cases h : x.id = f.id
    · rw [if_pos h, if_pos hid.symm, if_pos (h.trans hid.symm)]
    · rw [if_neg h, if_neg (fun e => h (e.trans hid))]
  rw [fibers]

/-- Two partial maps that agree on a list's members filter it alike. -/
theorem filterMap_congr_mem {α β : Type} {f g : α → Option β} :
    ∀ (l : List α), (∀ x ∈ l, f x = g x) → l.filterMap f = l.filterMap g
  | [], _ => rfl
  | x :: xs, h => by
    rw [List.filterMap_cons, List.filterMap_cons, h x List.mem_cons_self,
      filterMap_congr_mem xs (fun y hy => h y (List.mem_cons_of_mem _ hy))]

/-- The completed view ignores a fiber edit that keeps the fiber's exit. -/
theorem completedExits_rupdate {m : RState} {g x : RFiber} (hx : m.fiber? g.id = some x)
    (exit : x.exit = g.exit) (nodup : (m.fibers.map RunFiber.id).Nodup) :
    (m.update g).completedExits = m.completedExits := by
  unfold RunMachine.completedExits RunMachine.update
  rw [List.filterMap_map]
  refine filterMap_congr_mem _ fun y hy => ?_
  show (if y.id = g.id then g else y).exit.map (fun ex => ((if y.id = g.id then g else y).id, ex)) =
    y.exit.map fun ex => (y.id, ex)
  by_cases h : y.id = g.id
  · have yx : y = x := Option.some.inj ((rfiber?_of_mem nodup hy).symm.trans (by rw [h]; exact hx))
    subst yx
    rw [if_pos h, ← exit, h]
  · rw [if_neg h]

/-- **The scoped exit's callback is idle on typed code**: `TypedProg` never types a raw scope-exit
marker as current code (decisions row 188 (a)), so `prepareScopedExitR` leaves the iteration. -/
theorem prepareScopedExitR_of_typed {root : ProgramSource} {w : World} {ty : EffTy} {it : RIter}
    (h : TypedProg root w ty it.fiber.frame.current) : prepareScopedExitR it = it := by
  unfold prepareScopedExitR
  split
  · rename_i previous scope ex next heq
    rw [heq] at h
    cases h with
    | fiber _ _ _ notScopeExit _ _ _ => exact absurd rfl (notScopeExit _ _ _)
  · rfl

/-- A frame stays typed when its current code is prepared at a typed view. -/
theorem codeOk_prepare {root : ProgramSource} {w : World} {m : RState} {host : FiberId}
    {final : EffTy} {fr : RSaved} (C : List (FiberId × ExitV)) (view : ViewTyped w C)
    (h : CodeOk root w m host final fr) :
    CodeOk root w m host final { fr with current := prepareR C fr.current } := by
  obtain ⟨tin, current, stack, prov⟩ := h
  exact ⟨tin, prepareR_typed C fr.current view current, stack, ⟨prov.recorded, prov.deferred⟩⟩

/-- **A frame-only clause's `continue` settles typed**: the iteration keeps the evaluator's machine,
moves only the fiber's frame to one typed at its declared type, and queues nothing; the glue then
prepares the new code (typed, `prepareR_typed`), the scoped-exit callback is idle on it, and
`settle` queues `loop`. The machine handed to the evaluator may hold an older record of the fiber
(`loop` edits it before evaluating); the configuration is typed with the evaluated one installed. -/
theorem settle_frame_continue {root : ProgramSource} {rootTy : EffTy} {w : World} {m : RState}
    {rest : List RCmd} {f f0 : RFiber} {y y' : Bool}
    (typed : ConfigTyped root rootTy w (m.update f) (.deliver f.id y :: rest))
    (hf0 : m.fiber? f.id = some f0) (exit0 : f0.exit = f.exit) (running : f.running = true)
    (fr : RSaved) (code : ∀ ty, w.Γ f.id = some ty → CodeOk root w (m.update f) f.id ty fr) :
    ∃ w', w.leHost w' ∧
      ConfigTyped root rootTy w'
        (settle f.id rest (prepareIterR ⟨m, { f with frame := fr }, y', .continue_, []⟩)).1
        (settle f.id rest (prepareIterR ⟨m, { f with frame := fr }, y', .continue_, []⟩)).2 := by
  have id0 : f0.id = f.id := rfiber?_id hf0
  have look : (m.update f).fiber? f.id = some f := by
    have := rfiber?_update_self (m := m) (f := f0) (g := f) (by rw [id0]; exact hf0) id0.symm
    exact this
  have nodup : (m.fibers.map RunFiber.id).Nodup := by
    rw [← rupdate_ids m f]
    exact typed.machine.wide.fiberIds
  have view : ViewTyped w m.completedExits := by
    rw [← completedExits_rupdate (g := f) (x := f0) hf0 exit0 nodup]
    exact viewTyped_completed typed.machine
  let fr' : RSaved := { fr with current := prepareR m.completedExits fr.current }
  have code' : ∀ ty, w.Γ f.id = some ty → CodeOk root w (m.update f) f.id ty fr' :=
    fun ty declared => codeOk_prepare m.completedExits view (code ty declared)
  obtain ⟨ty, declared⟩ : ∃ ty, w.Γ f.id = some ty :=
    Option.isSome_iff_exists.mp ((typed.machine.wide.fibers f.id).mpr
      (List.mem_map.mpr ⟨f, rfiber?_mem look, rfl⟩))
  obtain ⟨tin, current, _, _⟩ := code' ty declared
  have idle : prepareScopedExitR ⟨m, { f with frame := fr' }, y', .continue_, []⟩ =
      ⟨m, { f with frame := fr' }, y', .continue_, []⟩ := prepareScopedExitR_of_typed current
  have glue : prepareIterR ⟨m, { f with frame := fr }, y', .continue_, []⟩ =
      ⟨m, { f with frame := fr' }, y', .continue_, []⟩ := idle
  rw [glue]
  have step := (configTyped_frame_step typed rfl look running fr' code'
    (raceRegistrationR_typed current)).1 y'
  rw [rupdate_rupdate m (show ({ f with frame := fr' } : RFiber).id = f.id from rfl)] at step
  exact ⟨w, leHost_refl w, step⟩

/-! ## The evaluation step from its clauses

The interface the clauses meet. `Evaluating` is the state the evaluator is handed: the
configuration typed with the evaluated fiber installed under a `deliver` head (both `deliver` and,
after its loop top, `loop` reach it), while the evaluator's input machine may hold an older record
of that fiber with the same exit. A clause is stated over the actual outcome — the clause's
iteration after the glue (`prepareIterR`), settled — and the unchanged configuration judgment. -/

/-- An edit that installs a fiber's own record is no edit. -/
theorem rupdate_self {m : RState} {f : RFiber} (hf : m.fiber? f.id = some f)
    (nodup : (m.fibers.map RunFiber.id).Nodup) : m.update f = m := by
  unfold RunMachine.update
  have fibers : (m.fibers.map fun x => if x.id = f.id then f else x) = m.fibers := by
    conv => rhs; rw [← List.map_id m.fibers]
    apply List.map_congr_left
    intro x hx
    show (if x.id = f.id then f else x) = x
    by_cases h : x.id = f.id
    · rw [if_pos h]
      exact (Option.some.inj ((rfiber?_of_mem nodup hx).symm.trans (by rw [h]; exact hf))).symm
    · rw [if_neg h]
  rw [fibers]

/-- **The state the evaluator is handed**: the configuration typed with fiber `f` installed under
the `deliver` head that continues it; the evaluator's machine `m` holds a record of `f`'s id with
`f`'s exit; `f` runs; the machine has not halted. -/
structure Evaluating (root : ProgramSource) (rootTy : EffTy) (w : World) (m : RState)
    (rest : List RCmd) (f : RFiber) (y : Bool) : Prop where
  typed : ConfigTyped root rootTy w (m.update f) (.deliver f.id y :: rest)
  stale : ∃ f0, m.fiber? f.id = some f0 ∧ f0.exit = f.exit
  running : f.running = true
  live : m.stuck = none

/-- What a step of fiber `f` leaves typed: the settled iteration at a later world. -/
def SettlesTyped (root : ProgramSource) (rootTy : EffTy) (w : World) (id : FiberId)
    (rest : List RCmd) (it : RIter) : Prop :=
  ∃ w', w.leHost w' ∧ ConfigTyped root rootTy w' (settle id rest it).1 (settle id rest it).2

/-- **Clause soundness for fiber operation `op`** (the handler clause meets `op`'s contract): from
the evaluated state with `op` current, the clause's iteration after the glue settles typed. -/
def FiberClauseKeeps (root : ProgramSource) (rootTy : EffTy) (op : FiberOp) : Prop :=
  ∀ (w : World) (m : RState) (rest : List RCmd) (f : RFiber) (y : Bool)
    (next : op.answer → RProgram),
    Evaluating root rootTy w m rest f y → f.frame.current = .vis (.inr op) next →
    SettlesTyped root rootTy w f.id rest
      (prepareIterR (evaluateFiberR (interpRAt root.program m.completedExits) m f y op next))

/-- **Clause soundness for store operation `op`**: the store step's answered iteration settles typed. -/
def StoreClauseKeeps (root : ProgramSource) (rootTy : EffTy) (op : SyncOp) : Prop :=
  ∀ (w : World) (m : RState) (rest : List RCmd) (f : RFiber) (y : Bool) (next : Val → RProgram),
    Evaluating root rootTy w m rest f y → f.frame.current = .vis (.inl op) next →
    SettlesTyped root rootTy w f.id rest
      (prepareIterR (evaluateRawR (interpRAt root.program m.completedExits) m f y))

/-- **The walk keeps `I`**: an exit current is delivered through the saved stack and settles typed. -/
def WalkKeeps (root : ProgramSource) (rootTy : EffTy) : Prop :=
  ∀ (w : World) (m : RState) (rest : List RCmd) (f : RFiber) (y : Bool) (ex : ExitV),
    Evaluating root rootTy w m rest f y → f.frame.current = .pure ex →
    SettlesTyped root rootTy w f.id rest
      (prepareIterR (deliverR (interpRAt root.program m.completedExits) m f y ex))

/-- **The raw evaluation from its clauses**, by the current code's head. -/
theorem evaluateRaw_keeps {root : ProgramSource} {rootTy : EffTy}
    (fibers : ∀ op, FiberClauseKeeps root rootTy op) (stores : ∀ op, StoreClauseKeeps root rootTy op)
    (walk : WalkKeeps root rootTy) {w : World} {m : RState} {rest : List RCmd} {f : RFiber} {y : Bool}
    (ev : Evaluating root rootTy w m rest f y) :
    SettlesTyped root rootTy w f.id rest
      (prepareIterR (evaluateRawR (interpRAt root.program m.completedExits) m f y)) := by
  cases hc : f.frame.current with
  | pure ex =>
    have unfolded : evaluateRawR (interpRAt root.program m.completedExits) m f y =
        deliverR (interpRAt root.program m.completedExits) m f y ex := by
      unfold evaluateRawR
      rw [hc]
    rw [unfolded]
    exact walk w m rest f y ex ev hc
  | vis op next =>
    cases op with
    | inl sop => exact stores sop w m rest f y next ev hc
    | inr fop =>
      have unfolded : evaluateRawR (interpRAt root.program m.completedExits) m f y =
          evaluateFiberR (interpRAt root.program m.completedExits) m f y fop next := by
        unfold evaluateRawR
        rw [hc]
      rw [unfolded]
      exact fibers fop w m rest f y next ev hc

/-- **The evaluation from its clauses**: the construction glue first (a frame-only edit, typed by
`prepareR_typed`; a registration marker is left alone), then the raw evaluation. -/
theorem evaluate_keeps {root : ProgramSource} {rootTy : EffTy}
    (fibers : ∀ op, FiberClauseKeeps root rootTy op) (stores : ∀ op, StoreClauseKeeps root rootTy op)
    (walk : WalkKeeps root rootTy) {w : World} {m : RState} {rest : List RCmd} {f : RFiber} {y : Bool}
    (ev : Evaluating root rootTy w m rest f y) :
    SettlesTyped root rootTy w f.id rest
      (evaluateR (interpRAt root.program m.completedExits) m f y) := by
  obtain ⟨f0, hf0, exit0⟩ := ev.stale
  have id0 : f0.id = f.id := rfiber?_id hf0
  have look : (m.update f).fiber? f.id = some f :=
    rfiber?_update_self (m := m) (f := f0) (g := f) (by rw [id0]; exact hf0) id0.symm
  have nodup : (m.fibers.map RunFiber.id).Nodup := by
    rw [← rupdate_ids m f]
    exact ev.typed.machine.wide.fiberIds
  have view : ViewTyped w m.completedExits := by
    rw [← completedExits_rupdate (g := f) (x := f0) hf0 exit0 nodup]
    exact viewTyped_completed ev.typed.machine
  let f1 := answerR f (prepareR m.completedExits f.frame.current)
  have ev1 : Evaluating root rootTy w m rest f1 y := by
    refine ⟨?_, ⟨f0, hf0, exit0⟩, ev.running, ev.live⟩
    cases hmark : raceRegistrationR f.frame.current with
    | none =>
      have code : ∀ ty, w.Γ f.id = some ty → CodeOk root w (m.update f) f.id ty f.frame :=
        fun ty declared => ev.typed.code f (rfiber?_mem look) ev.running
          ⟨y, Or.inr List.mem_cons_self⟩ hmark ty declared
      obtain ⟨ty, declared⟩ : ∃ ty, w.Γ f.id = some ty :=
        Option.isSome_iff_exists.mp ((ev.typed.machine.wide.fibers f.id).mpr
          (List.mem_map.mpr ⟨f, rfiber?_mem look, rfl⟩))
      obtain ⟨tin, current, _, _⟩ := codeOk_prepare m.completedExits view (code ty declared)
      have step : ConfigTyped root rootTy w ((m.update f).update f1) (.deliver f.id y :: rest) :=
        (configTyped_frame_step ev.typed rfl look ev.running
          { f.frame with current := prepareR m.completedExits f.frame.current }
          (fun ty' declared' => codeOk_prepare m.completedExits view (code ty' declared'))
          (raceRegistrationR_typed current)).2 y
      rw [rupdate_rupdate m (show f1.id = f.id from rfl)] at step
      exact step
    | some r =>
      have shape : ∃ k, f.frame.current = .vis (.inr (.raceRegister r)) k := by
        unfold raceRegistrationR at hmark
        split at hmark
        · rename_i raceId k heq
          cases hmark
          exact ⟨k, heq⟩
        · cases hmark
      obtain ⟨k, hk⟩ := shape
      have same : f1 = f := by
        show answerR f (prepareR m.completedExits f.frame.current) = f
        rw [hk]
        show { f with frame := { f.frame with current := .vis (.inr (.raceRegister r)) k } } = f
        rw [← hk]
      rw [same]
      exact ev.typed
  exact evaluateRaw_keeps fibers stores walk ev1

/-- **`deliver` keeps `I` from the clauses** (`M6Ledger.step_deliver`'s shape): the head's authority
finds the running fiber, which is its own record, and the evaluation settles typed. -/
theorem deliver_preserves_of_clauses (root : ProgramSource) (rootTy : EffTy)
    (fibers : ∀ op, FiberClauseKeeps root rootTy op) (stores : ∀ op, StoreClauseKeeps root rootTy op)
    (walk : WalkKeeps root rootTy) (id : FiberId) (y : Bool) :
    StepPreserves root rootTy (.deliver id y) := by
  intro w m rest live typed
  obtain ⟨f, hf, running, _⟩ := typed.queue.authority _ List.mem_cons_self
  have fid : f.id = id := rfiber?_id hf
  subst fid
  have nodup := typed.machine.wide.fiberIds
  have ev : Evaluating root rootTy w m rest f y := by
    refine ⟨?_, ⟨f, hf, rfl⟩, running, live⟩
    rw [rupdate_self hf nodup]
    exact typed
  have keeps := evaluate_keeps fibers stores walk ev
  show ∃ w', w.leHost w' ∧ ConfigTyped root rootTy w'
    (letI := termEvaluatorFor root.program
     driveStep (interpR root.program) m (.deliver f.id y) rest).1
    (letI := termEvaluatorFor root.program
     driveStep (interpR root.program) m (.deliver f.id y) rest).2
  simp only [driveStep, hf]
  exact keeps

/-! ## The clauses: shared shapes -/

/-- The evaluated fiber is its own record in the configuration's machine. -/
theorem Evaluating.look {root : ProgramSource} {rootTy : EffTy} {w : World} {m : RState}
    {rest : List RCmd} {f : RFiber} {y : Bool} (ev : Evaluating root rootTy w m rest f y) :
    (m.update f).fiber? f.id = some f := by
  obtain ⟨f0, hf0, _⟩ := ev.stale
  have id0 : f0.id = f.id := rfiber?_id hf0
  exact rfiber?_update_self (m := m) (f := f0) (g := f) (by rw [id0]; exact hf0) id0.symm

/-- The evaluated fiber's code and stack, when its current code is no registration marker. -/
theorem Evaluating.code {root : ProgramSource} {rootTy : EffTy} {w : World} {m : RState}
    {rest : List RCmd} {f : RFiber} {y : Bool} (ev : Evaluating root rootTy w m rest f y)
    (marker : raceRegistrationR f.frame.current = none) :
    ∀ ty, w.Γ f.id = some ty → CodeOk root w (m.update f) f.id ty f.frame :=
  fun ty declared => ev.typed.code f (rfiber?_mem ev.look) ev.running
    ⟨y, Or.inr List.mem_cons_self⟩ marker ty declared

/-- The evaluated fiber is declared. -/
theorem Evaluating.declared {root : ProgramSource} {rootTy : EffTy} {w : World} {m : RState}
    {rest : List RCmd} {f : RFiber} {y : Bool} (ev : Evaluating root rootTy w m rest f y) :
    ∃ ty, w.Γ f.id = some ty :=
  Option.isSome_iff_exists.mp ((ev.typed.machine.wide.fibers f.id).mpr
    (List.mem_map.mpr ⟨f, rfiber?_mem ev.look, rfl⟩))

/-- The evaluator's completed view is typed at the step's world. -/
theorem Evaluating.view {root : ProgramSource} {rootTy : EffTy} {w : World} {m : RState}
    {rest : List RCmd} {f : RFiber} {y : Bool} (ev : Evaluating root rootTy w m rest f y) :
    ViewTyped w m.completedExits := by
  obtain ⟨f0, hf0, exit0⟩ := ev.stale
  have nodup : (m.fibers.map RunFiber.id).Nodup := by
    rw [← rupdate_ids m f]
    exact ev.typed.machine.wide.fiberIds
  rw [← completedExits_rupdate (g := f) (x := f0) hf0 exit0 nodup]
  exact viewTyped_completed ev.typed.machine

/-- **A frame-only clause whose iteration continues settles typed**, from the new frame's typing. -/
theorem Evaluating.settle_continue {root : ProgramSource} {rootTy : EffTy} {w : World} {m : RState}
    {rest : List RCmd} {f : RFiber} {y y' : Bool} (ev : Evaluating root rootTy w m rest f y)
    (fr : RSaved) (code : ∀ ty, w.Γ f.id = some ty → CodeOk root w (m.update f) f.id ty fr) :
    SettlesTyped root rootTy w f.id rest
      (prepareIterR ⟨m, { f with frame := fr }, y', .continue_, []⟩) := by
  obtain ⟨f0, hf0, exit0⟩ := ev.stale
  exact settle_frame_continue ev.typed hf0 exit0 ev.running fr code

/-- **A frame-only clause whose iteration is answered settles typed**: the glue leaves it, and
`settle` queues `deliver`. -/
theorem Evaluating.settle_answered {root : ProgramSource} {rootTy : EffTy} {w : World} {m : RState}
    {rest : List RCmd} {f : RFiber} {y y' : Bool} (ev : Evaluating root rootTy w m rest f y)
    (fr : RSaved) (code : ∀ ty, w.Γ f.id = some ty → CodeOk root w (m.update f) f.id ty fr) :
    SettlesTyped root rootTy w f.id rest
      (prepareIterR ⟨m, { f with frame := fr }, y', .answered, []⟩) := by
  obtain ⟨ty, declared⟩ := ev.declared
  obtain ⟨tin, current, _, _⟩ := code ty declared
  have step := (configTyped_frame_step ev.typed rfl ev.look ev.running fr code
    (raceRegistrationR_typed current)).2 y'
  rw [rupdate_rupdate m (show ({ f with frame := fr } : RFiber).id = f.id from rfl)] at step
  exact ⟨w, leHost_refl w, step⟩

/-- **An inline answer**: the clause installs the continuation at answer `v` the operation's post
admits; the stack and everything else stay. -/
theorem Evaluating.answer_typed {root : ProgramSource} {rootTy : EffTy} {w : World} {m : RState}
    {rest : List RCmd} {f : RFiber} {y : Bool} (ev : Evaluating root rootTy w m rest f y)
    {op : FiberOp} {next : op.answer → RProgram} (hc : f.frame.current = .vis (.inr op) next)
    (marker : raceRegistrationR f.frame.current = none)
    (notGuard : ∀ kind, op ≠ .guard_ kind) (notUnguard : ∀ ex, op ≠ .unguard ex)
    (notFinish : ∀ ex, op ≠ .finishFinalizer ex)
    (notScopeExit : ∀ prev sc ex, op ≠ .scopeExit prev sc ex) (v : op.answer)
    (post : ∀ cert, fiberPre root w op cert → fiberPost w op cert v) :
    ∀ ty, w.Γ f.id = some ty →
      CodeOk root w (m.update f) f.id ty { f.frame with current := next v } := by
  intro ty declared
  obtain ⟨tin, current, stack, prov⟩ := ev.code marker ty declared
  rw [hc] at current
  obtain ⟨cert, pre, typedNext⟩ := TypedProg.fiber_inv current notGuard notUnguard notFinish notScopeExit
  exact ⟨tin, typedNext w (leHost_refl w) v (post cert pre), stack, ⟨prov.recorded, prov.deferred⟩⟩

/-! ## The clauses: inline answers and no-ops -/

theorem clause_suspend (root : ProgramSource) (rootTy : EffTy) (p : Point) :
    FiberClauseKeeps root rootTy (.suspend p) := by
  intro w m rest f y next ev hc
  exact ev.settle_continue _ (ev.answer_typed hc (by rw [hc]; rfl) (fun _ h => nomatch h)
    (fun _ h => nomatch h) (fun _ h => nomatch h) (fun _ _ _ h => nomatch h) .unit
    (fun _ _ => trivial))

theorem clause_foreignRelease (root : ProgramSource) (rootTy : EffTy) (c : Capture) (ex : ExitV) :
    FiberClauseKeeps root rootTy (.foreignRelease c ex) := by
  intro w m rest f y next ev hc
  exact ev.settle_continue _ (ev.answer_typed hc (by rw [hc]; rfl) (fun _ h => nomatch h)
    (fun _ h => nomatch h) (fun _ h => nomatch h) (fun _ _ _ h => nomatch h) .unit
    (fun _ _ => rfl))

theorem clause_closeWalk (root : ProgramSource) (rootTy : EffTy) (strategy : FinalizerStrategy)
    (order : List FinName) (ex : ExitV) : FiberClauseKeeps root rootTy (.closeWalk strategy order ex) := by
  intro w m rest f y next ev hc
  exact ev.settle_continue _ (ev.answer_typed hc (by rw [hc]; rfl) (fun _ h => nomatch h)
    (fun _ h => nomatch h) (fun _ h => nomatch h) (fun _ _ _ h => nomatch h) .unit
    (fun _ _ => rfl))

theorem clause_frontier (root : ProgramSource) (rootTy : EffTy) (reason : PendingReason) (p : Point) :
    FiberClauseKeeps root rootTy (.frontier reason p) := by
  intro w m rest f y next ev hc
  exact ev.settle_continue f.frame (ev.code (by rw [hc]; rfl))

theorem clause_construction (root : ProgramSource) (rootTy : EffTy) :
    FiberClauseKeeps root rootTy .construction := by
  intro w m rest f y next ev hc
  have view := ev.view
  refine ev.settle_continue { f.frame with current := prepareR m.completedExits (next m.completedExits) } ?_
  intro ty declared
  obtain ⟨tin, current, stack, prov⟩ := ev.code (by rw [hc]; rfl) ty declared
  rw [hc] at current
  obtain ⟨cert, _, typedNext⟩ := TypedProg.fiber_inv current (fun _ h => nomatch h)
    (fun _ h => nomatch h) (fun _ h => nomatch h) (fun _ _ _ h => nomatch h)
  exact ⟨tin, prepareR_typed _ _ view (typedNext w (leHost_refl w) m.completedExits view), stack,
    ⟨prov.recorded, prov.deferred⟩⟩

theorem clause_sync (root : ProgramSource) (rootTy : EffTy) (v : Val) :
    FiberClauseKeeps root rootTy (.sync v) := by
  intro w m rest f y next ev hc
  exact ev.settle_answered _ (ev.answer_typed hc (by rw [hc]; rfl) (fun _ h => nomatch h)
    (fun _ h => nomatch h) (fun _ h => nomatch h) (fun _ _ _ h => nomatch h) v (fun _ _ => rfl))


/-! ## The clauses: the frame pushers -/

/-- **`guard_`**: the guard installs its body and saves the resume frame (`saveR`), the arrow
`guard_frame` types from the body's type to the guard's. -/
theorem clause_guard_ (root : ProgramSource) (rootTy : EffTy) (kind : GuardKind) :
    FiberClauseKeeps root rootTy (.guard_ kind) := by
  intro w m rest f y next ev hc
  refine ev.settle_continue { f.frame with
    current := next none, stack := .resume kind (fun ex => next (some ex)) :: f.frame.stack } ?_
  intro ty declared
  obtain ⟨tin, current, stack, prov⟩ := ev.code (by rw [hc]; rfl) ty declared
  rw [hc] at current
  obtain ⟨mid, body, frame⟩ := TypedProg.guard_frame current
  exact ⟨mid, body, hostStack_push frame stack, ⟨prov.recorded, prov.deferred⟩⟩

/-- The frame `mask flag body` installs (`Laws/Program/EvaluateR.lean`, the `mask` arm;
`internal/effect.ts`'s `interruptible`/`uninterruptible`): the answer frame saved, the mask set with
the restore frame pushed when it changes, and the body current unless the mask turns interruptible
with an interrupt recorded, when the recorded cause is current. -/
def maskFrame (fr : RSaved) (flag : Bool) (body : RProgram) (next : ExitV → RProgram) : RSaved :=
  let saved : RSaved := { fr with stack := .answer next :: fr.stack }
  let old := saved.interruptible
  let stack := if old = flag then saved.stack else .restoreMask old :: saved.stack
  let frame : RSaved := { saved with interruptible := flag, stack }
  { frame with current :=
      if flag && !old && frame.interruptedCause.isSome then .pure (.failure frame.pendingCause)
      else body }

theorem evaluateFiberR_mask (interp : RInterp) (m : RState) (f : RFiber) (y : Bool) (flag : Bool)
    (body : Body) (next : ExitV → RProgram) :
    evaluateFiberR interp m f y (.mask flag body) next =
      ⟨m, { f with frame := maskFrame f.frame flag (bodyR interp body) next }, y, .continue_, []⟩ :=
  rfl

/-- **`mask`**: the body's program is typed at the certificate (`bodyTyped_typed`, from `J`'s
source and service facts), or the recorded interrupt is delivered (`InterruptProvenance`); the
answer frame carries the certificate to the continuation and the restore frame is an identity
arrow. -/
theorem clause_mask (root : ProgramSource) (rootTy : EffTy) (flag : Bool) (body : Body) :
    FiberClauseKeeps root rootTy (.mask flag body) := by
  intro w m rest f y next ev hc
  rw [evaluateFiberR_mask]
  refine ev.settle_continue _ ?_
  intro ty declared
  obtain ⟨tin, current, stack, prov⟩ := ev.code (by rw [hc]; rfl) ty declared
  rw [hc] at current
  obtain ⟨cert, pre, typedNext⟩ := TypedProg.fiber_inv current (fun _ h => nomatch h)
    (fun _ h => nomatch h) (fun _ h => nomatch h) (fun _ _ _ h => nomatch h)
  have typedBody : TypedProg root w cert (bodyR (interpRAt root.program m.completedExits) body) :=
    bodyTyped_typed root ev.typed.machine.sourceWF ev.typed.machine.services m.completedExits pre
  have answer : HostStack root w (m.update f) f.id cert ty (.answer next :: f.frame.stack) :=
    hostStack_push (answerFrame_typed (fun _ _ _ hex => hex) typedNext) stack
  refine ⟨cert, ?_, ?_, ⟨prov.recorded, prov.deferred⟩⟩
  · show TypedProg root w cert
      (if flag && !f.frame.interruptible && f.frame.interruptedCause.isSome then
        .pure (.failure f.frame.pendingCause)
      else bodyR (interpRAt root.program m.completedExits) body)
    split
    · exact TypedProg.pure (strongExit_of_clean w cert _ (pendingCause_clean prov)
        (pendingCause_noShapeDefect cert prov))
    · exact typedBody
  · show HostStack root w (m.update f) f.id cert ty
      (if f.frame.interruptible = flag then .answer next :: f.frame.stack
       else .restoreMask f.frame.interruptible :: .answer next :: f.frame.stack)
    split
    · exact answer
    · exact hostStack_push (.restoreMask cert _) answer

end Effect4.Program.Typed
