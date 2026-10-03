import Effect4.Laws.Program.Typed.Commands.Observe
import Effect4.Laws.Program.Typed.Body
import Effect4.Laws.Program.Typed.HostWalk

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
the edit keeps, or is vacuous at a running fiber (not parked, not exited); a race registration
marker current carries its registration facts (`RegistrationState`, decisions row 188 (b)): the
race, hosted here, its token declared, and the stack a reply at the token's type meets. -/
theorem fiberTyped_frame {root : ProgramSource} {w : World} {m : RState} {f : RFiber}
    (old : FiberTyped root w m f) (hf : m.fiber? f.id = some f) (running : f.running = true)
    (fr : RSaved)
    (position : ∀ ty, w.Γ f.id = some ty → ∃ tin, PositionStack root w tin ty fr.stack)
    (prov : InterruptProvenance fr)
    (registration : ∀ raceId, raceRegistrationR fr.current = some raceId →
      ∃ race resultTy final, m.race? raceId = some race ∧ race.host = f.id ∧
        w.Θ race.host race.token = some resultTy ∧ w.Γ f.id = some final ∧
        HostStack root w m f.id resultTy final fr.stack) :
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
        obtain ⟨race, resultTy, final, found, host, token, declared, stack⟩ := registration raceId hm
        exact ⟨race, resultTy, found, host, token, final, declared,
          hostStack_races (m := m) (m' := m.update { f with frame := fr })
            (racesKept_of_eq fun _ => rfl) stack, prov⟩
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

/-- **The fiber edit of a frame step**: from a typed configuration headed by the `loop` or
`deliver` that owns the running fiber `f`, a new frame for `f` that keeps `f` typed gives the
configuration with the frame installed and the head dropped. No other command owns `f`
(`QueueOk.owners`), so no delivery reads its stack and no `loop` or `deliver` its code. -/
theorem configTyped_frame_edit {root : ProgramSource} {rootTy : EffTy} {w : World} {m : RState}
    {c : RCmd} {rest : List RCmd} {f : RFiber} (typed : ConfigTyped root rootTy w m (c :: rest))
    (owner : Guard.commandOwner m c = some f.id) (hf : m.fiber? f.id = some f)
    (running : f.running = true) (fr : RSaved)
    (fresh : FiberTyped root w (m.update { f with frame := fr }) { f with frame := fr }) :
    ConfigTyped root rootTy w (m.update { f with frame := fr }) rest := by
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
  have look : (m.update g).fiber? g.id = some g := rfiber?_update_self hf rfl
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
        exact ⟨tin, positionStack_of_host stack⟩) prov (fun _ h => by rw [marker] at h; cases h)
  have edited : ConfigTyped root rootTy w (m.update g) rest :=
    configTyped_frame_edit typed owner hf running fr fresh
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

/-! ## Read-only store clauses (Concept 4)

Helpers of `M6Ledger.step_loop` and `M6Ledger.step_deliver`, via `StoreClauseKeeps` and
`evaluateRaw_keeps`/`evaluate_keeps`. These preserve the unchanged `ConfigTyped` judgment for
four actual same-state store operations, including the real `[.drainDue]` queue prefix.
The operation's returned value meets `storePost`; `TypedProg.store_inv` supplies the typed
continuation. Existing frame and queue lemmas complete the configuration proof.
This is the operation-clause handler proof pattern of Plotkin--Pretnar (2009, sections 2--5),
applied here to the concrete evaluator. It is not the whole store family, scheduler progress,
host adequacy, or backend correctness. Source-well-formedness and the existing queue/world
hypotheses stay in `Evaluating`; no output-preservation premise is added.
-/

/-- DrainDue has no payload obligation, owner, token, registration tail or code read. -/
theorem configTyped_cons_drainDue {root : ProgramSource} {rootTy : EffTy}
    {w : World} {m : RState} {q : List RCmd} (typed : ConfigTyped root rootTy w m q) :
    ConfigTyped root rootTy w m (.drainDue :: q) := by
  refine ⟨typed.machine,
    readCode_cons (fun _ _ h => nomatch h) (fun _ _ h => nomatch h) typed.code,
    queueOk_cons ?_ typed.queue⟩
  exact ⟨trivial, trivial, trivial, (fun _ h => nomatch h), trivial,
    (fun _ h => nomatch h), (fun _ _ _ _ h => nomatch h),
    (fun _ _ _ h => nomatch h), (fun _ _ h => nomatch h),
    (fun _ _ _ h => nomatch h), (fun _ _ _ _ _ h => nomatch h),
    (fun _ _ _ h => nomatch h)⟩

/-- The actual successful-store queue: drain the due work before delivering the answer. -/
theorem Evaluating.settle_answered_drain {root : ProgramSource} {rootTy : EffTy}
    {w : World} {m : RState} {rest : List RCmd} {f : RFiber} {y y' : Bool}
    (ev : Evaluating root rootTy w m rest f y) (fr : RSaved)
    (code : ∀ ty, w.Γ f.id = some ty → CodeOk root w (m.update f) f.id ty fr) :
    SettlesTyped root rootTy w f.id rest
      (prepareIterR ⟨m, { f with frame := fr }, y', .answered, [.drainDue]⟩) := by
  obtain ⟨w', ord, typed⟩ := ev.settle_answered (y' := y') fr code
  exact ⟨w', ord, configTyped_cons_drainDue typed⟩

/-- Store inversion gives the same-world continuation without any fiber-control exclusions. -/
theorem Evaluating.store_answer_typed {root : ProgramSource} {rootTy : EffTy}
    {w : World} {m : RState} {rest : List RCmd} {f : RFiber} {y : Bool}
    (ev : Evaluating root rootTy w m rest f y) {op : SyncOp} {next : Val → RProgram}
    (hc : f.frame.current = .vis (.inl op) next) (v : Val)
    (post : ∀ cert, storePre root w op cert → storePost w op cert v) :
    ∀ ty, w.Γ f.id = some ty →
      CodeOk root w (m.update f) f.id ty { f.frame with current := next v } := by
  intro ty declared
  obtain ⟨tin, current, stack, prov⟩ := ev.code (by rw [hc]; rfl) ty declared
  rw [hc] at current
  obtain ⟨cert, pre, typedNext⟩ := TypedProg.store_inv current
  exact ⟨tin, typedNext w (leHost_refl w) v (post cert pre), stack,
    ⟨prov.recorded, prov.deferred⟩⟩

/-- Successful read-only store evaluation uses its exact answer and retains drainDue. -/
theorem Evaluating.store_same {root : ProgramSource} {rootTy : EffTy}
    {w : World} {m : RState} {rest : List RCmd} {f : RFiber} {y : Bool}
    (ev : Evaluating root rootTy w m rest f y) {op : SyncOp} {next : Val → RProgram}
    (hc : f.frame.current = .vis (.inl op) next) (v : Val)
    (step : syncOpStep op m.state = some (m.state, v))
    (post : ∀ cert, storePre root w op cert → storePost w op cert v) :
    SettlesTyped root rootTy w f.id rest
      (prepareIterR (evaluateRawR (interpRAt root.program m.completedExits) m f y)) := by
  simp only [evaluateRawR, hc, step]
  exact ev.settle_answered_drain _ (ev.store_answer_typed hc v post)

/-- The operation's existing certificate and precondition are available from current code. -/
theorem Evaluating.store_pre {root : ProgramSource} {rootTy : EffTy}
    {w : World} {m : RState} {rest : List RCmd} {f : RFiber} {y : Bool}
    (ev : Evaluating root rootTy w m rest f y) {op : SyncOp} {next : Val → RProgram}
    (hc : f.frame.current = .vis (.inl op) next) : ∃ cert, storePre root w op cert := by
  obtain ⟨ty, declared⟩ := ev.declared
  obtain ⟨tin, current, _, _⟩ := ev.code (by rw [hc]; rfl) ty declared
  rw [hc] at current
  obtain ⟨cert, pre, _⟩ := TypedProg.store_inv current
  exact ⟨cert, pre⟩

theorem clause_clockNow (root : ProgramSource) (rootTy : EffTy) :
    StoreClauseKeeps root rootTy .clockNow := by
  intro w m rest f y next ev hc
  exact ev.store_same hc (Val.nat m.state.timers.now.toNat) rfl (fun _ _ => ⟨_, rfl⟩)

theorem clause_refGet (root : ProgramSource) (rootTy : EffTy) (cell : RefKey) :
    StoreClauseKeeps root rootTy (.refGet cell) := by
  intro w m rest f y next ev hc
  have store := storeTyped_of_typedState ev.typed.machine
  have state : w.state = m.state := ev.typed.machine.wide.state
  obtain ⟨cert, pre⟩ := ev.store_pre hc
  obtain ⟨t, declared⟩ := pre
  obtain ⟨a, ha⟩ := cell_readable store declared
  have step : syncOpStep (.refGet cell) m.state = some (m.state, a) := by
    rw [← state]
    simp only [syncOpStep, refStep, refPeek, ha, Option.map_some]
  exact ev.store_same hc a step
    (fun _ _ => ⟨t, declared, store.values cell.index a ha t declared⟩)

theorem clause_deferredIsDone (root : ProgramSource) (rootTy : EffTy) (key : DeferredKey) :
    StoreClauseKeeps root rootTy (.deferredIsDone key) := by
  intro w m rest f y next ev hc
  have store := storeTyped_of_typedState ev.typed.machine
  have state : w.state = m.state := ev.typed.machine.wide.state
  obtain ⟨cert, pre⟩ := ev.store_pre hc
  obtain ⟨c, hc0⟩ := promise_readable store pre
  have step : syncOpStep (.deferredIsDone key) m.state =
      some (m.state, Val.bool c.completion.isSome) := by
    rw [← state]
    simp only [syncOpStep, DeferredStore.isDone, DeferredStore.cellAt, hc0, Option.map_some]
  exact ev.store_same hc (Val.bool c.completion.isSome) step (fun _ _ => ⟨_, rfl⟩)

theorem clause_deferredPoll (root : ProgramSource) (rootTy : EffTy) (key : DeferredKey) :
    StoreClauseKeeps root rootTy (.deferredPoll key) := by
  intro w m rest f y next ev hc
  have store := storeTyped_of_typedState ev.typed.machine
  have state : w.state = m.state := ev.typed.machine.wide.state
  obtain ⟨cert, pre⟩ := ev.store_pre hc
  obtain ⟨c, hc0⟩ := promise_readable store pre
  have step : syncOpStep (.deferredPoll key) m.state =
      some (m.state, Val.bool c.completion.isSome) := by
    rw [← state]
    simp only [syncOpStep, DeferredStore.poll, DeferredStore.cellAt, hc0, Option.map_some]
  exact ev.store_same hc (Val.bool c.completion.isSome) step (fun _ _ => ⟨_, rfl⟩)


/-! ## The clauses no typed code reaches -/

/-- **`scopeExit`**: a raw scope-exit marker is no typed code (`TypedProg.fiber` excludes it,
decisions row 188 (a)); the generated callback is consumed by `prepareScopedExitR` inside the
preceding delivery, never evaluated as a counted operation. -/
theorem clause_scopeExit (root : ProgramSource) (rootTy : EffTy) (prev : Ctx) (scope : Nat)
    (ex : ExitV) : FiberClauseKeeps root rootTy (.scopeExit prev scope ex) := by
  intro w m rest f y next ev hc
  obtain ⟨ty, declared⟩ := ev.declared
  obtain ⟨tin, current, _, _⟩ := ev.code (by rw [hc]; rfl) ty declared
  rw [hc] at current
  cases current with
  | fiber _ _ _ notScopeExit _ _ _ => exact absurd rfl (notScopeExit _ _ _)

/-- **`refuse`**: its pre is `False`; no typed code refuses. -/
theorem clause_refuse (root : ProgramSource) (rootTy : EffTy) (cause : CauseV) :
    FiberClauseKeeps root rootTy (.refuse cause) := by
  intro w m rest f y next ev hc
  obtain ⟨ty, declared⟩ := ev.declared
  obtain ⟨tin, current, _, _⟩ := ev.code (by rw [hc]; rfl) ty declared
  rw [hc] at current
  obtain ⟨_, pre, _⟩ := TypedProg.fiber_inv current (fun _ h => nomatch h) (fun _ h => nomatch h)
    (fun _ h => nomatch h) (fun _ _ _ h => nomatch h)
  exact (pre : False).elim


/-! ## The actual loop prefix — M6.step_loop, conditional on the evaluator clauses
Checked against f409507f. This composes the existing handler premises; it does not discharge them.
-/
namespace LoopPrefix
open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Sched Effect4.Program.Denote
open Effect4.Program.Typed Effect4.Program.Typed.Contracts

/-- The counter and override are quiet fields; their updates use existing preservation. -/
theorem budget_fields {root : ProgramSource} {rootTy : EffTy} {w : World} {m : RState}
    {q : List RCmd} {f : RFiber} (typed : ConfigTyped root rootTy w m q)
    (look : m.fiber? f.id = some f) (count : Nat) (override : Option Bool) :
    ConfigTyped root rootTy w
      (m.update { f with currentOpCount := count, yieldOverride := override }) q := by
  have quiet : QuietEdit (fun x : RFiber =>
      { x with currentOpCount := count, yieldOverride := override }) :=
    { id := fun _ => rfl
      frame := fun _ => rfl
      running := fun _ => rfl
      parked := fun _ => rfl
      pending := fun _ => rfl
      finalizing := fun _ => rfl
      exit := fun _ => rfl
      dispatcher := fun _ => rfl
      context := fun _ => rfl
      observers := fun x => ⟨[], (List.append_nil _).symm, fun _ h => nomatch h⟩ }
  have moved := configTyped_modify_quiet typed f.id quiet
    (fun _ _ _ member => Or.inl member)
  simpa only [RunMachine.modify, look] using moved

/-- The loop's deferred-interrupt delivery keeps the actual saved stack. A direct race marker
uses its already-correlated token reply stack, as interruptRecord's existing proof does. -/
theorem top_keeps {root : ProgramSource} {rootTy : EffTy} {w : World} {m : RState}
    {rest : List RCmd} {f : RFiber} {y : Bool}
    (typed : ConfigTyped root rootTy w m (.loop f.id y :: rest))
    (look : m.fiber? f.id = some f) (running : f.running = true) :
    ConfigTyped root rootTy w (m.update (runloopTop f)) (.loop f.id y :: rest) := by
  cases deferred : f.frame.deferredInterrupt with
  | false =>
    have unchanged : runloopTop f = f := by
      change (if f.frame.deferredInterrupt then _ else f) = f
      rw [deferred]
      rfl
    rw [unchanged, rupdate_self look typed.machine.wide.fiberIds]
    exact typed
  | true =>
    let fr : RSaved := { f.frame with
      current := .pure (.failure f.frame.pendingCause), deferredInterrupt := false }
    have changed : runloopTop f = { f with frame := fr } := by
      change (if f.frame.deferredInterrupt then _ else f) = _
      rw [deferred]
      rfl
    rw [changed]
    refine (configTyped_frame_step typed rfl look running fr ?_ rfl).1 y
    intro final declared
    have old := typed.machine.fiber (rfiber?_mem look)
    obtain ⟨_, _, prov⟩ := old.position declared
    have newProv : InterruptProvenance fr :=
      ⟨prov.recorded, fun h => Bool.noConfusion h⟩
    cases marker : raceRegistrationR f.frame.current with
    | none =>
      obtain ⟨mid, _, stack, _⟩ := typed.code f (rfiber?_mem look) running
        ⟨y, Or.inl List.mem_cons_self⟩ marker final declared
      exact ⟨mid, TypedProg.pure (strongExit_of_clean w mid _ (pendingCause_clean prov)
        (pendingCause_noShapeDefect mid prov)), stack, newProv⟩
    | some raceId =>
      obtain ⟨_, resultTy, _, _, _, final0, declared0, stack, _⟩ := old.registration raceId marker
      have same : final0 = final := Option.some.inj (declared0.symm.trans declared)
      subst same
      exact ⟨resultTy, TypedProg.pure
        (strongExit_of_clean w resultTy _ (pendingCause_clean prov)
          (pendingCause_noShapeDefect resultTy prov)), stack, newProv⟩

/-- The body reached after the injected guard is typed independently of its saved callback;
unguard delivers the successful Yield reply through that saved callback. -/
theorem yield_body_typed (root : ProgramSource) (w : World) (previous : RProgram) :
    TypedProg root w (EffTy.pure .unit)
      (.vis (.inr (.yieldNow 0)) fun v =>
        .vis (.inr (.unguard (.success v))) (seqR fun _ => previous)) :=
  TypedProg.fiber (op := .yieldNow 0) (fun _ h => nomatch h) (fun _ h => nomatch h)
    (fun _ h => nomatch h) (fun _ _ _ h => nomatch h) () trivial (fun w' _ ans post => by
      change ans = Val.unit at post
      subst post
      exact TypedProg.unguard (ty := EffTy.pure .unit) ⟨trivial, trivial⟩)

/-- Executing the injected success guard saves either an ordinary constant callback or the
existing race's correlated registration callback; both meet the original host stack. -/
theorem injected_frame_code {root : ProgramSource} {rootTy : EffTy} {w : World} {m : RState}
    {rest : List RCmd} {f : RFiber} {y : Bool}
    (typed : ConfigTyped root rootTy w m (.loop f.id y :: rest))
    (look : m.fiber? f.id = some f) (running : f.running = true)
    (final : EffTy) (declared : w.Γ f.id = some final) :
    CodeOk root w m f.id final
      { f.frame with
        current := .vis (.inr (.yieldNow 0)) fun v =>
          .vis (.inr (.unguard (.success v))) (seqR fun _ => f.frame.current)
        stack := .resume .onSuccess (seqR fun _ => f.frame.current) :: f.frame.stack } := by
  have old := typed.machine.fiber (rfiber?_mem look)
  obtain ⟨_, _, prov⟩ := old.position declared
  refine ⟨EffTy.pure .unit, yield_body_typed root w f.frame.current, ?_, ⟨prov.recorded, prov.deferred⟩⟩
  cases marker : raceRegistrationR f.frame.current with
  | none =>
    obtain ⟨mid, current, stack, _⟩ := typed.code f (rfiber?_mem look) running
      ⟨y, Or.inl List.mem_cons_self⟩ marker final declared
    refine hostStack_push (.resume .onSuccess (seqR fun _ => f.frame.current) ?_ ?_) stack
    · intro later ord ex _ arm
      cases ex with
      | success v => exact typedProg_mono root w later mid f.frame.current ord current
      | failure c => cases arm
    · intro later _ ex admitted arm
      cases ex with
      | success v => cases arm
      | failure c => exact exitOk_failure_of_errorN (subN_never mid.error) admitted
  | some raceId =>
    obtain ⟨race, resultTy, found, hosted, token, final0, declared0, stack, _⟩ :=
      old.registration raceId marker
    have same : final0 = final := Option.some.inj (declared0.symm.trans declared)
    subst same
    exact .cons (.inr (.mk (fun _ => marker)
      (fun _ _ _ admitted => exitOk_failure_of_errorN (subN_never resultTy.error) admitted)
      found hosted token)) stack

/-- The same owned, running fiber can be continued by deliver instead of loop. -/
theorem loop_to_deliver {root : ProgramSource} {rootTy : EffTy} {w : World} {m : RState}
    {rest : List RCmd} {f : RFiber} {y : Bool}
    (typed : ConfigTyped root rootTy w m (.loop f.id y :: rest))
    (look : m.fiber? f.id = some f) (running : f.running = true) (y' : Bool) :
    ConfigTyped root rootTy w m (.deliver f.id y' :: rest) := by
  obtain ⟨f0, look0, _, parked⟩ := typed.queue.authority _ List.mem_cons_self
  have same : f0 = f := Option.some.inj (look0.symm.trans look)
  subst f0
  exact configTyped_cons_deliver (configTyped_tail typed) look running parked
    (owner_free typed.queue rfl) y'
    (fun marker ty declared => typed.code f (rfiber?_mem look) running
      ⟨y, Or.inl List.mem_cons_self⟩ marker ty declared)

/-- The full actual loop step, conditional only on the existing evaluator's operation/walk
clauses. The injected guard is reduced directly because a saved registration callback need
not make its temporary current wrapper TypedProg. -/
theorem loop_preserves_of_clauses (root : ProgramSource) (rootTy : EffTy)
    (fibers : ∀ op, FiberClauseKeeps root rootTy op)
    (stores : ∀ op, StoreClauseKeeps root rootTy op) (walk : WalkKeeps root rootTy)
    (id : FiberId) (y : Bool) : StepPreserves root rootTy (.loop id y) := by
  intro w m rest live typed
  letI := termEvaluatorFor root.program
  obtain ⟨f, hf, running, _⟩ := typed.queue.authority _ List.mem_cons_self
  have fid : f.id = id := rfiber?_id hf
  subst fid
  let top := runloopTop f
  let charged := countOp top
  have topId : top.id = f.id := by
    unfold top runloopTop
    split <;> rfl
  have chargedId : charged.id = f.id := topId
  have chargedRunning : charged.running = true := by
    change (runloopTop f).running = true
    unfold runloopTop
    split <;> exact running
  have chargedExit : charged.exit = f.exit := by
    change (runloopTop f).exit = f.exit
    unfold runloopTop
    split <;> rfl
  have topTyped := top_keeps typed hf running
  have topLook : (m.update top).fiber? top.id = some top := rfiber?_update_self hf topId
  have counted := budget_fields topTyped topLook (top.currentOpCount + 1) top.yieldOverride
  change ConfigTyped root rootTy w ((m.update top).update charged) (.loop f.id y :: rest) at counted
  rw [rupdate_rupdate m (show charged.id = top.id from rfl)] at counted
  have chargedTyped : ConfigTyped root rootTy w (m.update charged) (.loop charged.id y :: rest) := by
    rw [chargedId]
    exact counted
  have chargedLook : (m.update charged).fiber? charged.id = some charged :=
    rfiber?_update_self hf chargedId
  show ∃ w', w.leHost w' ∧ ConfigTyped root rootTy w'
    (driveStep (interpR root.program) m (.loop f.id y) rest).1
    (driveStep (interpR root.program) m (.loop f.id y) rest).2
  simp only [driveStep, hf]
  by_cases injects : (!y && !charged.preventYield && yieldVerdict charged) = true
  · let fr : RSaved := { charged.frame with
      current := .vis (.inr (.yieldNow 0)) fun v =>
        .vis (.inr (.unguard (.success v))) (seqR fun _ => charged.frame.current)
      stack := .resume .onSuccess (seqR fun _ => charged.frame.current) :: charged.frame.stack }
    let framed : RFiber := { charged with frame := fr }
    let g : RFiber := { framed with yieldOverride := none }
    let events : List (RunEvent EffName EffThunk Val Err Defect FiberId Ann Ctx RProgram Unit) :=
      [RunEvent.yieldInjected charged.id charged.currentOpCount]
    let wrapped : RFiber := { charged with
      yieldOverride := none
      frame := { charged.frame with current :=
        ((guardR .onSuccess (.vis (.inr (.yieldNow 0)) fun v => .pure (.success v))).bind
          (seqR fun _ => charged.frame.current)) } }
    have injected : injectYield m charged y = some ⟨m.emit events, wrapped, true, .continue_, []⟩ := by
      unfold injectYield
      rw [if_pos injects]
    have iterationEq : iteration (interpR root.program) m f y =
        ⟨m.emit events, g, true, .continue_, []⟩ := by
      calc
        iteration (interpR root.program) m f y =
            evaluateR (interpRAt root.program (m.emit events).completedExits)
              (m.emit events) wrapped true := by
          unfold iteration
          dsimp only
          rw [injected]
        _ = ⟨m.emit events, g, true, .continue_, []⟩ := rfl
    have frameTyped := (configTyped_frame_step chargedTyped rfl chargedLook chargedRunning fr
      (fun ty declared => injected_frame_code chargedTyped chargedLook chargedRunning ty declared)
      rfl).1 true
    change ConfigTyped root rootTy w ((m.update charged).update framed)
      (.loop charged.id true :: rest) at frameTyped
    rw [rupdate_rupdate m (show framed.id = charged.id from rfl)] at frameTyped
    have framedLook : (m.update framed).fiber? framed.id = some framed :=
      rfiber?_update_self hf chargedId
    have output := budget_fields frameTyped framedLook charged.currentOpCount none
    change ConfigTyped root rootTy w ((m.update framed).update g)
      (.loop charged.id true :: rest) at output
    rw [rupdate_rupdate m (show g.id = framed.id from rfl)] at output
    have emitted := configTyped_emit output events
    rw [chargedId] at emitted
    rw [iterationEq]
    exact ⟨w, leHost_refl w, emitted⟩
  · have noInjection : injectYield m charged y = none := by
      unfold injectYield
      rw [if_neg injects]
    have iterationEq : iteration (interpR root.program) m f y =
        evaluateR (interpRAt root.program m.completedExits) m charged y := by
      unfold iteration
      dsimp only
      rw [noInjection]
    have ev : Evaluating root rootTy w m rest charged y :=
      ⟨loop_to_deliver chargedTyped chargedLook chargedRunning y,
        ⟨f, by rw [chargedId]; exact hf, chargedExit.symm⟩, chargedRunning, live⟩
    have keeps := evaluate_keeps fibers stores walk ev
    rw [chargedId] at keeps
    rw [iterationEq]
    exact keeps

end LoopPrefix


/-! ## The walk: an exit delivered through the saved stack

`unguard`, `finishFinalizer` and a bare exit deliver an exit through the fiber's saved stack
(`deliverR`, `popR`); the walk over a host stack is typed (`HostWalk.lean`). Four outcomes: typed
code over the remaining stack (a frame-only step), a scope's exit callback (its close is the one
premise below, finding F-WF of the receipt), a race registration marker (the fiber's registration
clause), or the exit the whole stack delivered (`finish` queued). -/

/-- A registration marker current is the race's `raceRegister` operation. -/
theorem raceRegistrationR_shape {p : RProgram} {r : Nat} (h : raceRegistrationR p = some r) :
    ∃ k, p = .vis (.inr (.raceRegister r)) k := by
  cases p with
  | pure _ => cases h
  | vis op k =>
    cases op with
    | inl _ => cases h
    | inr fop =>
      cases fop with
      | raceRegister _ =>
        cases h
        exact ⟨k, rfl⟩
      | _ => cases h

/-- A walk that completes leaves the stack empty and the current code as it was handed. -/
theorem popR_done (interp : RInterp) (ex : ExitV) (s : List ScopeFrame) (frame : RSaved) :
    ∀ ex', (popR interp ex s frame).2 = some ex' →
      (popR interp ex s frame).1.stack = [] ∧ (popR interp ex s frame).1.current = frame.current := by
  fun_induction popR interp ex s frame <;> aesop

/-- **The frame step for a registration marker** (decisions row 188 (b)): a walk that stopped at a
registration arrow leaves the race's marker current over a host stack at the token's type
(`HostMarker`); the fiber is typed by its registration clause and the queued `loop` reads no code. -/
theorem configTyped_frame_marker {root : ProgramSource} {rootTy : EffTy} {w : World} {m : RState}
    {c : RCmd} {rest : List RCmd} {f : RFiber} (typed : ConfigTyped root rootTy w m (c :: rest))
    (owner : Guard.commandOwner m c = some f.id) (hf : m.fiber? f.id = some f)
    (running : f.running = true) (fr : RSaved) {ty : EffTy} (declared : w.Γ f.id = some ty)
    (marker : HostMarker root w m f.id ty fr) (y : Bool) :
    ConfigTyped root rootTy w (m.update { f with frame := fr }) (.loop f.id y :: rest) := by
  let g : RFiber := { f with frame := fr }
  have hmem : f ∈ m.fibers := rfiber?_mem hf
  have old := typed.machine.fiber hmem
  obtain ⟨raceId, race, resultTy, hmark, found, host, token, stack, prov⟩ := marker
  have notParked : f.parked = .notParked := by
    cases hp : f.parked with
    | notParked => rfl
    | withGuard _ =>
      have idle := old.parkedIdle (by rw [hp]; exact fun h => nomatch h)
      rw [running] at idle
      cases idle
  have look : (m.update g).fiber? g.id = some g := rfiber?_update_self hf rfl
  have fresh : FiberTyped root w (m.update g) g :=
    fiberTyped_frame old hf running fr
      (fun ty' declared' => by
        have same : ty' = ty := Option.some.inj (declared'.symm.trans declared)
        subst same
        exact ⟨resultTy, positionStack_of_host stack⟩)
      prov
      (fun raceId' hm => by
        rw [hmark] at hm
        cases hm
        exact ⟨race, resultTy, ty, found, host, token, declared, stack⟩)
  have edited := configTyped_frame_edit typed owner hf running fr fresh
  have freeG : g.id ∉ rest.filterMap (Guard.commandOwner (m.update g)) := by
    rw [commandOwner_rupdate]
    exact owner_free typed.queue owner
  refine configTyped_cons_loop edited look running notParked freeG y (fun hnone => ?_)
  change raceRegistrationR fr.current = none at hnone
  rw [hmark] at hnone
  cases hnone

/-- **The frame step for a completed walk** (decisions row 134 (c)): the exit the stack delivered is
the fiber's at its declaration (the queue's payload), the stack is empty (`finish`'s delivery
clause), and the queued `finish` reads no code. -/
theorem configTyped_frame_finish {root : ProgramSource} {rootTy : EffTy} {w : World} {m : RState}
    {c : RCmd} {rest : List RCmd} {f : RFiber} (typed : ConfigTyped root rootTy w m (c :: rest))
    (owner : Guard.commandOwner m c = some f.id) (hf : m.fiber? f.id = some f)
    (running : f.running = true) (fr : RSaved) (empty : fr.stack = [])
    (prov : InterruptProvenance fr) (marker : raceRegistrationR fr.current = none) (ex : ExitV)
    (exit : ∀ ty, w.Γ f.id = some ty → ExitOk w ty ex) :
    ConfigTyped root rootTy w (m.update { f with frame := fr }) (.finish f.id ex :: rest) := by
  let g : RFiber := { f with frame := fr }
  have hmem : f ∈ m.fibers := rfiber?_mem hf
  have old := typed.machine.fiber hmem
  have notParked : f.parked = .notParked := by
    cases hp : f.parked with
    | notParked => rfl
    | withGuard _ =>
      have idle := old.parkedIdle (by rw [hp]; exact fun h => nomatch h)
      rw [running] at idle
      cases idle
  have look : (m.update g).fiber? g.id = some g := rfiber?_update_self hf rfl
  have fresh : FiberTyped root w (m.update g) g :=
    fiberTyped_frame old hf running fr (fun ty _ => ⟨ty, by rw [empty]; exact .nil ty⟩) prov
      (fun _ h => by rw [marker] at h; cases h)
  have edited := configTyped_frame_edit typed owner hf running fr fresh
  refine configTyped_cons_plain edited (.finish f.id ex) exit ⟨g, look, running, notParked⟩ ?_ ?_
    trivial rfl (fun _ _ _ h => nomatch h) (fun _ _ h => nomatch h) (fun _ _ _ h => nomatch h)
    (fun _ _ _ _ _ h => nomatch h) (fun _ _ h => nomatch h) (fun _ _ h => nomatch h)
  · intro x hx
    rw [look] at hx
    cases hx
    exact empty
  · intro o ho
    cases ho
    rw [commandOwner_rupdate]
    exact owner_free typed.queue owner

/-- **The scoped-exit callback's close** (finding F-WF of the receipt): the walk stopped at a
`scoped` guard's slot and left the scope's exit callback current (`HostCallback`), which
`prepareScopedExitR` consumes: it closes the scope and restores the context. Isolated as the one
premise of the walk: re-establishing `J`'s store well-formedness needs the closing exit `validIn`
the store, which membership at `unknown` does not give; the repair is the owner's. -/
def ScopedExitKeeps (root : ProgramSource) (rootTy : EffTy) : Prop :=
  ∀ (w : World) (m : RState) (rest : List RCmd) (f : RFiber) (y : Bool) (fr : RSaved),
    Evaluating root rootTy w m rest f y →
    (∀ ty, w.Γ f.id = some ty → HostCallback root w (m.update f) f.id ty fr) →
    SettlesTyped root rootTy w f.id rest
      (prepareIterR ⟨m, { f with frame := fr }, y, .continue_, []⟩)

/-- **A walk that stopped at a registration marker settles typed**: the glue leaves the marker, and
`settle` queues `loop`, which reads no code of a marker-current fiber. -/
theorem Evaluating.settle_marker {root : ProgramSource} {rootTy : EffTy} {w : World} {m : RState}
    {rest : List RCmd} {f : RFiber} {y : Bool} (ev : Evaluating root rootTy w m rest f y)
    (fr : RSaved) {ty : EffTy} (declared : w.Γ f.id = some ty)
    (marker : HostMarker root w (m.update f) f.id ty fr) :
    SettlesTyped root rootTy w f.id rest
      (prepareIterR ⟨m, { f with frame := fr }, y, .continue_, []⟩) := by
  have ⟨raceId, _, _, hmark, _⟩ := marker
  obtain ⟨k, hk⟩ := raceRegistrationR_shape hmark
  have inert : prepareIterR ⟨m, { f with frame := fr }, y, .continue_, []⟩ =
      ⟨m, { f with frame := fr }, y, .continue_, []⟩ := by
    obtain ⟨cur, stk, intr, ic, di⟩ := fr
    change cur = _ at hk
    subst hk
    rfl
  rw [inert]
  have step := configTyped_frame_marker ev.typed rfl ev.look ev.running fr declared marker y
  rw [rupdate_rupdate m (show ({ f with frame := fr } : RFiber).id = f.id from rfl)] at step
  exact ⟨w, leHost_refl w, step⟩

/-- **A walk that delivered its exit settles typed**: the glue prepares the (typed) current code the
walk left in place, the callback is idle on it, and `settle` queues `finish` with the exit. -/
theorem Evaluating.settle_finished {root : ProgramSource} {rootTy : EffTy} {w : World} {m : RState}
    {rest : List RCmd} {f : RFiber} {y : Bool} (ev : Evaluating root rootTy w m rest f y)
    (fr : RSaved) (empty : fr.stack = []) (cur : fr.current = f.frame.current)
    (prov : InterruptProvenance fr) (marker : raceRegistrationR f.frame.current = none)
    (ex : ExitV) (exit : ∀ ty, w.Γ f.id = some ty → ExitOk w ty ex) :
    SettlesTyped root rootTy w f.id rest
      (prepareIterR ⟨m, { f with frame := fr }, y, .finished ex, []⟩) := by
  obtain ⟨ty, declared⟩ := ev.declared
  obtain ⟨tin, current, _, _⟩ := ev.code marker ty declared
  let fr' : RSaved := { fr with current := prepareR m.completedExits fr.current }
  have prepared : TypedProg root w tin fr'.current := by
    show TypedProg root w tin (prepareR m.completedExits fr.current)
    rw [cur]
    exact prepareR_typed _ _ ev.view current
  have glue : prepareIterR ⟨m, { f with frame := fr }, y, .finished ex, []⟩ =
      ⟨m, { f with frame := fr' }, y, .finished ex, []⟩ :=
    prepareScopedExitR_of_typed prepared
  rw [glue]
  have step := configTyped_frame_finish ev.typed rfl ev.look ev.running fr' empty
    ⟨prov.recorded, prov.deferred⟩ (raceRegistrationR_typed prepared) ex exit
  rw [rupdate_rupdate m (show ({ f with frame := fr' } : RFiber).id = f.id from rfl)] at step
  exact ⟨w, leHost_refl w, step⟩

/-- **A delivery through the saved stack settles typed**, given the scoped-exit close: a success
with a deferred interrupt installs the recorded cause as typed code; otherwise the walk over the
host stack (`popR_hostTyped`, the hook laws of the machine's interpreter at the typed view) ends
in typed code, the callback, a marker or the delivered exit, each settled by its frame step. -/
theorem Evaluating.deliver_keeps {root : ProgramSource} {rootTy : EffTy}
    (close : ScopedExitKeeps root rootTy) {w : World} {m : RState} {rest : List RCmd} {f : RFiber}
    {y : Bool} (ev : Evaluating root rootTy w m rest f y)
    (marker : raceRegistrationR f.frame.current = none) (ex : ExitV)
    (payload : ∀ tin, TypedProg root w tin f.frame.current → ExitOk w tin ex) :
    SettlesTyped root rootTy w f.id rest
      (prepareIterR (deliverR (interpRAt root.program m.completedExits) m f y ex)) := by
  obtain ⟨ty, declared⟩ := ev.declared
  have same : ∀ ty', w.Γ f.id = some ty' → ty' = ty :=
    fun _ h => Option.some.inj (h.symm.trans declared)
  obtain ⟨tin, current, stack, prov⟩ := ev.code marker ty declared
  have hex := payload tin current
  have laws := hookLawsAt_interpRAt root w m.completedExits ev.view
  rcases deliverR_cases (interpRAt root.program m.completedExits) m f y ex with h | h <;> rw [h]
  · have walk := popR_hostTyped root _ w (m.update f) f.id laws stack ex
      { f.frame with deferredInterrupt := false } hex ⟨prov.recorded, fun h => nomatch h⟩
    have done := popR_done (interpRAt root.program m.completedExits) ex f.frame.stack
      { f.frame with deferredInterrupt := false }
    have ints := popR_interrupts (interpRAt root.program m.completedExits) ex f.frame.stack
      { f.frame with deferredInterrupt := false }
    unfold walkIter
    revert walk done ints
    generalize popR (interpRAt root.program m.completedExits) ex f.frame.stack
      { f.frame with deferredInterrupt := false } = r
    obtain ⟨frame, o⟩ := r
    intro walk done ints
    have prov' : InterruptProvenance frame :=
      ⟨fun c hc => prov.recorded c (by rw [← ints.1]; exact hc),
        fun h => by rw [ints.2] at h; exact nomatch h⟩
    cases o with
    | none =>
      rcases walk with code | callback | hmarker
      · exact ev.settle_continue frame (fun ty' d => by rw [same ty' d]; exact code)
      · exact close w m rest f y frame ev (fun ty' d => by rw [same ty' d]; exact callback)
      · exact ev.settle_marker frame declared hmarker
    | some ex' =>
      obtain ⟨empty, cur⟩ := done ex' rfl
      exact ev.settle_finished frame empty cur prov' marker ex'
        (fun ty' d => by rw [same ty' d]; exact walk)
  · exact ev.settle_continue _ (fun ty' d => by
      obtain ⟨tin', _, stack', prov''⟩ := ev.code marker ty' d
      exact ⟨tin', TypedProg.pure (strongExit_of_clean w tin' _ (pendingCause_clean prov'')
        (pendingCause_noShapeDefect tin' prov'')), stack', ⟨prov''.recorded, fun h => nomatch h⟩⟩)

/-- **The walk keeps `I`**, given the scoped-exit close: a bare exit is typed at the current code's
type (`TypedProg.pure_inv`). -/
theorem walkKeeps_of_scopedExit {root : ProgramSource} {rootTy : EffTy}
    (close : ScopedExitKeeps root rootTy) : WalkKeeps root rootTy := by
  intro w m rest f y ex ev hc
  exact ev.deliver_keeps close (by rw [hc]; rfl) ex
    (fun tin current => by rw [hc] at current; exact TypedProg.pure_inv current)

/-- **`unguard`**: the guard's exit is delivered through the saved stack (`TypedProg.unguard`'s
payload is typed at the code's type). -/
theorem clause_unguard {root : ProgramSource} {rootTy : EffTy} (close : ScopedExitKeeps root rootTy)
    (ex : ExitV) : FiberClauseKeeps root rootTy (.unguard ex) := by
  intro w m rest f y next ev hc
  show SettlesTyped root rootTy w f.id rest
    (prepareIterR (deliverR (interpRAt root.program m.completedExits) m f y ex))
  exact ev.deliver_keeps close (by rw [hc]; rfl) ex
    (fun tin current => by rw [hc] at current; exact unguard_payload_inv root w tin ex next current)

/-- **`finishFinalizer`**: the finalizer's restored exit is delivered through the saved stack. -/
theorem clause_finishFinalizer {root : ProgramSource} {rootTy : EffTy}
    (close : ScopedExitKeeps root rootTy) (ex : ExitV) :
    FiberClauseKeeps root rootTy (.finishFinalizer ex) := by
  intro w m rest f y next ev hc
  show SettlesTyped root rootTy w f.id rest
    (prepareIterR (deliverR (interpRAt root.program m.completedExits) m f y ex))
  exact ev.deliver_keeps close (by rw [hc]; rfl) ex
    (fun tin current => by
      rw [hc] at current
      exact finishFinalizer_payload_inv root w tin ex next current)


/-! ## The clauses that edit the fiber's context -/

/-- The evaluator's machine after a trace event is the evaluated state's machine with that event. -/
theorem Evaluating.emit {root : ProgramSource} {rootTy : EffTy} {w : World} {m : RState}
    {rest : List RCmd} {f : RFiber} {y : Bool} (ev : Evaluating root rootTy w m rest f y)
    (events : List (RunEvent EffName EffThunk Val Err Defect FiberId Ann Ctx RProgram Unit)) :
    Evaluating root rootTy w (m.emit events) rest f y :=
  ⟨configTyped_emit ev.typed events, ev.stale, ev.running, ev.live⟩

/-- **A running fiber's context moves** to one whose services fit (`setContext`'s pre, decisions row
90; `scoped`'s `withScope`), with its cached budget: every clause of `J` at the fiber but the
services reads fields the edit keeps; the queue's owner and reads are the fiber's own. -/
theorem Evaluating.recontext {root : ProgramSource} {rootTy : EffTy} {w : World} {m : RState}
    {rest : List RCmd} {f : RFiber} {y : Bool} (ev : Evaluating root rootTy w m rest f y)
    (ctx : Ctx) (services : ServicesFit w ctx.services) (maxOps : Nat) (prevent : Bool) :
    Evaluating root rootTy w m rest
      { f with context := ctx, maxOpsBeforeYield := maxOps, preventYield := prevent } y := by
  let g : RFiber := { f with context := ctx, maxOpsBeforeYield := maxOps, preventYield := prevent }
  have look := ev.look
  have hmem : f ∈ (m.update f).fibers := rfiber?_mem look
  have old := ev.typed.machine.fiber hmem
  have notParked : f.parked = .notParked := by
    cases hp : f.parked with
    | notParked => rfl
    | withGuard _ =>
      have idle := old.parkedIdle (by rw [hp]; exact fun h => nomatch h)
      rw [ev.running] at idle
      cases idle
  have lookG : ((m.update f).update g).fiber? g.id = some g := rfiber?_update_self look rfl
  have view : ObsView (m.update f) ((m.update f).update g) :=
    obsView_rupdate look rfl (PendingWeaker.refl _)
  have moved := fiberTyped_transport old view (Nat.le_refl _) (Nat.le_refl _)
  have fresh : FiberTyped root w ((m.update f).update g) g :=
    ⟨⟨moved.ok.c0, moved.ok.c1, moved.ok.c2, moved.ok.c3, moved.ok.c4, services⟩, moved.delivery,
      moved.below, moved.pendingShape, moved.parkedIdle, moved.parkedBelow, moved.exited,
      moved.exitedStack, moved.deferredCause, moved.pendingOwner, moved.observers,
      moved.registration, moved.code, moved.tokens, moved.raceObservers, moved.targetsBelow,
      moved.observersBelow⟩
  have free := owner_free_rest ev.typed.queue (c := .deliver f.id y) rfl
  have typed : ConfigTyped root rootTy w ((m.update f).update g) (.deliver f.id y :: rest) := by
    refine configTyped_rupdate_code ev.typed look rfl (PendingWeaker.refl _) rfl (fun p => p)
      (fun k hk => Or.inl (fiberKeys_internal hmem hk)) ?_ ?_ ?_ fresh
    · intro token r hr
      have off : g.parked ≠ .withGuard token := by
        show f.parked ≠ _
        rw [notParked]
        exact fun h => nomatch h
      rw [requestOfR_of_not_parked lookG off] at hr
      cases hr
    · intro c hc h
      rcases List.mem_cons.mp hc with rfl | hc
      · exact ⟨g, lookG, ev.running, notParked⟩
      · exact commandAuthority_frame (g := g) look rfl rfl rfl rfl c (free c hc) h
    · intro _ _ marker ty declared
      exact codeOk_races (m := m.update f) (m' := (m.update f).update g)
        (racesKept_of_eq fun _ => rfl) (ev.code marker ty declared)
  rw [rupdate_rupdate m (show g.id = f.id from rfl)] at typed
  obtain ⟨f0, hf0, exit0⟩ := ev.stale
  exact ⟨typed, ⟨f0, hf0, exit0⟩, ev.running, ev.live⟩

/-- **`setContext`**: the context set (its services fit, the pre), the budget cached from it, the
trace event, and `unit` answered. -/
theorem clause_setContext (root : ProgramSource) (rootTy : EffTy) (ctx : Ctx) :
    FiberClauseKeeps root rootTy (.setContext ctx) := by
  intro w m rest f y next ev hc
  obtain ⟨ty, declared⟩ := ev.declared
  obtain ⟨tin, current, _, _⟩ := ev.code (by rw [hc]; rfl) ty declared
  rw [hc] at current
  obtain ⟨_, pre, _⟩ := TypedProg.fiber_inv current (fun _ h => nomatch h) (fun _ h => nomatch h)
    (fun _ h => nomatch h) (fun _ _ _ h => nomatch h)
  show SettlesTyped root rootTy w f.id rest
    (prepareIterR (FiberAction.setContext _ m f y ctx (answerWith next)))
  unfold FiberAction.setContext
  rcases hb : (interpRAt root.program m.completedExits).budgetOf ctx with ⟨maxOps, prevent⟩
  have ev' := (ev.recontext ctx pre maxOps prevent).emit [RunEvent.contextSet f.id ctx]
  exact ev'.settle_continue _ (ev'.answer_typed hc
    (by show raceRegistrationR f.frame.current = none; rw [hc]; rfl) (fun _ h => nomatch h)
    (fun _ h => nomatch h) (fun _ h => nomatch h) (fun _ _ _ h => nomatch h) .unit
    (fun _ _ => rfl))

/-- **`getId`**: the fiber's own id, answered as a number. -/
theorem clause_getId (root : ProgramSource) (rootTy : EffTy) :
    FiberClauseKeeps root rootTy .getId := by
  intro w m rest f y next ev hc
  exact ev.settle_continue _ (ev.answer_typed hc (by rw [hc]; rfl) (fun _ h => nomatch h)
    (fun _ h => nomatch h) (fun _ h => nomatch h) (fun _ _ _ h => nomatch h) (Val.nat f.id.value)
    (fun _ _ => ⟨f.id, rfl⟩))

/-- **`ambientScope`**: the context's ambient scope, present by `J` (`ambientScope_live`, decisions
row 156), answered as its handle; without one, the `missingService` defect, which the exit judgment
admits at every type (part one excludes only `badName` and `notImplemented`). -/
theorem clause_ambientScope (root : ProgramSource) (rootTy : EffTy) :
    FiberClauseKeeps root rootTy .ambientScope := by
  intro w m rest f y next ev hc
  show SettlesTyped root rootTy w f.id rest
    (prepareIterR (FiberAction.ambientScope _ m f y (answerWith next)))
  unfold FiberAction.ambientScope
  rw [show (interpRAt root.program m.completedExits).ambientScope = Ctx.ambientScope from rfl]
  cases hscope : Ctx.ambientScope f.context with
  | some scope =>
    have live : ScopeLive w scope :=
      ambientScope_live ev.typed.machine (rfiber?_mem ev.look) hscope
    exact ev.settle_continue _ (ev.answer_typed hc (by rw [hc]; rfl) (fun _ h => nomatch h)
      (fun _ h => nomatch h) (fun _ h => nomatch h) (fun _ _ _ h => nomatch h)
      (Val.scopeHandle scope) (fun _ _ => fits_scopeHandle _ _ live))
  | none =>
    refine ev.settle_continue { f.frame with current := .pure (.failure (Cause.die .missingService)) }
      (fun ty declared => ?_)
    obtain ⟨tin, _, stack, prov⟩ := ev.code (by rw [hc]; rfl) ty declared
    refine ⟨tin, TypedProg.pure (strongExit_of_clean w tin _ rfl ?_), stack,
      ⟨prov.recorded, prov.deferred⟩⟩
    intro reason member
    simp only [Cause.die_reasons, List.mem_singleton] at member
    subst member
    exact ⟨(fun h => nomatch h), (fun h => nomatch h)⟩

end Effect4.Program.Typed
