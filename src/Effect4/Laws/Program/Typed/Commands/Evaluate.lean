import Effect4.Laws.Program.Typed.Commands.Observe
import Effect4.Laws.Program.Typed.Body
import Effect4.Laws.Program.Typed.HostWalk

/-!
# Laws.Program.Typed.Commands.Evaluate — the evaluation step as handler soundness

Concept 4 (the configuration invariant `I`); questions `deliver_preserves` and
`loop_preserves`. `deliver` settles one evaluation of the fiber's current code
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

Not established here: the clauses proved in `Clauses/*` (every clause is assembled in
`Clauses/All.lean`); progress.
-/

set_option autoImplicit false
namespace Effect4.Program.Typed
open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Sched Effect4.Program.Denote
open Contracts

/-! ## The frame of the fiber a queued `loop` or `deliver` owns -/

/-- Every fiber but `id` keeps its stack, provenance and mask from `m` to `m'`. -/
def StackViewExcept (m m' : RState) (id : FiberId) : Prop :=
  ∀ i f', i ≠ id → m'.fiber? i = some f' → ∃ f, m.fiber? i = some f ∧ f'.id = f.id ∧
    f'.frame.stack = f.frame.stack ∧ (InterruptProvenance f.frame → InterruptProvenance f'.frame) ∧
    MaskView f f'

/-- Editing fiber `g` keeps every other fiber's stack. -/
theorem stackViewExcept_rupdate {m : RState} {f g : RFiber} (hid : g.id = f.id) :
    StackViewExcept m (m.update g) f.id := by
  intro i f' hi hf'
  rw [rfiber?_update_other (fun h => hi (h.trans hid))] at hf'
  exact ⟨f', hf', rfl, rfl, id, MaskView.refl f'⟩

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
    obtain ⟨f, hf, hid, hstack, hprov, hmask⟩ := view host f' (fun e => owner (by rw [e]; rfl)) hf'
    obtain ⟨replyTy, ok, stack⟩ := h f hf
    exact ⟨replyTy, ok, stackReply_view kept hid hstack hprov hmask stack⟩
  | raceCancel _ host _ remaining visited =>
    intro f' hf'
    obtain ⟨f, hf, hid, hstack, hprov, hmask⟩ := view host f' (fun e => owner (by rw [e]; rfl)) hf'
    obtain ⟨answer, error, cols, stack⟩ := h f hf
    exact ⟨answer, error, cols, stackReply_view kept hid hstack hprov hmask stack⟩
  | closeParAwait host _ targets =>
    intro f' hf'
    obtain ⟨f, hf, hid, hstack, hprov, hmask⟩ := view host f' (fun e => owner (by rw [e]; rfl)) hf'
    obtain ⟨answer, error, row, cols, protocol, stack⟩ := h f hf
    exact ⟨answer, error, row, cols, protocol, stackReplyAt_view kept hid hstack hprov hmask stack⟩
  | finish host _ =>
    intro f' hf'
    obtain ⟨f, hf, _, hstack, _, _⟩ := view host f' (fun e => owner (by rw [e]; rfl)) hf'
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
      ∀ ty, w.Γ g.id = some ty → MCodeOk root w (m.update g) g ty)
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
    · exact Or.inl (readG hrun reads marker ty declared)
    · exact (code x hold hrun reads marker ty declared).races (racesKept_of_eq view.races)
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
      MCodeOk root w m f ty) :
    ConfigTyped root rootTy w m (.deliver f.id yielding :: q) := by
  have wide := typed.machine.wide
  refine ⟨typed.machine, ?_, queueOk_cons ?_ typed.queue⟩
  · intro x hx run reads marker ty declared
    by_cases same : x.id = f.id
    · have xf : x = f := rfiber?_same hf (rfiber?_of_mem wide.fiberIds hx) same
      rw [xf] at marker declared ⊢
      exact Or.inl (code marker ty declared)
    · obtain ⟨y, r⟩ := reads
      refine (typed.code x hx run ⟨y, ?_⟩ marker ty declared).cons fun y' h => ?_
      · rcases r with r | r
        · rcases List.mem_cons.mp r with h | h
          · cases h
          · exact Or.inl h
        · rcases List.mem_cons.mp r with h | h
          · injection h with hid _
            exact absurd hid same
          · exact Or.inr h
      · injection h with hid _
        exact absurd hid.symm same
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

/-- The fiber `f` with a new context, its cached budget, and a new frame: what a step of `f` that
moves its context installs (`setContext`, `scoped`, a scope's exit callback). -/
abbrev resetFiber (f : RFiber) (ctx : Ctx) (maxOps : Nat) (prevent : Bool) (fr : RSaved) : RFiber :=
  { f with context := ctx, maxOpsBeforeYield := maxOps, preventYield := prevent, frame := fr }

/-- **A running fiber whose context and frame move stays typed**: every clause but the position and
the services reads fields the edit keeps, or is vacuous at a running fiber (not parked, not
exited); the new context's services fit; a race registration marker current carries its
registration facts (`RegistrationState`, decisions row 188 (b)). -/
theorem fiberTyped_reset {root : ProgramSource} {w : World} {m : RState} {f : RFiber}
    (old : FiberTyped root w m f) (hf : m.fiber? f.id = some f) (running : f.running = true)
    (ctx : Ctx) (services : ServicesFit w ctx.services) (maxOps : Nat) (prevent : Bool) (fr : RSaved)
    (position : ∀ ty, w.Γ f.id = some ty →
      ∃ tin flag, MPositionStack root w tin (finalPos ty flag) fr.stack)
    (prov : InterruptProvenance fr)
    (registration : ∀ raceId, raceRegistrationR fr.current = some raceId →
      ∃ race resultTy, m.race? raceId = some race ∧ race.host = f.id ∧
        w.Θ race.host race.token = some resultTy ∧
        RaceReply root w m (resetFiber f ctx maxOps prevent fr) race resultTy) :
    FiberTyped root w (m.update (resetFiber f ctx maxOps prevent fr))
      (resetFiber f ctx maxOps prevent fr) := by
  have view : ObsView m (m.update (resetFiber f ctx maxOps prevent fr)) :=
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
  refine ⟨⟨⟨fun ty declared => ?_⟩, moved.ok.c1, moved.ok.c2, moved.ok.c3, moved.ok.c4,
      services⟩, fun token hp => ?_, moved.below, moved.pendingShape, moved.parkedIdle,
    moved.parkedBelow, moved.exited, fun hx => ?_, fun _ => ?_, moved.pendingOwner,
    moved.observers, fun raceId hm => ?_, fun _ hr _ _ _ _ => ?_, moved.tokens,
    moved.raceObservers, moved.targetsBelow, moved.observersBelow, moved.children⟩
  · obtain ⟨tin, flag, stack⟩ := position ty declared
    exact ⟨tin, flag, stack, prov⟩
  · change f.parked = .withGuard token at hp
    rw [notParked] at hp
    cases hp
  · change f.exit.isSome = true at hx
    rw [live] at hx
    cases hx
  · exact prov.deferred (by assumption)
  · obtain ⟨race, resultTy, found, host, token, reply⟩ := registration raceId hm
    exact ⟨race, resultTy, found, host, token,
      reply.races (m := m) (m' := m.update (resetFiber f ctx maxOps prevent fr))
        (racesKept_of_eq fun _ => rfl)⟩
  · change f.running = false at hr
    rw [running] at hr
    cases hr

/-- **A running fiber whose frame moves stays typed**: `fiberTyped_reset` at the fiber's own
context. -/
theorem fiberTyped_frame {root : ProgramSource} {w : World} {m : RState} {f : RFiber}
    (old : FiberTyped root w m f) (hf : m.fiber? f.id = some f) (running : f.running = true)
    (fr : RSaved)
    (position : ∀ ty, w.Γ f.id = some ty →
      ∃ tin flag, MPositionStack root w tin (finalPos ty flag) fr.stack)
    (prov : InterruptProvenance fr)
    (registration : ∀ raceId, raceRegistrationR fr.current = some raceId →
      ∃ race resultTy, m.race? raceId = some race ∧ race.host = f.id ∧
        w.Θ race.host race.token = some resultTy ∧
        RaceReply root w m { f with frame := fr } race resultTy) :
    FiberTyped root w (m.update { f with frame := fr }) { f with frame := fr } :=
  fiberTyped_reset old hf running f.context old.ok.c5 f.maxOpsBeforeYield f.preventYield fr
    position prov registration

/-- **The fiber edit of a step**: from a typed configuration headed by the `loop` or `deliver` that
owns the running fiber `f`, a new record of `f` with a new context, budget and frame that keeps `f`
typed gives the configuration with the record installed and the head dropped. No other command
owns `f` (`QueueOk.owners`), so no delivery reads its stack and no `loop` or `deliver` its code. -/
theorem configTyped_reset_edit {root : ProgramSource} {rootTy : EffTy} {w : World} {m : RState}
    {c : RCmd} {rest : List RCmd} {f : RFiber} (typed : ConfigTyped root rootTy w m (c :: rest))
    (owner : Guard.commandOwner m c = some f.id) (hf : m.fiber? f.id = some f)
    (running : f.running = true) (ctx : Ctx) (maxOps : Nat) (prevent : Bool) (fr : RSaved)
    (fresh : FiberTyped root w (m.update (resetFiber f ctx maxOps prevent fr))
      (resetFiber f ctx maxOps prevent fr)) :
    ConfigTyped root rootTy w (m.update (resetFiber f ctx maxOps prevent fr)) rest := by
  let g : RFiber := resetFiber f ctx maxOps prevent fr
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

/-- **The fiber edit of a frame step**: `configTyped_reset_edit` at the fiber's own context. -/
theorem configTyped_frame_edit {root : ProgramSource} {rootTy : EffTy} {w : World} {m : RState}
    {c : RCmd} {rest : List RCmd} {f : RFiber} (typed : ConfigTyped root rootTy w m (c :: rest))
    (owner : Guard.commandOwner m c = some f.id) (hf : m.fiber? f.id = some f)
    (running : f.running = true) (fr : RSaved)
    (fresh : FiberTyped root w (m.update { f with frame := fr }) { f with frame := fr }) :
    ConfigTyped root rootTy w (m.update { f with frame := fr }) rest :=
  configTyped_reset_edit typed owner hf running f.context f.maxOpsBeforeYield f.preventYield fr fresh

/-- **The step**: from a typed configuration headed by the `loop` or `deliver` that owns the
running fiber `f`, a new record of `f` with a context whose services fit, its budget, and a frame
whose code is typed at that context (its current code no race registration marker) gives the
configuration with the record installed, under either head. Every frame-only and
context-moving clause ends here. -/
theorem configTyped_reset_step {root : ProgramSource} {rootTy : EffTy} {w : World} {m : RState}
    {c : RCmd} {rest : List RCmd} {f : RFiber} (typed : ConfigTyped root rootTy w m (c :: rest))
    (owner : Guard.commandOwner m c = some f.id) (hf : m.fiber? f.id = some f)
    (running : f.running = true) (ctx : Ctx) (services : ServicesFit w ctx.services) (maxOps : Nat)
    (prevent : Bool) (fr : RSaved)
    (code : ∀ ty, w.Γ f.id = some ty → MCodeOk root w m (resetFiber f ctx maxOps prevent fr) ty)
    (marker : raceRegistrationR fr.current = none) :
    (∀ y, ConfigTyped root rootTy w (m.update (resetFiber f ctx maxOps prevent fr))
      (.loop f.id y :: rest)) ∧
    (∀ y, ConfigTyped root rootTy w (m.update (resetFiber f ctx maxOps prevent fr))
      (.deliver f.id y :: rest)) := by
  let g : RFiber := resetFiber f ctx maxOps prevent fr
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
    obtain ⟨_, _, _, _, _, _, _, p⟩ := code ty declared
    exact p
  have look : (m.update g).fiber? g.id = some g := rfiber?_update_self hf rfl
  have fresh : FiberTyped root w (m.update g) g :=
    fiberTyped_reset old hf running ctx services maxOps prevent fr
      (fun ty' declared' => by
        obtain ⟨_, tin, flag, _, _, _, stack, _⟩ := code ty' declared'
        exact ⟨tin, flag, MPositionStack.of_host stack⟩) prov
      (fun _ h => by rw [marker] at h; cases h)
  have edited : ConfigTyped root rootTy w (m.update g) rest :=
    configTyped_reset_edit typed owner hf running ctx maxOps prevent fr fresh
  have freeG : g.id ∉ rest.filterMap (Guard.commandOwner (m.update g)) := by
    rw [commandOwner_update]
    exact owner_free typed.queue owner
  have codeG : raceRegistrationR g.frame.current = none → ∀ ty, w.Γ g.id = some ty →
      MCodeOk root w (m.update g) g ty :=
    fun _ ty' declared' => (code ty' declared').races (racesKept_of_eq (m := m) (m' := m.update g) fun _ => rfl)
  exact ⟨fun y => configTyped_cons_loop edited look running notParked freeG y codeG,
    fun y => configTyped_cons_deliver edited look running notParked freeG y codeG⟩

/-- **The frame step**: `configTyped_reset_step` at the fiber's own context. -/
theorem configTyped_frame_step {root : ProgramSource} {rootTy : EffTy} {w : World} {m : RState}
    {c : RCmd} {rest : List RCmd} {f : RFiber} (typed : ConfigTyped root rootTy w m (c :: rest))
    (owner : Guard.commandOwner m c = some f.id) (hf : m.fiber? f.id = some f)
    (running : f.running = true) (fr : RSaved)
    (code : ∀ ty, w.Γ f.id = some ty → MCodeOk root w m { f with frame := fr } ty)
    (marker : raceRegistrationR fr.current = none) :
    (∀ y, ConfigTyped root rootTy w (m.update { f with frame := fr }) (.loop f.id y :: rest)) ∧
    (∀ y, ConfigTyped root rootTy w (m.update { f with frame := fr }) (.deliver f.id y :: rest)) :=
  configTyped_reset_step typed owner hf running f.context
    (typed.machine.fiber (rfiber?_mem hf)).ok.c5 f.maxOpsBeforeYield f.preventYield fr code marker

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

/-- The fiber arm's inversion at the ambient judgment: an operation that is none of the four
control markers is typed by its certificate, its ambient pre, a continuation for every answer its
post admits at every later world, at the row the operation steps to, and its entry bound. -/
theorem ambientProg_fiber_inv {root : ProgramSource} {w : World} {available : Env.Requirement}
    {position : AmbientPosition} {op : FiberOp} {k : op.answer → RProgram}
    (h : AmbientProg root w available position (.vis (.inr op) k))
    (notGuard : ∀ kind, op ≠ .guard_ kind) (notUnguard : ∀ ex, op ≠ .unguard ex)
    (notFinish : ∀ ex, op ≠ .finishFinalizer ex)
    (notScopeExit : ∀ prev sc ex, op ≠ .scopeExit prev sc ex) :
    ∃ cert, ambientFiberPre root w available op cert ∧
      (∀ later, w.leHost later → ∀ ans, ambientFiberPost later available op cert ans →
        AmbientProg root later (ambientFiberInput available op ans) position (k ans)) ∧
      Row.Subset position.failureRow available ∧ position.WF := by
  cases h with
  | fiber _ _ _ _ cert pre next entry => exact ⟨cert, pre, next, entry⟩
  | guard => exact absurd rfl (notGuard _)
  | unguard => exact absurd rfl (notUnguard _)
  | finishFinalizer => exact absurd rfl (notFinish _)
  | scopedGuard => exact absurd rfl (notGuard _)

/-- The store arm's inversion at the ambient judgment. -/
theorem ambientProg_store_inv {root : ProgramSource} {w : World} {available : Env.Requirement}
    {position : AmbientPosition} {op : SyncOp} {k : Val → RProgram}
    (h : AmbientProg root w available position (.vis (.inl op) k)) :
    ∃ cert, ambientStorePre root w available op cert ∧
      (∀ later, w.leHost later → ∀ ans, storePost later op cert ans →
        AmbientProg root later available position (k ans)) ∧
      Row.Subset position.failureRow available ∧ position.WF := by
  cases h with
  | store cert pre next entry => exact ⟨cert, pre, next, entry⟩

/-- **Construction glue keeps typing** (`prepareR`, `Laws/Program/DenoteR.lean`): a `construction`
operation answers the completed view, which is exactly its post when the view is typed; a guard
prepares its body, its run and skip arms untouched; nothing else moves. -/
theorem prepareR_typed {root : ProgramSource} (C : List (FiberId × ExitV)) (c : RProgram) :
    ∀ {w : World} {available : Env.Requirement} {position : AmbientPosition}, ViewTyped w C →
      AmbientProg root w available position c →
        AmbientProg root w available position (prepareR C c) := by
  fun_induction prepareR C c with
  | case1 ex => exact fun _ h => h
  | case2 k ih =>
    intro w available position view h
    obtain ⟨cert, _, next, _⟩ := ambientProg_fiber_inv h (fun _ h => nomatch h)
      (fun _ h => nomatch h) (fun _ h => nomatch h) (fun _ _ _ h => nomatch h)
    exact ih view (next w (leHost_refl w) C view)
  | case3 kind k ih =>
    intro w available position view h
    cases h with
    | fiber notGuard _ _ _ _ _ _ _ => exact absurd rfl (notGuard kind)
    | guard mid body run skip entry => exact .guard mid (ih view body) run skip entry
    | scopedGuard mid prev sc body callback live services widen entry =>
      exact .scopedGuard mid prev sc (ih view body) callback live services widen entry
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

/-- **The scoped exit's callback is idle on typed code**: the ambient judgment never types a raw
scope-exit marker as current code (decisions row 188 (a)), so `prepareScopedExitR` leaves the
iteration. -/
theorem prepareScopedExitR_of_typed {root : ProgramSource} {w : World} {available : Env.Requirement}
    {position : AmbientPosition} {it : RIter}
    (h : AmbientProg root w available position it.fiber.frame.current) :
    prepareScopedExitR it = it := by
  unfold prepareScopedExitR
  split
  · rename_i previous scope ex next heq
    rw [heq] at h
    cases h with
    | fiber _ _ _ notScopeExit _ _ _ _ => exact absurd rfl (notScopeExit _ _ _)
  · rfl

/-- A fiber's code stays typed when its current code is prepared at a typed view. -/
theorem codeOk_prepare {root : ProgramSource} {w : World} {m : RState} {f : RFiber}
    {final : EffTy} (C : List (FiberId × ExitV)) (view : ViewTyped w C)
    (h : MCodeOk root w m f final) :
    MCodeOk root w m { f with frame := { f.frame with current := prepareR C f.frame.current } }
      final := by
  obtain ⟨row, tin, flag, covered, bit, code, stack, prov⟩ := h
  exact ⟨row, tin, flag, covered, bit, prepareR_typed C f.frame.current view code, stack,
    ⟨prov.recorded, prov.deferred⟩⟩

/-- **A continue iteration whose glue has run settles typed**: the step installs the typed record
and `settle` queues `loop`. -/
theorem settle_reset_ready {root : ProgramSource} {rootTy : EffTy} {w : World} {m : RState}
    {rest : List RCmd} {f f0 : RFiber} {y y' : Bool}
    (typed : ConfigTyped root rootTy w (m.update f) (.deliver f.id y :: rest))
    (hf0 : m.fiber? f.id = some f0) (running : f.running = true)
    (ctx : Ctx) (services : ServicesFit w ctx.services) (maxOps : Nat) (prevent : Bool) (fr : RSaved)
    (code : ∀ ty, w.Γ f.id = some ty →
      MCodeOk root w (m.update f) (resetFiber f ctx maxOps prevent fr) ty) :
    ∃ w', w.leHost w' ∧
      ConfigTyped root rootTy w'
        (settle f.id rest ⟨m, resetFiber f ctx maxOps prevent fr, y', .continue_, [], []⟩).1
        (settle f.id rest ⟨m, resetFiber f ctx maxOps prevent fr, y', .continue_, [], []⟩).2 := by
  have same : f0.id = f.id := rfiber?_id hf0
  have look : (m.update f).fiber? f.id = some f := by
    have := rfiber?_update_self (m := m) (f := f0) (g := f) (by rw [same]; exact hf0) same.symm
    exact this
  obtain ⟨ty, declared⟩ : ∃ ty, w.Γ f.id = some ty :=
    Option.isSome_iff_exists.mp ((typed.machine.wide.fibers f.id).mpr
      (List.mem_map.mpr ⟨f, rfiber?_mem look, rfl⟩))
  obtain ⟨_, _, _, _, _, current, _, _⟩ := code ty declared
  have step := (configTyped_reset_step typed rfl look running ctx services maxOps prevent fr code
    (raceRegistrationR_ambient current)).1 y'
  rw [rupdate_rupdate m (show (resetFiber f ctx maxOps prevent fr).id = f.id from rfl)] at step
  exact ⟨w, leHost_refl w, step⟩

/-- **A step's `continue` settles typed**: the iteration keeps the evaluator's machine, moves only
the fiber's record to one whose code is typed at its declared type, and queues nothing; the glue
then prepares the new code (typed, `prepareR_typed`), the scoped-exit callback is idle on it, and
`settle` queues `loop`. The machine handed to the evaluator may hold an older record of the fiber
(`loop` edits it before evaluating); the configuration is typed with the evaluated one
installed. -/
theorem settle_reset_continue {root : ProgramSource} {rootTy : EffTy} {w : World} {m : RState}
    {rest : List RCmd} {f f0 : RFiber} {y y' : Bool}
    (typed : ConfigTyped root rootTy w (m.update f) (.deliver f.id y :: rest))
    (hf0 : m.fiber? f.id = some f0) (exit0 : f0.exit = f.exit) (running : f.running = true)
    (ctx : Ctx) (services : ServicesFit w ctx.services) (maxOps : Nat) (prevent : Bool) (fr : RSaved)
    (code : ∀ ty, w.Γ f.id = some ty →
      MCodeOk root w (m.update f) (resetFiber f ctx maxOps prevent fr) ty) :
    ∃ w', w.leHost w' ∧
      ConfigTyped root rootTy w'
        (settle f.id rest (prepareIterR ⟨m, resetFiber f ctx maxOps prevent fr, y', .continue_, [], []⟩)).1
        (settle f.id rest (prepareIterR ⟨m, resetFiber f ctx maxOps prevent fr, y', .continue_, [], []⟩)).2 := by
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
  have code' : ∀ ty, w.Γ f.id = some ty →
      MCodeOk root w (m.update f) (resetFiber f ctx maxOps prevent fr') ty :=
    fun ty declared => codeOk_prepare (f := resetFiber f ctx maxOps prevent fr) m.completedExits view
      (code ty declared)
  obtain ⟨ty, declared⟩ : ∃ ty, w.Γ f.id = some ty :=
    Option.isSome_iff_exists.mp ((typed.machine.wide.fibers f.id).mpr
      (List.mem_map.mpr ⟨f, rfiber?_mem look, rfl⟩))
  obtain ⟨_, _, _, _, _, current, _, _⟩ := code' ty declared
  have idle : prepareScopedExitR ⟨m, resetFiber f ctx maxOps prevent fr', y', .continue_, [], []⟩ =
      ⟨m, resetFiber f ctx maxOps prevent fr', y', .continue_, [], []⟩ :=
    prepareScopedExitR_of_typed current
  have glue : prepareIterR ⟨m, resetFiber f ctx maxOps prevent fr, y', .continue_, [], []⟩ =
      ⟨m, resetFiber f ctx maxOps prevent fr', y', .continue_, [], []⟩ := idle
  rw [glue]
  exact settle_reset_ready typed hf0 running ctx services maxOps prevent fr' code'

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

/-- A settlement typed from a later world is typed from an earlier one. -/
theorem SettlesTyped.mono {root : ProgramSource} {rootTy : EffTy} {w w' : World} (ord : w.leHost w')
    {id : FiberId} {rest : List RCmd} {it : RIter} (h : SettlesTyped root rootTy w' id rest it) :
    SettlesTyped root rootTy w id rest it :=
  let ⟨w'', o, typed⟩ := h
  ⟨w'', leHost_trans _ _ _ ord o, typed⟩

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
      have code : ∀ ty, w.Γ f.id = some ty → MCodeOk root w (m.update f) f ty :=
        fun ty declared => (ev.typed.code f (rfiber?_mem look) ev.running
          ⟨y, Or.inr List.mem_cons_self⟩ hmark ty declared).code_of_deliver List.mem_cons_self
      obtain ⟨ty, declared⟩ : ∃ ty, w.Γ f.id = some ty :=
        Option.isSome_iff_exists.mp ((ev.typed.machine.wide.fibers f.id).mpr
          (List.mem_map.mpr ⟨f, rfiber?_mem look, rfl⟩))
      obtain ⟨_, _, _, _, _, current, _, _⟩ :=
        codeOk_prepare m.completedExits view (code ty declared)
      have step : ConfigTyped root rootTy w ((m.update f).update f1) (.deliver f.id y :: rest) :=
        (configTyped_frame_step ev.typed rfl look ev.running
          { f.frame with current := prepareR m.completedExits f.frame.current }
          (fun ty' declared' => codeOk_prepare m.completedExits view (code ty' declared'))
          (raceRegistrationR_ambient current)).2 y
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

/-- **`deliver` keeps `I` from the clauses** (`deliver_preserves`'s shape): the head's authority
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
    ∀ ty, w.Γ f.id = some ty → MCodeOk root w (m.update f) f ty :=
  fun ty declared => (ev.typed.code f (rfiber?_mem ev.look) ev.running
    ⟨y, Or.inr List.mem_cons_self⟩ marker ty declared).code_of_deliver List.mem_cons_self

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
    (fr : RSaved)
    (code : ∀ ty, w.Γ f.id = some ty → MCodeOk root w (m.update f) { f with frame := fr } ty) :
    SettlesTyped root rootTy w f.id rest
      (prepareIterR ⟨m, { f with frame := fr }, y', .continue_, [], []⟩) := by
  obtain ⟨f0, hf0, exit0⟩ := ev.stale
  exact settle_reset_continue ev.typed hf0 exit0 ev.running f.context
    (ev.typed.machine.fiber (rfiber?_mem ev.look)).ok.c5 f.maxOpsBeforeYield f.preventYield fr code

/-- **A clause that moves the fiber's context settles typed**: the new context's services fit, and
the new frame's code is typed at it. -/
theorem Evaluating.settle_reset {root : ProgramSource} {rootTy : EffTy} {w : World} {m : RState}
    {rest : List RCmd} {f : RFiber} {y y' : Bool} (ev : Evaluating root rootTy w m rest f y)
    (ctx : Ctx) (services : ServicesFit w ctx.services) (maxOps : Nat) (prevent : Bool) (fr : RSaved)
    (code : ∀ ty, w.Γ f.id = some ty →
      MCodeOk root w (m.update f) (resetFiber f ctx maxOps prevent fr) ty) :
    SettlesTyped root rootTy w f.id rest
      (prepareIterR ⟨m, resetFiber f ctx maxOps prevent fr, y', .continue_, [], []⟩) := by
  obtain ⟨f0, hf0, exit0⟩ := ev.stale
  exact settle_reset_continue ev.typed hf0 exit0 ev.running ctx services maxOps prevent fr code

/-- **A clause whose glue has run settles typed** (the scoped exit's close, which restores the
previous context). -/
theorem Evaluating.settle_ready {root : ProgramSource} {rootTy : EffTy} {w : World} {m : RState}
    {rest : List RCmd} {f : RFiber} {y y' : Bool} (ev : Evaluating root rootTy w m rest f y)
    (ctx : Ctx) (services : ServicesFit w ctx.services) (maxOps : Nat) (prevent : Bool) (fr : RSaved)
    (code : ∀ ty, w.Γ f.id = some ty →
      MCodeOk root w (m.update f) (resetFiber f ctx maxOps prevent fr) ty) :
    SettlesTyped root rootTy w f.id rest
      ⟨m, resetFiber f ctx maxOps prevent fr, y', .continue_, [], []⟩ := by
  obtain ⟨f0, hf0, _⟩ := ev.stale
  exact settle_reset_ready ev.typed hf0 ev.running ctx services maxOps prevent fr code

/-- **A frame-only clause whose iteration is answered settles typed**: the glue leaves it, and
`settle` queues `deliver`. -/
theorem Evaluating.settle_answered {root : ProgramSource} {rootTy : EffTy} {w : World} {m : RState}
    {rest : List RCmd} {f : RFiber} {y y' : Bool} (ev : Evaluating root rootTy w m rest f y)
    (fr : RSaved)
    (code : ∀ ty, w.Γ f.id = some ty → MCodeOk root w (m.update f) { f with frame := fr } ty) :
    SettlesTyped root rootTy w f.id rest
      (prepareIterR ⟨m, { f with frame := fr }, y', .answered, [], []⟩) := by
  obtain ⟨ty, declared⟩ := ev.declared
  obtain ⟨_, _, _, _, _, current, _, _⟩ := code ty declared
  have step := (configTyped_frame_step ev.typed rfl ev.look ev.running fr code
    (raceRegistrationR_ambient current)).2 y'
  rw [rupdate_rupdate m (show ({ f with frame := fr } : RFiber).id = f.id from rfl)] at step
  exact ⟨w, leHost_refl w, step⟩

/-- **An inline answer**: the clause installs the continuation at answer `v` the operation's post
admits at the fiber's row, which the operation leaves unchanged; the stack and everything else
stay. -/
theorem Evaluating.answer_typed {root : ProgramSource} {rootTy : EffTy} {w : World} {m : RState}
    {rest : List RCmd} {f : RFiber} {y : Bool} (ev : Evaluating root rootTy w m rest f y)
    {op : FiberOp} {next : op.answer → RProgram} (hc : f.frame.current = .vis (.inr op) next)
    (marker : raceRegistrationR f.frame.current = none)
    (notGuard : ∀ kind, op ≠ .guard_ kind) (notUnguard : ∀ ex, op ≠ .unguard ex)
    (notFinish : ∀ ex, op ≠ .finishFinalizer ex)
    (notScopeExit : ∀ prev sc ex, op ≠ .scopeExit prev sc ex) (v : op.answer)
    (post : ∀ row cert, ambientFiberPre root w row op cert → ambientFiberPost w row op cert v)
    (input : ∀ row, ambientFiberInput row op v = row) :
    ∀ ty, w.Γ f.id = some ty →
      MCodeOk root w (m.update f) { f with frame := { f.frame with current := next v } } ty := by
  intro ty declared
  obtain ⟨row, tin, flag, covered, bit, code, stack, prov⟩ := ev.code marker ty declared
  rw [hc] at code
  obtain ⟨cert, pre, typedNext, _⟩ :=
    ambientProg_fiber_inv code notGuard notUnguard notFinish notScopeExit
  have continued := typedNext w (leHost_refl w) v (post row cert pre)
  rw [input row] at continued
  exact ⟨row, tin, flag, covered, bit, continued, stack, ⟨prov.recorded, prov.deferred⟩⟩

/-! ## The clauses: inline answers and no-ops -/

theorem clause_suspend (root : ProgramSource) (rootTy : EffTy) (p : Point) :
    FiberClauseKeeps root rootTy (.suspend p) := by
  intro w m rest f y next ev hc
  exact ev.settle_continue _ (ev.answer_typed hc (by rw [hc]; rfl) (fun _ h => nomatch h)
    (fun _ h => nomatch h) (fun _ h => nomatch h) (fun _ _ _ h => nomatch h) .unit
    (fun _ _ _ => trivial) (fun _ => rfl))

theorem clause_foreignRelease (root : ProgramSource) (rootTy : EffTy) (c : Capture) (ex : ExitV) :
    FiberClauseKeeps root rootTy (.foreignRelease c ex) := by
  intro w m rest f y next ev hc
  exact ev.settle_continue _ (ev.answer_typed hc (by rw [hc]; rfl) (fun _ h => nomatch h)
    (fun _ h => nomatch h) (fun _ h => nomatch h) (fun _ _ _ h => nomatch h) .unit
    (fun _ _ _ => rfl) (fun _ => rfl))

theorem clause_closeWalk (root : ProgramSource) (rootTy : EffTy) (strategy : FinalizerStrategy)
    (order : List FinName) (ex : ExitV) : FiberClauseKeeps root rootTy (.closeWalk strategy order ex) := by
  intro w m rest f y next ev hc
  exact ev.settle_continue _ (ev.answer_typed hc (by rw [hc]; rfl) (fun _ h => nomatch h)
    (fun _ h => nomatch h) (fun _ h => nomatch h) (fun _ _ _ h => nomatch h) .unit
    (fun _ _ _ => rfl) (fun _ => rfl))

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
  obtain ⟨row, tin, flag, covered, bit, current, stack, prov⟩ := ev.code (by rw [hc]; rfl) ty declared
  rw [hc] at current
  obtain ⟨cert, _, typedNext, _⟩ := ambientProg_fiber_inv current (fun _ h => nomatch h)
    (fun _ h => nomatch h) (fun _ h => nomatch h) (fun _ _ _ h => nomatch h)
  exact ⟨row, tin, flag, covered, bit,
    prepareR_typed _ _ view (typedNext w (leHost_refl w) m.completedExits view), stack,
    ⟨prov.recorded, prov.deferred⟩⟩

theorem clause_sync (root : ProgramSource) (rootTy : EffTy) (v : Val) :
    FiberClauseKeeps root rootTy (.sync v) := by
  intro w m rest f y next ev hc
  exact ev.settle_answered _ (ev.answer_typed hc (by rw [hc]; rfl) (fun _ h => nomatch h)
    (fun _ h => nomatch h) (fun _ h => nomatch h) (fun _ _ _ h => nomatch h) v (fun _ _ _ => rfl)
    (fun _ => rfl))

/-! ## The clauses: the frame pushers -/

/-- **A guard's ambient typing is the saved frame's arrow**: the body is typed at a middle position
at the guard's own row, and the frame the evaluator saves (`saveR`, `Laws/Program/EvaluateR.lean`)
is a machine frame from that position to the guard's, at the fiber's mask: an ordinary guard's
`resume`, a protected `onExit`'s `protect`, a `scoped` guard's `scopedResume`. -/
theorem ambientProg_guard_frame {root : ProgramSource} {w : World} {row : Env.Requirement}
    {position : AmbientPosition} {kind : GuardKind} {k : Option ExitV → RProgram} (b : Bool)
    (h : AmbientProg root w row position (.vis (.inr (.guard_ kind)) k)) :
    ∃ mid : AmbientPosition, AmbientProg root w row mid (k none) ∧
      MFrame root w (mid, b) (position, b) (.resume kind fun ex => k (some ex)) := by
  cases h with
  | fiber notGuard _ _ _ _ _ _ _ => exact absurd rfl (notGuard kind)
  | guard mid body run skip entry =>
    refine ⟨mid, body, ?_⟩
    cases kind with
    | onExit interruptible =>
      cases interruptible with
      | false => exact .protect _ (fun w' o ex hex => run w' o ex ⟨by cases ex <;> rfl, hex⟩) entry.2
      | true =>
        exact .resume _ _ (fun h => nomatch h) (fun w' o ex hex arm => run w' o ex ⟨arm, hex⟩) skip
          entry.2
    | onSuccess =>
      exact .resume _ _ (fun h => nomatch h) (fun w' o ex hex arm => run w' o ex ⟨arm, hex⟩) skip
        entry.2
    | onFailure =>
      exact .resume _ _ (fun h => nomatch h) (fun w' o ex hex arm => run w' o ex ⟨arm, hex⟩) skip
        entry.2
    | all =>
      exact .resume _ _ (fun h => nomatch h) (fun w' o ex hex arm => run w' o ex ⟨arm, hex⟩) skip
        entry.2
  | scopedGuard mid prev sc body callback live services widen entry =>
    refine ⟨mid, body, .scopedResume _ prev sc callback
      (fun w' ord => ⟨scopeLive_mono ord.1 live, ?_⟩) widen entry.2⟩
    exact servicesFit_map ord.1.2.1 ord.1.2.2.1 ord.1.2.2.2.1 ord.2 ord.1.1.2
      (serviceTy_of_le ord.1) services

/-- **`guard_`**: the guard installs its body and saves the resume frame (`saveR`), the arrow
`ambientProg_guard_frame` types from the body's position to the guard's. -/
theorem clause_guard_ (root : ProgramSource) (rootTy : EffTy) (kind : GuardKind) :
    FiberClauseKeeps root rootTy (.guard_ kind) := by
  intro w m rest f y next ev hc
  refine ev.settle_continue { f.frame with
    current := next none, stack := .resume kind (fun ex => next (some ex)) :: f.frame.stack } ?_
  intro ty declared
  obtain ⟨row, tin, flag, covered, bit, current, stack, prov⟩ := ev.code (by rw [hc]; rfl) ty declared
  rw [hc] at current
  obtain ⟨mid, body, frame⟩ := ambientProg_guard_frame tin.2 current
  exact ⟨row, (mid, tin.2), flag, covered, bit, body, .cons (.inl frame) stack,
    ⟨prov.recorded, prov.deferred⟩⟩

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
      ⟨m, { f with frame := maskFrame f.frame flag (bodyR interp body) next }, y, .continue_, [], []⟩ :=
  rfl

/-- **The row a mask's answer returns at is its body's exit row**: a captured release returns at
the keys both contexts hold (`ambientFiberInput`, `bodyPosition`), every other body at the row it
entered at. A release is entered only protected (`ReleaseMaskAllowed`, the pre). -/
theorem mask_answerInput (available : Env.Requirement) (flag : Bool) (body : Body) (cert : EffTy)
    (ex : ExitV) (allowed : ReleaseMaskAllowed (.mask flag body)) :
    ambientFiberInput available (.mask flag body) ex = ambientInput (bodyPosition available body cert) ex := by
  cases body with
  | release point previous =>
    have masked := allowed flag point previous rfl
    subst masked
    cases ex <;> rfl
  | _ => cases flag <;> cases ex <;> rfl

/-- **`mask`**: the body's program is typed at its position (`bodyTyped_ambient`, from `J`'s source
and service facts and the pre's coverage), or the recorded interrupt is delivered there; the answer
frame carries the body's exit to the continuation at the row the operation's input names, and the
restore frame is an identity arrow on positions. -/
theorem clause_mask (root : ProgramSource) (rootTy : EffTy) (flag : Bool) (body : Body) :
    FiberClauseKeeps root rootTy (.mask flag body) := by
  intro w m rest f y next ev hc
  rw [evaluateFiberR_mask]
  refine ev.settle_continue _ ?_
  intro ty declared
  obtain ⟨row, ⟨q, b⟩, final, covered, bit, current, stack, prov⟩ :=
    ev.code (by rw [hc]; rfl) ty declared
  change b = f.frame.interruptible at bit
  subst bit
  change AmbientProg root w row q f.frame.current at current
  rw [hc] at current
  obtain ⟨cert, ⟨typedB, requires, acquired, allowed, coverage⟩, typedNext, _⟩ :=
    ambientProg_fiber_inv current (fun _ h => nomatch h) (fun _ h => nomatch h)
      (fun _ h => nomatch h) (fun _ _ _ h => nomatch h)
  let p := bodyPosition row body cert
  have typedBody : AmbientProg root w row p (bodyR (interpRAt root.program m.completedExits) body) :=
    bodyTyped_ambient root ev.typed.machine.sourceWF ev.typed.machine.services m.completedExits
      typedB requires acquired coverage
  have answer : MFrame root w (p, f.frame.interruptible) (q, f.frame.interruptible) (.answer next) :=
    .answer next fun w' o ex hex => by
      have post : ambientFiberPost w' row (.mask flag body) cert ex := by
        cases body <;> exact hex.1
      have continued := typedNext w' o ex post
      rw [mask_answerInput row flag body cert ex allowed] at continued
      exact continued
  have answered : MHostStack root w (m.update f) f.id (p, f.frame.interruptible) (finalPos ty final)
      (.answer next :: f.frame.stack) := by
    exact .cons (.inl answer) stack
  refine ⟨row, (p, flag), final, covered, rfl, ?_, ?_, ⟨prov.recorded, prov.deferred⟩⟩
  · show AmbientProg root w row p
      (if flag && !f.frame.interruptible && f.frame.interruptedCause.isSome then
        .pure (.failure f.frame.pendingCause)
      else bodyR (interpRAt root.program m.completedExits) body)
    split
    · exact .pure (ambientExit_failure (strongExit_of_clean w _ _ (pendingCause_clean prov)
        (pendingCause_noShapeDefect _ prov)) (ambient_entry typedBody))
        ⟨ambient_entry typedBody, ambient_wf typedBody⟩
    · exact typedBody
  · show MHostStack root w (m.update f) f.id (p, flag) (finalPos ty final)
      (if f.frame.interruptible = flag then .answer next :: f.frame.stack
       else .restoreMask f.frame.interruptible :: .answer next :: f.frame.stack)
    split
    · rename_i same
      rw [← same]
      exact answered
    · exact .cons (.inl (.restoreMask f.frame.interruptible (ambient_wf typedBody))) answered

/-- The frame `getInterruptible` installs (`Laws/Program/EvaluateR.lean`, the `getInterruptible`
arm; `internal/effect.ts:4340-4352` at a constant body): the mask's frame at a false flag, over the
saved state of the entry flag as the code. -/
theorem evaluateFiberR_getInterruptible (interp : RInterp) (m : RState) (f : RFiber) (y : Bool)
    (next : Val → RProgram) :
    evaluateFiberR interp m f y .getInterruptible next =
      ⟨m, { f with
          frame := maskFrame f.frame false
            (.pure (.success (interp.restoreValue f.frame.interruptible))) (seqR next) },
        y, .continue_, [], []⟩ :=
  rfl

/-- **`getInterruptible`** (decisions row 245): the mask at a constant body. The answer is a saved
image, a member of the saved state's type in every world (`fits_savedMask`); the answer frame
carries it to the continuation at the row's post (`fits_maskRestore_inv`), a failure there being
covered by the operation's entry; the restore frame is an identity arrow on positions, as
`clause_mask`'s is. -/
theorem clause_getInterruptible (root : ProgramSource) (rootTy : EffTy) :
    FiberClauseKeeps root rootTy .getInterruptible := by
  intro w m rest f y next ev hc
  rw [evaluateFiberR_getInterruptible]
  refine ev.settle_continue _ ?_
  intro ty declared
  obtain ⟨row, ⟨q, b⟩, final, covered, bit, current, stack, prov⟩ :=
    ev.code (by rw [hc]; rfl) ty declared
  change b = f.frame.interruptible at bit
  subst bit
  change AmbientProg root w row q f.frame.current at current
  rw [hc] at current
  obtain ⟨_, _, typedNext, entry, _⟩ := ambientProg_fiber_inv current (fun _ h => nomatch h)
    (fun _ h => nomatch h) (fun _ h => nomatch h) (fun _ _ _ h => nomatch h)
  let p : AmbientPosition := (EffTy.pure Ty.maskRestore, row, row)
  have answer : MFrame root w (p, f.frame.interruptible) (q, f.frame.interruptible)
      (.answer (seqR next)) :=
    .answer _ fun w' o ex hex => by
      rw [ambientInput_const]
      cases ex with
      | success v => exact typedNext w' o v (fits_maskRestore_inv hex.1.1)
      | failure c =>
        exact .pure (ambientExit_failure (exitOk_failure_of_errorN (Bounds.subN_never _) hex.1) entry)
          ⟨entry, ambient_wf current⟩
  have answered : MHostStack root w (m.update f) f.id (p, f.frame.interruptible) (finalPos ty final)
      (.answer (seqR next) :: f.frame.stack) := by
    exact .cons (.inl answer) stack
  refine ⟨row, (p, false), final, covered, rfl, ?_, ?_, ⟨prov.recorded, prov.deferred⟩⟩
  · show AmbientProg root w row p (.pure (.success (Val.savedMask f.frame.interruptible)))
    exact .pure (ambientExit_const (strongExit_success w _ _ (fits_savedMask w _)))
      ⟨Row.subset_refl _, Row.subset_refl _⟩
  · show MHostStack root w (m.update f) f.id (p, false) (finalPos ty final)
      (if f.frame.interruptible = false then .answer (seqR next) :: f.frame.stack
       else .restoreMask f.frame.interruptible :: .answer (seqR next) :: f.frame.stack)
    split
    · rename_i same
      rw [← same]
      exact answered
    · exact .cons (.inl (.restoreMask f.frame.interruptible (Row.subset_refl _))) answered

/-! ## Read-only store clauses (Concept 4)

Helpers of `loop_preserves` and `deliver_preserves`, via `StoreClauseKeeps` and
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
    (code : ∀ ty, w.Γ f.id = some ty → MCodeOk root w (m.update f) { f with frame := fr } ty) :
    SettlesTyped root rootTy w f.id rest
      (prepareIterR ⟨m, { f with frame := fr }, y', .answered, [.drainDue], []⟩) := by
  obtain ⟨w', ord, typed⟩ := ev.settle_answered (y' := y') fr code
  exact ⟨w', ord, configTyped_cons_drainDue typed⟩

/-- Store inversion gives the same-world continuation, at the same row, without any fiber-control
exclusions. -/
theorem Evaluating.store_answer_typed {root : ProgramSource} {rootTy : EffTy}
    {w : World} {m : RState} {rest : List RCmd} {f : RFiber} {y : Bool}
    (ev : Evaluating root rootTy w m rest f y) {op : SyncOp} {next : Val → RProgram}
    (hc : f.frame.current = .vis (.inl op) next) (v : Val)
    (post : ∀ cert, storePre root w op cert → storePost w op cert v) :
    ∀ ty, w.Γ f.id = some ty →
      MCodeOk root w (m.update f) { f with frame := { f.frame with current := next v } } ty := by
  intro ty declared
  obtain ⟨row, tin, flag, covered, bit, current, stack, prov⟩ := ev.code (by rw [hc]; rfl) ty declared
  rw [hc] at current
  obtain ⟨cert, pre, typedNext, _⟩ := ambientProg_store_inv current
  exact ⟨row, tin, flag, covered, bit, typedNext w (leHost_refl w) v (post cert pre.1), stack,
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
  obtain ⟨_, _, _, _, _, current, _, _⟩ := ev.code (by rw [hc]; rfl) ty declared
  rw [hc] at current
  obtain ⟨cert, pre, _⟩ := ambientProg_store_inv current
  exact ⟨cert, pre.1⟩

theorem clause_clockNow (root : ProgramSource) (rootTy : EffTy) :
    StoreClauseKeeps root rootTy .clockNow := by
  intro w m rest f y next ev hc
  exact ev.store_same hc (Val.nat m.state.timers.now.toNat) rfl (fun _ _ => ⟨_, rfl⟩)

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

/-- **`scopeExit`**: a raw scope-exit marker is no typed code (the fiber arm excludes it,
decisions row 188 (a)); the generated callback is consumed by `prepareScopedExitR` inside the
preceding delivery, never evaluated as a counted operation. -/
theorem clause_scopeExit (root : ProgramSource) (rootTy : EffTy) (prev : Ctx) (scope : Nat)
    (ex : ExitV) : FiberClauseKeeps root rootTy (.scopeExit prev scope ex) := by
  intro w m rest f y next ev hc
  obtain ⟨ty, declared⟩ := ev.declared
  obtain ⟨_, _, _, _, _, current, _, _⟩ := ev.code (by rw [hc]; rfl) ty declared
  rw [hc] at current
  cases current with
  | fiber _ _ _ notScopeExit _ _ _ _ => exact absurd rfl (notScopeExit _ _ _)

/-- **`refuse`**: its pre is `False`; no typed code refuses. -/
theorem clause_refuse (root : ProgramSource) (rootTy : EffTy) (cause : CauseV) :
    FiberClauseKeeps root rootTy (.refuse cause) := by
  intro w m rest f y next ev hc
  obtain ⟨ty, declared⟩ := ev.declared
  obtain ⟨_, _, _, _, _, current, _, _⟩ := ev.code (by rw [hc]; rfl) ty declared
  rw [hc] at current
  obtain ⟨_, pre, _⟩ := ambientProg_fiber_inv current (fun _ h => nomatch h) (fun _ h => nomatch h)
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
    (fun _ _ _ member => Or.inl member) (fun _ _ kept => Or.inl kept)
  simpa only [RunMachine.modify, look] using moved

/-- The loop's deferred-interrupt delivery keeps the actual saved stack: the recorded failure is
installed at the stack's input position, whose failure row the fiber's row holds (`ReadOk.stackAt`).
A direct race marker uses its already-correlated token reply stack, as interruptRecord's existing
proof does. -/
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
    obtain ⟨_, _, _, prov⟩ := old.position declared
    have newProv : InterruptProvenance fr :=
      ⟨prov.recorded, fun h => Bool.noConfusion h⟩
    cases marker : raceRegistrationR f.frame.current with
    | none =>
      obtain ⟨row, tin, flag, covered, bit, fail, wf, stack, _⟩ := (typed.code f (rfiber?_mem look)
        running ⟨y, Or.inl List.mem_cons_self⟩ marker final declared).stackAt
      exact ⟨row, tin, flag, covered, bit,
        .pure (ambientExit_failure (strongExit_of_clean w _ _ (pendingCause_clean prov)
          (pendingCause_noShapeDefect _ prov)) fail) ⟨fail, wf⟩, stack, newProv⟩
    | some raceId =>
      obtain ⟨_, resultTy, _, _, _, row, ⟨final0, flag, declared0, covered, stack, _⟩, _⟩ :=
        old.registration raceId marker
      have same : final0 = final := Option.some.inj (declared0.symm.trans declared)
      subst same
      exact ⟨row, (((resultTy, row, row) : AmbientPosition), f.frame.interruptible), flag, covered,
        rfl, .pure (ambientExit_failure (strongExit_of_clean w _ _ (pendingCause_clean prov)
          (pendingCause_noShapeDefect _ prov)) (Row.subset_refl _))
          ⟨Row.subset_refl _, Row.subset_refl _⟩, stack, newProv⟩

/-- The body reached after the injected guard is typed at the fiber's row independently of its
saved callback; unguard delivers the successful Yield reply through that saved callback. -/
theorem yield_body_typed (root : ProgramSource) (w : World) (row : Env.Requirement)
    (previous : RProgram) :
    AmbientProg root w row ((EffTy.pure .unit, row, row) : AmbientPosition)
      (.vis (.inr (.yieldNow 0)) fun v =>
        .vis (.inr (.unguard (.success v))) (seqR fun _ => previous)) :=
  .fiber (op := .yieldNow 0) (fun _ h => nomatch h) (fun _ h => nomatch h)
    (fun _ h => nomatch h) (fun _ _ _ h => nomatch h) () trivial (fun w' _ ans post => by
      change ans = Val.unit at post
      subst post
      exact .unguard (ambientExit_const (strongExit_success w' _ _ trivial))
        ⟨Row.subset_refl _, Row.subset_refl _⟩)
    ⟨Row.subset_refl _, Row.subset_refl _⟩

/-- Executing the injected success guard saves either an ordinary constant callback or the
existing race's correlated registration callback; both meet the original host stack. A failure
the guard skips is covered by the replaced code's entry. -/
theorem injected_frame_code {root : ProgramSource} {rootTy : EffTy} {w : World} {m : RState}
    {rest : List RCmd} {f : RFiber} {y : Bool}
    (typed : ConfigTyped root rootTy w m (.loop f.id y :: rest))
    (look : m.fiber? f.id = some f) (running : f.running = true)
    (notDeferred : f.frame.deferredInterrupt = false)
    (final : EffTy) (declared : w.Γ f.id = some final) :
    MCodeOk root w m { f with frame := { f.frame with
        current := .vis (.inr (.yieldNow 0)) fun v =>
          .vis (.inr (.unguard (.success v))) (seqR fun _ => f.frame.current)
        stack := .resume .onSuccess (seqR fun _ => f.frame.current) :: f.frame.stack } } final := by
  have old := typed.machine.fiber (rfiber?_mem look)
  obtain ⟨_, _, _, prov⟩ := old.position declared
  cases marker : raceRegistrationR f.frame.current with
  | none =>
    obtain ⟨row, tin, flag, covered, bit, current, stack, _⟩ := (typed.code f (rfiber?_mem look)
      running ⟨y, Or.inl List.mem_cons_self⟩ marker final declared).code_of_not_deferred notDeferred
    refine ⟨row, (((EffTy.pure .unit, row, row) : AmbientPosition), tin.2), flag, covered, bit,
      yield_body_typed root w row f.frame.current,
      .cons (.inl (.resume .onSuccess (seqR fun _ => f.frame.current) (fun h => nomatch h) ?_ ?_
        (ambient_wf current))) stack, ⟨prov.recorded, prov.deferred⟩⟩
    · intro later ord ex _ arm
      rw [ambientInput_const]
      cases ex with
      | success v => exact ambientProg_mono root ord current
      | failure c => cases arm
    · intro later _ ex admitted arm
      rw [ambientInput_const]
      cases ex with
      | success v => cases arm
      | failure c =>
        exact ambientExit_failure (exitOk_failure_of_errorN (Bounds.subN_never _) admitted.1)
          (ambient_entry current)
  | some raceId =>
    obtain ⟨race, resultTy, found, hosted, token, row, ⟨final0, flag, declared0, covered, stack, _⟩,
      entrants⟩ := old.registration raceId marker
    have same : final0 = final := Option.some.inj (declared0.symm.trans declared)
    subst same
    have live : f.exit = none := by
      cases hx : f.exit with
      | none => rfl
      | some _ =>
        have stopped := (old.exited (by rw [hx]; rfl)).2
        rw [running] at stopped
        cases stopped
    exact ⟨row, (((EffTy.pure .unit, row, row) : AmbientPosition), f.frame.interruptible), flag,
      covered, rfl, yield_body_typed root w row f.frame.current,
      .cons (.inr (.mk (fun _ => marker)
        (fun _ _ _ admitted => exitOk_failure_of_errorN (Bounds.subN_never _) admitted)
        found hosted token (entrants live))) stack, ⟨prov.recorded, prov.deferred⟩⟩

/-- The same owned, running fiber can be continued by deliver instead of loop. -/
theorem loop_to_deliver {root : ProgramSource} {rootTy : EffTy} {w : World} {m : RState}
    {rest : List RCmd} {f : RFiber} {y : Bool}
    (typed : ConfigTyped root rootTy w m (.loop f.id y :: rest))
    (look : m.fiber? f.id = some f) (running : f.running = true)
    (notDeferred : f.frame.deferredInterrupt = false) (y' : Bool) :
    ConfigTyped root rootTy w m (.deliver f.id y' :: rest) := by
  obtain ⟨f0, look0, _, parked⟩ := typed.queue.authority _ List.mem_cons_self
  have same : f0 = f := Option.some.inj (look0.symm.trans look)
  subst f0
  exact configTyped_cons_deliver (configTyped_tail typed) look running parked
    (owner_free typed.queue rfl) y'
    (fun marker ty declared => (typed.code f (rfiber?_mem look) running
      ⟨y, Or.inl List.mem_cons_self⟩ marker ty declared).code_of_not_deferred notDeferred)

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
  have chargedNotDeferred : charged.frame.deferredInterrupt = false := by
    change (runloopTop f).frame.deferredInterrupt = false
    unfold runloopTop
    split
    · rfl
    · rename_i h
      exact Bool.eq_false_iff.mpr h
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
    have injected : injectYield m charged y = some ⟨m.emit events, wrapped, true, .continue_, [], []⟩ := by
      unfold injectYield
      rw [if_pos injects]
    have iterationEq : iteration (interpR root.program) m f y =
        ⟨m.emit events, g, true, .continue_, [], []⟩ := by
      calc
        iteration (interpR root.program) m f y =
            evaluateR (interpRAt root.program (m.emit events).completedExits)
              (m.emit events) wrapped true := by
          unfold iteration
          dsimp only
          rw [injected]
        _ = ⟨m.emit events, g, true, .continue_, [], []⟩ := rfl
    have frameTyped := (configTyped_frame_step chargedTyped rfl chargedLook chargedRunning fr
      (fun ty declared => injected_frame_code chargedTyped chargedLook chargedRunning
        chargedNotDeferred ty declared)
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
      ⟨loop_to_deliver chargedTyped chargedLook chargedRunning chargedNotDeferred y,
        ⟨f, by rw [chargedId]; exact hf, chargedExit.symm⟩, chargedRunning, live⟩
    have keeps := evaluate_keeps fibers stores walk ev
    rw [chargedId] at keeps
    rw [iterationEq]
    exact keeps

end LoopPrefix

/-! ## The walk: an exit delivered through the saved stack

`unguard`, `finishFinalizer` and a bare exit deliver an exit through the fiber's saved stack
(`deliverR`, `popR`); the walk over a host stack is typed (`HostWalk.lean`). Four outcomes: typed
code over the remaining stack (a frame-only step), a scope's exit callback (the scope closed and
the context restored, `Evaluating.settle_callback`, finding F-CLOSE), a race registration marker (the
fiber's registration clause), or the exit the whole stack delivered (`finish` queued). -/

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
registration arrow leaves the race's marker current over a host stack at the token's type, at a row
the walk's row covers (`MHostMarker`); the fiber is typed by its registration clause, its reply at
that row, and the queued `loop` reads no code. -/
theorem configTyped_frame_marker {root : ProgramSource} {rootTy : EffTy} {w : World} {m : RState}
    {c : RCmd} {rest : List RCmd} {f : RFiber} (typed : ConfigTyped root rootTy w m (c :: rest))
    (owner : Guard.commandOwner m c = some f.id) (hf : m.fiber? f.id = some f)
    (running : f.running = true) (fr : RSaved) {ty : EffTy} {flag : Bool}
    (declared : w.Γ f.id = some ty) {covered : Env.Requirement}
    (cov : f.context.services.Satisfies covered)
    (marker : MHostMarker root w m f.id covered (finalPos ty flag) fr) (y : Bool) :
    ConfigTyped root rootTy w (m.update { f with frame := fr }) (.loop f.id y :: rest) := by
  let g : RFiber := { f with frame := fr }
  have hmem : f ∈ m.fibers := rfiber?_mem hf
  have old := typed.machine.fiber hmem
  obtain ⟨raceId, race, resultTy, r, hmark, found, host, token, sub, entrants, stack, prov⟩ := marker
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
        exact ⟨_, flag, MPositionStack.of_host stack⟩)
      prov
      (fun raceId' hm => by
        rw [hmark] at hm
        cases hm
        exact ⟨race, resultTy, found, host, token, r,
          ⟨ty, flag, declared, f.context.services.satisfies_weaken cov sub, stack, prov⟩,
          fun _ => entrants⟩)
  have edited := configTyped_frame_edit typed owner hf running fr fresh
  have freeG : g.id ∉ rest.filterMap (Guard.commandOwner (m.update g)) := by
    rw [commandOwner_update]
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
    fiberTyped_frame old hf running fr (fun ty _ => ⟨finalPos ty true, true, by rw [empty]; exact .nil _⟩) prov
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
    rw [commandOwner_update]
    exact owner_free typed.queue owner

/-- **Closing a present scope keeps `I`** at the world over the closed store, when the closing exit
fits `Exit<unknown, unknown>` (finding F-CLOSE): the state half of `scopeCloseUnsafe`
(`ScopeStore.closeState`, `internal/effect.ts:3778-3798`) grows the store (`scopeCloseSnapshot_keys`)
and keeps its well-formedness (the closing exit is valid in the store, `fits_validIn`; every memo
entry's layer scope stays present) and the scope column (`scopeStoreOk_closeState`); the heap, the
cells, the externals, the due list and the timers are untouched. Shared by the `closeScope` row and
the scoped exit's close. -/
theorem configTyped_closeState {root : ProgramSource} {rootTy : EffTy} {w : World} {m : RState}
    {q : List RCmd} (typed : ConfigTyped root rootTy w m q) {scope : Nat} {entry : ScopeEntry}
    (hentry : m.state.scopes.entryAt scope = some entry) {ex : ExitV}
    (hex : FitsExit w ⟨.unknown, .unknown, Env.Requirement.empty⟩ ex) :
    w.leHost { w with state := { m.state with scopes := m.state.scopes.closeState scope ex } } ∧
      ConfigTyped root rootTy
        { w with state := { m.state with scopes := m.state.scopes.closeState scope ex } }
        { m with state := { m.state with scopes := m.state.scopes.closeState scope ex } } q := by
  have wide := typed.machine.wide
  let s : Stores := { m.state with scopes := m.state.scopes.closeState scope ex }
  have snap : scopeCloseSnapshot scope ex m.state =
      some (s, entry.scope.strategy, entry.scope.closeOrder) := by
    unfold scopeCloseSnapshot
    rw [hentry]
    rfl
  have le : m.state.le s := (scopeCloseSnapshot_keys scope ex m.state s _ _ snap).1
  have valid : (reifyExitVal ex).validIn m.state = true := by
    have v := fits_validIn (storeTyped_of_typedState typed.machine) hex
    rw [wide.state] at v
    exact v
  have closing : ∀ e ∈ m.state.scopes.entries,
      (e.scope.closingExit?.map fun exit => (reifyExitVal exit).validIn s).getD true = true := by
    intro e he
    have h0 := wide.wf.2.1 e he
    cases hc : e.scope.closingExit? with
    | none => rfl
    | some x =>
      rw [hc] at h0
      exact Val.validIn_mono le _ h0
  have wf : s.WF := by
    refine ⟨fun v hv => Val.validIn_mono le v (wide.wf.1 v hv), fun e he => ?_,
      fun mm hm me hme => ?_, wide.wf.2.2.2⟩
    · change e ∈ (m.state.scopes.closeState scope ex).entries at he
      unfold ScopeStore.closeState at he
      rw [hentry] at he
      rcases ScopeStore.mem_setEntry he with rfl | old
      · cases hcl : entry.scope.isClosed with
        | true =>
          change ((entry.scope.closeState ex).closingExit?.map
            fun exit => (reifyExitVal exit).validIn s).getD true = true
          rw [Effect4.Scope.closeState_idempotent _ _ hcl]
          exact closing entry (List.mem_of_find?_eq_some hentry)
        | false =>
          change ((entry.scope.closeState ex).closingExit?.map
            fun exit => (reifyExitVal exit).validIn s).getD true = true
          rw [Effect4.Scope.close_closingExit _ _ hcl]
          exact Val.validIn_mono le _ valid
      · exact closing e old
    · obtain ⟨cell, present⟩ := wide.wf.2.2.1 mm hm me hme
      exact ⟨cell, ScopeStore.entryAt_closeState_isSome _ _ _ _ present⟩
  have ord : w.leHost { w with state := s } :=
    leHost_restate (by rw [wide.state]; exact le) (by rw [wide.state]) (by rw [wide.state])
      (by rw [wide.state])
  have stores : StoresOk (preds root) { w with state := s } Expect.root s := by
    obtain ⟨c0, c1, c2, c3, c4, c5⟩ := storesOk_world ord rfl rfl rfl wide.stores
    exact ⟨c0, c1, ⟨c2.c0⟩, scopeStoreOk_closeState c3 scope (fitsExit_mono ord hex), c4, c5⟩
  exact ⟨ord, (configTyped_restate typed le rfl rfl rfl wf stores (fun _ h => h)
    wide.live.dueOwners (fun _ h => h)).2⟩

/-- **`Scope.close`'s installed program at the ambient judgment** (decisions rows 136, 151 (a″),
349): at every row, at `⟨unit, never⟩`. A lone finalizer runs at the row (`finalizer_ambient`, which
a captured release meets by the merge of its captured context, `releaseContext`) and is voided; two
or more are the walk, administrative code (`closeWalk_typed`, `ambientProg_of_admin`). No finalizer
installs no program: the close answers `void` (`clause_closeScope`). The ambient counterpart of
`closeScope_installs`. Consumer: `clause_closeScope`. -/
theorem closeScope_installs_ambient (root : ProgramSource) (w : World) (scope : Nat) (exit : ExitV)
    (flag : Bool) (st st' : Stores) (code : RProgram)
    (admitted : ∀ entry ∈ st.scopes.entries, ∀ fin ∈ entry.scope.closeOrder,
      FinalizerAdmitted root w fin)
    (exitFits : FitsExit w ⟨.unknown, .unknown, Env.Requirement.empty⟩ exit)
    (h : closeScopeR scope exit flag st = some (st', some code)) (row : Env.Requirement) :
    AmbientProg root w row ((EffTy.pure .unit, row, row) : AmbientPosition) code := by
  unfold closeScopeR at h
  cases hs : scopeCloseSnapshot scope exit st with
  | none =>
    rw [hs] at h
    cases h
  | some snapshot =>
    obtain ⟨state, strategy, order⟩ := snapshot
    rw [hs] at h
    have hcode := (Prod.mk.inj (Option.some.inj h)).2
    match order, hs, hcode with
    | [], _, hcode => cases hcode
    | [fin], hs, hcode =>
      cases hcode
      obtain ⟨entry, hentry, hfin⟩ := lone_of_snapshot hs
      exact ambient_seqGuard (mid := ⟨.unknown, .never, Env.Requirement.empty⟩)
        (finalizer_ambient root (admitted entry hentry fin hfin) exitFits) (Bounds.subN_never _)
        (fun _ _ _ _ =>
          .pure (ambientExit_const ⟨trivial, trivial⟩) ⟨Row.subset_refl _, Row.subset_refl _⟩)
    | _ :: _ :: _, hs, hcode =>
      cases hcode
      obtain ⟨entry, hentry, horder⟩ := mem_of_snapshot hs
      exact ambientProg_of_admin root
        (closeWalk_typed root w strategy _ exit (fun fin hf => admitted entry hentry fin (horder ▸ hf))
          exitFits)
        (.fiber _ _ rfl fun _ => .fiber _ _ rfl fun _ => .pure _) row

/-- **`closeScope`** (`Scope.close`; latest's `scopeClose`,
`vendor/effect-4.0.1/src/internal/effect.ts:3929-3935`): the close's state half
(`configTyped_closeState`) keeps `I`, and so does the installed frame. No finalizer answers `void`
over the saved answer frame. Otherwise the closer is masked first: an interruptible closer's
restoring slot sits over the answer frame, an identity arrow on positions as `clause_mask`'s is, and
the program (`closeScope_installs_ambient`) runs at the operation's row. A captured release's context
is merged over the current one, so a failure leaves at a row the entry row covers.
Consumer: `deliver_preserves_of_clauses` through `Clauses/All.lean`. -/
@[semantics "scope-lifetime-finalization" (requirement := R11)]
theorem clause_closeScope (root : ProgramSource) (rootTy : EffTy) (scope : Nat) (ex : ExitV) :
    FiberClauseKeeps root rootTy (.closeScope scope ex) := by
  intro w m rest f y next ev hc
  have wide := ev.typed.machine.wide
  obtain ⟨ty, declared⟩ := ev.declared
  obtain ⟨row, ⟨q, b⟩, flag, covered, bit, current, stack, prov⟩ :=
    ev.code (by rw [hc]; rfl) ty declared
  change b = f.frame.interruptible at bit
  subst bit
  change AmbientProg root w row q f.frame.current at current
  rw [hc] at current
  obtain ⟨_, ⟨live, hex⟩, typedNext, _⟩ := ambientProg_fiber_inv current (fun _ h => nomatch h)
    (fun _ h => nomatch h) (fun _ h => nomatch h) (fun _ _ _ h => nomatch h)
  have answer : MFrame root w (((EffTy.pure .unit, row, row) : AmbientPosition), f.frame.interruptible)
      (q, f.frame.interruptible) (.answer next) :=
    .answer next fun w' o ex hex => by
      rw [ambientInput_const]
      exact typedNext w' o ex hex.1
  have present : (m.state.scopes.entryAt scope).isSome = true := by
    have l : (w.state.scopes.entryAt scope).isSome = true := live
    rw [wide.state] at l
    exact l
  obtain ⟨entry, hentry⟩ := Option.isSome_iff_exists.mp present
  let s : Stores := { m.state with scopes := m.state.scopes.closeState scope ex }
  have snap : scopeCloseSnapshot scope ex m.state =
      some (s, entry.scope.strategy, entry.scope.closeOrder) := by
    unfold scopeCloseSnapshot
    rw [hentry]
    rfl
  obtain ⟨code, hcode⟩ : ∃ code, ∀ flag, closeScopeR scope ex flag m.state = some (s, code) :=
    ⟨_, fun flag => by
      unfold closeScopeR
      rw [snap]
      rfl⟩
  have hmach : ∀ flag fid, (interpRAt root.program m.completedExits).closeScope scope ex flag fid
      m.state = some (s, code) := fun flag _ => hcode flag
  show SettlesTyped root rootTy w f.id rest (prepareIterR
    (FiberAction.closeScope (interpRAt root.program m.completedExits) m (saveAnswerR f next) y scope ex))
  unfold FiberAction.closeScope
  rw [hmach]
  obtain ⟨ord, restated⟩ := configTyped_closeState ev.typed hentry hex
  have ev1 : Evaluating root rootTy { w with state := s } { m with state := s } rest f y :=
    ⟨restated, ev.stale, ev.running, ev.live⟩
  have answered : MHostStack root { w with state := s } (({ m with state := s } : RState).update f) f.id
      (((EffTy.pure .unit, row, row) : AmbientPosition), f.frame.interruptible) (finalPos ty flag)
      (.answer next :: f.frame.stack) :=
    .cons (.inl (MFrame.mono ord answer))
      ((MHostStack.races (m := m.update f) (m' := ({ m with state := s } : RState).update f)
        (racesKept_of_eq fun _ => rfl) stack).mono ord)
  cases code with
  | none =>
    -- nothing closes: `void_`, with no mask
    dsimp only
    let fr' : RSaved := { f.frame with current := .pure (.success .unit), stack := .answer next :: f.frame.stack }
    refine SettlesTyped.mono ord (ev1.settle_continue fr' (fun ty' declared' => ?_))
    have same : ty' = ty := Option.some.inj (declared'.symm.trans declared)
    subst same
    exact ⟨row, (((EffTy.pure .unit, row, row) : AmbientPosition), f.frame.interruptible), flag,
      covered, rfl, .pure (ambientExit_const ⟨trivial, trivial⟩) ⟨Row.subset_refl _, Row.subset_refl _⟩,
      answered, ⟨prov.recorded, prov.deferred⟩⟩
  | some code =>
    dsimp only
    have finsAdm := finalizersAdmitted_of_typedState ev.typed.machine
    rw [wide.state] at finsAdm
    have typedCode := closeScope_installs_ambient root w scope ex false m.state s code finsAdm hex
      (hcode false) row
    rcases Bool.eq_false_or_eq_true f.frame.interruptible with masking | masked
    · -- an interruptible closer: masked first, its restoring slot over the answer frame
      rw [termCore_enterUninterruptible_true (fr := (saveAnswerR f next).frame) masking]
      let fr' : RSaved :=
        { f.frame with
          current := code
          interruptible := false
          stack := .restoreMask true :: .answer next :: f.frame.stack }
      refine SettlesTyped.mono ord (ev1.settle_continue fr' (fun ty' declared' => ?_))
      have same : ty' = ty := Option.some.inj (declared'.symm.trans declared)
      subst same
      refine ⟨row, (((EffTy.pure .unit, row, row) : AmbientPosition), false), flag, covered, rfl,
        ambientProg_mono root ord typedCode, ?_, ⟨prov.recorded, prov.deferred⟩⟩
      rw [masking] at answered
      exact .cons (.inl (.restoreMask true (ambient_wf typedCode))) answered
    · -- an already masked closer: no second restoring slot
      rw [termCore_enterUninterruptible_false (fr := (saveAnswerR f next).frame) masked]
      let fr' : RSaved := { f.frame with current := code, stack := .answer next :: f.frame.stack }
      refine SettlesTyped.mono ord (ev1.settle_continue fr' (fun ty' declared' => ?_))
      have same : ty' = ty := Option.some.inj (declared'.symm.trans declared)
      subst same
      exact ⟨row, (((EffTy.pure .unit, row, row) : AmbientPosition), f.frame.interruptible), flag,
        covered, rfl, ambientProg_mono root ord typedCode, answered, ⟨prov.recorded, prov.deferred⟩⟩

/-- The callback recognizer's inversion: a scope's exit callback is that operation at the head. -/
theorem scopeExitCallback?_some {p : RProgram} {prev : Ctx} {sc : Nat} {ex : ExitV}
    (h : Contracts.scopeExitCallback? p = some (prev, sc, ex)) :
    ∃ next, p = .vis (.inr (.scopeExit prev sc ex)) next := by
  unfold Contracts.scopeExitCallback? at h
  split at h
  · cases h
    exact ⟨_, rfl⟩
  · cases h

/-- **A finalizer's boundary under any continuation, at the ambient judgment** (`finalizerR`,
`Laws/Program/DenoteR.lean`; the ambient instance of `finalizerBind_typed`, `Typed/Seq.lean`): with
the cleanup typed at rc.112's finalizer type `⟨unknown, never⟩` at a row (`finPosition`) and the
body's exit at a position within that row, whose failure row the row holds, the boundary bound to
any continuation is typed at that position, a captured context's included. A succeeding cleanup
ends in the `finishFinalizer` marker, which reads no continuation; a failing cleanup after a failed
body combines both causes (`exitOk_restore`); every other failure skips the bind. The cleanup's
work is `ambient_finalizer_guarantees`'s. A step of the claim `step-deliver-preserves`; consumer:
`Evaluating.settle_callback`. -/
theorem ambient_finalizerBind (root : ProgramSource) {w : World} {row : Env.Requirement}
    {result : AmbientPosition} {ex : ExitV} {cleanup : RProgram}
    (payload : AmbientExit w row result ex) (entry : Row.Subset result.failureRow row)
    (wf : result.WF) (cleanupTyped : AmbientProg root w row (finPosition row) cleanup)
    (next : ExitV → RProgram) :
    AmbientProg root w row result ((finalizerR ex cleanup).bind next) := by
  -- the work: the cleanup after a success; after a failure, its failure combined with the body's
  have work : ∀ originalExit, ExitOk w result.type originalExit → AmbientProg root w row
      (((⟨.unknown, result.type.error, Env.Requirement.empty⟩ : EffTy), row, row) : AmbientPosition)
      (match originalExit with
      | .success _ => cleanup
      | .failure _ => (guardR .onFailure cleanup).bind fun
          | .success value => .pure (.success value)
          | .failure cause => .pure (Exit.restoreAfterFinalizer originalExit (.failure cause))) := by
    intro originalExit originalPayload
    cases originalExit with
    | success _ =>
      exact ambientProg_widen root (before := (⟨.unknown, .never, Env.Requirement.empty⟩, row, row))
        (Ty.subN_refl _) (Bounds.subN_never _) (Row.subset_refl _) (Row.subset_refl _) cleanupTyped
    | failure _ =>
      refine ambient_guardBind root cleanupTyped (fun _ ordered exit arm clean => ?_)
        (fun _ _ exit clean absent => ?_) (Row.subset_refl _)
      · cases exit with
        | success _ => exact Bool.noConfusion arm
        | failure _ =>
          rw [ambientInput_const]
          exact .pure (ambientExit_const (exitOk_restore
              (exitOk_failure_of_errorN (Ty.subN_refl _)
                (strongExit_mono _ _ _ _ ordered originalPayload))
              (exitOk_failure_of_errorN (Bounds.subN_never _) clean.1)))
            ⟨Row.subset_refl _, Row.subset_refl _⟩
      · cases exit with
        | success _ =>
          rw [ambientInput_const]
          exact ambientExit_const (exitOk_success_of_answerN (Ty.subN_refl _) clean.1)
        | failure _ => exact Bool.noConfusion absent
  unfold finalizerR
  rw [Effects.Program.bind_assoc]
  refine ambient_guardBind root (work ex payload.1) (fun _ ordered exit arm _ => ?_)
    (fun _ _ exit done absent => ?_) entry wf
  · cases exit with
    | success _ =>
      rw [ambientInput_const]
      exact .finishFinalizer ⟨strongExit_mono _ _ _ _ ordered payload.1, payload.2⟩ ⟨entry, wf⟩
    | failure _ => exact Bool.noConfusion arm
  · cases exit with
    | success _ => exact Bool.noConfusion absent
    | failure _ =>
      rw [ambientInput_const]
      exact ambientExit_failure (exitOk_failure_of_errorN (Ty.subN_refl _) done.1) entry

/-- **The unsafe close's program at the ambient judgment** (`closeScopeUnsafeR`,
`Laws/Program/InterpR.lean`; the ambient instance of `closeScopeUnsafe_installs`,
`Typed/Adequacy.lean`): at every row, at rc.112's finalizer type `⟨unknown, never⟩`
(`internal/effect.ts:3849`). A lone finalizer runs at the row (`finalizer_ambient`: a captured
release under its captured context merged over the current one, `releaseContext`); two or more
are the walk, administrative code at `⟨unit, never⟩` (`closeWalk_typed`, `ambientProg_of_admin`),
widened. The finalizers need only their admission. A step of the claim `step-deliver-preserves`;
consumer: `Evaluating.settle_callback`. -/
theorem closeScopeUnsafe_ambient (root : ProgramSource) (w : World) (scope : Nat) (exit : ExitV)
    (flag : Bool) (st st' : Stores) (program : Option RProgram)
    (admitted : ∀ entry ∈ st.scopes.entries, ∀ fin ∈ entry.scope.closeOrder,
      FinalizerAdmitted root w fin)
    (exitFits : FitsExit w ⟨.unknown, .unknown, Env.Requirement.empty⟩ exit)
    (h : closeScopeUnsafeR scope exit flag st = some (st', program)) (row : Env.Requirement) :
    ∀ code, program = some code → AmbientProg root w row (finPosition row) code := by
  unfold closeScopeUnsafeR at h
  cases hs : scopeCloseSnapshot scope exit st with
  | none =>
    rw [hs] at h
    cases h
  | some snapshot =>
    obtain ⟨state, strategy, order⟩ := snapshot
    rw [hs] at h
    simp only at h
    obtain ⟨_, rfl⟩ := h
    intro code hcode
    match order, hs, hcode with
    | [], _, hcode => cases hcode
    | [fin], hs, hcode =>
      cases hcode
      obtain ⟨entry, hentry, hfin⟩ := lone_of_snapshot hs
      exact finalizer_ambient root (admitted entry hentry fin hfin) exitFits
    | _ :: _ :: _, hs, hcode =>
      cases hcode
      obtain ⟨entry, hentry, horder⟩ := mem_of_snapshot hs
      refine ambientProg_widen root (before := (EffTy.pure .unit, row, row)) ?_ (Ty.subN_refl _)
        (Row.subset_refl _) (Row.subset_refl _)
        (ambientProg_of_admin root
          (closeWalk_typed root w strategy _ exit
            (fun fin hf => admitted entry hentry fin (horder ▸ hf)) exitFits)
          (.fiber _ _ rfl fun _ => .fiber _ _ rfl fun _ => .pure _) row)
      exact Ty.sub_unknown _

/-- **The scoped exit's close settles typed** (decisions row 188 (a); finding F-CLOSE): the walk
stopped at a `scoped` guard's slot and left the scope's exit callback current (`MHostCallback`),
which `prepareScopedExitR` consumes (`internal/effect.ts:3944-3947`): the previous context restored,
its services fitting (the slot's protocol); the scope, present by the same protocol, closed with
the callback's exit, which fits `Exit<unknown, unknown>` (`fitsExit_unknown`; the store edit is
`configTyped_closeState`); and the code installed is the `finishFinalizer` marker carrying the exit,
or the close's program (`closeScopeUnsafe_ambient`) under the finalizer boundary
(`ambient_finalizerBind`). Both are typed at the callback's position at the restored context's
keys, over the host stack below it. A captured release in the close runs under its captured context
merged over the current one (`releaseContext`), so it is typed at that row too.
Consumer: `Evaluating.deliver_keeps`. -/
@[semantics "scope-lifetime-finalization" (requirement := R11)]
theorem Evaluating.settle_callback {root : ProgramSource} {rootTy : EffTy} {w : World}
    {m : RState} {rest : List RCmd} {f : RFiber} {y : Bool} (ev : Evaluating root rootTy w m rest f y)
    (fr : RSaved) {ty : EffTy} {flag : Bool} (declared : w.Γ f.id = some ty)
    (callback : MHostCallback root w (m.update f) f.id (finalPos ty flag) fr) :
    SettlesTyped root rootTy w f.id rest
      (prepareIterR ⟨m, { f with frame := fr }, y, .continue_, [], []⟩) := by
  have wide := ev.typed.machine.wide
  obtain ⟨tin, prev, sc, ex, hcb, payload, ⟨live, services⟩, entry, wf, bit, stack, prov⟩ :=
    callback
  obtain ⟨next, hcur⟩ := scopeExitCallback?_some hcb
  have present : (m.state.scopes.entryAt sc).isSome = true := by
    have l : (w.state.scopes.entryAt sc).isSome = true := live
    rw [wide.state] at l
    exact l
  obtain ⟨scopeEntry, hentry⟩ := Option.isSome_iff_exists.mp present
  let s : Stores := { m.state with scopes := m.state.scopes.closeState sc ex }
  have snap : scopeCloseSnapshot sc ex m.state =
      some (s, scopeEntry.scope.strategy, scopeEntry.scope.closeOrder) := by
    unfold scopeCloseSnapshot
    rw [hentry]
    rfl
  obtain ⟨program, hprog⟩ :
      ∃ program, ∀ flag, closeScopeUnsafeR sc ex flag m.state = some (s, program) :=
    ⟨_, fun _ => by
      unfold closeScopeUnsafeR
      rw [snap]
      rfl⟩
  have hexFits : FitsExit w ⟨.unknown, .unknown, Env.Requirement.empty⟩ ex :=
    fitsExit_unknown payload.1.1
  -- the store edit: the scope closed with the callback's exit
  obtain ⟨ord, restated⟩ := configTyped_closeState ev.typed hentry hexFits
  have ev1 : Evaluating root rootTy { w with state := s } { m with state := s } rest f y :=
    ⟨restated, ev.stale, ev.running, ev.live⟩
  -- any code typed at the callback's position, at the restored context's keys, settles
  suffices settles : ∀ code, AmbientProg root w prev.services.keysRow tin.1 code →
      SettlesTyped root rootTy w f.id rest
        ⟨{ m with state := s }, resetFiber f prev prev.maxOpsBeforeYield prev.preventYield
          { fr with current := code }, y, .continue_, [], []⟩ by
    have finsAdm := finalizersAdmitted_of_typedState ev.typed.machine
    rw [wide.state] at finsAdm
    have installs := closeScopeUnsafe_ambient root w sc ex false m.state s program finsAdm hexFits
      (hprog false) prev.services.keysRow
    cases program with
    | none =>
      have glue : prepareIterR ⟨m, { f with frame := fr }, y, .continue_, [], []⟩ =
          ⟨{ m with state := s }, resetFiber f prev prev.maxOpsBeforeYield prev.preventYield
            { fr with current := .vis (.inr (.finishFinalizer ex)) next }, y, .continue_, [], []⟩ := by
        simp only [prepareIterR, prepareScopedExitR, answerR, hcur, prepareR, hprog]
      rw [glue]
      exact settles _ (.finishFinalizer payload ⟨entry, wf⟩)
    | some c =>
      have glue : prepareIterR ⟨m, { f with frame := fr }, y, .continue_, [], []⟩ =
          ⟨{ m with state := s }, resetFiber f prev prev.maxOpsBeforeYield prev.preventYield
            { fr with current := (finalizerR ex c).bind next }, y, .continue_, [], []⟩ := by
        simp only [prepareIterR, prepareScopedExitR, answerR, hcur, prepareR, hprog]
      rw [glue]
      exact settles _ (ambient_finalizerBind root payload entry wf (installs c rfl) next)
  intro code typedCode
  refine SettlesTyped.mono ord (ev1.settle_ready prev (servicesFit_mono ord services)
    prev.maxOpsBeforeYield prev.preventYield { fr with current := code } (fun ty' declared' => ?_))
  have same : ty' = ty := Option.some.inj (declared'.symm.trans declared)
  subst same
  exact ⟨prev.services.keysRow, tin, flag,
    (Provision.satisfies_iff_subset_keysRow _ _).mpr (Row.subset_refl _), bit,
    ambientProg_mono root ord typedCode,
    MHostStack.races (racesKept_of_eq (m := m.update f)
      (m' := ({ m with state := s } : RState).update f) fun _ => rfl) (MHostStack.mono ord stack),
    ⟨prov.recorded, prov.deferred⟩⟩

/-- **A walk that stopped at a registration marker settles typed**: the glue leaves the marker, and
`settle` queues `loop`, which reads no code of a marker-current fiber. -/
theorem Evaluating.settle_marker {root : ProgramSource} {rootTy : EffTy} {w : World} {m : RState}
    {rest : List RCmd} {f : RFiber} {y : Bool} (ev : Evaluating root rootTy w m rest f y)
    (fr : RSaved) {ty : EffTy} {flag : Bool} (declared : w.Γ f.id = some ty)
    {covered : Env.Requirement} (cov : f.context.services.Satisfies covered)
    (marker : MHostMarker root w (m.update f) f.id covered (finalPos ty flag) fr) :
    SettlesTyped root rootTy w f.id rest
      (prepareIterR ⟨m, { f with frame := fr }, y, .continue_, [], []⟩) := by
  have ⟨raceId, _, _, _, hmark, _⟩ := marker
  obtain ⟨k, hk⟩ := raceRegistrationR_shape hmark
  have inert : prepareIterR ⟨m, { f with frame := fr }, y, .continue_, [], []⟩ =
      ⟨m, { f with frame := fr }, y, .continue_, [], []⟩ := by
    obtain ⟨cur, stk, intr, ic, di⟩ := fr
    change cur = _ at hk
    subst hk
    rfl
  rw [inert]
  have step := configTyped_frame_marker ev.typed rfl ev.look ev.running fr declared cov marker y
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
      (prepareIterR ⟨m, { f with frame := fr }, y, .finished ex, [], []⟩) := by
  obtain ⟨ty, declared⟩ := ev.declared
  obtain ⟨row, tin, _, _, _, current, _, _⟩ := ev.code marker ty declared
  let fr' : RSaved := { fr with current := prepareR m.completedExits fr.current }
  have prepared : AmbientProg root w row tin.1 fr'.current := by
    show AmbientProg root w row tin.1 (prepareR m.completedExits fr.current)
    rw [cur]
    exact prepareR_typed _ _ ev.view current
  have glue : prepareIterR ⟨m, { f with frame := fr }, y, .finished ex, [], []⟩ =
      ⟨m, { f with frame := fr' }, y, .finished ex, [], []⟩ :=
    prepareScopedExitR_of_typed prepared
  rw [glue]
  have step := configTyped_frame_finish ev.typed rfl ev.look ev.running fr' empty
    ⟨prov.recorded, prov.deferred⟩ (raceRegistrationR_ambient prepared) ex exit
  rw [rupdate_rupdate m (show ({ f with frame := fr' } : RFiber).id = f.id from rfl)] at step
  exact ⟨w, leHost_refl w, step⟩

/-- **A delivery through the saved stack settles typed**: a success with a deferred interrupt
installs the recorded cause at the code's position, whose failure row the code's entry covers;
otherwise the walk over the host stack (`ambient_popR_hostTyped`, the hook laws of the machine's
interpreter at the typed view) ends in typed code, the callback, a marker or the delivered exit,
each settled by its step. -/
theorem Evaluating.deliver_keeps {root : ProgramSource} {rootTy : EffTy}
    {w : World} {m : RState} {rest : List RCmd} {f : RFiber} {y : Bool} (ev : Evaluating root rootTy w m rest f y)
    (marker : raceRegistrationR f.frame.current = none) (ex : ExitV)
    (payload : ∀ row (tin : AmbientPosition), AmbientProg root w row tin f.frame.current →
      AmbientExit w row tin ex) :
    SettlesTyped root rootTy w f.id rest
      (prepareIterR (deliverR (interpRAt root.program m.completedExits) m f y ex)) := by
  obtain ⟨ty, declared⟩ := ev.declared
  have same : ∀ ty', w.Γ f.id = some ty' → ty' = ty :=
    fun _ h => Option.some.inj (h.symm.trans declared)
  obtain ⟨row, tin, flag, covered, bit, current, stack, prov⟩ := ev.code marker ty declared
  obtain ⟨hex, sub⟩ := ambientExit_self (payload row tin.1 current)
  have laws := mHookLaws_interpRAt root w m.completedExits ev.view
  rcases deliverR_cases (interpRAt root.program m.completedExits) m f y ex with h | h <;> rw [h]
  · have walk := ambient_popR_hostTyped root _ w (m.update f) f.id laws row stack ex
      { f.frame with deferredInterrupt := false } hex sub bit.symm ⟨prov.recorded, fun h => nomatch h⟩
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
      rcases walk with ⟨row', tin', sub', mask', code', stack', prov''⟩ | callback | hmarker
      · exact ev.settle_continue frame (fun ty' d => by
          rw [same ty' d]
          exact ⟨row', tin', flag, f.context.services.satisfies_weaken covered sub', mask', code',
            stack', prov''⟩)
      · exact ev.settle_callback frame declared callback
      · exact ev.settle_marker frame declared covered hmarker
    | some ex' =>
      obtain ⟨empty, cur⟩ := done ex' rfl
      exact ev.settle_finished frame empty cur prov' marker ex'
        (fun ty' d => by rw [same ty' d]; exact walk.1.1)
  · exact ev.settle_continue _ (fun ty' d => by
      rw [same ty' d]
      exact ⟨row, tin, flag, covered, bit,
        .pure (ambientExit_failure (strongExit_of_clean w _ _ (pendingCause_clean prov)
          (pendingCause_noShapeDefect _ prov)) (ambient_entry current))
          ⟨ambient_entry current, ambient_wf current⟩, stack,
        ⟨prov.recorded, fun h => nomatch h⟩⟩)

/-- **The walk keeps `I`**: a bare exit is typed at the current code's position at its row. -/
theorem walkKeeps (root : ProgramSource) (rootTy : EffTy) : WalkKeeps root rootTy := by
  intro w m rest f y ex ev hc
  exact ev.deliver_keeps (by rw [hc]; rfl) ex
    (fun row tin current => by rw [hc] at current; exact ambientProg_pure_inv current)

/-- **`unguard`**: the guard's exit is delivered through the saved stack (the `unguard` arm's
payload is typed at the code's position at its row). -/
theorem clause_unguard (root : ProgramSource) (rootTy : EffTy) (ex : ExitV) :
    FiberClauseKeeps root rootTy (.unguard ex) := by
  intro w m rest f y next ev hc
  show SettlesTyped root rootTy w f.id rest
    (prepareIterR (deliverR (interpRAt root.program m.completedExits) m f y ex))
  exact ev.deliver_keeps (by rw [hc]; rfl) ex
    (fun row tin current => by rw [hc] at current; exact ambientProg_unguard_inv current)

/-- The cleanup-end marker's inversion at the ambient judgment: its payload is typed at the code's
position at its row. -/
theorem ambientProg_finishFinalizer_inv {root : ProgramSource} {w : World} {available : Env.Requirement}
    {position : AmbientPosition} {ex : ExitV} {k : ExitV → RProgram}
    (h : AmbientProg root w available position (.vis (.inr (.finishFinalizer ex)) k)) :
    AmbientExit w available position ex := by
  cases h with
  | fiber _ _ notFinish _ _ _ _ _ => exact absurd rfl (notFinish ex)
  | finishFinalizer payload _ => exact payload

/-- **`finishFinalizer`**: the finalizer's restored exit is delivered through the saved stack. -/
theorem clause_finishFinalizer (root : ProgramSource) (rootTy : EffTy) (ex : ExitV) :
    FiberClauseKeeps root rootTy (.finishFinalizer ex) := by
  intro w m rest f y next ev hc
  show SettlesTyped root rootTy w f.id rest
    (prepareIterR (deliverR (interpRAt root.program m.completedExits) m f y ex))
  exact ev.deliver_keeps (by rw [hc]; rfl) ex
    (fun row tin current => by rw [hc] at current; exact ambientProg_finishFinalizer_inv current)

/-! ## The clauses that edit the fiber's context -/

/-- The evaluator's machine after a trace event is the evaluated state's machine with that event. -/
theorem Evaluating.emit {root : ProgramSource} {rootTy : EffTy} {w : World} {m : RState}
    {rest : List RCmd} {f : RFiber} {y : Bool} (ev : Evaluating root rootTy w m rest f y)
    (events : List (RunEvent EffName EffThunk Val Err Defect FiberId Ann Ctx RProgram Unit)) :
    Evaluating root rootTy w (m.emit events) rest f y :=
  ⟨configTyped_emit ev.typed events, ev.stale, ev.running, ev.live⟩

/-- **`setContext`**: the context set (its services fit, the pre), the budget cached from it, the
trace event, and `unit` answered at the new context's keys (the operation's input). -/
theorem clause_setContext (root : ProgramSource) (rootTy : EffTy) (ctx : Ctx) :
    FiberClauseKeeps root rootTy (.setContext ctx) := by
  intro w m rest f y next ev hc
  show SettlesTyped root rootTy w f.id rest
    (prepareIterR (FiberAction.setContext _ m f y ctx (answerWith next)))
  unfold FiberAction.setContext
  rcases hb : (interpRAt root.program m.completedExits).budgetOf ctx with ⟨maxOps, prevent⟩
  obtain ⟨ty, declared⟩ := ev.declared
  obtain ⟨_, _, _, _, _, current0, _, _⟩ := ev.code (by rw [hc]; rfl) ty declared
  rw [hc] at current0
  obtain ⟨_, services, _⟩ := ambientProg_fiber_inv current0 (fun _ h => nomatch h)
    (fun _ h => nomatch h) (fun _ h => nomatch h) (fun _ _ _ h => nomatch h)
  refine (ev.emit [RunEvent.contextSet f.id ctx]).settle_reset ctx services maxOps prevent
    { f.frame with current := next .unit } (fun ty' declared' => ?_)
  obtain ⟨row, tin, flag, _, bit, current, stack, prov⟩ := ev.code (by rw [hc]; rfl) ty' declared'
  rw [hc] at current
  obtain ⟨cert, pre, typedNext, _⟩ := ambientProg_fiber_inv current (fun _ h => nomatch h)
    (fun _ h => nomatch h) (fun _ h => nomatch h) (fun _ _ _ h => nomatch h)
  exact ⟨ctx.services.keysRow, tin, flag,
    (Provision.satisfies_iff_subset_keysRow _ _).mpr (Row.subset_refl _), bit,
    typedNext w (leHost_refl w) .unit (show ambientFiberPost w row (.setContext ctx) cert Val.unit from rfl),
    stack.races (racesKept_of_eq (m := m.update f) (m' := (m.emit [RunEvent.contextSet f.id ctx]).update f)
      fun _ => rfl), ⟨prov.recorded, prov.deferred⟩⟩

/-- **`getId`**: the fiber's own id, answered as a number. -/
theorem clause_getId (root : ProgramSource) (rootTy : EffTy) :
    FiberClauseKeeps root rootTy .getId := by
  intro w m rest f y next ev hc
  exact ev.settle_continue _ (ev.answer_typed hc (by rw [hc]; rfl) (fun _ h => nomatch h)
    (fun _ h => nomatch h) (fun _ h => nomatch h) (fun _ _ _ h => nomatch h) (Val.nat f.id.value)
    (fun _ _ _ => ⟨f.id, rfl⟩) (fun _ => rfl))

/-- **`ambientScope`**: the context's ambient scope, present by `J` (`ambientScope_live`, decisions
row 156), answered as its handle; without one, the `missingService` defect, which the exit judgment
admits at every type (part one excludes only `badName` and `notImplemented`), at the code's
position, whose failure row its entry covers. -/
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
      (Val.scopeHandle scope) (fun _ _ _ => fits_scopeHandle _ _ live) (fun _ => rfl))
  | none =>
    refine ev.settle_continue { f.frame with current := .pure (.failure (Cause.die .missingService)) }
      (fun ty declared => ?_)
    obtain ⟨row, tin, flag, covered, bit, current, stack, prov⟩ := ev.code (by rw [hc]; rfl) ty declared
    have clean : NoShapeDefect tin.1.type (.failure (Cause.die .missingService)) := by
      intro reason member
      simp only [Cause.die_reasons, List.mem_singleton] at member
      subst member
      exact ⟨(fun h => nomatch h), (fun h => nomatch h)⟩
    exact ⟨row, tin, flag, covered, bit,
      .pure (ambientExit_failure (strongExit_of_clean w _ _ rfl clean) (ambient_entry current))
        ⟨ambient_entry current, ambient_wf current⟩, stack, ⟨prov.recorded, prov.deferred⟩⟩

/-! ## `scoped`: a scope made, the context extended, the body guarded -/

/-- **The `scoped` arm's code at the ambient judgment** (decisions row 188 (a); the ambient instance
of `scopedGuardBind_typed`, `Typed/Seq.lean`): the `onExit false` guard over a body typed at `mid`,
bound to the scope's exit callback, is typed at `result` when the scope is present, the context the
callback restores fits, and every exit of `mid` lands at `result` within that context's keys
(`ProgramArrow.scopedGuard`, `Typed/Residual.lean`, whose `widen` reads those keys). The body closes
by `ProgramArrow.close`. A step of the claim `step-deliver-preserves`; consumer: `clause_scoped`. -/
theorem ambient_scopedGuardBind (root : ProgramSource) {w : World} {row : Env.Requirement}
    {mid result : AmbientPosition} {a : RProgram} {prev : Ctx} {sc : Nat}
    {j : ExitV → RProgram} (ha : AmbientProg root w row mid a) (live : ScopeLive w sc)
    (services : ServicesFit w prev.services)
    (widen : ∀ w', w.leHost w' → ∀ ex, AmbientExit w' (ambientInput mid ex) mid ex →
      AmbientExit w' prev.services.keysRow result ex)
    (entry : Row.Subset result.failureRow row) (wf : result.WF) :
    AmbientProg root w row result
      ((guardR (.onExit false) a).bind fun ex => .vis (.inr (.scopeExit prev sc ex)) j) := by
  show AmbientProg root w row result (.vis (.inr (.guard_ (.onExit false))) _)
  refine .scopedGuard mid prev sc ?_ (fun _ => rfl) live services widen ⟨entry, wf⟩
  show AmbientProg root w row mid
    ((a.bind fun ex => .vis (.inr (.unguard ex)) Effects.Program.pure).bind _)
  rw [Effects.Program.bind_assoc]
  exact ProgramArrow.close ha fun ex => .vis (.inr (.scopeExit prev sc ex)) j

/-- **`scoped`** (`internal/effect.ts:3938-3948`, decisions row 188 (a)): a fresh sequential scope
made in the store (the `scopeMake` row's step, so the store's order, well-formedness and typing are
the row's, and the new entry is empty), the fiber's context extended with it (`withScope`; the scope
service fits because the scope is present), and the body run under the `onExit` guard bound to the
scope's exit callback (`ambient_scopedGuardBind`) over the saved answer frame keep `I`. The body
runs at the new context's keys, which hold the operation's row and the body's requirement row (the
pre gives that row without the scope key, `bodyRequires`; the install adds the key). The guard's
exits land at the operation's row, which the previous context's keys hold. The world grows by the
store. Consumer: `deliver_preserves_of_clauses` through `Clauses/All.lean`. -/
@[semantics "scope-lifetime-finalization" (requirement := R11)]
theorem clause_scoped (root : ProgramSource) (rootTy : EffTy) (body : Point) :
    FiberClauseKeeps root rootTy (.scoped body) := by
  intro w m rest f y next ev hc
  have wide := ev.typed.machine.wide
  have c5 : ServicesFit w f.context.services :=
    (ev.typed.machine.fiber (rfiber?_mem ev.look)).ok.c5
  obtain ⟨ty, declared⟩ := ev.declared
  obtain ⟨row, tin, flag, covered, bit, current, stack, prov⟩ :=
    ev.code (by rw [hc]; rfl) ty declared
  rw [hc] at current
  obtain ⟨cert, ⟨⟨hpt, hstk⟩, hreq⟩, typedNext, _, _⟩ := ambientProg_fiber_inv current
    (fun _ h => nomatch h) (fun _ h => nomatch h) (fun _ h => nomatch h) (fun _ _ _ h => nomatch h)
  change EffTy at cert
  change Row.Subset (Row.diff cert.requires (Env.Requirement.single Env.scopeKey)) row at hreq
  -- the store with the new scope: the `scopeMake` row's step
  let scope := m.state.nextName
  let s : Stores :=
    { m.state with scopes := m.state.scopes.make scope .sequential, nextName := scope + 1 }
  have step : syncOpStep (.scopeMake .sequential) m.state = some (s, Val.scopeHandle scope) :=
    syncOpStep_scopeMake m.state .sequential
  have le : m.state.le s := syncOpStep_le _ _ _ _ step
  have swf : s.WF := syncOpStep_wf _ _ _ _ wide.wf rfl step
  have ord : w.leHost { w with state := s } :=
    leHost_restate (by rw [wide.state]; exact le) (by rw [wide.state]; rfl)
      (by rw [wide.state]; rfl) (by rw [wide.state]; rfl)
  have stores : StoresOk (preds root) { w with state := s } Expect.root s := by
    obtain ⟨c0, c1, c2, ⟨c3⟩, c4, _⟩ := storesOk_world ord rfl rfl rfl wide.stores
    refine ⟨c0, c1, c2, ⟨fun e he => ?_⟩, c4, trivial⟩
    change e ∈ m.state.scopes.entries ++ [⟨scope, Scope.make .sequential⟩] at he
    rcases List.mem_append.mp he with old | new
    · exact c3 e old
    · rw [List.mem_singleton] at new
      subst new
      exact ⟨⟨trivial⟩⟩
  obtain ⟨_, restated⟩ := configTyped_restate ev.typed le rfl rfl rfl swf stores
    (Guard.internalKeys_state_subset _ s
      (Guard.storeKeys_mono (List.Subset.refl _) (List.Subset.refl _)))
    (fun o ho owner priority mode => wide.live.dueOwners o ho owner priority mode)
    (List.Subset.refl _)
  have live' : ScopeLive { w with state := s } scope := ScopeStore.entryAt_make_self _ _ _
  have ev1 : Evaluating root rootTy { w with state := s } { m with state := s } rest f y :=
    ⟨restated, ev.stale, ev.running, ev.live⟩
  -- the context with the scope installed, its services fitting
  let ctx := f.context.withScope scope
  have handle := fits_scopeHandle _ _ live'
  have carrier : ({ w with state := s } : World).serviceTy Env.scopeKey = some Ty.scope := by
    show w.serviceTy Env.scopeKey = some Ty.scope
    rw [ev.typed.machine.services]
    exact serviceTy_scopeKey _
  have services : ServicesFit { w with state := s } ctx.services := by
    show ServicesFit _ (f.context.services.addV Env.scopeKey (Value.scope scope))
    exact servicesFit_addV (servicesFit_mono ord c5) carrier (fits_flatFits rfl handle)
      (fits_live _ _ _ handle)
  -- the body's row: the new context's keys, which hold the operation's row and the body's
  have kept : ctx.services.Satisfies row := satisfies_addV Env.scopeKey (Value.scope scope) covered
  have scopeCovers : ctx.services.Satisfies cert.requires := by
    intro k member
    by_cases isScope : k = Env.scopeKey
    · subst isScope
      show ((f.context.services.addV Env.scopeKey (Value.scope scope)).getV Env.scopeKey).isSome =
        true
      rw [Env.Context.getV_addV_same]
      rfl
    · exact kept k (hreq k
        ((Row.mem_diff k _ _).mpr ⟨member, fun h => isScope ((Row.mem_singleton _ _).mp h)⟩))
  have rowSub : Row.Subset row ctx.services.keysRow :=
    (Provision.satisfies_iff_subset_keysRow _ _).mp kept
  have restored : Row.Subset row f.context.services.keysRow :=
    (Provision.satisfies_iff_subset_keysRow _ _).mp covered
  -- the body at the new context's keys, guarded by the scope's exit callback
  have typedBody : AmbientProg root { w with state := s } ctx.services.keysRow
      (((cert, ctx.services.keysRow, ctx.services.keysRow) : AmbientPosition))
      (bodyR (interpRAt root.program m.completedExits) (.at_ body)) :=
    denoteAt_ambient root (w := { w with state := s }) ev.typed.machine.sourceWF
      ev.typed.machine.services (pointTyped_mono ord hpt)
      ((Provision.satisfies_iff_subset_keysRow _ _).mp scopeCovers)
      (ambientStackTyped_widen rowSub (ambientStackTyped_mono ord hstk))
  have typedCode : AmbientProg root { w with state := s } ctx.services.keysRow
      (((cert, row, row) : AmbientPosition))
      ((guardR (.onExit false) (bodyR (interpRAt root.program m.completedExits) (.at_ body))).bind
        fun ex => .vis (.inr (.scopeExit f.context scope ex)) Effects.Program.pure) :=
    ambient_scopedGuardBind root (result := ((cert, row, row) : AmbientPosition))
      (j := Effects.Program.pure) typedBody live' (servicesFit_mono ord c5)
      (fun _ _ ex hex => ⟨hex.1, by cases ex <;> exact restored⟩) rowSub (Row.subset_refl _)
  -- the answer frame carries the body's exit to the continuation at the operation's row
  have answerFrame : MFrame root { w with state := s }
      ((((cert, row, row) : AmbientPosition)), tin.2) (tin.1, tin.2) (.answer next) :=
    .answer next fun w'' o ex hex => by
      rw [ambientInput_const]
      exact typedNext w'' (leHost_trans _ _ _ ord o) ex hex.1
  let fr' : RSaved := { f.frame with
    current := (guardR (.onExit false)
      (bodyR (interpRAt root.program m.completedExits) (.at_ body))).bind
        fun ex => .vis (.inr (.scopeExit f.context scope ex)) Effects.Program.pure
    stack := .answer next :: f.frame.stack }
  refine SettlesTyped.mono ord (ev1.settle_reset ctx services ctx.maxOpsBeforeYield
    ctx.preventYield fr' (fun ty' declared' => ?_))
  have same : ty' = ty := Option.some.inj (declared'.symm.trans declared)
  subst same
  exact ⟨ctx.services.keysRow, ((((cert, row, row) : AmbientPosition)), tin.2), flag,
    (Provision.satisfies_iff_subset_keysRow _ _).mpr (Row.subset_refl _), bit, typedCode,
    .cons (.inl answerFrame) (MHostStack.races (racesKept_of_eq (m := m.update f)
      (m' := ({ m with state := s } : RState).update f) fun _ => rfl) (MHostStack.mono ord stack)),
    ⟨prov.recorded, prov.deferred⟩⟩

/-! ## `interruptScoped`: the scope's fiber finalizer -/

/-- **The saved answer frame around a `unit` reply**: the frame `saveAnswerR f (seqR next)` saves is
a machine frame from the reply's position at the operation's row to the operation's: a `unit`
success runs the continuation at the operation's post; a failure, clean at `never`, is the
operation's own, its failure row covered by the operation's entry. -/
theorem Evaluating.unitAnswerFrame {root : ProgramSource} {w : World} {row : Env.Requirement}
    {q : AmbientPosition} {b : Bool} {next : Val → RProgram}
    (typedNext : ∀ w', w.leHost w' → ∀ ans : Val, ans = Val.unit → AmbientProg root w' row q (next ans))
    (entry : Row.Subset q.failureRow row) (wf : q.WF) :
    MFrame root w ((((⟨.unit, .never, Env.Requirement.empty⟩ : EffTy), row, row) : AmbientPosition), b)
      (q, b) (.answer (seqR next)) :=
  .answer _ fun w' o ex hex => by
    rw [ambientInput_const]
    cases ex with
    | success v => exact typedNext w' o v (fits_unit_inv (w := w') (show Fits w' v .unit from hex.1.1))
    | failure c =>
      exact .pure (ambientExit_failure (exitOk_failure_of_errorN (Bounds.subN_never _) hex.1) entry)
        ⟨entry, wf⟩

/-- **`interruptScoped`** (`:5368`, D6b): on the fiber itself, `unit` answered; on another fiber, the
public interrupt program installed over the saved answer frame, typed at `unit` at the fiber's row
(`fiberValR (.interrupt target)`, whose pre is this row's, the target's declaration; finding
F-PRE); the frame carries the reply to the continuation. -/
theorem clause_interruptScoped (root : ProgramSource) (rootTy : EffTy) (target : FiberId) :
    FiberClauseKeeps root rootTy (.interruptScoped target) := by
  intro w m rest f y next ev hc
  show SettlesTyped root rootTy w f.id rest (prepareIterR
    (if target = f.id then ⟨m, answerR f (next .unit), y, .continue_, [], []⟩
     else FiberAction.interruptScoped _ m (saveAnswerR f (seqR next)) y target))
  split
  · exact ev.settle_continue _ (ev.answer_typed hc (by rw [hc]; rfl) (fun _ h => nomatch h)
      (fun _ h => nomatch h) (fun _ h => nomatch h) (fun _ _ _ h => nomatch h) .unit
      (fun _ _ _ => rfl) (fun _ => rfl))
  · rename_i other
    unfold FiberAction.interruptScoped
    rw [if_neg (show target ≠ (saveAnswerR f (seqR next)).id from other)]
    refine ev.settle_continue { f.frame with
      current := fiberValR (.interrupt target) rfl, stack := .answer (seqR next) :: f.frame.stack }
      (fun ty declared => ?_)
    obtain ⟨row, tin, flag, covered, bit, current, stack, prov⟩ := ev.code (by rw [hc]; rfl) ty declared
    rw [hc] at current
    obtain ⟨_, pre, typedNext, entry, wf⟩ := ambientProg_fiber_inv current (fun _ h => nomatch h)
      (fun _ h => nomatch h) (fun _ h => nomatch h) (fun _ _ _ h => nomatch h)
    refine ⟨row, ((((⟨.unit, .never, Env.Requirement.empty⟩ : EffTy), row, row) : AmbientPosition), tin.2),
      flag, covered, bit, ?_,
      .cons (.inl (Evaluating.unitAnswerFrame (fun w' o ans post => typedNext w' o ans post) entry wf))
        stack, ⟨prov.recorded, prov.deferred⟩⟩
    refine .fiber (op := .interrupt target) (fun _ h => nomatch h) (fun _ h => nomatch h)
      (fun _ h => nomatch h) (fun _ _ _ h => nomatch h) () pre (fun w' _ ans post => ?_)
      ⟨Row.subset_refl _, Row.subset_refl _⟩
    change ans = Val.unit at post
    subst post
    exact .pure (ambientExit_const (strongExit_success w' _ _ trivial)) ⟨Row.subset_refl _, Row.subset_refl _⟩

/-! ## `interruptAs`: the interrupt recorded on a declared target -/

/-- Editing two distinct fibers commutes. -/
theorem rupdate_comm (m : RState) {f g : RFiber} (hne : g.id ≠ f.id) :
    (m.update f).update g = (m.update g).update f := by
  unfold RunMachine.update
  have fibers : ((m.fibers.map fun x => if x.id = f.id then f else x).map
      fun x => if x.id = g.id then g else x) =
      ((m.fibers.map fun x => if x.id = g.id then g else x).map
        fun x => if x.id = f.id then f else x) := by
    rw [List.map_map, List.map_map]
    apply List.map_congr_left
    intro x _
    show (if (if x.id = f.id then f else x).id = g.id then g else if x.id = f.id then f else x) =
      (if (if x.id = g.id then g else x).id = f.id then f else if x.id = g.id then g else x)
    by_cases hf : x.id = f.id
    · by_cases hg : x.id = g.id
      · exact absurd (hg.symm.trans hf) hne
      · simp only [if_pos hf, if_neg hg, if_neg (show f.id ≠ g.id from fun h => hne h.symm)]
    · by_cases hg : x.id = g.id
      · simp only [if_neg hf, if_pos hg, if_neg hne]
      · simp only [if_neg hf, if_neg hg]
  rw [fibers]

/-- A trace event and a fiber edit commute. -/
theorem emit_update_comm (m : RState) (g : RFiber)
    (events : List (RunEvent EffName EffThunk Val Err Defect FiberId Ann Ctx RProgram Unit)) :
    (m.emit events).update g = (m.update g).emit events := by
  cases events <;> rfl

/-- An interrupt record keeps the fiber's id. -/
theorem interruptRecord_id (interp : RInterp) (who : Option FiberId) (extra : ReasonAnnotations Ann)
    (t : RFiber) : (interruptRecord interp who extra t).1.id = t.id := by
  unfold interruptRecord interruptWithCause
  aesop

/-- **`interruptAs`** (`:871-884`, D6b): the target is declared (the pre), so it is a fiber of the
machine; the interrupt is recorded on it (`configTyped_interruptRecord`), its evaluation queued when it
was idle and interruptible, and `afterInterrupt` queued for the host, whose reply (`unit`, the
target's exit awaited as a value) walks the saved stack through the answer frame saved first. On the
fiber itself the record is overwritten by the fiber's own settlement, as the machine does. -/
theorem clause_interruptAs (root : ProgramSource) (rootTy : EffTy) (target who : FiberId) :
    FiberClauseKeeps root rootTy (.interruptAs target who) := by
  intro w m rest f y next ev hc
  obtain ⟨ty, declared⟩ := ev.declared
  obtain ⟨row, ⟨q, b⟩, flag, covered, bit, current, stack, prov⟩ := ev.code (by rw [hc]; rfl) ty declared
  change b = f.frame.interruptible at bit
  subst bit
  change AmbientProg root w row q f.frame.current at current
  rw [hc] at current
  obtain ⟨_, pre, typedNext, entry, wf⟩ := ambientProg_fiber_inv current (fun _ h => nomatch h)
    (fun _ h => nomatch h) (fun _ h => nomatch h) (fun _ _ _ h => nomatch h)
  have wide := ev.typed.machine.wide
  have hmem : f ∈ (m.update f).fibers := rfiber?_mem ev.look
  have old := ev.typed.machine.fiber hmem
  have notParked : f.parked = .notParked := by
    cases hp : f.parked with
    | notParked => rfl
    | withGuard _ =>
      have idle := old.parkedIdle (by rw [hp]; exact fun h => nomatch h)
      rw [ev.running] at idle
      cases idle
  -- the saved answer frame, an arrow from `unit` to the code's type
  let fr' : RSaved := { f.frame with stack := .answer (seqR next) :: f.frame.stack }
  let g : RFiber := { f with frame := fr' }
  have pushed : MHostStack root w (m.update f) f.id
      ((((⟨.unit, .never, Env.Requirement.empty⟩ : EffTy), row, row) : AmbientPosition),
        f.frame.interruptible) (finalPos ty flag) fr'.stack :=
    .cons (.inl (Evaluating.unitAnswerFrame (fun w' o ans post => typedNext w' o ans post) entry wf))
      stack
  have same : ∀ ty', w.Γ f.id = some ty' → ty' = ty :=
    fun _ h => Option.some.inj (h.symm.trans declared)
  have fresh : FiberTyped root w ((m.update f).update g) g :=
    fiberTyped_frame old ev.look ev.running fr'
      (fun ty' d => by
        rw [same ty' d]
        exact ⟨_, flag, MPositionStack.of_host pushed⟩)
      ⟨prov.recorded, prov.deferred⟩
      (fun _ h => by
        change raceRegistrationR f.frame.current = some _ at h
        rw [hc, raceRegistrationR_ambient current] at h
        cases h)
  have edited : ConfigTyped root rootTy w (m.update g) rest := by
    rw [← rupdate_rupdate m (show g.id = f.id from rfl)]
    exact configTyped_frame_edit ev.typed rfl ev.look ev.running fr' fresh
  obtain ⟨f0, hf0, _⟩ := ev.stale
  have lookG : (m.update g).fiber? f.id = some g :=
    rfiber?_update_self (f := f0) (g := g) (by rw [rfiber?_id hf0]; exact hf0) (rfiber?_id hf0).symm
  obtain ⟨sourceTy, hsource⟩ := Option.isSome_iff_exists.mp pre
  have after : ConfigTyped root rootTy w (m.update g)
      (.afterInterrupt f.id y (.join target .awaitValue) :: rest) := by
    refine configTyped_cons_plain edited _ trivial ⟨g, lookG, ev.running, notParked⟩ ?_ ?_ trivial
      rfl (fun _ _ _ h => nomatch h) (fun _ _ h => nomatch h) (fun _ _ _ h => nomatch h)
      (fun _ _ _ _ _ h => nomatch h) (fun _ _ h => nomatch h) (fun _ _ h => nomatch h)
    · intro x hx
      rw [lookG] at hx
      cases hx
      exact ⟨EffTy.pure .unit, ⟨sourceTy, hsource, rfl⟩, row, ty, flag, declared, covered,
        pushed.races (racesKept_of_eq (m := m.update f) (m' := m.update g) fun _ => rfl),
        ⟨prov.recorded, prov.deferred⟩⟩
    · intro o ho
      cases ho
      rw [commandOwner_update]
      exact owner_free ev.typed.queue rfl
  -- the target is a fiber of the machine
  have targetMem : target ∈ (m.update f).fibers.map RunFiber.id := (wide.fibers target).mp pre
  obtain ⟨t₁, ht₁⟩ : ∃ t₁, (m.update f).fiber? target = some t₁ := by
    obtain ⟨x, hx, hid⟩ := List.mem_map.mp targetMem
    refine ⟨x, ?_⟩
    rw [← hid]
    exact rfiber?_of_mem wide.fiberIds hx
  show SettlesTyped root rootTy w f.id rest
    (prepareIterR (FiberAction.interruptAs _ m g y target who))
  unfold FiberAction.interruptAs
  by_cases self : target = f.id
  · subst self
    rw [hf0]
    have sourceId : f0.id = g.id := rfiber?_id hf0
    have installed : ((m.emit [.interruptRecorded (some who) f.id]).update g).fiber? g.id = some g := lookG
    let changed := interruptRecord (interpR root.program) (some who) (stackAnnotationsOf f.id) g
    have changedId : changed.1.id = g.id := interruptRecord_id _ _ _ _
    have recorded := configTyped_interruptRecord
      (configTyped_emit after [.interruptRecorded (some who) f.id]) installed
      (some who) (stackAnnotationsOf f.id)
    have finalLook : (((m.emit [.interruptRecorded (some who) f.id]).update g).update changed.1).fiber?
        changed.1.id = some changed.1 := rfiber?_update_self installed changedId
    have same := rupdate_self finalLook recorded.machine.wide.fiberIds
    refine ⟨w, leHost_refl w, ?_⟩
    simp only [prepareIterR, settle, applyFiberEdits, List.foldl_cons, List.foldl_nil,
      applyFiberEdit, List.nil_append]
    rw [sourceId, installed]
    dsimp only
    have delta : interruptWithCause
        (interruptCause (interpRAt root.program m.completedExits) (some who)
          ((interpRAt root.program m.completedExits).stackAnnotations g.id) g.id) g = changed := rfl
    rw [delta]
    have finalLook' : (((m.emit [.interruptRecorded (some who) f.id]).update g).update changed.1).fiber?
        g.id = some changed.1 := by
      rw [← changedId]
      exact finalLook
    rw [finalLook']
    simp only [settleOutcome]
    rw [same, List.append_assoc]
    exact recorded
  · have ht : m.fiber? target = some t₁ := by
      rw [← rfiber?_update_other (m := m) (g := f) self]
      exact ht₁
    rw [ht]
    have targetId : t₁.id = target := rfiber?_id ht
    have installed : ((m.emit [.interruptRecorded (some who) target]).update g).fiber? target = some t₁ := by
      rw [rfiber?_update_other (m := m.emit _) (g := g) self]
      exact ht
    let changed := interruptRecord (interpR root.program) (some who) (stackAnnotationsOf f.id) t₁
    have changedId : changed.1.id = target := (interruptRecord_id _ _ _ _).trans targetId
    have recorded := configTyped_interruptRecord
      (configTyped_emit after [.interruptRecorded (some who) target]) installed
      (some who) (stackAnnotationsOf f.id)
    have ownerLook : (((m.emit [.interruptRecorded (some who) target]).update g).update changed.1).fiber?
        g.id = some g := by
      rw [rfiber?_update_other (show g.id ≠ changed.1.id from fun same => self (changedId.symm.trans same.symm))]
      exact lookG
    have same := rupdate_self ownerLook recorded.machine.wide.fiberIds
    refine ⟨w, leHost_refl w, ?_⟩
    simp only [prepareIterR, settle, applyFiberEdits, List.foldl_cons, List.foldl_nil,
      applyFiberEdit, List.nil_append]
    rw [installed]
    dsimp only
    have delta : interruptWithCause
        (interruptCause (interpRAt root.program m.completedExits) (some who)
          ((interpRAt root.program m.completedExits).stackAnnotations g.id) t₁.id) t₁ = changed := rfl
    rw [delta]
    rw [ownerLook]
    simp only [settleOutcome]
    rw [same, List.append_assoc]
    exact recorded

/-! ## `cancelRace`: the race's entrants interrupted through the queue -/

/-- **`cancelRace`** (`Machine/Fibers.lean`'s `cancelRace`, D6a): the answer frame saved; an unknown
race answers `unit` inline; a known race queues `raceCancel` for this host, whose reply contract
reads every live entrant's declaration (`RacePayload.live`, finding F-LIVE) and a `unit` reply over
the saved stack. -/
theorem clause_cancelRace (root : ProgramSource) (rootTy : EffTy) (raceId : Nat) :
    FiberClauseKeeps root rootTy (.cancelRace raceId) := by
  intro w m rest f y next ev hc
  obtain ⟨ty, declared⟩ := ev.declared
  obtain ⟨row, ⟨q, b⟩, flag, covered, bit, current, stack, prov⟩ := ev.code (by rw [hc]; rfl) ty declared
  change b = f.frame.interruptible at bit
  subst bit
  change AmbientProg root w row q f.frame.current at current
  rw [hc] at current
  obtain ⟨_, _, typedNext, entry, wf⟩ := ambientProg_fiber_inv current (fun _ h => nomatch h)
    (fun _ h => nomatch h) (fun _ h => nomatch h) (fun _ _ _ h => nomatch h)
  have hstack : MHostStack root w (m.update f) f.id
      ((((⟨.unit, .never, Env.Requirement.empty⟩ : EffTy), row, row) : AmbientPosition),
        f.frame.interruptible) (finalPos ty flag) (.answer (seqR next) :: f.frame.stack) :=
    .cons (.inl (Evaluating.unitAnswerFrame (fun w' o ans post => typedNext w' o ans post) entry wf))
      stack
  have same : ∀ ty', w.Γ f.id = some ty' → ty' = ty :=
    fun _ h => Option.some.inj (h.symm.trans declared)
  show SettlesTyped root rootTy w f.id rest
    (prepareIterR (FiberAction.cancelRace _ m (saveAnswerR f (seqR next)) y raceId))
  unfold FiberAction.cancelRace
  cases hr : m.race? raceId with
  | none =>
    refine ev.settle_continue { f.frame with
      current := .pure (.success Val.unit), stack := .answer (seqR next) :: f.frame.stack }
      (fun ty' d => ?_)
    rw [same ty' d]
    exact ⟨row, ((((⟨.unit, .never, Env.Requirement.empty⟩ : EffTy), row, row) : AmbientPosition),
      f.frame.interruptible), flag, covered, rfl,
      .pure (ambientExit_const (strongExit_success w _ _ trivial)) ⟨Row.subset_refl _, Row.subset_refl _⟩,
      hstack, ⟨prov.recorded, prov.deferred⟩⟩
  | some race =>
    let fr' : RSaved := { f.frame with stack := .answer (seqR next) :: f.frame.stack }
    let g : RFiber := { f with frame := fr' }
    have hmem : f ∈ (m.update f).fibers := rfiber?_mem ev.look
    have old := ev.typed.machine.fiber hmem
    have notParked : f.parked = .notParked := by
      cases hp : f.parked with
      | notParked => rfl
      | withGuard _ =>
        have idle := old.parkedIdle (by rw [hp]; exact fun h => nomatch h)
        rw [ev.running] at idle
        cases idle
    have fresh : FiberTyped root w ((m.update f).update g) g :=
      fiberTyped_frame old ev.look ev.running fr'
        (fun ty' d => by
          rw [same ty' d]
          exact ⟨_, flag, MPositionStack.of_host hstack⟩)
        ⟨prov.recorded, prov.deferred⟩
        (fun _ h => by
          change raceRegistrationR f.frame.current = some _ at h
          rw [hc, raceRegistrationR_ambient current] at h
          cases h)
    have edited : ConfigTyped root rootTy w (m.update g) rest := by
      rw [← rupdate_rupdate m (show g.id = f.id from rfl)]
      exact configTyped_frame_edit ev.typed rfl ev.look ev.running fr' fresh
    obtain ⟨f0, hf0, _⟩ := ev.stale
    have lookG : (m.update g).fiber? f.id = some g :=
      rfiber?_update_self (f := f0) (g := g) (by rw [rfiber?_id hf0]; exact hf0) (rfiber?_id hf0).symm
    have wide := ev.typed.machine.wide
    obtain ⟨resultTy, payload⟩ := wide.races race
      (List.mem_of_find?_eq_some (show (m.update f).races.find? _ = some race from hr))
    refine ⟨w, leHost_refl w, ?_⟩
    show ConfigTyped root rootTy w (m.update g) (.raceCancel raceId f.id y race.state.live [] :: rest)
    refine configTyped_cons_plain edited _ trivial ⟨g, lookG, ev.running, notParked⟩ ?_ ?_ trivial
      rfl (fun _ _ _ h => nomatch h) (fun _ _ h => nomatch h) (fun _ _ _ h => nomatch h)
      (fun _ _ _ _ _ h => nomatch h) (fun _ _ h => nomatch h) (fun _ _ h => nomatch h)
    · intro x hx
      rw [lookG] at hx
      cases hx
      refine ⟨resultTy.answer, resultTy.error, fun id hid => ?_, row, ty, flag, declared, covered,
        hstack.races (racesKept_of_eq (m := m.update f) (m' := m.update g) fun _ => rfl),
        ⟨prov.recorded, prov.deferred⟩⟩
      exact payload.live id (by simpa only [List.nil_append] using hid)
    · intro o ho
      cases ho
      rw [commandOwner_update]
      exact owner_free ev.typed.queue rfl

end Effect4.Program.Typed
