import Effect4.Laws.Program.Typed.Commands.Evaluate

/-!
# Laws.Program.Typed.Commands.Clauses.Park — the park/await clauses (M6)

Concept 4 (the configuration invariant `I`); questions `M6Ledger.step_deliver` and
`M6Ledger.step_loop`, through `evaluate_keeps` and `loop_preserves_of_clauses`, which read
`∀ op, FiberClauseKeeps root rootTy op`. A fiber that parks takes the machine's next token
(`m.nextToken`, the counter then bumped) and the world declares it (`World.addToken`): the token
transport (`configTyped_token`) moves the whole configuration to that world, and the park edit then
installs the parked fiber at its declared token.

Not established here: progress, that a parked fiber is ever resumed, the clauses outside this file.
-/

set_option autoImplicit false
namespace Effect4.Program.Typed
open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Sched Effect4.Program.Denote
open Effect4.Laws.Effects Contracts

/-! ## A fresh token declared -/

section Token
variable {w : World} {n : FiberId} {tok : Nat} {ty : EffTy}

theorem addToken_Θ_self : (w.addToken n tok ty).Θ n tok = some ty := by
  show (if n = n then tableInsert (w.Θ n) tok ty else w.Θ n) tok = some ty
  rw [if_pos rfl]
  unfold tableInsert
  rw [if_pos rfl]

theorem addToken_Θ_other {id : FiberId} {t : Nat} (ne : (id, t) ≠ (n, tok)) :
    (w.addToken n tok ty).Θ id t = w.Θ id t := by
  show (if id = n then tableInsert (w.Θ id) tok ty else w.Θ id) t = w.Θ id t
  by_cases hid : id = n
  · rw [if_pos hid]
    unfold tableInsert
    rw [if_neg (fun ht => ne (by rw [hid, ht]))]
  · rw [if_neg hid]

theorem addToken_leHost (fresh : w.Θ n tok = none) : w.leHost (w.addToken n tok ty) :=
  ⟨(park_extension w n tok ty fresh).1, fun _ _ h => h⟩

end Token

/-! ## The clauses at a world whose token table grew at one key

Every clause reads the token table positively (a declaration exists) except three: a resume's code
(`ResumeOk`, at a queued `resume` and a dispatcher task) and the due list's completions. Each of those
reads sits at an internal or queued key, below the counter, so never at the fresh key. -/

section World
variable {w w' : World} (ord : w.leHost w') (hΓ : w'.Γ = w.Γ) {key : FiberId × Nat}
  (back : ∀ id t ty, w'.Θ id t = some ty → (id, t) ≠ key → w.Θ id t = some ty)

include ord in
theorem theta_of {id : FiberId} {t : Nat} {ty : EffTy} (h : w.Θ id t = some ty) :
    w'.Θ id t = some ty :=
  ord.1.2.2.2.2.2.1 id t ty h

include ord in
theorem theta_isSome {id : FiberId} {t : Nat} (h : (w.Θ id t).isSome = true) :
    (w'.Θ id t).isSome = true := by
  obtain ⟨ty, hty⟩ := Option.isSome_iff_exists.mp h
  rw [theta_of ord hty]
  rfl

include ord in
theorem racePayload_tok {root : ProgramSource} {race : RRace} {ty : EffTy}
    (h : RacePayload root w race ty) : RacePayload root w' race ty := by
  refine ⟨theta_of ord h.token, strongExit_mono _ _ _ _ ord h.failures,
    fun pair hp => fits_mono ord (h.winner pair hp),
    fun ex hx => strongExit_mono _ _ _ _ ord (h.accepted ex hx),
    fun wait hw => strongExit_mono _ _ _ _ ord (h.cleanup wait hw),
    fun id hid => by
      obtain ⟨t, declared, ha, he⟩ := h.live id hid
      exact ⟨t, ord.1.2.1 _ _ declared, ha, he⟩,
    fun code hc => ?_⟩
  obtain ⟨cty, typed, ha, he⟩ := h.programs code hc
  exact ⟨cty, typedProg_mono root w w' cty code ord typed, ha, he⟩

include ord in
theorem countdownAt_tok {m : RState} {waiter : FiberId} {token : Nat}
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
      refine ⟨answer, error, tokenTy, ⟨theta_of ord payload.token,
        fun ex hx => strongExit_mono _ _ _ _ ord (payload.collected ex hx),
        fun id hid target ht => fiberColumnsBelow_ext (fun _ _ d => ord.1.2.1 _ _ d)
          (payload.targets id hid target ht), ?_⟩, hin answer error incomingOk⟩
      have resume := payload.resume
      split at resume
      · exact resume
      · exact resume
      · exact strongExit_mono _ _ _ _ ord resume
      · exact strongExit_mono _ _ _ _ ord resume

include ord in
theorem storedObserverOk_tok {root : ProgramSource} {m : RState} {source : FiberId} (o : Observer)
    (h : StoredObserverOk root w m source o) : StoredObserverOk root w' m source o := by
  cases o with
  | resumeAwait waiter token mode =>
    obtain ⟨sourceTy, declared, token'⟩ := h
    exact ⟨sourceTy, ord.1.2.1 _ _ declared, theta_of ord token'⟩
  | countdown waiter token =>
    exact countdownAt_tok ord (fun _ _ hc => fiberColumnsBelow_ext (fun _ _ d => ord.1.2.1 _ _ d) hc) h
  | raceCallback raceId =>
    unfold StoredObserverOk at h ⊢
    dsimp only at h ⊢
    split at h
    · trivial
    · obtain ⟨resultTy, payload, live⟩ := h
      exact ⟨resultTy, racePayload_tok ord payload,
        fun hl => fiberColumnsBelow_ext (fun _ _ d => ord.1.2.1 _ _ d) (live hl)⟩
  | dropScopeFinalizer scope k => exact h
  | untrackChild parent => trivial
  | callback k => trivial

include ord in
theorem observerCommandOk_tok {root : ProgramSource} {m : RState} {source : FiberId}
    {exit : ExitV} (o : Observer) (h : ObserverCommandOk root w m source exit o) :
    ObserverCommandOk root w' m source exit o := by
  cases o with
  | resumeAwait waiter token mode =>
    obtain ⟨sourceTy, declared, token', typed⟩ := h
    exact ⟨sourceTy, ord.1.2.1 _ _ declared, theta_of ord token', strongExit_mono _ _ _ _ ord typed⟩
  | countdown waiter token =>
    exact countdownAt_tok ord (fun _ _ hc => strongExit_mono _ _ _ _ ord hc) h
  | raceCallback raceId =>
    unfold ObserverCommandOk at h ⊢
    dsimp only at h ⊢
    split at h
    · trivial
    · obtain ⟨resultTy, payload, live⟩ := h
      exact ⟨resultTy, racePayload_tok ord payload, fun hl => strongExit_mono _ _ _ _ ord (live hl)⟩
  | dropScopeFinalizer scope k => exact h
  | untrackChild parent => trivial
  | callback k => trivial

include ord in
theorem enrollRaceOk_tok {root : ProgramSource} {m : RState} {raceId : Nat} {child : FiberId}
    (h : EnrollRaceOk root w m raceId child) : EnrollRaceOk root w' m raceId child := by
  unfold EnrollRaceOk at h ⊢
  obtain ⟨below, h⟩ := h
  refine ⟨below, ?_⟩
  split at h
  · obtain ⟨resultTy, payload, cols⟩ := h
    exact ⟨resultTy, racePayload_tok ord payload,
      fiberColumnsBelow_ext (fun _ _ d => ord.1.2.1 _ _ d) cols⟩
  · trivial

include ord back in
theorem resumeOk_tok {root : ProgramSource} {target : FiberId} {token : Nat} {code : RProgram}
    (off : (target, token) ≠ key) (h : Contracts.ResumeOk (TypedProg root) w target token code) :
    Contracts.ResumeOk (TypedProg root) w' target token code := by
  intro ty declared
  exact typedProg_mono root w w' ty code ord (h ty (back _ _ _ declared off))

include ord hΓ back in
theorem rcmdOk_tok {root : ProgramSource} (c : RCmd) (off : ∀ k ∈ Guard.commandKeys c, k ≠ key)
    (h : RCmdOk (preds root) w c) : RCmdOk (preds root) w' c := by
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
  | resume target token code => exact resumeOk_tok ord back (off _ (List.mem_singleton_self _)) h
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

include ord hΓ back in
theorem queueOk_tok {root : ProgramSource} {m : RState} {q : List RCmd} (queue : QueueOk root w m q)
    (off : ∀ k ∈ q.flatMap Guard.commandKeys, k ≠ key) : QueueOk root w' m q :=
  ⟨fun c hc => rcmdOk_tok ord hΓ back c
      (fun k hk => off k (List.mem_flatMap.mpr ⟨c, hc, hk⟩)) (queue.payload c hc),
    queue.authority,
    fun c hc => commandDelivery_mono ord (fun _ _ h => by rw [hΓ]; exact h)
      (racesKept_of_eq fun _ => rfl) (fun _ _ => rfl) (queue.delivery c hc), queue.owners,
    queue.registration, queue.keys,
    fun s e o ho => ⟨(queue.observer s e o ho).1,
      observerCommandOk_tok ord o (queue.observer s e o ho).2⟩,
    fun r c hc => enrollRaceOk_tok ord (queue.enroll r c hc),
    queue.noRaceAfterInterrupt, queue.links, queue.raceObservers⟩

include ord hΓ back in
theorem runFiberOk_tok {root : ProgramSource} {f : RFiber} (off : ∀ k ∈ Guard.fiberKeys f, k ≠ key)
    (h : RunFiberOk (preds root) w Expect.root f) : RunFiberOk (preds root) w' Expect.root f := by
  obtain ⟨⟨c0⟩, c1, c2, c3, ⟨c4⟩, c5⟩ := h
  refine ⟨⟨fun ty declared => ?_⟩, fun p hp => ?_, fun v hv ty declared => ?_,
    fun v hv ty declared => ?_, ⟨fun b hb => ⟨fun t ht => ?_⟩⟩, servicesFit_mono ord c5⟩
  · change w'.Γ f.id = some ty at declared
    rw [hΓ] at declared
    obtain ⟨tin, stack, provenance⟩ := c0 ty declared
    exact ⟨tin, positionStack_mono ord stack, provenance⟩
  · obtain ⟨id, isSome⟩ := c1 p hp
    exact ⟨id, theta_isSome ord isSome⟩
  · change w'.Γ f.id = some ty at declared
    rw [hΓ] at declared
    exact strongExit_mono _ _ _ _ ord (c2 v hv ty declared)
  · change w'.Γ f.id = some ty at declared
    rw [hΓ] at declared
    exact strongExit_mono _ _ _ _ ord (c3 v hv ty declared)
  · have task := (c4 b hb).c0 t ht
    cases t with
    | resume target token code =>
      refine resumeOk_tok ord back (off _ ?_) task
      exact List.mem_append_right _ (List.mem_flatMap.mpr ⟨b, hb,
        List.mem_flatMap.mpr ⟨_, ht, List.mem_singleton_self _⟩⟩)
    | start _ => trivial
    | wake _ _ => trivial

include ord hΓ back in
theorem fiberTyped_tok {root : ProgramSource} {m : RState} {x : RFiber}
    (off : ∀ k ∈ Guard.fiberKeys x, k ≠ key) (h : FiberTyped root w m x) : FiberTyped root w' m x := by
  refine ⟨runFiberOk_tok ord hΓ back off h.ok, fun token hp => ?_, h.below, h.pendingShape,
    h.parkedIdle, h.parkedBelow, h.exited, h.exitedStack, h.deferredCause,
    fun p hp => theta_isSome ord (h.pendingOwner p hp),
    fun o ho => storedObserverOk_tok ord o (h.observers o ho), fun raceId marker => ?_,
    fun hx hr hm ty declared => ?_, fun token hp => theta_isSome ord (h.tokens token hp),
    h.raceObservers, h.targetsBelow, h.observersBelow, fun c hc => by rw [hΓ]; exact h.children c hc⟩
  · obtain ⟨tin, final, declared, final', stack, provenance⟩ := h.delivery token hp
    exact ⟨tin, final, theta_of ord declared, by rw [hΓ]; exact final', hostStack_mono ord stack,
      provenance⟩
  · obtain ⟨race, resultTy, found, host, token, reply⟩ := h.registration raceId marker
    exact ⟨race, resultTy, found, host, theta_of ord token, stackReply_world ord hΓ reply⟩
  · rw [hΓ] at declared
    exact codeOk_mono ord (h.code hx hr hm ty declared)

include ord back in
theorem storesOk_tok {root : ProgramSource} (hΡ : w'.Ρ = w.Ρ) (hPi : w'.«Π» = w.«Π») {e : Expect}
    {s : Stores} (off : ∀ o ∈ s.deferreds.due, (o.waiter, o.token) ≠ key)
    (h : StoresOk (preds root) w e s) : StoresOk (preds root) w' e s := by
  obtain ⟨c0, c1, ⟨c2⟩, ⟨c3⟩, c4, c5⟩ := h
  refine ⟨⟨fun o ho ty declared => ?_, MemoTableTyped.mono ord (PromiseTableOk.memo c0)⟩,
    fun i v hv ty declared => ?_,
    ⟨fun i cell hc a e' declared c hcomp => ?_⟩, ⟨fun entry he => ?_⟩, fun mm hm => ?_, c5⟩
  · exact completionStrong_mono ord (PromiseTableOk.due c0 o ho ty (back _ _ _ declared (off o ho)))
  · rw [hΡ] at declared
    exact fits_mono ord (c1 i v hv ty declared)
  · rw [hPi] at declared
    exact completionStrong_mono ord (c2 i cell hc a e' declared c hcomp)
  · exact ⟨⟨scopeStateOk_world ord (c3 entry he).c0.c0⟩⟩
  · exact ⟨fun v0 hv => ⟨finNameOk_world ord ((c4 mm hm).c0 v0 hv).c0⟩⟩

end World

/-! ## The token transport -/

/-- The bumped counter keeps every lookup: the fibers, the races and the store are the old ones. -/
theorem obsView_bump (m : RState) (k : Nat) : ObsView m { m with nextToken := k } :=
  ObsView.ofLookup (fun _ => rfl) (fun _ => rfl) (fun _ h => h)

/-- **A fresh token declared keeps `I`**: the counter bumped and the world declaring the old counter
at fiber `n` (declared). Every key a negative token read sits at is internal or queued, so below the
old counter (`InternalKeysBelow`, `ReservedKeysR`), never the fresh key. -/
theorem configTyped_token {root : ProgramSource} {rootTy : EffTy} {w : World} {m : RState}
    {q : List RCmd} (typed : ConfigTyped root rootTy w m q) {n : FiberId}
    (declared : (w.Γ n).isSome = true) (ty : EffTy) :
    w.leHost (w.addToken n m.nextToken ty) ∧
      ConfigTyped root rootTy (w.addToken n m.nextToken ty) { m with nextToken := m.nextToken + 1 } q := by
  have wide := typed.machine.wide
  have fresh : w.Θ n m.nextToken = none :=
    valid_nextToken_fresh rootTy w m typed.machine.typed.1 n
  have ord : w.leHost (w.addToken n m.nextToken ty) := addToken_leHost fresh
  have hΓ : (w.addToken n m.nextToken ty).Γ = w.Γ := rfl
  have back : ∀ id t ty', (w.addToken n m.nextToken ty).Θ id t = some ty' →
      (id, t) ≠ (n, m.nextToken) → w.Θ id t = some ty' := by
    intro id t ty' h ne
    rwa [addToken_Θ_other ne] at h
  have below : ∀ {id : FiberId} {t : Nat}, t < m.nextToken → (id, t) ≠ (n, m.nextToken) :=
    fun lt same => Nat.lt_irrefl _ (by injection same with _ ht; rw [ht] at lt; exact lt)
  have internal : ∀ k ∈ Guard.internalKeys m, k ≠ (n, m.nextToken) :=
    fun k hk => below (wide.keysBelow k hk)
  let m' : RState := { m with nextToken := m.nextToken + 1 }
  have view : ObsView m m' := obsView_bump m _
  have bump : m.nextToken ≤ m'.nextToken := Nat.le_succ _
  refine ⟨ord, machineTyped_of ?_ (fun x hx => fiberTyped_transport
      (fiberTyped_tok ord hΓ back (fun k hk => internal k (fiberKeys_internal hx hk))
        (typed.machine.fiber hx)) view (Nat.le_refl _) bump),
    readCode_races (m := m) rfl (racesKept_of_eq fun _ => rfl) (readCode_world ord hΓ typed.code),
    queueOk_transport (queueOk_tok ord hΓ back typed.queue
      (fun k hk => below (typed.queue.keys.below k hk))) view (Nat.le_refl _)
      (fun _ _ h => h) (fun c _ h => commandDelivery_mono (m := m) (m' := m') (leHost_refl _) (fun _ _ d => d)
        (racesKept_of_eq fun _ => rfl) (fun _ _ => rfl) h) (fun _ _ _ h => h) bump⟩
  exact
    { ids := wide.ids
      fibers := wide.fibers
      heap := wide.heap
      promises := wide.promises
      tokenBound := fun id t ty' h => by
        by_cases same : (id, t) = (n, m.nextToken)
        · injection same with _ ht
          rw [ht]
          exact Nat.lt_succ_self _
        · exact Nat.lt_succ_of_lt (wide.tokenBound id t ty' (back id t ty' h same))
      tokenTargets := fun id t ty' h => by
        by_cases same : (id, t) = (n, m.nextToken)
        · injection same with hid _
          rw [hid]
          exact declared
        · exact wide.tokenTargets id t ty' (back id t ty' h same)
      state := wide.state
      wf := wide.wf
      cells := wide.cells
      rootDeclared := wide.rootDeclared
      races := fun r hr => by
        obtain ⟨resultTy, payload⟩ := wide.races r hr
        exact ⟨resultTy, racePayload_tok ord payload⟩
      stores := storesOk_tok ord back rfl rfl
        (fun o ho => internal _ (by
          rw [internalKeys_fibers]
          exact List.mem_append_left _ (List.mem_append_left _
            (List.mem_append_right _ (List.mem_map.mpr ⟨o, ho, rfl⟩))))) wide.stores
      fiberIds := wide.fiberIds
      raceIds := wide.raceIds
      racesBelow := wide.racesBelow
      raceHosts := wide.raceHosts
      keysBelow := fun k hk => Nat.lt_succ_of_lt (wide.keysBelow k hk)
      requestsBelow := fun fiber t r h => Nat.lt_succ_of_lt (wide.requestsBelow fiber t r h)
      requestsOwned := wide.requestsOwned
      services := wide.services
      live := ⟨wide.live.running, wide.live.dueOwners⟩
      timers := WakeTyped.mono (fun id => ord.1.2.2.2.2.2.1 id) wide.timers
      waiters := fun k cell hc a e hk => WakeTyped.mono (fun id => ord.1.2.2.2.2.2.1 id)
        (wide.waiters k cell hc a e hk)
      liveBelow := wide.liveBelow
      sourceWF := wide.sourceWF }

end Effect4.Program.Typed
