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
    fun hx hr hm hp ty declared => ?_, fun token hp => theta_isSome ord (h.tokens token hp),
    h.raceObservers, h.targetsBelow, h.observersBelow, fun c hc => by rw [hΓ]; exact h.children c hc⟩
  · obtain ⟨tin, final, declared, final', stack, provenance⟩ := h.delivery token hp
    exact ⟨tin, final, theta_of ord declared, by rw [hΓ]; exact final', hostStack_mono ord stack,
      provenance⟩
  · obtain ⟨race, resultTy, found, host, token, reply⟩ := h.registration raceId marker
    exact ⟨race, resultTy, found, host, theta_of ord token, stackReply_world ord hΓ reply⟩
  · rw [hΓ] at declared
    exact codeOk_mono ord (h.code hx hr hm hp ty declared)

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

/-- A key below the counter is not the fresh key. -/
theorem key_ne_of_lt {k : FiberId × Nat} {n : FiberId} {t : Nat} (h : k.2 < t) : k ≠ (n, t) :=
  fun same => Nat.lt_irrefl t (by rw [same] at h; exact h)

/-- The bumped counter keeps every command's owner. -/
theorem commandOwner_bump (M : RState) (k : Nat) :
    Guard.commandOwner (Code := RProgram) { M with nextToken := k } = Guard.commandOwner M := by
  funext c
  cases c <;> rfl

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
    fun lt => key_ne_of_lt lt
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

/-! ## `yieldNow`: a park on the fresh token, its resume posted on the fiber's own dispatcher -/

/-- The fiber `yieldNow` leaves before `settle` (`FiberAction.yieldNow`, `Machine/Fibers.lean:1592-1602`):
the answer frame saved, `success void` current, the resume task posted, parked on the token. -/
abbrev yieldFiber (f : RFiber) (next : Val → RProgram) (token priority : Nat) : RFiber :=
  { f with
    frame := { f.frame with current := .pure (.success .unit),
                            stack := .answer (seqR next) :: f.frame.stack }
    dispatcher := f.dispatcher.enqueue priority (.resume f.id token (.pure (.success .unit)))
    parked := .withGuard token
    pending := f.pending ++ [⟨token, none, [], [], .void, false⟩] }

theorem evaluateFiberR_yieldNow (root : ProgramSource) (C : List (FiberId × ExitV)) (m : RState)
    (f : RFiber) (y : Bool) (priority : Nat) (next : Val → RProgram) :
    evaluateFiberR (interpRAt root.program C) m f y (.yieldNow priority) next =
      ⟨(({ m with nextToken := m.nextToken + 1 } : RState).arm f.id).emit
          [.parkedOn f.id m.nextToken], yieldFiber f next m.nextToken priority, y, .parked, []⟩ :=
  rfl

/-- **`yieldNow`** (`internal/effect.ts:986-992`): the fiber saves the answer frame, takes the fresh
token (declared at `unit`, `configTyped_token`), posts its own resume (`success void`, typed at the
token) and parks; a deferred interrupt clears the park and the same entry continues. -/
theorem clause_yieldNow (root : ProgramSource) (rootTy : EffTy) (priority : Nat) :
    FiberClauseKeeps root rootTy (.yieldNow priority) := by
  intro w m rest f y next ev hc
  rw [evaluateFiberR_yieldNow]
  let M0 : RState := m.update f
  let tok : Nat := m.nextToken
  let M1 : RState := { M0 with nextToken := tok + 1 }
  let w1 : World := w.addToken f.id tok (EffTy.pure .unit)
  let task : RTask := .resume f.id tok (.pure (.success .unit))
  have hmem : f ∈ M0.fibers := rfiber?_mem ev.look
  have old : FiberTyped root w M0 f := ev.typed.machine.fiber hmem
  have wide := ev.typed.machine.wide
  have notParked : f.parked = .notParked := by
    cases hp : f.parked with
    | notParked => rfl
    | withGuard _ =>
      have idle := old.parkedIdle (by rw [hp]; exact fun h => nomatch h)
      rw [ev.running] at idle
      cases idle
  have live : f.exit = none := by
    cases hx : f.exit with
    | none => rfl
    | some _ =>
      have stopped := (old.exited (by rw [hx]; rfl)).2
      rw [ev.running] at stopped
      cases stopped
  have hpend : f.pending = [] := by
    have shape := old.pendingShape
    unfold Guard.PendingShape at shape
    rw [notParked] at shape
    exact shape
  -- the code and stack at the evaluated state
  obtain ⟨ty, declared⟩ := ev.declared
  have same : ∀ ty', w.Γ f.id = some ty' → ty' = ty :=
    fun _ h => Option.some.inj (h.symm.trans declared)
  obtain ⟨tin, current, stack, prov⟩ := ev.code (by rw [hc]; rfl) ty declared
  rw [hc] at current
  obtain ⟨_, _, typedNext⟩ := TypedProg.fiber_inv current (fun _ h => nomatch h)
    (fun _ h => nomatch h) (fun _ h => nomatch h) (fun _ _ _ h => nomatch h)
  have typedNext' : ∀ w', w.leHost w' → ∀ ans : Val, ans = Val.unit →
      TypedProg root w' tin (next ans) :=
    fun w' o ans post => typedNext w' o ans post
  have hstack : HostStack root w M0 f.id (EffTy.pure .unit) ty (.answer (seqR next) :: f.frame.stack) :=
    hostStack_push (Evaluating.unitAnswerFrame typedNext') stack
  -- the token transport
  obtain ⟨ord, bumped⟩ := configTyped_token (configTyped_tail ev.typed)
    (show (w.Γ f.id).isSome = true by rw [declared]; rfl) (EffTy.pure .unit)
  have back : ∀ id t ty', w1.Θ id t = some ty' → (id, t) ≠ (f.id, tok) → w.Θ id t = some ty' :=
    fun id t ty' h ne => by rwa [addToken_Θ_other ne] at h
  have internal : ∀ k ∈ Guard.fiberKeys f, k ≠ (f.id, tok) :=
    fun k hk => key_ne_of_lt (wide.keysBelow k (fiberKeys_internal hmem hk))
  have hf1 : M1.fiber? f.id = some f := ev.look
  have freeM0 : f.id ∉ rest.filterMap (Guard.commandOwner M0) := owner_free ev.typed.queue rfl
  have free1 : f.id ∉ rest.filterMap (Guard.commandOwner M1) := by
    rw [commandOwner_bump]
    exact freeM0
  have taskOk : Contracts.ResumeOk (TypedProg root) w1 f.id tok (.pure (.success .unit)) := by
    intro ty' d
    rw [addToken_Θ_self] at d
    cases d
    exact TypedProg.pure (strongExit_success w1 _ _ trivial)
  have okF : RunFiberOk (preds root) w1 Expect.root f := runFiberOk_tok ord rfl back internal old.ok
  obtain ⟨_, _, c2, c3, ⟨c4⟩, c5⟩ := okF
  have dispatcherOk : ∀ b ∈ (f.dispatcher.enqueue priority task).buckets, ∀ t ∈ b.tasks,
      TaskOk (preds root) w1 Expect.root t := by
    intro b hb t ht
    rcases mem_insert_tasks hb ht with rfl | ⟨b', hb', ht'⟩
    · exact taskOk
    · exact (c4 b' hb').c0 t ht'
  have keysG : ∀ (g : RFiber), g.observers = f.observers →
      g.dispatcher = f.dispatcher.enqueue priority task →
      ∀ k ∈ Guard.fiberKeys g, k ∈ Guard.internalKeys M1 ∨
        (k.2 < M1.nextToken ∧ requestOfR M1 k.1 k.2 = none) := by
    intro g hobs hdisp k hk
    unfold Guard.fiberKeys at hk
    rw [hobs, hdisp] at hk
    rcases List.mem_append.mp hk with ho | hb
    · exact Or.inl (fiberKeys_internal hmem (List.mem_append_left _ ho))
    · rcases List.mem_append.mp (bucketKeys_insert hb) with hold | hnew
      · exact Or.inl (fiberKeys_internal hmem (List.mem_append_right _ hold))
      · rw [show Guard.taskKeys task = [(f.id, tok)] from rfl, List.mem_singleton] at hnew
        subst hnew
        refine Or.inr ⟨Nat.lt_succ_self _, requestOfR_of_not_parked hf1 ?_⟩
        rw [notParked]
        exact fun h => nomatch h
  show SettlesTyped root rootTy w f.id rest (prepareIterR ⟨_, yieldFiber f next tok priority, y, .parked, []⟩)
  refine ⟨w1, ord, ?_⟩
  show ConfigTyped root rootTy w1
    (settle f.id rest ⟨((({ m with nextToken := m.nextToken + 1 } : RState).arm f.id).emit
      [.parkedOn f.id m.nextToken]), yieldFiber f next tok priority, y, .parked, []⟩).1
    (settle f.id rest ⟨((({ m with nextToken := m.nextToken + 1 } : RState).arm f.id).emit
      [.parkedOn f.id m.nextToken]), yieldFiber f next tok priority, y, .parked, []⟩).2
  unfold settle
  dsimp only
  split
  · -- a deferred interrupt: the park cleared, the same entry continues (`:662-667`)
    rename_i hdef
    let g : RFiber := { yieldFiber f next tok priority with parked := .notParked, pending := [] }
    have lookG : (M1.update g).fiber? g.id = some g := rfiber?_update_self hf1 rfl
    have stackG : ∀ ty', w1.Γ g.id = some ty' →
        HostStack root w1 (M1.update g) g.id (EffTy.pure .unit) ty' g.frame.stack := by
      intro ty' d
      rw [same ty' d]
      exact hostStack_races (m := M0) (racesKept_of_eq fun _ => rfl) (hostStack_mono ord hstack)
    have pG : InterruptProvenance g.frame := ⟨prov.recorded, prov.deferred⟩
    have codeG : ∀ ty', w1.Γ g.id = some ty' → CodeOk root w1 (M1.update g) g.id ty' g.frame :=
      fun ty' d => ⟨EffTy.pure .unit, TypedProg.pure (strongExit_success w1 _ _ trivial), stackG ty' d, pG⟩
    have cleared : PendingWeaker f.pending g.pending := fun _ _ h => nomatch h
    have view : ObsView M1 (M1.update g) := obsView_rupdate hf1 rfl cleared
    have fresh : FiberTyped root w1 (M1.update g) g :=
      { ok := ⟨⟨fun ty' d => ⟨_, positionStack_of_host (stackG ty' d), pG⟩⟩,
          (fun _ hp => nomatch hp), c2, c3, ⟨fun b hb => ⟨fun t ht => dispatcherOk b hb t ht⟩⟩, c5⟩
        delivery := fun _ h => nomatch h
        below := old.below
        pendingShape := rfl
        parkedIdle := fun h => absurd rfl h
        parkedBelow := fun _ h => nomatch h
        exited := fun hx => by
          rw [show g.exit = none from live] at hx
          cases hx
        exitedStack := fun hx => by
          rw [show g.exit = none from live] at hx
          cases hx
        deferredCause := old.deferredCause
        pendingOwner := fun _ hp => nomatch hp
        observers := fun o ho => storedObserverOk_view view o
          (storedObserverOk_view (obsView_bump M0 _) o (storedObserverOk_tok ord o (old.observers o ho)))
        registration := fun _ h => nomatch h
        code := fun _ h => by
          rw [show g.running = true from ev.running] at h
          cases h
        tokens := fun _ h => nomatch h
        raceObservers := old.raceObservers
        targetsBelow := fun _ hp => nomatch hp
        observersBelow := old.observersBelow
        children := old.children }
    have noRequest : ∀ tok' r, requestOfR (M1.update g) g.id tok' = some r →
        requestOfR M1 f.id tok' = some r := by
      intro tok' r hr
      rw [requestOfR_of_not_parked lookG (fun h => nomatch h)] at hr
      cases hr
    have edited := configTyped_rupdate_owner (g := g) bumped hf1 rfl cleared free1
      (keysG g rfl rfl) noRequest
      (fun c hc h => commandAuthority_flags (g := g) hf1 rfl rfl notParked.symm rfl free1 c hc h)
      (fun _ reads => by
        obtain ⟨y', r⟩ := reads
        rcases r with r | r
        · exact (free1 (List.mem_filterMap.mpr ⟨_, r, rfl⟩)).elim
        · exact (free1 (List.mem_filterMap.mpr ⟨_, r, rfl⟩)).elim) fresh
    have freeG : g.id ∉ rest.filterMap (Guard.commandOwner (M1.update g)) := by
      rw [commandOwner_rupdate]
      exact free1
    have looped := configTyped_cons_loop edited lookG ev.running rfl freeG y (fun _ => codeG)
    have final := configTyped_emit (configTyped_congr (m := M1.update g)
      (m' := (M1.update g).arm f.id) rfl rfl rfl rfl rfl rfl rfl looped) [.parkedOn f.id m.nextToken]
    refine configTyped_congr (m := ((M1.update g).arm f.id).emit [.parkedOn f.id m.nextToken]) ?_ rfl
      rfl rfl rfl rfl rfl final
    exact (congrArg RunMachine.fibers (rupdate_rupdate m (show g.id = f.id from rfl))).symm
  · -- the park: idle on the token, the `void` record, the resume posted
    rename_i hdef
    let g : RFiber := { yieldFiber f next tok priority with running := false }
    let pend : RPending := ⟨tok, none, [], [], .void, false⟩
    have lookG : (M1.update g).fiber? g.id = some g := rfiber?_update_self hf1 rfl
    have hpOf : g.pending = [pend] := by
      show f.pending ++ [pend] = [pend]
      rw [hpend]
      rfl
    have weakOff : PendingWeakerOff tok f.pending g.pending := by
      rw [hpOf, hpend]
      exact pendingWeakerOff_single pend
    have viewOff : ObsViewOff (g.id, tok) M1 (M1.update g) := obsViewOff_rupdate (g := g) hf1 rfl weakOff
    have stackG : ∀ ty', w1.Γ g.id = some ty' →
        HostStack root w1 (M1.update g) g.id (EffTy.pure .unit) ty' g.frame.stack := by
      intro ty' d
      rw [same ty' d]
      exact hostStack_races (m := M0) (racesKept_of_eq fun _ => rfl) (hostStack_mono ord hstack)
    have pG : InterruptProvenance g.frame := ⟨prov.recorded, prov.deferred⟩
    have tokenOf : ∀ token, g.parked = .withGuard token → token = tok := by
      intro token h
      have h' : Parked.withGuard tok = .withGuard token := h
      injection h' with e
      exact e.symm
    have declaredG : w1.Θ g.id tok = some (EffTy.pure .unit) := addToken_Θ_self
    have pendOk : ∀ p ∈ g.pending, (w1.Θ g.id p.token).isSome = true := by
      intro p hp
      rw [hpOf, List.mem_singleton] at hp
      subst hp
      show (w1.Θ g.id tok).isSome = true
      rw [declaredG]
      rfl
    have fresh : FiberTyped root w1 (M1.update g) g :=
      { ok := ⟨⟨fun ty' d => ⟨_, positionStack_of_host (stackG ty' d), pG⟩⟩,
          fun p hp => ⟨g.id, pendOk p hp⟩, c2, c3,
          ⟨fun b hb => ⟨fun t ht => dispatcherOk b hb t ht⟩⟩, c5⟩
        delivery := fun token h => by
          rw [tokenOf token h]
          obtain ⟨d⟩ : ∃ _ : w1.Γ g.id = some ty, True := ⟨declared, trivial⟩
          exact ⟨EffTy.pure .unit, ty, declaredG, d, stackG ty d, pG⟩
        below := old.below
        pendingShape := by
          show ∃ p, g.pending = [p] ∧ p.token = tok
          exact ⟨pend, hpOf, rfl⟩
        parkedIdle := fun _ => rfl
        parkedBelow := fun token h => by
          rw [tokenOf token h]
          exact Nat.lt_succ_self _
        exited := fun hx => by
          rw [show g.exit = none from live] at hx
          cases hx
        exitedStack := fun hx => by
          rw [show g.exit = none from live] at hx
          cases hx
        deferredCause := old.deferredCause
        pendingOwner := pendOk
        observers := fun o ho => storedObserverOk_off viewOff o
          (fun hk => internal _ (List.mem_append_left _ (List.mem_flatMap.mpr ⟨o, ho, hk⟩)) rfl)
          (storedObserverOk_view (obsView_bump M0 _) o (storedObserverOk_tok ord o (old.observers o ho)))
        registration := fun _ h => nomatch h
        code := fun _ _ _ hp => nomatch hp
        tokens := fun token h => by
          rw [tokenOf token h, declaredG]
          rfl
        raceObservers := old.raceObservers
        targetsBelow := fun p hp id hid => by
          rw [hpOf, List.mem_singleton] at hp
          subst hp
          cases hid
        observersBelow := old.observersBelow
        children := old.children }
    have noRequest : ∀ tok' r, requestOfR (M1.update g) g.id tok' = some r →
        requestOfR M1 f.id tok' = some r := by
      intro tok' r hr
      by_cases hp : g.parked = .withGuard tok'
      · rw [requestOfR_of_parked lookG hp] at hr
        cases hr
      · rw [requestOfR_of_not_parked lookG hp] at hr
        cases hr
    have edited := configTyped_rupdate_park (g := g) bumped hf1 rfl weakOff
      (fun x hx o ho hk => internal _ (by
        have := key_ne_of_lt (n := g.id) (t := tok)
          (wide.keysBelow _ (fiberKeys_internal hx (List.mem_append_left _
            (List.mem_flatMap.mpr ⟨o, ho, hk⟩))))
        exact absurd rfl this) rfl)
      (fun s e o ho hk => key_ne_of_lt (ev.typed.queue.keys.below _
        (List.mem_flatMap.mpr ⟨.observe s e o, List.mem_cons_of_mem _ ho, hk⟩)) rfl)
      free1 (keysG g rfl rfl) noRequest
      (fun c hc h => commandAuthority_unowned (g := g) hf1 rfl live free1
        bumped.queue.registration c hc h)
      (fun h => Bool.noConfusion h) fresh
    have final := configTyped_emit (configTyped_congr (m := M1.update g)
      (m' := (M1.update g).arm f.id) rfl rfl rfl rfl rfl rfl rfl edited) [.parkedOn f.id m.nextToken]
    refine configTyped_congr (m := ((M1.update g).arm f.id).emit [.parkedOn f.id m.nextToken]) ?_ rfl
      rfl rfl rfl rfl rfl final
    exact (congrArg RunMachine.fibers (rupdate_rupdate m (show g.id = f.id from rfl))).symm

/-! ## `await`: an exited target answers at once; a live one parks -/

/-- **`await`'s park branch** (`FiberAction.join`'s live-target arm): the clause at a target the
evaluator's machine holds and that has not exited. Its proof reads `J` with the parked fiber's code
clause dropped (the owner's repair of `FiberTyped.code`, 2026-10-02). -/
def AwaitParks (root : ProgramSource) (rootTy : EffTy) (target : FiberId)
    (mode : Supervision.ObserverMode) : Prop :=
  ∀ (w : World) (m : RState) (rest : List RCmd) (f : RFiber) (y : Bool)
    (next : (FiberOp.await target mode).answer → RProgram) (t : RFiber),
    Evaluating root rootTy w m rest f y → f.frame.current = .vis (.inr (.await target mode)) next →
    m.fiber? target = some t → t.exit = none →
    SettlesTyped root rootTy w f.id rest
      (prepareIterR (evaluateFiberR (interpRAt root.program m.completedExits) m f y
        (.await target mode) next))

/-- The target the evaluator's machine finds is a fiber of the configuration, and an exited one is
not the running fiber: its exit is typed at its declaration. -/
theorem Evaluating.target_exit {root : ProgramSource} {rootTy : EffTy} {w : World} {m : RState}
    {rest : List RCmd} {f : RFiber} {y : Bool} (ev : Evaluating root rootTy w m rest f y)
    {target : FiberId} {t : RFiber} (ht : m.fiber? target = some t) {exit : ExitV}
    (hx : t.exit = some exit) : ∀ ty, w.Γ target = some ty → ExitOk w ty exit := by
  obtain ⟨f0, hf0, exit0⟩ := ev.stale
  have hmem : f ∈ (m.update f).fibers := rfiber?_mem ev.look
  have live : f.exit = none := by
    cases hfx : f.exit with
    | none => rfl
    | some _ =>
      have stopped := ((ev.typed.machine.fiber hmem).exited (by rw [hfx]; rfl)).2
      rw [ev.running] at stopped
      cases stopped
  have other : target ≠ f.id := by
    intro same
    rw [same, hf0] at ht
    cases ht
    rw [exit0, live] at hx
    cases hx
  have ht' : (m.update f).fiber? target = some t := by
    rw [rfiber?_update_other other]
    exact ht
  have tid : t.id = target := rfiber?_id ht
  intro ty declared
  exact (ev.typed.machine.fiber (rfiber?_mem ht')).ok.c3 exit hx ty (by rw [tid]; exact declared)

/-- The target the pre declares is a fiber of the evaluator's machine. -/
theorem Evaluating.target_found {root : ProgramSource} {rootTy : EffTy} {w : World} {m : RState}
    {rest : List RCmd} {f : RFiber} {y : Bool} (ev : Evaluating root rootTy w m rest f y)
    {target : FiberId} (pre : (w.Γ target).isSome = true) : ∃ t, m.fiber? target = some t := by
  have wide := ev.typed.machine.wide
  have mem : target ∈ m.fibers.map RunFiber.id := by
    rw [← rupdate_ids m f]
    exact (wide.fibers target).mp pre
  have nodup : (m.fibers.map RunFiber.id).Nodup := by
    rw [← rupdate_ids m f]
    exact wide.fiberIds
  obtain ⟨x, hx, hid⟩ := List.mem_map.mp mem
  exact ⟨x, by rw [← hid]; exact rfiber?_of_mem nodup hx⟩

/-- **`await`** (`internal/effect.ts:5291`, `:5304`): the target, declared by the pre, is a fiber of
the machine (no `unknownFiber` halt); an exited target's exit, typed at its declaration, answers at
once over the saved answer frame (by effect, or encoded as a value); a live target parks
(`AwaitParks`). -/
theorem clause_await_of_parks (root : ProgramSource) (rootTy : EffTy) (target : FiberId)
    (mode : Supervision.ObserverMode) (parks : AwaitParks root rootTy target mode) :
    FiberClauseKeeps root rootTy (.await target mode) := by
  intro w m rest f y next ev hc
  obtain ⟨ty, declared⟩ := ev.declared
  obtain ⟨tin, current, stack, prov⟩ := ev.code (by rw [hc]; rfl) ty declared
  rw [hc] at current
  obtain ⟨cert, pre, typedNext⟩ := TypedProg.fiber_inv current (fun _ h => nomatch h)
    (fun _ h => nomatch h) (fun _ h => nomatch h) (fun _ _ _ h => nomatch h)
  obtain ⟨t, ht⟩ := ev.target_found pre
  cases hx : t.exit with
  | none => exact parks w m rest f y next t ev hc ht hx
  | some exit =>
    obtain ⟨sourceTy, hsrc⟩ := Option.isSome_iff_exists.mp pre
    have exitOk : ExitOk w sourceTy exit := ev.target_exit ht hx sourceTy hsrc
    have same : ∀ ty', w.Γ f.id = some ty' → ty' = ty :=
      fun _ h => Option.some.inj (h.symm.trans declared)
    cases mode with
    | joinEffect =>
      show SettlesTyped root rootTy w f.id rest (prepareIterR
        (FiberAction.join (interpRAt root.program m.completedExits) m (saveAnswerR f next) y target
          .joinEffect))
      simp only [FiberAction.join, ht, hx]
      refine ev.settle_continue { f.frame with
        current := .pure exit, stack := .answer next :: f.frame.stack } (fun ty' d => ?_)
      rw [same ty' d]
      exact ⟨sourceTy, TypedProg.pure exitOk,
        hostStack_push (answerFrame_typed
          (post := fun w' ans => fiberPost w' (.await target .joinEffect) cert ans)
          (fun w' o ex hex => ⟨sourceTy, o.1.2.1 _ _ hsrc, hex⟩) typedNext) stack,
        ⟨prov.recorded, prov.deferred⟩⟩
    | awaitValue =>
      show SettlesTyped root rootTy w f.id rest (prepareIterR
        (FiberAction.join (interpRAt root.program m.completedExits) m (saveAnswerR f (seqR next)) y
          target .awaitValue))
      simp only [FiberAction.join, ht, hx]
      refine ev.settle_continue { f.frame with
        current := .pure (.success (reifyExitVal exit)), stack := .answer (seqR next) :: f.frame.stack }
        (fun ty' d => ?_)
      rw [same ty' d]
      exact ⟨EffTy.pure (.exitOf sourceTy.answer sourceTy.error), TypedProg.pure ⟨exitOk.1, trivial⟩,
        hostStack_push (seqFrame_typed
          (post := fun w' ans => fiberPost w' (.await target .awaitValue) cert ans) rfl
          (fun w' o v hv => ⟨sourceTy, o.1.2.1 _ _ hsrc, hv⟩) typedNext) stack,
        ⟨prov.recorded, prov.deferred⟩⟩

/-! ## The countdown parks: no live target answers at once -/

/-- **A continue after a consumed token settles typed** (`countdownPark` takes the token before its
walk): the counter bumped, the world declaring the unused token (`configTyped_token`). -/
theorem Evaluating.settle_continue_bump {root : ProgramSource} {rootTy : EffTy} {w : World}
    {m : RState} {rest : List RCmd} {f : RFiber} {y y' : Bool}
    (ev : Evaluating root rootTy w m rest f y) (fr : RSaved)
    (code : ∀ ty, w.Γ f.id = some ty → CodeOk root w (m.update f) f.id ty fr) :
    SettlesTyped root rootTy w f.id rest
      (prepareIterR ⟨{ m with nextToken := m.nextToken + 1 }, { f with frame := fr }, y', .continue_, []⟩) := by
  obtain ⟨ty, declared⟩ := ev.declared
  obtain ⟨ord, bumped⟩ := configTyped_token ev.typed
    (show (w.Γ f.id).isSome = true by rw [declared]; rfl) (EffTy.pure .unit)
  have ev' : Evaluating root rootTy (w.addToken f.id m.nextToken (EffTy.pure .unit))
      { m with nextToken := m.nextToken + 1 } rest f y := ⟨bumped, ev.stale, ev.running, ev.live⟩
  exact SettlesTyped.mono ord (ev'.settle_continue fr (fun ty' d => codeOk_races (m := m.update f)
    (racesKept_of_eq fun _ => rfl) (codeOk_mono ord (code ty' d))))

/-- **A countdown's park branch**: the clause where the walk over the operation's targets (after the
token is taken) meets a live target. Its proof reads `J` with the parked fiber's code clause dropped
(the owner's repair of `FiberTyped.code`, 2026-10-02). -/
def CountdownParks (root : ProgramSource) (rootTy : EffTy) (op : FiberOp)
    (targetsOf : RFiber → List FiberId) : Prop :=
  ∀ (w : World) (m : RState) (rest : List RCmd) (f : RFiber) (y : Bool) (next : op.answer → RProgram)
    (exits : List ExitV) (target : FiberId) (remaining : List FiberId),
    Evaluating root rootTy w m rest f y → f.frame.current = .vis (.inr op) next →
    countdownWalk ({ m with nextToken := m.nextToken + 1 } : RState) (targetsOf f) [] =
      (exits, some (target, remaining)) →
    SettlesTyped root rootTy w f.id rest
      (prepareIterR (evaluateFiberR (interpRAt root.program m.completedExits) m f y op next))

/-- The exits a walk collects are exited targets' exits, typed at the columns every target's
declaration is below. -/
theorem Evaluating.walk_exits {root : ProgramSource} {rootTy : EffTy} {w : World} {m : RState}
    {rest : List RCmd} {f : RFiber} {y : Bool} (ev : Evaluating root rootTy w m rest f y)
    {targets : List FiberId} {a e : Ty}
    (cols : ∀ t ∈ targets, ∃ fty, w.Γ t = some fty ∧ fty.answer.sub a = true ∧ fty.error.sub e = true)
    {k : Nat} : ∀ ex ∈ (countdownWalk ({ m with nextToken := k } : RState) targets []).1,
      FitsExit w ⟨a, e, Env.Requirement.empty⟩ ex := by
  intro ex hex
  obtain ⟨⟨extra, hextra, found⟩, _⟩ := countdownWalk_spec ({ m with nextToken := k } : RState) targets []
  rw [hextra, List.nil_append] at hex
  obtain ⟨t, ht, g, hg, gx⟩ := found ex hex
  obtain ⟨fty, d, ha, he⟩ := cols t ht
  exact fitsExit_sub ha he (ev.target_exit (t := g) hg gx fty d).1

/-- **`awaitAll`** (`fiberAwaitAll`, `internal/effect.ts:779-813`): the token taken, a walk with no
live target answers the collected exits, typed at the certificate's list of exits (the pre's
columns), over the saved answer frame; a live target parks (`CountdownParks`). -/
theorem clause_awaitAll_of_parks (root : ProgramSource) (rootTy : EffTy) (targets : List FiberId)
    (parks : CountdownParks root rootTy (.awaitAll targets) fun _ => targets) :
    FiberClauseKeeps root rootTy (.awaitAll targets) := by
  intro w m rest f y next ev hc
  cases hw : countdownWalk ({ m with nextToken := m.nextToken + 1 } : RState) targets [] with
  | mk exits live =>
    cases live with
    | some p => exact parks w m rest f y next exits p.1 p.2 ev hc hw
    | none =>
      obtain ⟨ty, declared⟩ := ev.declared
      obtain ⟨tin, current, stack, prov⟩ := ev.code (by rw [hc]; rfl) ty declared
      rw [hc] at current
      obtain ⟨cert, ⟨a, e, hcert, cols⟩, typedNext⟩ := TypedProg.fiber_inv current
        (fun _ h => nomatch h) (fun _ h => nomatch h) (fun _ h => nomatch h) (fun _ _ _ h => nomatch h)
      have typedExits := ev.walk_exits cols (k := m.nextToken + 1)
      rw [hw] at typedExits
      have value : Fits w (exitsVal exits) cert := by
        rw [hcert]
        exact awaitAll_delivered (targets := targets) typedExits
      have same : ∀ ty', w.Γ f.id = some ty' → ty' = ty :=
        fun _ h => Option.some.inj (h.symm.trans declared)
      show SettlesTyped root rootTy w f.id rest (prepareIterR
        (FiberAction.awaitAll (interpRAt root.program m.completedExits) m (saveAnswerR f (seqR next)) y
          targets false))
      have hout : FiberAction.outcomeOf ({ m with nextToken := m.nextToken + 1 } : RState) false =
          .continue_ := by
        simp only [FiberAction.outcomeOf, ev.live]
        rfl
      simp only [FiberAction.awaitAll, countdownPark, hw, hout]
      refine ev.settle_continue_bump { f.frame with
        current := .pure (.success (exitsVal exits)), stack := .answer (seqR next) :: f.frame.stack }
        (fun ty' d => ?_)
      rw [same ty' d]
      exact ⟨EffTy.pure cert, TypedProg.pure ⟨value, trivial⟩,
        hostStack_push (seqFrame_typed
          (post := fun w' ans => fiberPost w' (.awaitAll targets) cert ans) rfl
          (fun _ _ _ hv => hv) typedNext) stack, ⟨prov.recorded, prov.deferred⟩⟩

/-- **`awaitAllFailFast`** (`Effect.all` with concurrency, S5 §7.4): `awaitAll`'s clause; fail-fast
changes only what a later failing exit does to the remaining targets. -/
theorem clause_awaitAllFailFast_of_parks (root : ProgramSource) (rootTy : EffTy)
    (targets : List FiberId)
    (parks : CountdownParks root rootTy (.awaitAllFailFast targets) fun _ => targets) :
    FiberClauseKeeps root rootTy (.awaitAllFailFast targets) := by
  intro w m rest f y next ev hc
  cases hw : countdownWalk ({ m with nextToken := m.nextToken + 1 } : RState) targets [] with
  | mk exits live =>
    cases live with
    | some p => exact parks w m rest f y next exits p.1 p.2 ev hc hw
    | none =>
      obtain ⟨ty, declared⟩ := ev.declared
      obtain ⟨tin, current, stack, prov⟩ := ev.code (by rw [hc]; rfl) ty declared
      rw [hc] at current
      obtain ⟨cert, ⟨a, e, hcert, cols⟩, typedNext⟩ := TypedProg.fiber_inv current
        (fun _ h => nomatch h) (fun _ h => nomatch h) (fun _ h => nomatch h) (fun _ _ _ h => nomatch h)
      have typedExits := ev.walk_exits cols (k := m.nextToken + 1)
      rw [hw] at typedExits
      have value : Fits w (exitsVal exits) cert := by
        rw [hcert]
        exact awaitAll_delivered (targets := targets) typedExits
      have same : ∀ ty', w.Γ f.id = some ty' → ty' = ty :=
        fun _ h => Option.some.inj (h.symm.trans declared)
      show SettlesTyped root rootTy w f.id rest (prepareIterR
        (FiberAction.awaitAll (interpRAt root.program m.completedExits) m (saveAnswerR f (seqR next)) y
          targets true))
      have hout : FiberAction.outcomeOf ({ m with nextToken := m.nextToken + 1 } : RState) false =
          .continue_ := by
        simp only [FiberAction.outcomeOf, ev.live]
        rfl
      simp only [FiberAction.awaitAll, countdownPark, hw, hout]
      refine ev.settle_continue_bump { f.frame with
        current := .pure (.success (exitsVal exits)), stack := .answer (seqR next) :: f.frame.stack }
        (fun ty' d => ?_)
      rw [same ty' d]
      exact ⟨EffTy.pure cert, TypedProg.pure ⟨value, trivial⟩,
        hostStack_push (seqFrame_typed
          (post := fun w' ans => fiberPost w' (.awaitAllFailFast targets) cert ans) rfl
          (fun _ _ _ hv => hv) typedNext) stack, ⟨prov.recorded, prov.deferred⟩⟩

/-- **`awaitNewChildren`** (`awaitAllChildren`'s count-down over the children not in the snapshot):
the token taken, a walk with no live child answers `void` over the saved answer frame; a live child
parks (`CountdownParks`). -/
theorem clause_awaitNewChildren_of_parks (root : ProgramSource) (rootTy : EffTy)
    (snapshot : List FiberId)
    (parks : CountdownParks root rootTy (.awaitNewChildren snapshot)
      fun f => f.children.filter fun c => !(snapshot.contains c)) :
    FiberClauseKeeps root rootTy (.awaitNewChildren snapshot) := by
  intro w m rest f y next ev hc
  cases hw : countdownWalk ({ m with nextToken := m.nextToken + 1 } : RState)
      ((saveAnswerR f (seqR next)).children.filter fun c => !(snapshot.contains c)) [] with
  | mk exits live =>
    cases live with
    | some p => exact parks w m rest f y next exits p.1 p.2 ev hc hw
    | none =>
      obtain ⟨ty, declared⟩ := ev.declared
      obtain ⟨tin, current, stack, prov⟩ := ev.code (by rw [hc]; rfl) ty declared
      rw [hc] at current
      obtain ⟨_, _, typedNext⟩ := TypedProg.fiber_inv current
        (fun _ h => nomatch h) (fun _ h => nomatch h) (fun _ h => nomatch h) (fun _ _ _ h => nomatch h)
      have typedNext' : ∀ w', w.leHost w' → ∀ ans : Val, ans = Val.unit →
          TypedProg root w' tin (next ans) :=
        fun w' o ans post => typedNext w' o ans post
      have same : ∀ ty', w.Γ f.id = some ty' → ty' = ty :=
        fun _ h => Option.some.inj (h.symm.trans declared)
      show SettlesTyped root rootTy w f.id rest (prepareIterR
        (FiberAction.awaitNewChildren (interpRAt root.program m.completedExits) m
          (saveAnswerR f (seqR next)) y snapshot))
      have hout : FiberAction.outcomeOf ({ m with nextToken := m.nextToken + 1 } : RState) false =
          .continue_ := by
        simp only [FiberAction.outcomeOf, ev.live]
        rfl
      simp only [FiberAction.awaitNewChildren, countdownPark, hw, hout]
      refine ev.settle_continue_bump { f.frame with
        current := .pure (.success .unit), stack := .answer (seqR next) :: f.frame.stack }
        (fun ty' d => ?_)
      rw [same ty' d]
      exact ⟨EffTy.pure .unit, TypedProg.pure (strongExit_success w _ _ trivial),
        hostStack_push (Evaluating.unitAnswerFrame typedNext') stack, ⟨prov.recorded, prov.deferred⟩⟩

/-! ## The park on the fresh token, shared by the park branches -/

/-- The park's cancel program (`FiberAction.join`, `countdownPark`: an `AsyncFinalizer` over
`cancelPark`, `Laws/Program/InterpR.lean`'s `denoteStoreCancel`) drops the park's observers, answers
`unit`, then the incoming failure: the frame passes any type through. -/
theorem parkCancelThenFail_typed (root : ProgramSource) {w : World} {ty : EffTy} (host : FiberId)
    (token : Nat) {cause : CauseV} (typed : ExitOk w ty (.failure cause)) :
    TypedProg root w ty ((interpR root.program).cancelThenFail
      ((interpR root.program).cancelName (interpR root.program).parkCancelName host token) cause) := by
  show TypedProg root w ty ((guardR .onSuccess (fiberValR (.dropObservers token) rfl)).bind
    (seqR fun _ => .pure (.failure cause)))
  refine seq_typed_clean root (mid := EffTy.pure .unit) ?_
    (fun w' o _ _ => TypedProg.pure (strongExit_mono _ _ _ _ o typed)) rfl
  refine TypedProg.fiber (fun _ h => nomatch h) (fun _ h => nomatch h) (fun _ h => nomatch h)
    (fun _ _ _ h => nomatch h) PUnit.unit trivial ?_
  intro w' _ ans post
  have unit : ans = Val.unit := post
  subst unit
  exact TypedProg.pure ⟨trivial, trivial⟩

/-- The park's cancel frame pushed on a host stack. -/
theorem hostStack_parkFinalizer (root : ProgramSource) {w : World} {m : RState} {ty final : EffTy}
    (host : FiberId) (token : Nat) {owner : FiberId} {stack : List ScopeFrame}
    (h : HostStack root w m owner ty final stack) :
    HostStack root w m owner ty final
      (.asyncFinalizer ((interpR root.program).cancelName (interpR root.program).parkCancelName host
        token) :: stack) :=
  hostStack_push (.asyncFinalizer _ fun _ _ => ⟨rfl, fun _ _ _ typed _ =>
    parkCancelThenFail_typed root host token typed⟩) h

/-- **The park on the fresh token keeps `I`** (the park clauses' shared shape, no deferred
interrupt): the evaluated fiber becomes idle and parked on `m.nextToken`, declared at `tin`
(`configTyped_token`), with one pending record there; its frame's stack meets `tin`, its dispatcher's
tasks are typed at the new world, and its current code makes no external request. -/
theorem Evaluating.park_fresh {root : ProgramSource} {rootTy : EffTy} {w : World} {m : RState}
    {rest : List RCmd} {f : RFiber} {y : Bool} (ev : Evaluating root rootTy w m rest f y)
    (tin : EffTy) (fr : RSaved) (d : Dispatcher EffName EffThunk Val Err Defect FiberId Ann RProgram)
    (p : RPending)
    (stack : ∀ ty, w.Γ f.id = some ty → HostStack root w (m.update f) f.id tin ty fr.stack)
    (prov : InterruptProvenance fr) (ptoken : p.token = m.nextToken)
    (ptargets : ∀ id ∈ p.waitingOn.toList ++ p.remaining, id.value < m.nextId)
    (request : externalRequestR fr.current = none) (marker : raceRegistrationR fr.current = none)
    (tasks : ∀ b ∈ d.buckets, ∀ t ∈ b.tasks,
      TaskOk (preds root) (w.addToken f.id m.nextToken tin) Expect.root t)
    (keys : ∀ k ∈ Guard.bucketKeys d.buckets, k ∈ Guard.fiberKeys f ∨ k = (f.id, m.nextToken)) :
    w.leHost (w.addToken f.id m.nextToken tin) ∧
      ConfigTyped root rootTy (w.addToken f.id m.nextToken tin)
        (({ (m.update f) with nextToken := m.nextToken + 1 } : RState).update
          { f with frame := fr, dispatcher := d, parked := .withGuard m.nextToken,
                   pending := f.pending ++ [p], running := false }) rest := by
  let M0 : RState := m.update f
  let tok : Nat := m.nextToken
  let M1 : RState := { M0 with nextToken := tok + 1 }
  let w1 : World := w.addToken f.id tok tin
  let g : RFiber := { f with frame := fr, dispatcher := d, parked := .withGuard tok,
                             pending := f.pending ++ [p], running := false }
  have hmem : f ∈ M0.fibers := rfiber?_mem ev.look
  have old : FiberTyped root w M0 f := ev.typed.machine.fiber hmem
  have wide := ev.typed.machine.wide
  have notParked : f.parked = .notParked := by
    cases hp : f.parked with
    | notParked => rfl
    | withGuard _ =>
      have idle := old.parkedIdle (by rw [hp]; exact fun h => nomatch h)
      rw [ev.running] at idle
      cases idle
  have live : f.exit = none := by
    cases hx : f.exit with
    | none => rfl
    | some _ =>
      have stopped := (old.exited (by rw [hx]; rfl)).2
      rw [ev.running] at stopped
      cases stopped
  have hpend : f.pending = [] := by
    have shape := old.pendingShape
    unfold Guard.PendingShape at shape
    rw [notParked] at shape
    exact shape
  obtain ⟨ty, declared⟩ := ev.declared
  have same : ∀ ty', w.Γ f.id = some ty' → ty' = ty :=
    fun _ h => Option.some.inj (h.symm.trans declared)
  obtain ⟨ord, bumped⟩ := configTyped_token (configTyped_tail ev.typed)
    (show (w.Γ f.id).isSome = true by rw [declared]; rfl) tin
  have back : ∀ id t ty', w1.Θ id t = some ty' → (id, t) ≠ (f.id, tok) → w.Θ id t = some ty' :=
    fun id t ty' h ne => by rwa [addToken_Θ_other ne] at h
  have internal : ∀ k ∈ Guard.fiberKeys f, k ≠ (f.id, tok) :=
    fun k hk => key_ne_of_lt (wide.keysBelow k (fiberKeys_internal hmem hk))
  have hf1 : M1.fiber? f.id = some f := ev.look
  have free1 : f.id ∉ rest.filterMap (Guard.commandOwner M1) := by
    rw [commandOwner_bump]
    exact owner_free ev.typed.queue rfl
  obtain ⟨_, _, c2, c3, _, c5⟩ := runFiberOk_tok ord rfl back internal old.ok
  have lookG : (M1.update g).fiber? g.id = some g := rfiber?_update_self hf1 rfl
  have hpOf : g.pending = [p] := by
    show f.pending ++ [p] = [p]
    rw [hpend]
    rfl
  have weakOff : PendingWeakerOff tok f.pending g.pending := by
    rw [hpOf, hpend]
    have single := pendingWeakerOff_single p
    rwa [ptoken] at single
  have viewOff : ObsViewOff (g.id, tok) M1 (M1.update g) := obsViewOff_rupdate (g := g) hf1 rfl weakOff
  have stackG : ∀ ty', w1.Γ g.id = some ty' → HostStack root w1 (M1.update g) g.id tin ty' g.frame.stack :=
    fun ty' d' => hostStack_races (m := M0) (racesKept_of_eq fun _ => rfl)
      (hostStack_mono ord (stack ty' d'))
  have tokenOf : ∀ token, g.parked = .withGuard token → token = tok := by
    intro token h
    have h' : Parked.withGuard tok = .withGuard token := h
    injection h' with e
    exact e.symm
  have declaredG : w1.Θ g.id tok = some tin := addToken_Θ_self
  have pendOk : ∀ q ∈ g.pending, (w1.Θ g.id q.token).isSome = true := by
    intro q hq
    rw [hpOf, List.mem_singleton] at hq
    subst hq
    rw [ptoken]
    show (w1.Θ g.id tok).isSome = true
    rw [declaredG]
    rfl
  have fresh : FiberTyped root w1 (M1.update g) g :=
    { ok := ⟨⟨fun ty' d' => ⟨tin, positionStack_of_host (stackG ty' d'), prov⟩⟩,
        fun q hq => ⟨g.id, pendOk q hq⟩, c2, c3, ⟨fun b hb => ⟨fun t ht => tasks b hb t ht⟩⟩, c5⟩
      delivery := fun token h => by
        rw [tokenOf token h]
        exact ⟨tin, ty, declaredG, declared, stackG ty declared, prov⟩
      below := old.below
      pendingShape := by
        show ∃ q, g.pending = [q] ∧ q.token = tok
        exact ⟨p, hpOf, ptoken⟩
      parkedIdle := fun _ => rfl
      parkedBelow := fun token h => by
        rw [tokenOf token h]
        exact Nat.lt_succ_self _
      exited := fun hx => by
        rw [show g.exit = none from live] at hx
        cases hx
      exitedStack := fun hx => by
        rw [show g.exit = none from live] at hx
        cases hx
      deferredCause := prov.deferred
      pendingOwner := pendOk
      observers := fun o ho => storedObserverOk_off viewOff o
        (fun hk => internal _ (List.mem_append_left _ (List.mem_flatMap.mpr ⟨o, ho, hk⟩)) rfl)
        (storedObserverOk_view (obsView_bump M0 _) o (storedObserverOk_tok ord o (old.observers o ho)))
      registration := fun _ h => by
        change raceRegistrationR fr.current = some _ at h
        rw [marker] at h
        cases h
      code := fun _ _ _ hp => nomatch hp
      tokens := fun token h => by
        rw [tokenOf token h, declaredG]
        rfl
      raceObservers := old.raceObservers
      targetsBelow := fun q hq id hid => by
        rw [hpOf, List.mem_singleton] at hq
        subst hq
        exact ptargets id hid
      observersBelow := old.observersBelow
      children := old.children }
  have noRequest : ∀ tok' r, requestOfR (M1.update g) g.id tok' = some r →
      requestOfR M1 f.id tok' = some r := by
    intro tok' r hr
    by_cases hp : g.parked = .withGuard tok'
    · rw [requestOfR_of_parked lookG hp] at hr
      change externalRequestR fr.current = some r at hr
      rw [request] at hr
      cases hr
    · rw [requestOfR_of_not_parked lookG hp] at hr
      cases hr
  have keysG : ∀ k ∈ Guard.fiberKeys g, k ∈ Guard.internalKeys M1 ∨
      (k.2 < M1.nextToken ∧ requestOfR M1 k.1 k.2 = none) := by
    intro k hk
    unfold Guard.fiberKeys at hk
    rcases List.mem_append.mp hk with ho | hb
    · exact Or.inl (fiberKeys_internal hmem (List.mem_append_left _ ho))
    · rcases keys k hb with hold | rfl
      · exact Or.inl (fiberKeys_internal hmem hold)
      · refine Or.inr ⟨Nat.lt_succ_self _, requestOfR_of_not_parked hf1 ?_⟩
        rw [notParked]
        exact fun h => nomatch h
  exact ⟨ord, configTyped_rupdate_park (g := g) bumped hf1 rfl weakOff
    (fun x hx o ho hk => key_ne_of_lt (n := g.id) (t := tok)
      (wide.keysBelow _ (fiberKeys_internal hx (List.mem_append_left _
        (List.mem_flatMap.mpr ⟨o, ho, hk⟩)))) rfl)
    (fun s e o ho hk => key_ne_of_lt (ev.typed.queue.keys.below _
      (List.mem_flatMap.mpr ⟨.observe s e o, List.mem_cons_of_mem _ ho, hk⟩)) rfl)
    free1 keysG noRequest
    (fun c hc h => commandAuthority_unowned (g := g) hf1 rfl live free1
      bumped.queue.registration c hc h)
    (fun h => Bool.noConfusion h) fresh⟩

/-- **An observer at a fresh key appended to a fiber keeps `I`** (the target of a park): its keys are
below the counter and unrequested, its waiter below `nextId`, it holds no race's key, and it is typed
on the edited machine; nothing else about the fiber moves. -/
theorem configTyped_addObserver {root : ProgramSource} {rootTy : EffTy} {w : World} {M : RState}
    {q : List RCmd} (typed : ConfigTyped root rootTy w M q) {t : RFiber}
    (ht : M.fiber? t.id = some t) (o : Observer)
    (keysOk : ∀ k ∈ Guard.observerKeys o,
      k.2 < M.nextToken ∧ requestOfR M k.1 k.2 = none ∧ k.1.value < M.nextId)
    (raceOff : ∀ raceId race, M.race? raceId = some race → (race.host, race.token) ∉ Guard.observerKeys o)
    (ok : StoredObserverOk root w (M.update { t with observers := t.observers ++ [o] }) t.id o) :
    ConfigTyped root rootTy w (M.update { t with observers := t.observers ++ [o] }) q := by
  let t' : RFiber := { t with observers := t.observers ++ [o] }
  have hmem : t ∈ M.fibers := rfiber?_mem ht
  have old := typed.machine.fiber hmem
  have lookT : (M.update t').fiber? t'.id = some t' := rfiber?_update_self ht rfl
  have view : ObsView M (M.update t') := obsView_rupdate ht rfl (PendingWeaker.refl _)
  have moved := fiberTyped_transport old view (Nat.le_refl _) (Nat.le_refl _)
  have ctl : ∀ id, ((M.update t').fiber? id).map ctlView = (M.fiber? id).map ctlView := by
    intro id
    rw [rfiber?_update]
    cases h : M.fiber? id with
    | none => rfl
    | some x =>
      by_cases hx : x.id = t'.id
      · rw [Option.map_some, if_pos hx]
        have xt : x = t := rfiber?_same ht h hx
        subst xt
        rfl
      · rw [Option.map_some, if_neg hx]
  have newOf : ∀ o' ∈ t'.observers, o' ∈ t.observers ∨ o' = o := fun o' ho' => by
    rcases List.mem_append.mp ho' with h | h
    · exact Or.inl h
    · exact Or.inr (List.mem_singleton.mp h)
  refine configTyped_rupdate_code typed ht rfl (PendingWeaker.refl _) rfl id ?_ ?_
    (fun c _ h => commandAuthority_view ctl view.races c h)
    (fun hrun reads marker ty d => codeOk_races (racesKept_of_eq view.races)
      (typed.code t hmem hrun reads marker ty d)) ?_
  · intro k hk
    unfold Guard.fiberKeys at hk
    rcases List.mem_append.mp hk with ho | hb
    · obtain ⟨o', ho', hk'⟩ := List.mem_flatMap.mp ho
      rcases newOf o' ho' with hold | rfl
      · exact Or.inl (fiberKeys_internal hmem (List.mem_append_left _
          (List.mem_flatMap.mpr ⟨o', hold, hk'⟩)))
      · exact Or.inr ⟨(keysOk k hk').1, (keysOk k hk').2.1⟩
    · exact Or.inl (fiberKeys_internal hmem (List.mem_append_right _ hb))
  · intro token r hr
    by_cases hp : t.parked = .withGuard token
    · rw [requestOfR_of_parked lookT hp] at hr
      rw [requestOfR_of_parked ht hp]
      exact hr
    · rw [requestOfR_of_not_parked lookT hp] at hr
      cases hr
  · obtain ⟨⟨c0⟩, c1, c2, c3, ⟨c4⟩, c5⟩ := moved.ok
    exact
      { ok := ⟨⟨c0⟩, c1, c2, c3, ⟨c4⟩, c5⟩
        delivery := moved.delivery
        below := moved.below
        pendingShape := moved.pendingShape
        parkedIdle := moved.parkedIdle
        parkedBelow := moved.parkedBelow
        exited := moved.exited
        exitedStack := moved.exitedStack
        deferredCause := moved.deferredCause
        pendingOwner := moved.pendingOwner
        observers := fun o' ho' => by
          rcases newOf o' ho' with hold | rfl
          · exact moved.observers o' hold
          · exact ok
        registration := moved.registration
        code := moved.code
        tokens := moved.tokens
        raceObservers := fun r race hr o' ho' => by
          rcases newOf o' ho' with hold | rfl
          · exact moved.raceObservers r race hr o' hold
          · exact raceOff r race hr
        targetsBelow := moved.targetsBelow
        observersBelow := fun o' ho' k hk => by
          rcases newOf o' ho' with hold | rfl
          · exact moved.observersBelow o' hold k hk
          · exact (keysOk k hk).2.2
        children := moved.children }

end Effect4.Program.Typed
