import Effect4.Laws.Program.Typed.Commands.Evaluate

/-!
# Laws.Program.Typed.Commands.Clauses.Park — the park/await clauses (M6)

Concept 4 (the configuration invariant `I`); questions `deliver_preserves` and
`loop_preserves`, through `evaluate_keeps` and `loop_preserves_of_clauses`, which read
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
      exact ⟨t, ord.1.2.1 _ _ declared, ha, he⟩⟩

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
    (off : (target, token) ≠ key) (h : ResumeCode root w target token code) :
    ResumeCode root w' target token code := by
  intro ty declared row
  exact ambientProg_mono root ord (h ty (back _ _ _ declared off) row)

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
    obtain ⟨tin, flag, stack, provenance⟩ := c0 ty declared
    exact ⟨tin, flag, stack.mono ord, provenance⟩
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
  · obtain ⟨tin, row, declared, final, flag, final', covered, stack, provenance⟩ := h.delivery token hp
    exact ⟨tin, row, theta_of ord declared, final, flag, by rw [hΓ]; exact final', covered,
      stack.mono ord, provenance⟩
  · obtain ⟨race, resultTy, found, host, token, reply⟩ := h.registration raceId marker
    exact ⟨race, resultTy, found, host, theta_of ord token,
      reply.imp (fun _ ⟨final, flag, declaredF, covered, stack, provenance⟩ =>
        ⟨final, flag, by rw [hΓ]; exact declaredF, covered, stack.mono ord, provenance⟩)
        (fun _ e live => (e live).mono ord)⟩
  · rw [hΓ] at declared
    exact (h.code hx hr hm hp ty declared).mono ord

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
          [.parkedOn f.id m.nextToken], yieldFiber f next m.nextToken priority, y, .parked, [], []⟩ :=
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
  obtain ⟨row, ⟨q, b⟩, flag, covered, bit, current, stack, prov⟩ := ev.code (by rw [hc]; rfl) ty declared
  change b = f.frame.interruptible at bit
  subst bit
  change AmbientProg root w row q f.frame.current at current
  rw [hc] at current
  obtain ⟨_, _, typedNext, entry, wf⟩ := ambientProg_fiber_inv current (fun _ h => nomatch h)
    (fun _ h => nomatch h) (fun _ h => nomatch h) (fun _ _ _ h => nomatch h)
  let p : MachinePos :=
    ((((⟨.unit, .never, Env.Requirement.empty⟩ : EffTy), row, row) : AmbientPosition), f.frame.interruptible)
  have hstack : MHostStack root w M0 f.id p (finalPos ty flag) (.answer (seqR next) :: f.frame.stack) :=
    .cons (.inl (Evaluating.unitAnswerFrame (fun w' o ans post => typedNext w' o ans post) entry wf))
      stack
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
  have taskOk : ResumeCode root w1 f.id tok (.pure (.success .unit)) := by
    intro ty' d row'
    rw [addToken_Θ_self] at d
    cases d
    exact .pure (ambientExit_const (strongExit_success w1 _ _ trivial))
      ⟨Row.subset_refl _, Row.subset_refl _⟩
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
  show SettlesTyped root rootTy w f.id rest (prepareIterR ⟨_, yieldFiber f next tok priority, y, .parked, [], []⟩)
  refine ⟨w1, ord, ?_⟩
  show ConfigTyped root rootTy w1
    (settle f.id rest ⟨((({ m with nextToken := m.nextToken + 1 } : RState).arm f.id).emit
      [.parkedOn f.id m.nextToken]), yieldFiber f next tok priority, y, .parked, [], []⟩).1
    (settle f.id rest ⟨((({ m with nextToken := m.nextToken + 1 } : RState).arm f.id).emit
      [.parkedOn f.id m.nextToken]), yieldFiber f next tok priority, y, .parked, [], []⟩).2
  unfold settle settleOutcome
  dsimp only
  split
  · -- a deferred interrupt: the park cleared, the same entry continues (`:662-667`)
    rename_i hdef
    let g : RFiber := { yieldFiber f next tok priority with parked := .notParked, pending := [] }
    have lookG : (M1.update g).fiber? g.id = some g := rfiber?_update_self hf1 rfl
    have stackG : ∀ ty', w1.Γ g.id = some ty' →
        MHostStack root w1 (M1.update g) g.id p (finalPos ty' flag) g.frame.stack := by
      intro ty' d
      rw [same ty' d]
      exact (hstack.mono ord).races (racesKept_of_eq (m := M0) fun _ => rfl)
    have pG : InterruptProvenance g.frame := ⟨prov.recorded, prov.deferred⟩
    have codeG : ∀ ty', w1.Γ g.id = some ty' → MCodeOk root w1 (M1.update g) g ty' :=
      fun ty' d => ⟨row, p, flag, covered, rfl,
        .pure (ambientExit_const (strongExit_success w1 _ _ trivial)) ⟨Row.subset_refl _, Row.subset_refl _⟩,
        stackG ty' d, pG⟩
    have cleared : PendingWeaker f.pending g.pending := fun _ _ h => nomatch h
    have view : ObsView M1 (M1.update g) := obsView_rupdate hf1 rfl cleared
    have fresh : FiberTyped root w1 (M1.update g) g :=
      { ok := ⟨⟨fun ty' d => ⟨_, flag, MPositionStack.of_host (stackG ty' d), pG⟩⟩,
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
      rw [commandOwner_update]
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
        MHostStack root w1 (M1.update g) g.id p (finalPos ty' flag) g.frame.stack := by
      intro ty' d
      rw [same ty' d]
      exact (hstack.mono ord).races (racesKept_of_eq (m := M0) fun _ => rfl)
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
      { ok := ⟨⟨fun ty' d => ⟨_, flag, MPositionStack.of_host (stackG ty' d), pG⟩⟩,
          fun p hp => ⟨g.id, pendOk p hp⟩, c2, c3,
          ⟨fun b hb => ⟨fun t ht => dispatcherOk b hb t ht⟩⟩, c5⟩
        delivery := fun token h => by
          rw [tokenOf token h]
          obtain ⟨d⟩ : ∃ _ : w1.Γ g.id = some ty, True := ⟨declared, trivial⟩
          exact ⟨EffTy.pure .unit, row, declaredG, ty, flag, d, covered, stackG ty d, pG⟩
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

/-- **The saved answer frame around an exit reply**: a reply typed at `(replyTy, row, row)` runs the
continuation at every exit its type admits. -/
theorem ambient_answerFrame {root : ProgramSource} {w : World} {row : Env.Requirement}
    {q : AmbientPosition} {b : Bool} {replyTy : EffTy} {next : ExitV → RProgram}
    (run : ∀ w', w.leHost w' → ∀ ex, ExitOk w' replyTy ex → AmbientProg root w' row q (next ex)) :
    MFrame root w ((((replyTy, row, row) : AmbientPosition)), b) (q, b) (.answer next) :=
  .answer next fun w' o ex hex => by
    rw [ambientInput_const]
    exact run w' o ex hex.1

/-- **The saved answer frame around a value reply** (`seqR`): a success runs the continuation at
the value; a failure, at an error column below the operation's, is the operation's own, its failure
row covered by the operation's entry. `Evaluating.unitAnswerFrame` is the `unit` instance. -/
theorem ambient_seqFrame {root : ProgramSource} {w : World} {row : Env.Requirement}
    {q : AmbientPosition} {b : Bool} {replyTy : EffTy} {next : Val → RProgram}
    (errors : Ty.subN replyTy.error q.type.error = true)
    (run : ∀ w', w.leHost w' → ∀ v, Fits w' v replyTy.answer → AmbientProg root w' row q (next v))
    (entry : Row.Subset q.failureRow row) (wf : q.WF) :
    MFrame root w ((((replyTy, row, row) : AmbientPosition)), b) (q, b) (.answer (seqR next)) :=
  .answer _ fun w' o ex hex => by
    rw [ambientInput_const]
    cases ex with
    | success v => exact run w' o v hex.1.1
    | failure c =>
      exact .pure (ambientExit_failure (exitOk_failure_of_errorN errors hex.1) entry) ⟨entry, wf⟩

/-- **`await`** (`internal/effect.ts:5291`, `:5304`): the target, declared by the pre, is a fiber of
the machine (no `unknownFiber` halt); an exited target's exit, typed at its declaration, answers at
once at the fiber's row over the saved answer frame (by effect, or encoded as a value); a live
target parks (`AwaitParks`). -/
theorem clause_await_of_parks (root : ProgramSource) (rootTy : EffTy) (target : FiberId)
    (mode : Supervision.ObserverMode) (parks : AwaitParks root rootTy target mode) :
    FiberClauseKeeps root rootTy (.await target mode) := by
  intro w m rest f y next ev hc
  obtain ⟨ty, declared⟩ := ev.declared
  obtain ⟨row, ⟨q, b⟩, flag, covered, bit, current, stack, prov⟩ := ev.code (by rw [hc]; rfl) ty declared
  change b = f.frame.interruptible at bit
  subst bit
  change AmbientProg root w row q f.frame.current at current
  rw [hc] at current
  obtain ⟨cert, pre, typedNext, entry, wf⟩ := ambientProg_fiber_inv current (fun _ h => nomatch h)
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
      exact ⟨row, (((sourceTy, row, row) : AmbientPosition), f.frame.interruptible), flag, covered, rfl,
        .pure (ambientExit_const exitOk) ⟨Row.subset_refl _, Row.subset_refl _⟩,
        .cons (.inl (ambient_answerFrame (fun w' o ex hex => typedNext w' o ex ⟨sourceTy, o.1.2.1 _ _ hsrc, hex⟩)))
          stack, ⟨prov.recorded, prov.deferred⟩⟩
    | awaitValue =>
      show SettlesTyped root rootTy w f.id rest (prepareIterR
        (FiberAction.join (interpRAt root.program m.completedExits) m (saveAnswerR f (seqR next)) y
          target .awaitValue))
      simp only [FiberAction.join, ht, hx]
      refine ev.settle_continue { f.frame with
        current := .pure (.success (reifyExitVal exit)), stack := .answer (seqR next) :: f.frame.stack }
        (fun ty' d => ?_)
      rw [same ty' d]
      exact ⟨row, (((EffTy.pure (.exitOf sourceTy.answer sourceTy.error), row, row) : AmbientPosition),
          f.frame.interruptible), flag, covered, rfl,
        .pure (ambientExit_const ⟨exitOk.1, trivial⟩) ⟨Row.subset_refl _, Row.subset_refl _⟩,
        .cons (.inl (ambient_seqFrame (Bounds.subN_never _)
          (fun w' o v hv => typedNext w' o v ⟨sourceTy, o.1.2.1 _ _ hsrc, hv⟩) entry wf)) stack,
        ⟨prov.recorded, prov.deferred⟩⟩

/-! ## The countdown parks: no live target answers at once -/

/-- **A continue after a consumed token settles typed** (`countdownPark` takes the token before its
walk): the counter bumped, the world declaring the unused token (`configTyped_token`). -/
theorem Evaluating.settle_continue_bump {root : ProgramSource} {rootTy : EffTy} {w : World}
    {m : RState} {rest : List RCmd} {f : RFiber} {y y' : Bool}
    (ev : Evaluating root rootTy w m rest f y) (fr : RSaved)
    (code : ∀ ty, w.Γ f.id = some ty → MCodeOk root w (m.update f) { f with frame := fr } ty) :
    SettlesTyped root rootTy w f.id rest
      (prepareIterR ⟨{ m with nextToken := m.nextToken + 1 }, { f with frame := fr }, y', .continue_, [], []⟩) := by
  obtain ⟨ty, declared⟩ := ev.declared
  obtain ⟨ord, bumped⟩ := configTyped_token ev.typed
    (show (w.Γ f.id).isSome = true by rw [declared]; rfl) (EffTy.pure .unit)
  have ev' : Evaluating root rootTy (w.addToken f.id m.nextToken (EffTy.pure .unit))
      { m with nextToken := m.nextToken + 1 } rest f y := ⟨bumped, ev.stale, ev.running, ev.live⟩
  exact SettlesTyped.mono ord (ev'.settle_continue fr (fun ty' d =>
    ((code ty' d).mono ord).races (racesKept_of_eq (m := m.update f) fun _ => rfl)))

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

/-- Two lists related one for one. Core carries no `List.Forall₂`. -/
inductive Forall₂ {α β : Type} (R : α → β → Prop) : List α → List β → Prop
  | nil : Forall₂ R [] []
  | cons {a : α} {b : β} {as : List α} {bs : List β} :
      R a b → Forall₂ R as bs → Forall₂ R (a :: as) (b :: bs)

/-- A relation between two lists moves to another wherever it holds at the first list's members. -/
theorem forall₂_imp_mem {α β : Type} {R S : α → β → Prop} :
    ∀ {l₁ : List α} {l₂ : List β}, (∀ a ∈ l₁, ∀ b, R a b → S a b) →
      Forall₂ R l₁ l₂ → Forall₂ S l₁ l₂
  | _, _, _, .nil => .nil
  | _, _, H, .cons h rest =>
    .cons (H _ List.mem_cons_self _ h) (forall₂_imp_mem (fun a ha => H a (List.mem_cons_of_mem _ ha)) rest)

/-- **A walk that meets no live target collects each target's exit, in order**, when the machine
holds every target (`countdownWalk`, `Machine/Fibers.lean`; rc.112's `fiberAwaitAll` waits on its
targets one after another, `internal/effect.ts:779-813`). -/
theorem countdownWalk_forall₂ (M : RState) :
    ∀ (targets : List FiberId) (acc exits : List ExitV),
      (∀ t ∈ targets, (M.fiber? t).isSome = true) →
      countdownWalk M targets acc = (exits, none) →
      ∃ tail, exits = acc ++ tail ∧
        Forall₂ (fun t ex => ∃ g, M.fiber? t = some g ∧ g.exit = some ex) targets tail
  | [], acc, exits, _, h => by
    simp only [countdownWalk] at h
    cases h
    exact ⟨[], (List.append_nil _).symm, .nil⟩
  | t :: rest, acc, exits, found, h => by
    obtain ⟨g, hg⟩ := Option.isSome_iff_exists.mp (found t List.mem_cons_self)
    simp only [countdownWalk, hg] at h
    cases hx : g.exit with
    | none =>
      rw [hx] at h
      cases h
    | some ex =>
      rw [hx] at h
      obtain ⟨tail, htail, rel⟩ := countdownWalk_forall₂ M rest (acc ++ [ex]) exits
        (fun t' ht' => found t' (List.mem_cons_of_mem _ ht')) h
      exact ⟨ex :: tail, by rw [htail, List.append_assoc]; rfl, .cons ⟨g, hg, hx⟩ rel⟩

/-- Exits that fit their targets' columns one for one fit the tuple of those columns. -/
theorem fits_exits_tuple {w : World} {cols : FiberId → Ty × Ty} :
    ∀ {targets : List FiberId} {exits : List ExitV},
      Forall₂ (fun t ex => FitsExit w ⟨(cols t).1, (cols t).2, Env.Requirement.empty⟩ ex)
        targets exits →
      Fits w (exitsVal exits) (.tuple (targets.map fun t => .exitOf (cols t).1 (cols t).2))
  | _, _, .nil => by
    unfold exitsVal
    rw [fits_tuple]
    trivial
  | _, _, .cons h rest => by
    have ih := fits_exits_tuple rest
    unfold exitsVal at ih ⊢
    rw [fits_tuple] at ih ⊢
    simp only [List.map_cons]
    exact ⟨h, ih⟩

/-- **The exits a completed walk answers fit the await's certificate**, in either form of its pre:
the uniform list by every target's columns, the positional tuple by each target's own. -/
theorem Evaluating.awaitAll_value {root : ProgramSource} {rootTy : EffTy} {w : World} {m : RState}
    {rest : List RCmd} {f : RFiber} {y : Bool} (ev : Evaluating root rootTy w m rest f y)
    {targets : List FiberId} {exits : List ExitV} {k : Nat} {cert : Ty}
    (hw : countdownWalk ({ m with nextToken := k } : RState) targets [] = (exits, none))
    (pre : (∃ a e, cert = .list (.exitOf a e) ∧ ∀ t ∈ targets, ∃ fty, w.Γ t = some fty ∧
        fty.answer.sub a = true ∧ fty.error.sub e = true) ∨
      ∃ cols : FiberId → Ty × Ty,
        cert = .tuple (targets.map fun t => .exitOf (cols t).1 (cols t).2) ∧
        ∀ t ∈ targets, ∃ fty, w.Γ t = some fty ∧ fty.answer.sub (cols t).1 = true ∧
          fty.error.sub (cols t).2 = true) :
    Fits w (exitsVal exits) cert := by
  rcases pre with ⟨a, e, hcert, cols⟩ | ⟨cols, hcert, colsOk⟩
  · have typedExits := ev.walk_exits cols (k := k)
    rw [hw] at typedExits
    rw [hcert]
    exact awaitAll_delivered (targets := targets) typedExits
  · have found : ∀ t ∈ targets, (({ m with nextToken := k } : RState).fiber? t).isSome = true := by
      intro t ht
      obtain ⟨fty, d, _⟩ := colsOk t ht
      obtain ⟨g, hg⟩ := ev.target_found (show (w.Γ t).isSome = true by rw [d]; rfl)
      show (m.fiber? t).isSome = true
      rw [hg]
      rfl
    obtain ⟨tail, htail, rel⟩ := countdownWalk_forall₂ _ targets [] exits found hw
    rw [List.nil_append] at htail
    subst htail
    rw [hcert]
    refine fits_exits_tuple (forall₂_imp_mem (fun t ht ex found' => ?_) rel)
    obtain ⟨g, hg, gx⟩ := found'
    obtain ⟨fty, d, ha, he⟩ := colsOk t ht
    exact fitsExit_sub ha he (ev.target_exit (t := g) hg gx fty d).1

/-- **A completed walk's answer**: the value, typed at the reply's type at the fiber's row, over the
saved answer frame back to the operation's position. -/
theorem walkAnswer_codeOk {root : ProgramSource} {w : World} {m : RState} {f : RFiber} {ty : EffTy}
    {row : Env.Requirement} {q : AmbientPosition} {flag : Bool}
    (covered : f.context.services.Satisfies row)
    (stack : MHostStack root w m f.id (q, f.frame.interruptible) (finalPos ty flag) f.frame.stack)
    (prov : InterruptProvenance f.frame) {next : Val → RProgram} {replyTy : Ty} {v : Val}
    (value : Fits w v replyTy)
    (typedNext : ∀ w', w.leHost w' → ∀ ans, Fits w' ans replyTy → AmbientProg root w' row q (next ans))
    (entry : Row.Subset q.failureRow row) (wf : q.WF) :
    MCodeOk root w m { f with frame := { f.frame with
      current := .pure (.success v), stack := .answer (seqR next) :: f.frame.stack } } ty :=
  ⟨row, (((EffTy.pure replyTy, row, row) : AmbientPosition), f.frame.interruptible), flag, covered, rfl,
    .pure (ambientExit_const ⟨value, trivial⟩) ⟨Row.subset_refl _, Row.subset_refl _⟩,
    .cons (.inl (ambient_seqFrame (Bounds.subN_never _) typedNext entry wf)) stack,
    ⟨prov.recorded, prov.deferred⟩⟩

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
      show SettlesTyped root rootTy w f.id rest (prepareIterR
        (FiberAction.awaitAll (interpRAt root.program m.completedExits) m (saveAnswerR f (seqR next)) y
          targets false))
      have hout : FiberAction.outcomeOf ({ m with nextToken := m.nextToken + 1 } : RState) false =
          .continue_ := by
        simp only [FiberAction.outcomeOf, ev.live]
        rfl
      simp only [FiberAction.awaitAll, countdownParkEdits, hw, hout]
      refine ev.settle_continue_bump _ (fun ty declared => ?_)
      obtain ⟨row, ⟨q, b⟩, flag, covered, bit, current, stack, prov⟩ :=
        ev.code (by rw [hc]; rfl) ty declared
      change b = f.frame.interruptible at bit
      subst bit
      change AmbientProg root w row q f.frame.current at current
      rw [hc] at current
      obtain ⟨cert, pre, typedNext, entry, wf⟩ := ambientProg_fiber_inv current (fun _ h => nomatch h)
        (fun _ h => nomatch h) (fun _ h => nomatch h) (fun _ _ _ h => nomatch h)
      exact walkAnswer_codeOk covered stack prov (ev.awaitAll_value hw pre)
        (fun w' o ans hv => typedNext w' o ans hv) entry wf

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
      show SettlesTyped root rootTy w f.id rest (prepareIterR
        (FiberAction.awaitAll (interpRAt root.program m.completedExits) m (saveAnswerR f (seqR next)) y
          targets true))
      have hout : FiberAction.outcomeOf ({ m with nextToken := m.nextToken + 1 } : RState) false =
          .continue_ := by
        simp only [FiberAction.outcomeOf, ev.live]
        rfl
      simp only [FiberAction.awaitAll, countdownParkEdits, hw, hout]
      refine ev.settle_continue_bump _ (fun ty declared => ?_)
      obtain ⟨row, ⟨q, b⟩, flag, covered, bit, current, stack, prov⟩ :=
        ev.code (by rw [hc]; rfl) ty declared
      change b = f.frame.interruptible at bit
      subst bit
      change AmbientProg root w row q f.frame.current at current
      rw [hc] at current
      obtain ⟨cert, pre, typedNext, entry, wf⟩ := ambientProg_fiber_inv current (fun _ h => nomatch h)
        (fun _ h => nomatch h) (fun _ h => nomatch h) (fun _ _ _ h => nomatch h)
      exact walkAnswer_codeOk covered stack prov (ev.awaitAll_value hw pre)
        (fun w' o ans hv => typedNext w' o ans hv) entry wf

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
      show SettlesTyped root rootTy w f.id rest (prepareIterR
        (FiberAction.awaitNewChildren (interpRAt root.program m.completedExits) m
          (saveAnswerR f (seqR next)) y snapshot))
      have hout : FiberAction.outcomeOf ({ m with nextToken := m.nextToken + 1 } : RState) false =
          .continue_ := by
        simp only [FiberAction.outcomeOf, ev.live]
        rfl
      simp only [FiberAction.awaitNewChildren, countdownParkEdits, hw, hout]
      refine ev.settle_continue_bump _ (fun ty declared => ?_)
      obtain ⟨row, ⟨q, b⟩, flag, covered, bit, current, stack, prov⟩ :=
        ev.code (by rw [hc]; rfl) ty declared
      change b = f.frame.interruptible at bit
      subst bit
      change AmbientProg root w row q f.frame.current at current
      rw [hc] at current
      obtain ⟨_, _, typedNext, entry, wf⟩ := ambientProg_fiber_inv current (fun _ h => nomatch h)
        (fun _ h => nomatch h) (fun _ h => nomatch h) (fun _ _ _ h => nomatch h)
      exact walkAnswer_codeOk (replyTy := .unit) covered stack prov trivial
        (fun w' o ans hv => typedNext w' o ans (fits_unit_inv hv)) entry wf

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

/-- The park's cancel program is administrative code. -/
theorem parkCancelThenFail_admin (root : ProgramSource) (host : FiberId) (token : Nat) (cause : CauseV) :
    AdminCode ((interpR root.program).cancelThenFail
      ((interpR root.program).cancelName (interpR root.program).parkCancelName host token) cause) := by
  show AdminCode ((guardR .onSuccess (fiberValR (.dropObservers token) rfl)).bind
    (seqR fun _ => .pure (.failure cause)))
  exact (AdminCode.guard _ (AdminCode.fiberVal _ rfl rfl)).bind (AdminCode.seq _)

/-- The park's cancel frame pushed on a machine host stack at a constant row. -/
theorem mHostStack_parkFinalizer (root : ProgramSource) {w : World} {m : RState} {ty : EffTy}
    {row : Env.Requirement} {b : Bool} {tout : MachinePos} (host : FiberId) (token : Nat)
    {owner : FiberId} {stack : List ScopeFrame}
    (h : MHostStack root w m owner (((ty, row, row) : AmbientPosition), b) tout stack) :
    MHostStack root w m owner (((ty, row, row) : AmbientPosition), b) tout
      (.asyncFinalizer ((interpR root.program).cancelName (interpR root.program).parkCancelName host
        token) :: stack) :=
  .cons (.inl (.asyncFinalizer _ (fun _ _ => ⟨rfl, fun _ _ cause typed _ =>
    ambientProg_of_admin root (parkCancelThenFail_typed root host token typed)
      (parkCancelThenFail_admin root host token cause) row⟩) (Row.subset_refl _))) h

/-- **The park on the fresh token keeps `I`** (the park clauses' shared shape, no deferred
interrupt): the evaluated fiber becomes idle and parked on `m.nextToken`, declared at `tin`
(`configTyped_token`), with one pending record there; its frame's stack meets `tin`, its dispatcher's
tasks are typed at the new world, and its current code makes no external request. -/
theorem Evaluating.park_fresh {root : ProgramSource} {rootTy : EffTy} {w : World} {m : RState}
    {rest : List RCmd} {f : RFiber} {y : Bool} (ev : Evaluating root rootTy w m rest f y)
    (tin : EffTy) (row : Env.Requirement) (flag : Bool) (covered : f.context.services.Satisfies row)
    (fr : RSaved) (d : Dispatcher EffName EffThunk Val Err Defect FiberId Ann RProgram)
    (p : RPending)
    (stack : ∀ ty, w.Γ f.id = some ty → MHostStack root w (m.update f) f.id
      (((tin, row, row) : AmbientPosition), fr.interruptible) (finalPos ty flag) fr.stack)
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
  have stackG : ∀ ty', w1.Γ g.id = some ty' → MHostStack root w1 (M1.update g) g.id
      (((tin, row, row) : AmbientPosition), g.frame.interruptible) (finalPos ty' flag) g.frame.stack :=
    fun ty' d' => ((stack ty' d').mono ord).races (racesKept_of_eq (m := M0) fun _ => rfl)
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
    { ok := ⟨⟨fun ty' d' => ⟨_, flag, MPositionStack.of_host (stackG ty' d'), prov⟩⟩,
        fun q hq => ⟨g.id, pendOk q hq⟩, c2, c3, ⟨fun b hb => ⟨fun t ht => tasks b hb t ht⟩⟩, c5⟩
      delivery := fun token h => by
        rw [tokenOf token h]
        exact ⟨tin, row, declaredG, ty, flag, declared, covered, stackG ty declared, prov⟩
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

/-- The observer message commutes with the parked disposition; its target is the installed owner. -/
theorem settle_observe_park {M : RState} {g old : RFiber} {id target : FiberId} {rest : List RCmd} {y : Bool} {o : Observer}
    (hg : M.fiber? g.id = some old) :
    settle id rest ⟨M, g, y, .parked, [], [.observe target o]⟩ =
      let settled := settle id rest ⟨M, g, y, .parked, [], []⟩
      (settled.1.modify target (fun f => {f with observers := f.observers ++ [o]}), settled.2) := by
  have ho : old.id = g.id := rfiber?_id hg
  have own : (M.update g).fiber? g.id = some g := rfiber?_update_self (f := old) (by rw [ho]; exact hg) ho.symm
  by_cases self : target = g.id
  · subst target
    let go : RFiber := {g with observers := g.observers ++ [o]}
    have lookGO : ((M.update g).update go).fiber? g.id = some go :=
      rfiber?_update_self own rfl
    simp only [settle, applyFiberEdits, List.foldl_cons, List.foldl_nil, applyFiberEdit, RunMachine.observe,
      RunMachine.modify, own, List.nil_append]
    rw [lookGO]
    simp only [settleOutcome, FiberCore.deferredInterrupt, List.nil_append]
    cases hd : g.frame.deferredInterrupt with
    | true =>
      dsimp only [go]
      simp only [ite_true]
      simp only [rupdate_rupdate]
      rw [rfiber?_update_self (f := old) (by rw [ho]; exact hg) (g := {g with parked := .notParked, pending := []}) ho.symm]
      simp only [rupdate_rupdate]
    | false =>
      dsimp only [go]
      simp only [Bool.false_eq_true, ite_false]
      simp only [rupdate_rupdate]
      rw [rfiber?_update_self (f := old) (by rw [ho]; exact hg) (g := {g with running := false}) ho.symm]
      simp only [rupdate_rupdate]
  · cases ht : M.fiber? target with
    | none =>
      have noTarget : (M.update g).fiber? target = none := by rw [rfiber?_update_other self, ht]
      simp only [settle, applyFiberEdits, List.foldl_cons, List.foldl_nil, applyFiberEdit, RunMachine.observe,
        RunMachine.modify, noTarget, own, List.nil_append, settleOutcome, FiberCore.deferredInterrupt]
      cases hd : g.frame.deferredInterrupt with
      | true =>
        simp only [ite_true]
        rw [rfiber?_update_other (g := {g with parked := .notParked, pending := []}) self, ht]
        simp only [rupdate_rupdate]
      | false =>
        simp only [Bool.false_eq_true, ite_false]
        rw [rfiber?_update_other (g := {g with running := false}) self, ht]
        simp only [rupdate_rupdate]
    | some t =>
      have tid : t.id = target := rfiber?_id ht
      let to : RFiber := {t with observers := t.observers ++ [o]}
      have other : g.id ≠ to.id := by show g.id ≠ t.id; rw [tid]; exact Ne.symm self
      have targetLook : (M.update g).fiber? target = some t := by rw [rfiber?_update_other self, ht]
      have ownerLook : ((M.update g).update to).fiber? g.id = some g := by rw [rfiber?_update_other other]; exact own
      simp only [settle, applyFiberEdits, List.foldl_cons, List.foldl_nil, applyFiberEdit, RunMachine.observe,
        RunMachine.modify, targetLook, List.nil_append]
      rw [ownerLook]
      simp only [settleOutcome, FiberCore.deferredInterrupt, List.nil_append]
      cases hd : g.frame.deferredInterrupt with
      | true =>
        simp only [ite_true]
        rw [rfiber?_update_other (g := {g with parked := .notParked, pending := []}) self, ht]
        rw [rupdate_comm _ (show ({g with parked := .notParked, pending := []} : RFiber).id ≠ to.id from other)]
        simp only [rupdate_rupdate]
        rfl
      | false =>
        simp only [Bool.false_eq_true, ite_false]
        rw [rfiber?_update_other (g := {g with running := false}) self, ht]
        rw [rupdate_comm _ (show ({g with running := false} : RFiber).id ≠ to.id from other)]
        simp only [rupdate_rupdate]
        rfl

/-- `configTyped_cons_loop` for a fiber whose read code is `ReadOk` at the new queue (the stack
half alone when a deferred interrupt makes the loop top replace its code, decisions 2026-10-02). -/
theorem configTyped_cons_loop_read {root : ProgramSource} {rootTy : EffTy} {w : World} {m : RState}
    {q : List RCmd} (typed : ConfigTyped root rootTy w m q) {f : RFiber}
    (hf : m.fiber? f.id = some f) (running : f.running = true) (parked : f.parked = .notParked)
    (free : f.id ∉ q.filterMap (Guard.commandOwner m)) (yielding : Bool)
    (code : raceRegistrationR f.frame.current = none → ∀ ty, w.Γ f.id = some ty →
      ReadOk root w m (.loop f.id yielding :: q) f ty) :
    ConfigTyped root rootTy w m (.loop f.id yielding :: q) := by
  have wide := typed.machine.wide
  refine ⟨typed.machine, ?_, queueOk_cons ?_ typed.queue⟩
  · intro x hx run reads marker ty declared
    by_cases same : x.id = f.id
    · have xf : x = f := rfiber?_same hf (rfiber?_of_mem wide.fiberIds hx) same
      rw [xf] at marker declared ⊢
      exact code marker ty declared
    · obtain ⟨y, r⟩ := reads
      refine (typed.code x hx run ⟨y, ?_⟩ marker ty declared).cons fun y' h => ?_
      rotate_left
      · cases h
      rcases r with r | r
      · rcases List.mem_cons.mp r with h | h
        · injection h with hid _
          exact absurd hid same
        · exact Or.inl h
      · rcases List.mem_cons.mp r with h | h
        · cases h
        · exact Or.inr h
  · refine ⟨trivial, ⟨f, hf, running, parked⟩, trivial, ?_, trivial, (fun _ h => nomatch h),
      (fun _ _ _ _ h => nomatch h), (fun _ _ _ h => nomatch h), (fun _ _ h => nomatch h),
      (fun _ _ _ h => nomatch h), (fun _ _ _ _ _ h => nomatch h), (fun _ _ _ h => nomatch h)⟩
    intro o owner
    cases owner
    exact free

/-- **A park cleared by a deferred interrupt keeps `I`** (`settle`'s deferred arm over the park
clauses): the evaluated fiber took the fresh token (declared at `tin`), its frame `fr` saved over a
stack meeting `tin`; the park and its record are cleared and the same entry continues with `loop`,
whose top replaces the current code with the recorded failure, so the read is the stack half
(`ReadOk`). -/
theorem Evaluating.unpark_fresh {root : ProgramSource} {rootTy : EffTy} {w : World} {m : RState}
    {rest : List RCmd} {f : RFiber} {y : Bool} (ev : Evaluating root rootTy w m rest f y)
    (tin : EffTy) (row : Env.Requirement) (flag : Bool) (covered : f.context.services.Satisfies row)
    (fr : RSaved)
    (stack : ∀ ty, w.Γ f.id = some ty → MHostStack root w (m.update f) f.id
      (((tin, row, row) : AmbientPosition), fr.interruptible) (finalPos ty flag) fr.stack)
    (prov : InterruptProvenance fr) (frdef : fr.deferredInterrupt = true)
    (marker : raceRegistrationR fr.current = none) (y' : Bool) :
    w.leHost (w.addToken f.id m.nextToken tin) ∧
      ConfigTyped root rootTy (w.addToken f.id m.nextToken tin)
        (({ (m.update f) with nextToken := m.nextToken + 1 } : RState).update
          { f with frame := fr, parked := .notParked, pending := [] }) (.loop f.id y' :: rest) := by
  let M0 : RState := m.update f
  let tok : Nat := m.nextToken
  let M1 : RState := { M0 with nextToken := tok + 1 }
  let w1 : World := w.addToken f.id tok tin
  let g : RFiber := { f with frame := fr, parked := .notParked, pending := [] }
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
  obtain ⟨_, _, c2, c3, c4, c5⟩ := runFiberOk_tok ord rfl back internal old.ok
  have lookG : (M1.update g).fiber? g.id = some g := rfiber?_update_self hf1 rfl
  have stackG : ∀ ty', w1.Γ g.id = some ty' → MHostStack root w1 (M1.update g) g.id
      (((tin, row, row) : AmbientPosition), g.frame.interruptible) (finalPos ty' flag) g.frame.stack :=
    fun ty' d' => ((stack ty' d').mono ord).races (racesKept_of_eq (m := M0) fun _ => rfl)
  have cleared : PendingWeaker f.pending g.pending := fun _ _ h => nomatch h
  have view : ObsView M1 (M1.update g) := obsView_rupdate hf1 rfl cleared
  have fresh : FiberTyped root w1 (M1.update g) g :=
    { ok := ⟨⟨fun ty' d' => ⟨_, flag, MPositionStack.of_host (stackG ty' d'), prov⟩⟩,
        (fun _ hp => nomatch hp), c2, c3, c4, c5⟩
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
      deferredCause := prov.deferred
      pendingOwner := fun _ hp => nomatch hp
      observers := fun o ho => storedObserverOk_view view o
        (storedObserverOk_view (obsView_bump M0 _) o (storedObserverOk_tok ord o (old.observers o ho)))
      registration := fun _ h => by
        change raceRegistrationR fr.current = some _ at h
        rw [marker] at h
        cases h
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
    (fun k hk => Or.inl (fiberKeys_internal hmem hk)) noRequest
    (fun c hc h => commandAuthority_flags (g := g) hf1 rfl rfl notParked.symm rfl free1 c hc h)
    (fun _ reads => by
      obtain ⟨y'', r⟩ := reads
      rcases r with r | r
      · exact (free1 (List.mem_filterMap.mpr ⟨_, r, rfl⟩)).elim
      · exact (free1 (List.mem_filterMap.mpr ⟨_, r, rfl⟩)).elim) fresh
  have freeG : g.id ∉ rest.filterMap (Guard.commandOwner (M1.update g)) := by
    rw [commandOwner_update]
    exact free1
  exact ⟨ord, configTyped_cons_loop_read edited lookG ev.running rfl freeG y' (fun _ ty' d' =>
    Or.inr ⟨frdef, fun y'' hy => by
      rcases List.mem_cons.mp hy with h | h
      · cases h
      · exact free1 (List.mem_filterMap.mpr ⟨_, h, rfl⟩), row,
      (((tin, row, row) : AmbientPosition), g.frame.interruptible), flag, covered, rfl,
      Row.subset_refl _, (Row.subset_refl row : AmbientPosition.WF ((tin, row, row) : AmbientPosition)),
      stackG ty' d', prov⟩)⟩

/-! ## `await`'s park -/

/-- The glue leaves a parked fiber whose current is an `await`. -/
theorem prepareIterR_await {edits : List (FiberEdit Err Defect FiberId Ann)} {M : RState} {g : RFiber} {y : Bool} {target : FiberId}
    {mode : Supervision.ObserverMode} {k : (FiberOp.await target mode).answer → RProgram}
    (hg : g.frame.current = .vis (.inr (.await target mode)) k) :
    prepareIterR ⟨M, g, y, .parked, [], edits⟩ = ⟨M, g, y, .parked, [], edits⟩ := by
  rcases g with ⟨id, ⟨cur, stk, i, ic, di⟩, running, parked, pending, finalizing, exit, count,
    maxOps, prevent, yo, observers, children, dispatcher, context⟩
  change cur = _ at hg
  subst hg
  rfl

/-- **`await`'s park with no deferred interrupt** (`FiberAction.join`'s live-target arm,
`internal/effect.ts:5291`, `:5304`): the fiber parks on the fresh token, declared at the observer's
delivered type (`observerDeliveredType`), under the park's cancel frame over the saved answer frame
(`Evaluating.park_fresh`); the target, another fiber, gets the `resumeAwait` observer at the token
(`configTyped_addObserver`); the installed caller retains a self-join observer. -/
theorem Evaluating.join_parks {root : ProgramSource} {rootTy : EffTy} {w : World} {m : RState}
    {rest : List RCmd} {f : RFiber} {y : Bool} (ev : Evaluating root rootTy w m rest f y)
    {target : FiberId} {mode : Supervision.ObserverMode}
    {next : (FiberOp.await target mode).answer → RProgram}
    (hc : f.frame.current = .vis (.inr (.await target mode)) next)
    {t : RFiber} (ht : m.fiber? target = some t) (hx : t.exit = none)
    {sourceTy : EffTy} (hsrc : w.Γ target = some sourceTy) (next' : ExitV → RProgram)
    (row : Env.Requirement) (flag : Bool) (covered : f.context.services.Satisfies row)
    (frame : ∀ ty, w.Γ f.id = some ty → MHostStack root w (m.update f) f.id
      (((observerDeliveredType mode sourceTy, row, row) : AmbientPosition), f.frame.interruptible)
      (finalPos ty flag) (.answer next' :: f.frame.stack)) :
    SettlesTyped root rootTy w f.id rest
      (prepareIterR (FiberAction.join (interpRAt root.program m.completedExits) m (saveAnswerR f next')
        y target mode)) := by
  have wide := ev.typed.machine.wide
  have hmem : f ∈ (m.update f).fibers := rfiber?_mem ev.look
  have old := ev.typed.machine.fiber hmem
  let tok : Nat := m.nextToken
  let tin : EffTy := observerDeliveredType mode sourceTy
  let name := (interpR root.program).cancelName (interpR root.program).parkCancelName f.id tok
  let fr : RSaved := { f.frame with stack := .asyncFinalizer name :: .answer next' :: f.frame.stack }
  let p : RPending := ⟨tok, some target, [], [], .void, false⟩
  let gP : RFiber := { f with frame := fr, dispatcher := f.dispatcher, parked := .withGuard tok,
                              pending := f.pending ++ [p], running := false }
  obtain ⟨ty, declared⟩ := ev.declared
  obtain ⟨_, _, _, _, _, _, _, prov⟩ := ev.code (by rw [hc]; rfl) ty declared
  have tbelow : target.value < m.nextId := by
    obtain ⟨x, hx', hid⟩ := List.mem_map.mp ((wide.fibers target).mp (by rw [hsrc]; rfl))
    rw [← hid]
    exact (ev.typed.machine.fiber hx').below
  have ord0 : w.leHost (w.addToken f.id tok tin) :=
    addToken_leHost (valid_nextToken_fresh rootTy w (m.update f) ev.typed.machine.typed.1 f.id)
  have back : ∀ id t' ty', (w.addToken f.id tok tin).Θ id t' = some ty' → (id, t') ≠ (f.id, tok) →
      w.Θ id t' = some ty' := fun id t' ty' h ne => by rwa [addToken_Θ_other ne] at h
  have internal : ∀ k ∈ Guard.fiberKeys f, k ≠ (f.id, tok) :=
    fun k hk => key_ne_of_lt (wide.keysBelow k (fiberKeys_internal hmem hk))
  obtain ⟨_, _, _, _, ⟨c4⟩, _⟩ := runFiberOk_tok ord0 rfl back internal old.ok
  obtain ⟨ord, parked⟩ := ev.park_fresh tin row flag covered fr f.dispatcher p
    (fun ty' d => mHostStack_parkFinalizer root f.id tok (frame ty' d)) ⟨prov.recorded, prov.deferred⟩
    rfl
    (fun id hid => by
      rcases List.mem_append.mp hid with h | h
      · rw [List.mem_singleton.mp h]
        exact tbelow
      · cases h)
    (by show externalRequestR f.frame.current = none; rw [hc]; rfl)
    (by show raceRegistrationR f.frame.current = none; rw [hc]; rfl)
    (fun b hb t' ht' => (c4 b hb).c0 t' ht') (fun k hk => Or.inl (List.mem_append_right _ hk))
  let gE : RFiber := { f with frame := fr, parked := .withGuard tok, pending := f.pending ++ [p] }
  simp only [FiberAction.join, ht, hx]
  let base : RState := ({m with nextToken := m.nextToken + 1} : RState).emit [.parkedOn f.id tok]
  show SettlesTyped root rootTy w f.id rest (prepareIterR
    ⟨base, gE, y, .parked, [], [.observe target (.resumeAwait f.id tok mode)]⟩)
  rw [prepareIterR_await (g := gE) hc]
  refine ⟨w.addToken f.id tok tin, ord, ?_⟩
  have found : ∃ old, base.fiber? gE.id = some old := by
    change ∃ old, m.fiber? f.id = some old
    have look := ev.look
    rw [rfiber?_update] at look
    cases h : m.fiber? f.id with
    | none => rw [h] at look; cases look
    | some old => exact ⟨old, rfl⟩
  obtain ⟨previous, previousLook⟩ := found
  rw [settle_observe_park previousLook]
  have raceOff : ∀ (M : RState), M.races = (m.update f).races → ∀ r race, M.race? r = some race →
      (race.host, race.token) ∉ Guard.observerKeys (.resumeAwait f.id tok mode) := by
    intro M hM r race hr hk
    rw [show Guard.observerKeys (.resumeAwait f.id tok mode) = [(f.id, tok)] from rfl,
      List.mem_singleton] at hk
    have mem : race ∈ (m.update f).races := by
      rw [← hM]
      exact List.mem_of_find?_eq_some hr
    exact key_ne_of_lt (wide.keysBelow _ (raceKey_internal mem)) hk
  simp only [settle, settleOutcome, List.nil_append]
  split
  · rename_i hd
    let gD : RFiber := { f with frame := fr, parked := .notParked, pending := [] }
    let Md : RState := ({ (m.update f) with nextToken := m.nextToken + 1 } : RState).update gD
    obtain ⟨_, unparked⟩ := ev.unpark_fresh tin row flag covered fr
      (fun ty' d => mHostStack_parkFinalizer root f.id tok (frame ty' d)) ⟨prov.recorded, prov.deferred⟩
      hd (by show raceRegistrationR f.frame.current = none; rw [hc]; rfl) y
    have lookD : Md.fiber? f.id = some gD := rfiber?_update_self (f := f) ev.look rfl
    have added := configTyped_observe unparked target (.resumeAwait f.id tok mode)
      (fun k hk => by
        rw [show Guard.observerKeys (.resumeAwait f.id tok mode) = [(f.id, tok)] from rfl,
          List.mem_singleton] at hk
        subst hk
        exact ⟨Nat.lt_succ_self _, requestOfR_of_not_parked lookD (fun h => nomatch h), old.below⟩)
      (raceOff Md rfl) (fun t ht' => ⟨sourceTy, by rw [rfiber?_id ht']; exact hsrc, addToken_Θ_self⟩)
    refine configTyped_observe_congr (M := Md) (M' := (base).update gD) ?_ rfl rfl rfl rfl rfl rfl target _ added
    change (m.update gD).fibers = ((m.update f).update gD).fibers
    rw [rupdate_rupdate m (f := f) (g := gD) rfl]
  · let Mp : RState := ({ (m.update f) with nextToken := m.nextToken + 1 } : RState).update gP
    have lookP : Mp.fiber? f.id = some gP := rfiber?_update_self (f := f) ev.look rfl
    have added := configTyped_observe parked target (.resumeAwait f.id tok mode)
      (fun k hk => by
        rw [show Guard.observerKeys (.resumeAwait f.id tok mode) = [(f.id, tok)] from rfl,
          List.mem_singleton] at hk
        subst hk
        refine ⟨Nat.lt_succ_self _, ?_, old.below⟩
        rw [requestOfR_of_parked lookP rfl]
        show externalRequestR f.frame.current = none
        rw [hc]
        rfl)
      (raceOff Mp rfl) (fun t ht' => ⟨sourceTy, by rw [rfiber?_id ht']; exact hsrc, addToken_Θ_self⟩)
    refine configTyped_observe_congr (M := Mp) (M' := (base).update gP) ?_ rfl rfl rfl rfl rfl rfl target _ added
    change (m.update gP).fibers = ((m.update f).update gP).fibers
    rw [rupdate_rupdate m (f := f) (g := gP) rfl]

/-- **`await`'s park branch** (`AwaitParks`), both modes. -/
theorem awaitParks (root : ProgramSource) (rootTy : EffTy) (target : FiberId)
    (mode : Supervision.ObserverMode) : AwaitParks root rootTy target mode := by
  intro w m rest f y next t ev hc ht hx
  obtain ⟨ty, declared⟩ := ev.declared
  obtain ⟨row, ⟨q, b⟩, flag, covered, bit, current, stack, _⟩ := ev.code (by rw [hc]; rfl) ty declared
  change b = f.frame.interruptible at bit
  subst bit
  change AmbientProg root w row q f.frame.current at current
  rw [hc] at current
  obtain ⟨cert, pre, typedNext, entry, wf⟩ := ambientProg_fiber_inv current (fun _ h => nomatch h)
    (fun _ h => nomatch h) (fun _ h => nomatch h) (fun _ _ _ h => nomatch h)
  obtain ⟨sourceTy, hsrc⟩ := Option.isSome_iff_exists.mp pre
  have same : ∀ ty', w.Γ f.id = some ty' → ty' = ty :=
    fun _ h => Option.some.inj (h.symm.trans declared)
  cases mode with
  | joinEffect =>
    exact ev.join_parks hc ht hx hsrc next row flag covered (fun ty' d => by
      rw [same ty' d]
      exact .cons (.inl (ambient_answerFrame
        (fun w' o ex hex => typedNext w' o ex ⟨sourceTy, o.1.2.1 _ _ hsrc, hex⟩))) stack)
  | awaitValue =>
    exact ev.join_parks hc ht hx hsrc (seqR next) row flag covered (fun ty' d => by
      rw [same ty' d]
      exact .cons (.inl (ambient_seqFrame (Bounds.subN_never _)
        (fun w' o v hv => typedNext w' o v ⟨sourceTy, o.1.2.1 _ _ hsrc, hv⟩) entry wf)) stack)

/-- **`await`** (`internal/effect.ts:5291`, `:5304`), both modes: `clause_await_of_parks` at its park
branch (`awaitParks`). -/
theorem clause_await (root : ProgramSource) (rootTy : EffTy) (target : FiberId)
    (mode : Supervision.ObserverMode) : FiberClauseKeeps root rootTy (.await target mode) :=
  clause_await_of_parks root rootTy target mode (awaitParks root rootTy target mode)

/-! ## The countdown parks -/

/-- A machine that has not halted reports a park as parked. -/
theorem outcomeOf_parked {M : RState} (h : M.stuck = none) : FiberAction.outcomeOf M true = .parked := by
  unfold FiberAction.outcomeOf
  rw [h]
  rfl

/-- The fiber a countdown park leaves before `settle` (`countdownPark`'s live arm). -/
abbrev countdownFiber (root : ProgramSource) (f : RFiber) (next' : ExitV → RProgram) (p : RPending) :
    RFiber :=
  { f with
    frame := { f.frame with stack := .asyncFinalizer ((interpR root.program).cancelName
      (interpR root.program).parkCancelName f.id p.token) :: .answer next' :: f.frame.stack }
    parked := .withGuard p.token
    pending := f.pending ++ [p] }

/-- The countdown plan before its observer message: the token is taken and the park is recorded. -/
abbrev countdownMachine (m : RState) (_target waiter : FiberId) : RState :=
  (({ m with nextToken := m.nextToken + 1 } : RState).emit [.parkedOn waiter m.nextToken])

/-- **A countdown's park** (`countdownPark`'s live arm,
`internal/effect.ts:779-813`): the fiber parks on the fresh token, declared at the record's token
type `tt`, under the park's cancel frame over the saved answer frame (`Evaluating.park_fresh`), its
record carrying the collected exits and the targets after the live one; the live target, another
fiber, gets the countdown observer at the token, typed by the record's payload
(`configTyped_addObserver`); the installed caller retains a self-target observer. -/
theorem Evaluating.countdown_parks {root : ProgramSource} {rootTy : EffTy} {w : World} {m : RState}
    {rest : List RCmd} {f : RFiber} {y : Bool} (ev : Evaluating root rootTy w m rest f y)
    (marker : raceRegistrationR f.frame.current = none)
    (request : externalRequestR f.frame.current = none)
    {targets : List FiberId} (resumeWith : Resume EffName) (failFast : Bool) {exits : List ExitV}
    {target : FiberId} {remaining : List FiberId}
    (hw : countdownWalk ({ m with nextToken := m.nextToken + 1 } : RState) targets [] =
      (exits, some (target, remaining)))
    (tbelow : ∀ id ∈ targets, id.value < m.nextId) {a e : Ty} {tt : EffTy}
    (cols : ∀ id ∈ targets, FiberColumnsBelow w id a e)
    (exitsOk : ∀ ex ∈ exits, ExitOk w ⟨a, e, Env.Requirement.empty⟩ ex)
    (resumeOk : match resumeWith with
      | .exitsValue => tt = EffTy.pure (.list (.exitOf a e))
      | .void => tt = EffTy.pure .unit
      | .continueWith (.restore saved) => ExitOk (w.addToken f.id m.nextToken tt) tt saved
      | .continueWith _ => ExitOk (w.addToken f.id m.nextToken tt) tt outsideExit)
    (next' : ExitV → RProgram) (row : Env.Requirement) (flag : Bool)
    (covered : f.context.services.Satisfies row)
    (frame : ∀ ty, w.Γ f.id = some ty → MHostStack root w (m.update f) f.id
      (((tt, row, row) : AmbientPosition), f.frame.interruptible) (finalPos ty flag)
      (.answer next' :: f.frame.stack))
    (glue : ∀ (M : RState) (g : RFiber) (edits : List (FiberEdit Err Defect FiberId Ann)), g.frame.current = f.frame.current →
      prepareIterR ⟨M, g, y, .parked, [], edits⟩ = ⟨M, g, y, .parked, [], edits⟩) :
    SettlesTyped root rootTy w f.id rest (prepareIterR
      ⟨countdownMachine m target f.id,
        countdownFiber root f next' ⟨m.nextToken, some target, remaining, exits, resumeWith, failFast⟩,
        y, FiberAction.outcomeOf (countdownMachine m target f.id) true, [], [.observe target (.countdown f.id m.nextToken)]⟩) := by
  have wide := ev.typed.machine.wide
  have hmem : f ∈ (m.update f).fibers := rfiber?_mem ev.look
  have old := ev.typed.machine.fiber hmem
  let tok : Nat := m.nextToken
  let name := (interpR root.program).cancelName (interpR root.program).parkCancelName f.id tok
  let fr : RSaved := { f.frame with stack := .asyncFinalizer name :: .answer next' :: f.frame.stack }
  let p : RPending := ⟨tok, some target, remaining, exits, resumeWith, failFast⟩
  let gE : RFiber := { f with frame := fr, parked := .withGuard tok, pending := f.pending ++ [p] }
  let gP : RFiber := { f with frame := fr, dispatcher := f.dispatcher, parked := .withGuard tok,
                              pending := f.pending ++ [p], running := false }
  obtain ⟨⟨_, _, _⟩, hnext⟩ := countdownWalk_spec ({ m with nextToken := m.nextToken + 1 } : RState) targets []
  rw [hw] at hnext
  obtain ⟨tmem, ⟨t, hlook, _⟩, rsub⟩ := hnext target remaining rfl
  obtain ⟨ty, declared⟩ := ev.declared
  obtain ⟨_, _, _, _, _, _, _, prov⟩ := ev.code marker ty declared
  have ord0 : w.leHost (w.addToken f.id tok tt) :=
    addToken_leHost (valid_nextToken_fresh rootTy w (m.update f) ev.typed.machine.typed.1 f.id)
  have back : ∀ id t' ty', (w.addToken f.id tok tt).Θ id t' = some ty' → (id, t') ≠ (f.id, tok) →
      w.Θ id t' = some ty' := fun id t' ty' h ne => by rwa [addToken_Θ_other ne] at h
  have internal : ∀ k ∈ Guard.fiberKeys f, k ≠ (f.id, tok) :=
    fun k hk => key_ne_of_lt (wide.keysBelow k (fiberKeys_internal hmem hk))
  obtain ⟨_, _, _, _, ⟨c4⟩, _⟩ := runFiberOk_tok ord0 rfl back internal old.ok
  have ptargets : ∀ id ∈ p.waitingOn.toList ++ p.remaining, id ∈ targets := by
    intro id hid
    rcases List.mem_append.mp hid with h | h
    · rw [List.mem_singleton.mp h]
      exact tmem
    · exact rsub id h
  obtain ⟨ord, parked⟩ := ev.park_fresh tt row flag covered fr f.dispatcher p
    (fun ty' d => mHostStack_parkFinalizer root f.id tok (frame ty' d)) ⟨prov.recorded, prov.deferred⟩
    rfl (fun id hid => tbelow id (ptargets id hid)) request marker
    (fun b hb t' ht' => (c4 b hb).c0 t' ht') (fun k hk => Or.inl (List.mem_append_right _ hk))
  have hstuck : (countdownMachine m target f.id).stuck = none := ev.live
  rw [outcomeOf_parked hstuck, glue _ (countdownFiber root f next' p) _ rfl]
  refine ⟨w.addToken f.id tok tt, ord, ?_⟩
  have found : ∃ old, (countdownMachine m target f.id).fiber? gE.id = some old := by
    change ∃ old, m.fiber? f.id = some old
    have look := ev.look
    rw [rfiber?_update] at look
    cases h : m.fiber? f.id with
    | none => rw [h] at look; cases look
    | some old => exact ⟨old, rfl⟩
  obtain ⟨previous, previousLook⟩ := found
  rw [settle_observe_park previousLook]
  have raceOff : ∀ (M : RState), M.races = (m.update f).races → ∀ r race, M.race? r = some race →
      (race.host, race.token) ∉ Guard.observerKeys (.countdown f.id tok) := by
    intro M hM r race hr hk
    rw [show Guard.observerKeys (.countdown f.id tok) = [(f.id, tok)] from rfl,
      List.mem_singleton] at hk
    have mem : race ∈ (m.update f).races := by
      rw [← hM]
      exact List.mem_of_find?_eq_some hr
    exact key_ne_of_lt (wide.keysBelow _ (raceKey_internal mem)) hk
  simp only [settle, settleOutcome, List.nil_append]
  split
  · rename_i hd
    let gD : RFiber := { f with frame := fr, parked := .notParked, pending := [] }
    let Md : RState := ({ (m.update f) with nextToken := m.nextToken + 1 } : RState).update gD
    obtain ⟨_, unparked⟩ := ev.unpark_fresh tt row flag covered fr
      (fun ty' d => mHostStack_parkFinalizer root f.id tok (frame ty' d)) ⟨prov.recorded, prov.deferred⟩
      hd marker y
    have lookD : Md.fiber? f.id = some gD := rfiber?_update_self (f := f) ev.look rfl
    have added := configTyped_observe unparked target (.countdown f.id tok)
      (fun k hk => by
        rw [show Guard.observerKeys (.countdown f.id tok) = [(f.id, tok)] from rfl,
          List.mem_singleton] at hk
        subst hk
        exact ⟨Nat.lt_succ_self _, requestOfR_of_not_parked lookD (fun h => nomatch h), old.below⟩)
      (raceOff Md rfl) (fun t htM => by
        show CountdownAt _ (Md.update {t with observers := t.observers ++ [.countdown f.id tok]}) f.id tok _
        unfold CountdownAt
        rw [rfiber?_update, lookD, Option.map_some]
        dsimp only
        by_cases same : gD.id = t.id
        · rw [if_pos same]
          have eq : t = gD := rfiber?_same lookD htM same.symm
          subst t
          exact trivial
        · rw [if_neg same]
          exact trivial)
    refine configTyped_observe_congr (M := Md) (M' := (countdownMachine m target f.id).update gD) ?_ rfl rfl rfl rfl rfl rfl target _ added
    change (m.update gD).fibers = ((m.update f).update gD).fibers
    rw [rupdate_rupdate m (f := f) (g := gD) rfl]
  · let Mp : RState := ({ (m.update f) with nextToken := m.nextToken + 1 } : RState).update gP
    have lookP : Mp.fiber? f.id = some gP := rfiber?_update_self (f := f) ev.look rfl
    have hpend : f.pending = [] := by
      have notParked : f.parked = .notParked := by
        cases hp : f.parked with
        | notParked => rfl
        | withGuard _ =>
          have idle := old.parkedIdle (by rw [hp]; exact fun h => nomatch h)
          rw [ev.running] at idle
          cases idle
      have shape := old.pendingShape
      unfold Guard.PendingShape at shape
      rw [notParked] at shape
      exact shape
    have found : gP.pending.find? (fun q => q.token = tok) = some p := by
      show (f.pending ++ [p]).find? (fun q => q.token = tok) = some p
      rw [hpend, List.nil_append, List.find?_cons, decide_eq_true (show p.token = tok from rfl)]
    have colsW : ∀ id ∈ targets, FiberColumnsBelow (w.addToken f.id tok tt) id a e :=
      fun id hid => fiberColumnsBelow_ext (fun _ _ d => ord.1.2.1 _ _ d) (cols id hid)
    have added := configTyped_observe parked target (.countdown f.id tok)
      (fun k hk => by
        rw [show Guard.observerKeys (.countdown f.id tok) = [(f.id, tok)] from rfl,
          List.mem_singleton] at hk
        subst hk
        refine ⟨Nat.lt_succ_self _, ?_, old.below⟩
        rw [requestOfR_of_parked lookP rfl]
        exact request)
      (raceOff Mp rfl) (fun t htM => by
        show CountdownAt _ (Mp.update {t with observers := t.observers ++ [.countdown f.id tok]}) f.id tok _
        have payload : ∀ M source, source = target →
            ∃ a' e' tt', CountdownPayload (w.addToken f.id tok tt) M f.id p a' e' tt' ∧
              FiberColumnsBelow (w.addToken f.id tok tt) source a' e' := by
          intro M source same
          exact ⟨a, e, tt,
            ⟨addToken_Θ_self, fun ex hex => strongExit_mono _ _ _ _ ord (exitsOk ex hex),
              fun id hid fiber hfib => by
                rw [rfiber?_id hfib]
                exact colsW id (ptargets id hid), resumeOk⟩,
            by rw [same]; exact colsW target tmem⟩
        unfold CountdownAt
        rw [rfiber?_update, lookP, Option.map_some]
        dsimp only
        by_cases same : gP.id = t.id
        · rw [if_pos same]
          have eq : t = gP := rfiber?_same lookP htM same.symm
          subst t
          change (match gP.pending.find? (fun q => q.token = tok) with | none => True | some _ => _)
          rw [found]
          exact payload _ _ (rfiber?_id htM)
        · rw [if_neg same]
          change (match gP.pending.find? (fun q => q.token = tok) with | none => True | some _ => _)
          rw [found]
          exact payload _ _ (rfiber?_id htM))
    refine configTyped_observe_congr (M := Mp) (M' := (countdownMachine m target f.id).update gP) ?_ rfl rfl rfl rfl rfl rfl target _ added
    change (m.update gP).fibers = ((m.update f).update gP).fibers
    rw [rupdate_rupdate m (f := f) (g := gP) rfl]

/-- **A positional countdown's park** (`fiberPre`'s positional arm of `awaitAll` and
`awaitAllFailFast`: a tuple certificate of per-target exit columns, which `Layer.merge`'s siblings
use): as `Evaluating.countdown_parks`, the record resuming with the exits at the tuple of the
targets' columns. Planned: `J`'s countdown payload holds one pair of columns for every target, so
it cannot type this record; a positional payload must carry the columns in the targets' order.
`J` then admits a stale or a duplicate countdown firing that would append past them (seat B's
finding, 2026-10-12). Neither rc.112 nor 4.0.1 fires a target's observer twice (`fiberAwaitAll`,
`internal/effect.ts:779-813`, the same text in 4.0.1), so the proof needs `J` to say that each
countdown key has at most one firing to come.
Consumer: `awaitAllParks`, `awaitAllFailFastParks`. -/
@[semantics "reactive-scheduling" (requirement := R9)]
proof_goal Evaluating.countdown_parks_positional {root : ProgramSource} {rootTy : EffTy}
    {w : World} {m : RState} {rest : List RCmd} {f : RFiber} {y : Bool}
    (ev : Evaluating root rootTy w m rest f y)
    (marker : raceRegistrationR f.frame.current = none)
    (request : externalRequestR f.frame.current = none)
    {targets : List FiberId} (failFast : Bool) {exits : List ExitV}
    {target : FiberId} {remaining : List FiberId}
    (hw : countdownWalk ({ m with nextToken := m.nextToken + 1 } : RState) targets [] =
      (exits, some (target, remaining)))
    (tbelow : ∀ id ∈ targets, id.value < m.nextId) (cols : FiberId → Ty × Ty)
    (colsOk : ∀ id ∈ targets, FiberColumnsBelow w id (cols id).1 (cols id).2)
    (next' : ExitV → RProgram) (row : Env.Requirement) (flag : Bool)
    (covered : f.context.services.Satisfies row)
    (frame : ∀ ty, w.Γ f.id = some ty → MHostStack root w (m.update f) f.id
      (((EffTy.pure (.tuple (targets.map fun t => .exitOf (cols t).1 (cols t).2)), row, row) :
        AmbientPosition), f.frame.interruptible) (finalPos ty flag) (.answer next' :: f.frame.stack))
    (glue : ∀ (M : RState) (g : RFiber) (edits : List (FiberEdit Err Defect FiberId Ann)),
      g.frame.current = f.frame.current →
      prepareIterR ⟨M, g, y, .parked, [], edits⟩ = ⟨M, g, y, .parked, [], edits⟩) :
    SettlesTyped root rootTy w f.id rest (prepareIterR
      ⟨countdownMachine m target f.id,
        countdownFiber root f next' ⟨m.nextToken, some target, remaining, exits, .exitsValue, failFast⟩,
        y, FiberAction.outcomeOf (countdownMachine m target f.id) true, [],
        [.observe target (.countdown f.id m.nextToken)]⟩)

/-- The exits a walk collects are typed at columns every target's declaration is below. -/
theorem Evaluating.walk_exitOk {root : ProgramSource} {rootTy : EffTy} {w : World} {m : RState}
    {rest : List RCmd} {f : RFiber} {y : Bool} (ev : Evaluating root rootTy w m rest f y)
    {targets : List FiberId} {a e : Ty} (cols : ∀ t ∈ targets, FiberColumnsBelow w t a e) {k : Nat}
    {exits : List ExitV} {live : Option (FiberId × List FiberId)}
    (hw : countdownWalk ({ m with nextToken := k } : RState) targets [] = (exits, live)) :
    ∀ ex ∈ exits, ExitOk w ⟨a, e, Env.Requirement.empty⟩ ex := by
  intro ex hex
  obtain ⟨⟨extra, hextra, found⟩, _⟩ := countdownWalk_spec ({ m with nextToken := k } : RState) targets []
  rw [hw, List.nil_append] at hextra
  have e' : exits = extra := hextra
  rw [e'] at hex
  obtain ⟨t, ht, g, hg, gx⟩ := found ex hex
  obtain ⟨fty, d, ha, he⟩ := cols t ht
  exact exitOk_subN (ev.target_exit (t := g) hg gx fty d) ha he

/-- A declared fiber is below `nextId`. -/
theorem Evaluating.declared_below {root : ProgramSource} {rootTy : EffTy} {w : World} {m : RState}
    {rest : List RCmd} {f : RFiber} {y : Bool} (ev : Evaluating root rootTy w m rest f y)
    {id : FiberId} (h : (w.Γ id).isSome = true) : id.value < m.nextId := by
  obtain ⟨x, hx, hid⟩ := List.mem_map.mp ((ev.typed.machine.wide.fibers id).mp h)
  rw [← hid]
  exact (ev.typed.machine.fiber hx).below

theorem prepareIterR_awaitAll {edits : List (FiberEdit Err Defect FiberId Ann)} {M : RState} {g : RFiber} {y : Bool} {targets : List FiberId}
    {k : (FiberOp.awaitAll targets).answer → RProgram}
    (hg : g.frame.current = .vis (.inr (.awaitAll targets)) k) :
    prepareIterR ⟨M, g, y, .parked, [], edits⟩ = ⟨M, g, y, .parked, [], edits⟩ := by
  rcases g with ⟨id, ⟨cur, stk, i, ic, di⟩, running, parked, pending, finalizing, exit, count,
    maxOps, prevent, yo, observers, children, dispatcher, context⟩
  change cur = _ at hg
  subst hg
  rfl

theorem prepareIterR_awaitAllFailFast {edits : List (FiberEdit Err Defect FiberId Ann)} {M : RState} {g : RFiber} {y : Bool} {targets : List FiberId}
    {k : (FiberOp.awaitAllFailFast targets).answer → RProgram}
    (hg : g.frame.current = .vis (.inr (.awaitAllFailFast targets)) k) :
    prepareIterR ⟨M, g, y, .parked, [], edits⟩ = ⟨M, g, y, .parked, [], edits⟩ := by
  rcases g with ⟨id, ⟨cur, stk, i, ic, di⟩, running, parked, pending, finalizing, exit, count,
    maxOps, prevent, yo, observers, children, dispatcher, context⟩
  change cur = _ at hg
  subst hg
  rfl

theorem prepareIterR_awaitNewChildren {edits : List (FiberEdit Err Defect FiberId Ann)} {M : RState} {g : RFiber} {y : Bool} {snapshot : List FiberId}
    {k : (FiberOp.awaitNewChildren snapshot).answer → RProgram}
    (hg : g.frame.current = .vis (.inr (.awaitNewChildren snapshot)) k) :
    prepareIterR ⟨M, g, y, .parked, [], edits⟩ = ⟨M, g, y, .parked, [], edits⟩ := by
  rcases g with ⟨id, ⟨cur, stk, i, ic, di⟩, running, parked, pending, finalizing, exit, count,
    maxOps, prevent, yo, observers, children, dispatcher, context⟩
  change cur = _ at hg
  subst hg
  rfl

/-- **`awaitAll`'s park** (`CountdownParks`): the record resumes with the exits at the
certificate's columns (the pre's, raised to the checker's order). -/
theorem awaitAllParks (root : ProgramSource) (rootTy : EffTy) (targets : List FiberId) :
    ∀ (w : World) (m : RState) (rest : List RCmd) (f : RFiber) (y : Bool)
      (next : (FiberOp.awaitAll targets).answer → RProgram) (exits : List ExitV) (target : FiberId)
      (remaining : List FiberId),
      Evaluating root rootTy w m rest f y → f.frame.current = .vis (.inr (.awaitAll targets)) next →
      countdownWalk ({ m with nextToken := m.nextToken + 1 } : RState) targets [] =
        (exits, some (target, remaining)) →
      SettlesTyped root rootTy w f.id rest
        (prepareIterR (evaluateFiberR (interpRAt root.program m.completedExits) m f y
          (.awaitAll targets) next)) := by
  intro w m rest f y next exits target remaining ev hc hw
  obtain ⟨ty, declared⟩ := ev.declared
  obtain ⟨row, ⟨q, b⟩, flag, covered, bit, current, stack, _⟩ :=
    ev.code (by rw [hc]; rfl) ty declared
  change b = f.frame.interruptible at bit
  subst bit
  change AmbientProg root w row q f.frame.current at current
  rw [hc] at current
  obtain ⟨cert, pre, typedNext, entry, wf⟩ := ambientProg_fiber_inv current
    (fun _ h => nomatch h) (fun _ h => nomatch h) (fun _ h => nomatch h) (fun _ _ _ h => nomatch h)
  have same : ∀ ty', w.Γ f.id = some ty' → ty' = ty :=
    fun _ h => Option.some.inj (h.symm.trans declared)
  have below : ∀ id ∈ targets, id.value < m.nextId := fun id hid => by
    rcases pre with ⟨_, _, _, cols⟩ | ⟨_, _, cols⟩
    · obtain ⟨fty, d, _, _⟩ := cols id hid
      exact ev.declared_below (by rw [d]; rfl)
    · obtain ⟨fty, d, _, _⟩ := cols id hid
      exact ev.declared_below (by rw [d]; rfl)
  show SettlesTyped root rootTy w f.id rest (prepareIterR
    (FiberAction.awaitAll (interpRAt root.program m.completedExits) m (saveAnswerR f (seqR next)) y
      targets false))
  simp only [FiberAction.awaitAll, countdownParkEdits, hw]
  rcases pre with ⟨a, e, hcert, cols⟩ | ⟨cols, hcert, hall⟩
  · have colsN : ∀ id ∈ targets, FiberColumnsBelow w id a e := fun id hid => by
      obtain ⟨fty, d, ha, he⟩ := cols id hid
      exact ⟨fty, d, Ty.sub_le_subN ha, Ty.sub_le_subN he⟩
    exact ev.countdown_parks (by rw [hc]; rfl) (by rw [hc]; rfl) .exitsValue false hw below
      colsN (ev.walk_exitOk colsN hw) rfl (seqR next) row flag covered
      (fun ty' d => by
        rw [same ty' d]
        exact .cons (.inl (ambient_seqFrame (Bounds.subN_never _)
          (fun w' o v hv => typedNext w' o v (show Fits w' v cert by rw [hcert]; exact hv)) entry wf))
          stack)
      (fun _ _ _ hg => prepareIterR_awaitAll (hg.trans hc))
  · have colsN : ∀ id ∈ targets, FiberColumnsBelow w id (cols id).1 (cols id).2 := fun id hid => by
      obtain ⟨fty, d, ha, he⟩ := hall id hid
      exact ⟨fty, d, Ty.sub_le_subN ha, Ty.sub_le_subN he⟩
    exact ev.countdown_parks_positional (by rw [hc]; rfl) (by rw [hc]; rfl) false hw below cols colsN
      (seqR next) row flag covered
      (fun ty' d => by
        rw [same ty' d]
        exact .cons (.inl (ambient_seqFrame (Bounds.subN_never _)
          (fun w' o v hv => typedNext w' o v (show Fits w' v cert by rw [hcert]; exact hv)) entry wf))
          stack)
      (fun _ _ _ hg => prepareIterR_awaitAll (hg.trans hc))

/-- **`awaitAllFailFast`'s park** (`CountdownParks`): `awaitAll`'s, the record fail-fast. -/
theorem awaitAllFailFastParks (root : ProgramSource) (rootTy : EffTy) (targets : List FiberId) :
    ∀ (w : World) (m : RState) (rest : List RCmd) (f : RFiber) (y : Bool)
      (next : (FiberOp.awaitAllFailFast targets).answer → RProgram) (exits : List ExitV)
      (target : FiberId) (remaining : List FiberId),
      Evaluating root rootTy w m rest f y →
      f.frame.current = .vis (.inr (.awaitAllFailFast targets)) next →
      countdownWalk ({ m with nextToken := m.nextToken + 1 } : RState) targets [] =
        (exits, some (target, remaining)) →
      SettlesTyped root rootTy w f.id rest
        (prepareIterR (evaluateFiberR (interpRAt root.program m.completedExits) m f y
          (.awaitAllFailFast targets) next)) := by
  intro w m rest f y next exits target remaining ev hc hw
  obtain ⟨ty, declared⟩ := ev.declared
  obtain ⟨row, ⟨q, b⟩, flag, covered, bit, current, stack, _⟩ :=
    ev.code (by rw [hc]; rfl) ty declared
  change b = f.frame.interruptible at bit
  subst bit
  change AmbientProg root w row q f.frame.current at current
  rw [hc] at current
  obtain ⟨cert, pre, typedNext, entry, wf⟩ := ambientProg_fiber_inv current
    (fun _ h => nomatch h) (fun _ h => nomatch h) (fun _ h => nomatch h) (fun _ _ _ h => nomatch h)
  have same : ∀ ty', w.Γ f.id = some ty' → ty' = ty :=
    fun _ h => Option.some.inj (h.symm.trans declared)
  have below : ∀ id ∈ targets, id.value < m.nextId := fun id hid => by
    rcases pre with ⟨_, _, _, cols⟩ | ⟨_, _, cols⟩
    · obtain ⟨fty, d, _, _⟩ := cols id hid
      exact ev.declared_below (by rw [d]; rfl)
    · obtain ⟨fty, d, _, _⟩ := cols id hid
      exact ev.declared_below (by rw [d]; rfl)
  show SettlesTyped root rootTy w f.id rest (prepareIterR
    (FiberAction.awaitAll (interpRAt root.program m.completedExits) m (saveAnswerR f (seqR next)) y
      targets true))
  simp only [FiberAction.awaitAll, countdownParkEdits, hw]
  rcases pre with ⟨a, e, hcert, cols⟩ | ⟨cols, hcert, hall⟩
  · have colsN : ∀ id ∈ targets, FiberColumnsBelow w id a e := fun id hid => by
      obtain ⟨fty, d, ha, he⟩ := cols id hid
      exact ⟨fty, d, Ty.sub_le_subN ha, Ty.sub_le_subN he⟩
    exact ev.countdown_parks (by rw [hc]; rfl) (by rw [hc]; rfl) .exitsValue true hw below
      colsN (ev.walk_exitOk colsN hw) rfl (seqR next) row flag covered
      (fun ty' d => by
        rw [same ty' d]
        exact .cons (.inl (ambient_seqFrame (Bounds.subN_never _)
          (fun w' o v hv => typedNext w' o v (show Fits w' v cert by rw [hcert]; exact hv)) entry wf))
          stack)
      (fun _ _ _ hg => prepareIterR_awaitAllFailFast (hg.trans hc))
  · have colsN : ∀ id ∈ targets, FiberColumnsBelow w id (cols id).1 (cols id).2 := fun id hid => by
      obtain ⟨fty, d, ha, he⟩ := hall id hid
      exact ⟨fty, d, Ty.sub_le_subN ha, Ty.sub_le_subN he⟩
    exact ev.countdown_parks_positional (by rw [hc]; rfl) (by rw [hc]; rfl) true hw below cols colsN
      (seqR next) row flag covered
      (fun ty' d => by
        rw [same ty' d]
        exact .cons (.inl (ambient_seqFrame (Bounds.subN_never _)
          (fun w' o v hv => typedNext w' o v (show Fits w' v cert by rw [hcert]; exact hv)) entry wf))
          stack)
      (fun _ _ _ hg => prepareIterR_awaitAllFailFast (hg.trans hc))

/-- **`awaitNewChildren`'s park** (`CountdownParks`): the record resumes with `void`, its
columns `unknown` (every child is declared, `FiberTyped.children`). -/
theorem awaitNewChildrenParks (root : ProgramSource) (rootTy : EffTy) (snapshot : List FiberId) :
    ∀ (w : World) (m : RState) (rest : List RCmd) (f : RFiber) (y : Bool)
      (next : (FiberOp.awaitNewChildren snapshot).answer → RProgram) (exits : List ExitV)
      (target : FiberId) (remaining : List FiberId),
      Evaluating root rootTy w m rest f y →
      f.frame.current = .vis (.inr (.awaitNewChildren snapshot)) next →
      countdownWalk ({ m with nextToken := m.nextToken + 1 } : RState)
        ((saveAnswerR f (seqR next)).children.filter fun c => !(snapshot.contains c)) [] =
        (exits, some (target, remaining)) →
      SettlesTyped root rootTy w f.id rest
        (prepareIterR (evaluateFiberR (interpRAt root.program m.completedExits) m f y
          (.awaitNewChildren snapshot) next)) := by
  intro w m rest f y next exits target remaining ev hc hw
  obtain ⟨ty, declared⟩ := ev.declared
  obtain ⟨row, ⟨q, b⟩, flag, covered, bit, current, stack, _⟩ :=
    ev.code (by rw [hc]; rfl) ty declared
  change b = f.frame.interruptible at bit
  subst bit
  change AmbientProg root w row q f.frame.current at current
  rw [hc] at current
  obtain ⟨_, _, typedNext, entry, wf⟩ := ambientProg_fiber_inv current
    (fun _ h => nomatch h) (fun _ h => nomatch h) (fun _ h => nomatch h) (fun _ _ _ h => nomatch h)
  have same : ∀ ty', w.Γ f.id = some ty' → ty' = ty :=
    fun _ h => Option.some.inj (h.symm.trans declared)
  have kids : ∀ c ∈ f.children, (w.Γ c).isSome = true :=
    (ev.typed.machine.fiber (rfiber?_mem ev.look)).children
  have colsU : ∀ id ∈ (saveAnswerR f (seqR next)).children.filter (fun c => !(snapshot.contains c)),
      FiberColumnsBelow w id .unknown .unknown := fun id hid => by
    obtain ⟨fty, d⟩ := Option.isSome_iff_exists.mp (kids id (List.mem_filter.mp hid).1)
    exact ⟨fty, d, subN_unknown _, subN_unknown _⟩
  show SettlesTyped root rootTy w f.id rest (prepareIterR
    (FiberAction.awaitNewChildren (interpRAt root.program m.completedExits) m
      (saveAnswerR f (seqR next)) y snapshot))
  simp only [FiberAction.awaitNewChildren, countdownParkEdits, hw]
  exact ev.countdown_parks (by rw [hc]; rfl) (by rw [hc]; rfl) .void false hw
    (fun id hid => ev.declared_below (kids id (List.mem_filter.mp hid).1))
    colsU (ev.walk_exitOk colsU hw) rfl (seqR next) row flag covered
    (fun ty' d => by
      rw [same ty' d]
      exact .cons (.inl (Evaluating.unitAnswerFrame (fun w' o ans post => typedNext w' o ans post)
        entry wf)) stack)
    (fun _ _ _ hg => prepareIterR_awaitNewChildren (hg.trans hc))

/-- **`awaitAll`** (`fiberAwaitAll`, `internal/effect.ts:779-813`). -/
theorem clause_awaitAll (root : ProgramSource) (rootTy : EffTy) (targets : List FiberId) :
    FiberClauseKeeps root rootTy (.awaitAll targets) :=
  clause_awaitAll_of_parks root rootTy targets (awaitAllParks root rootTy targets)

/-- **`awaitAllFailFast`** (`Effect.all` with concurrency, S5 §7.4). -/
theorem clause_awaitAllFailFast (root : ProgramSource) (rootTy : EffTy) (targets : List FiberId) :
    FiberClauseKeeps root rootTy (.awaitAllFailFast targets) :=
  clause_awaitAllFailFast_of_parks root rootTy targets (awaitAllFailFastParks root rootTy targets)

/-- **`awaitNewChildren`** (`awaitAllChildren`'s count-down over the children not in the snapshot). -/
theorem clause_awaitNewChildren (root : ProgramSource) (rootTy : EffTy) (snapshot : List FiberId) :
    FiberClauseKeeps root rootTy (.awaitNewChildren snapshot) :=
  clause_awaitNewChildren_of_parks root rootTy snapshot (awaitNewChildrenParks root rootTy snapshot)

end Effect4.Program.Typed
