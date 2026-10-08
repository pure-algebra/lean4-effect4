import Effect4.Laws.Program.Typed.Commands.Clauses.Park

/-!
# Laws.Program.Typed.Commands.Clauses.Async — the `async` clause (M6)

Concept 4 (the configuration invariant `I`); question `deliver_preserves` and
`loop_preserves`, through `evaluate_keeps`, which reads `∀ op, FiberClauseKeeps root rootTy op`;
this file supplies the `.async` row (`evaluateFiberR`'s `async` arm, `Laws/Program/EvaluateR.lean`,
transcribing `internal/effect.ts`'s `callback` registration). The fiber saves the answer frame,
takes the fresh token, and runs the interpreter's registration (`interpR`'s `registerAsync`): a
Deferred's `_await` (`Deferred.ts:173-177`) answers at once from a completed cell or adds the waiter
to the cell's wake list; a sleep (`TestClock`'s `sleep`) adds the sleeper to the timer wake list; a
host registration changes nothing. With no immediate answer the fiber pushes the registration's
cancel frame and parks on the token.

The registration's store edit is typed by `configTyped_register`: the wake columns `J` carries
(decisions row 134 (a), (b)) gain the fiber's key, declared at the certificate, which `asyncPre`
puts above the sleep's `void` or the cell's columns. A host row parks with its external request
(`Evaluating.park_fresh_request`): the request's key is the fresh one, so no internal or queued key
meets it. Not established here: that a parked fiber is ever resumed (progress), the host's answer
to an external registration (the host boundary, `docs/core/host-boundary.md`).
-/

set_option autoImplicit false
namespace Effect4.Program.Typed
open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Sched Effect4.Program.Denote
open Effect4.Laws.Effects Contracts

/-! ## The registration rows -/

/-- What `asyncPre` admits, by row: a sleep at a certificate `void` fits, a Deferred's await at a
certificate above the cell's declared columns, a host row, a host slot. -/
theorem asyncPre_cases {root : ProgramSource} {w : World} {register : EffName} {cert : EffTy}
    (pre : asyncPre root w register cert) :
    (∃ millis, register = .store (.registerSleep millis) ∧ Ty.unit.sub cert.answer = true) ∨
    (∃ cell a e, (register = .registerAwait cell ∨ register = .store (.registerAwait cell)) ∧
      w.«Π» cell = some (a, e) ∧ a.sub cert.answer = true ∧ e.sub cert.error = true) ∨
    (∃ op request origin, register = .external op request origin) ∨
    (∃ x, register = .store (.externalRegister x)) := by
  unfold asyncPre at pre
  split at pre
  · exact Or.inl ⟨_, rfl, pre⟩
  · obtain ⟨a, e, hc, ha, he⟩ := pre
    exact Or.inr (Or.inl ⟨_, a, e, Or.inl rfl, hc, ha, he⟩)
  · obtain ⟨a, e, hc, ha, he⟩ := pre
    exact Or.inr (Or.inl ⟨_, a, e, Or.inr rfl, hc, ha, he⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨_, _, _, rfl⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨_, rfl⟩))
  · exact pre.elim

/-! ## The cancel frames (`asyncFinalizer` over `cancelAwait` and `cancelSleep`)

At the term instance a Deferred's cancel program is the store row `deferredAwaitCleanup` and a
sleep's is `sleepCancel` (`denoteCancel`, `denoteStoreCancel`, `Laws/Program/InterpR.lean`), each
answering `unit` and never failing with a typed error, then the incoming failure: the frame passes
the token's type through (`frameProtocols`' `asyncFinalizer` clause). -/

/-- One `unit`-answering store row, then the incoming failure, is typed at the failure's type. -/
theorem storeCancelThenFail_typed (root : ProgramSource) {w : World} {ty : EffTy} {op : SyncOp}
    (cert : StoreCert op) (pre : storePre root w op cert)
    (unit : ∀ w' ans, storePost w' op cert ans → ans = Val.unit) {cause : CauseV}
    (typed : ExitOk w ty (.failure cause)) :
    TypedProg root w ty ((guardR .onSuccess (storeR op)).bind (seqR fun _ => .pure (.failure cause))) := by
  refine seq_typed_clean root (mid := EffTy.pure .unit) ?_
    (fun w' o _ _ => TypedProg.pure (strongExit_mono _ _ _ _ o typed)) rfl
  refine TypedProg.store cert pre ?_
  intro w' _ ans post
  rw [unit w' ans post]
  exact TypedProg.pure ⟨trivial, trivial⟩

/-- A cancel frame whose program is typed at every later world, pushed on a host stack. -/
theorem hostStack_cancelFrame (root : ProgramSource) {w : World} {m : RState} {ty final : EffTy}
    {name : EffName}
    (cancel : ∀ w', w.leHost w' → ∀ cause, ExitOk w' ty (.failure cause) →
      TypedProg root w' ty ((interpR root.program).cancelThenFail name cause))
    {owner : FiberId} {stack : List ScopeFrame} (h : HostStack root w m owner ty final stack) :
    HostStack root w m owner ty final (.asyncFinalizer name :: stack) :=
  hostStack_push (.asyncFinalizer _ fun _ o => ⟨rfl, fun w'' o' cause typed _ =>
    cancel w'' (leHost_trans _ _ _ o o') cause typed⟩) h

/-- The cancel frame of a sleep (`clearTimeout`, `internal/effect.ts:6063`). -/
theorem hostStack_sleepCancel (root : ProgramSource) {w : World} {m : RState} {ty final : EffTy}
    (host : FiberId) (token : Nat) {owner : FiberId} {stack : List ScopeFrame}
    (h : HostStack root w m owner ty final stack) :
    HostStack root w m owner ty final
      (.asyncFinalizer ((interpR root.program).cancelName (.store .cancelSleep) host token) :: stack) :=
  hostStack_cancelFrame root (name := (interpR root.program).cancelName (.store .cancelSleep) host token)
    (fun _ _ _ typed => storeCancelThenFail_typed root (op := .sleepCancel host token) PUnit.unit
      trivial (fun _ _ post => post) typed) h

/-- The cancel frame of a Deferred's await (`Deferred.ts:178-185`), at a declared cell; both
spellings of the registration name the same cleanup row. -/
theorem hostStack_awaitCancel (root : ProgramSource) {w : World} {m : RState} {ty final : EffTy}
    {cell : DeferredKey} (declared : (w.«Π» cell).isSome = true) (host : FiberId) (token : Nat)
    {owner : FiberId} {stack : List ScopeFrame} (h : HostStack root w m owner ty final stack) :
    HostStack root w m owner ty final
        (.asyncFinalizer ((interpR root.program).cancelName (.cancelAwait cell) host token) :: stack) ∧
      HostStack root w m owner ty final
        (.asyncFinalizer ((interpR root.program).cancelName (.store (.cancelAwait cell)) host token) ::
          stack) := by
  have cancel : ∀ w', w.leHost w' → ∀ cause, ExitOk w' ty (.failure cause) →
      TypedProg root w' ty ((guardR .onSuccess (storeR (.deferredAwaitCleanup cell host token))).bind
        (seqR fun _ => .pure (.failure cause))) := fun _ o _ typed =>
    storeCancelThenFail_typed root (op := .deferredAwaitCleanup cell host token) PUnit.unit
      (theta_isSome' o declared) (fun _ _ post => post) typed
  exact ⟨hostStack_cancelFrame root
      (name := (interpR root.program).cancelName (.cancelAwait cell) host token) cancel h,
    hostStack_cancelFrame root
      (name := (interpR root.program).cancelName (.store (.cancelAwait cell)) host token) cancel h⟩
where
  theta_isSome' {w w' : World} (o : w.leHost w') {cell : DeferredKey}
      (h : (w.«Π» cell).isSome = true) : (w'.«Π» cell).isSome = true := by
    obtain ⟨types, ht⟩ := Option.isSome_iff_exists.mp h
    rw [o.1.2.2.1 _ _ ht]
    rfl

/-! ## The glue leaves a parked `async` -/

theorem prepareIterR_async {M : RState} {g : RFiber} {y : Bool} {register : EffName} {request : Val}
    {k : (FiberOp.async register request).answer → RProgram}
    (hg : g.frame.current = .vis (.inr (.async register request)) k) :
    prepareIterR ⟨M, g, y, .parked, []⟩ = ⟨M, g, y, .parked, []⟩ := by
  rcases g with ⟨id, ⟨cur, stk, i, ic, di⟩, running, parked, pending, finalizing, exit, count,
    maxOps, prevent, yo, observers, children, dispatcher, context⟩
  change cur = _ at hg
  subst hg
  rfl

/-! ## The registration's store edit -/

/-- A store edit that keeps the heap, the scopes, the memo world and the Deferred cells' count,
with its timers well-formed, is well-formed (`wf_cells` with the timers moved). -/
theorem wf_register {t s : Stores} (wf : t.WF) (le : t.le s) (refs : s.refs = t.refs)
    (scopes : s.scopes = t.scopes) (memo : s.memo = t.memo)
    (cellCount : s.deferreds.cells.length = t.deferreds.cells.length) (timers : s.timers.WF) :
    s.WF := by
  obtain ⟨hrefs, hscopes, hmemo, _⟩ := wf
  refine ⟨fun v hv => ?_, fun e he => ?_, fun mm hm entry he => ?_, timers⟩
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

/-- **A registration's store edit keeps `I`** at the world over the edited store
(`configTyped_frame`, except that the wake columns may gain one key `k0`): the edit grows the
store, keeps the heap, the external spellings, the due list and every cell's completion; the new
wake lists are typed at the world (the registration's key declared at a type its demand admits,
decisions row 134 (a), (b)); the new key is below the counter and unrequested. -/
theorem configTyped_register {root : ProgramSource} {rootTy : EffTy} {w : World} {M : RState}
    {q : List RCmd} (typed : ConfigTyped root rootTy w M q) {s : Stores}
    (le : M.state.le s) (refs : s.refs = M.state.refs)
    (cellCount : s.deferreds.cells.length = M.state.deferreds.cells.length)
    (cells : ∀ key c', s.deferreds.cellAt key = some c' →
      ∃ c, M.state.deferreds.cellAt key = some c ∧ c'.completion = c.completion)
    (externals : s.externals = M.state.externals) (due : s.deferreds.due = M.state.deferreds.due)
    (wf : s.WF) (stores : StoresOk (preds root) { w with state := s } Expect.root s)
    (timers : WakeTyped w SleepDemand s.timers.wake)
    (waiters : ∀ key cell, s.deferreds.cellAt key = some cell → ∀ a e, w.«Π» key = some (a, e) →
      WakeTyped w (AwaitDemand a e) cell.wake)
    {k0 : Guard.GuardKey} (keys : Guard.storeKeys s ⊆ Guard.storeKeys M.state ++ [k0])
    (below : k0.2 < M.nextToken) (free : requestOfR M k0.1 k0.2 = none) :
    w.leHost { w with state := s } ∧
      ConfigTyped root rootTy { w with state := s } { M with state := s } q := by
  obtain ⟨machine, code, queue⟩ := typed
  have wide := machine.wide
  have ord : w.leHost { w with state := s } :=
    leHost_cells (by rw [wide.state]; exact le) (by rw [refs, wide.state])
      (fun key c' h => by
        obtain ⟨c, hc, same⟩ := cells key c' h
        exact ⟨c, by rw [wide.state]; exact hc, same⟩)
      (by rw [externals, wide.state])
  have ext : Extends w.state.externals.allocated s.externals.allocated := by
    rw [externals, wide.state]
    exact fun _ _ h => h
  have internal : ∀ k ∈ Guard.internalKeys ({ M with state := s } : RState),
      k ∈ Guard.internalKeys M ∨ k = k0 := by
    intro k hk
    rw [Guard.internalKeys_store_decomposition] at hk
    rw [Guard.internalKeys_store_decomposition]
    rcases List.mem_append.mp hk with h | h
    · rcases List.mem_append.mp h with h | h
      · rcases List.mem_append.mp (keys h) with h | h
        · exact Or.inl (List.mem_append_left _ (List.mem_append_left _ h))
        · exact Or.inr (List.mem_singleton.mp h)
      · exact Or.inl (List.mem_append_left _ (List.mem_append_right _ h))
    · exact Or.inl (List.mem_append_right _ h)
  have wide' : MachineWide root rootTy { w with state := s } { M with state := s } := by
    refine ⟨wide.ids, wide.fibers, fun key => ?_, fun key => ?_, wide.tokenBound, wide.tokenTargets,
      rfl, wf, ⟨fun i v hv ty hty => ?_, fun i cell hc types hty c hcomp => ?_⟩, wide.rootDeclared,
      fun r hr => ?_, stores, wide.fiberIds, wide.raceIds, wide.racesBelow, wide.raceHosts,
      fun k hk => ?_, wide.requestsBelow, fun fiber token r hr hk => ?_, wide.services,
      ⟨wide.live.running, fun o ho => wide.live.dueOwners o (by rw [← due]; exact ho)⟩, timers,
      waiters, wide.liveBelow, wide.sourceWF⟩
    · show (w.Ρ key).isSome = true ↔ key.index < s.refs.length
      rw [refs]
      exact wide.heap key
    · show (w.«Π» key).isSome = true ↔ key.index < s.deferreds.cells.length
      rw [cellCount]
      exact wide.promises key
    · have hv' : w.state.refs[i]? = some v := by
        change s.refs[i]? = some v at hv
        rw [wide.state, ← refs]
        exact hv
      exact value_transport w { w with state := s } ty v ext (wide.cells.1 i v hv' ty hty)
    · obtain ⟨c0, hc0, same⟩ := cells ⟨i⟩ cell hc
      rw [same] at hcomp
      have hc0' : w.state.deferreds.cells[i]? = some c0 := by
        rw [wide.state]
        exact hc0
      exact completion_transport w { w with state := s } types (fun _ _ h => h) ext c
        (wide.cells.2 i c0 hc0' types hty c hcomp)
    · obtain ⟨resultTy, payload⟩ := wide.races r hr
      exact ⟨resultTy, racePayload_world ord rfl rfl payload⟩
    · rcases internal k hk with h | rfl
      · exact wide.keysBelow k h
      · exact below
    · rcases internal _ hk with h | h
      · exact wide.requestsOwned fiber token r hr h
      · subst h
        have hr' : requestOfR M fiber token = some r := hr
        rw [free] at hr'
        cases hr'
  have view : ObsView M { M with state := s } :=
    ObsView.ofLookup (fun _ => rfl) (fun _ => rfl) (fun sc h => le.2.2.1 sc h)
  have ctl : ∀ id, (({ M with state := s } : RState).fiber? id).map ctlView =
      (M.fiber? id).map ctlView := fun _ => rfl
  exact ⟨ord, machineTyped_of wide'
    (fun x hx => fiberTyped_transport (fiberTyped_world ord rfl rfl (machine.fiber hx)) view
      (Nat.le_refl _) (Nat.le_refl _)),
    readCode_world ord rfl (readCode_races (m := M) rfl (racesKept_of_eq fun _ => rfl) code),
    queueOk_transport (queueOk_world ord rfl rfl queue) view (Nat.le_refl _)
      (fun c _ h => commandAuthority_view ctl view.races c h)
      (fun c _ h => commandDelivery_view ctl (racesKept_of_eq view.races) c h) (fun _ _ _ hr => hr)
      (Nat.le_refl _)⟩

/-- A Deferred key is its index. -/
theorem deferredKey_eq {k k' : DeferredKey} (h : k.index = k'.index) : k = k' := by
  cases k
  cases k'
  cases h
  rfl

/-- **A sleep's registration keeps `I`** (`TimerStore.sleep`, decisions row 134 (a)): the sleeper's
key, declared at a type `void` fits, joins the timer wake list. -/
theorem configTyped_sleep {root : ProgramSource} {rootTy : EffTy} {W : World} {M : RState}
    {q : List RCmd} (typed : ConfigTyped root rootTy W M q) {fiber : FiberId} {token : Nat}
    {tin : EffTy} (millis : ClockMillis) (declared : W.Θ fiber token = some tin)
    (sub : Ty.unit.sub tin.answer = true) (below : token < M.nextToken)
    (free : requestOfR M fiber token = none) :
    W.leHost { W with state := { M.state with timers := M.state.timers.sleep fiber token millis } } ∧
      ConfigTyped root rootTy
        { W with state := { M.state with timers := M.state.timers.sleep fiber token millis } }
        { M with state := { M.state with timers := M.state.timers.sleep fiber token millis } } q := by
  have wide := typed.machine.wide
  let s : Stores := { M.state with timers := M.state.timers.sleep fiber token millis }
  have le : M.state.le s :=
    ⟨Nat.le_refl _, Nat.le_refl _, fun _ h => h, Nat.le_refl _, fun _ h => h, Nat.le_refl _⟩
  have ord : W.leHost { W with state := s } :=
    leHost_cells (by rw [wide.state]; exact le) (by rw [wide.state])
      (fun key c' h => ⟨c', by rw [wide.state]; exact h, rfl⟩) (by rw [wide.state])
  have stores : StoresOk (preds root) { W with state := s } Expect.root s := by
    obtain ⟨c0, c1, c2, c3, c4, c5⟩ := storesOk_world ord rfl rfl rfl wide.stores
    exact ⟨c0, c1, c2, c3, c4, c5⟩
  have keys : Guard.storeKeys s ⊆ Guard.storeKeys M.state ++ [(fiber, token)] := by
    intro k hk
    unfold Guard.storeKeys at hk ⊢
    rcases List.mem_append.mp hk with h | h
    · rcases (Guard.wakeKeys_register_mem M.state.timers.wake fiber token _ k).mp h with h | rfl
      · exact List.mem_append_left _ (List.mem_append_left _ h)
      · exact List.mem_append_right _ (List.mem_singleton_self _)
    · exact List.mem_append_left _ (List.mem_append_right _ h)
  exact configTyped_register typed le rfl rfl (fun key c' h => ⟨c', h, rfl⟩) rfl rfl
    (wf_register wide.wf le rfl rfl rfl rfl (TimerStore.sleep_wf wide.wf.2.2.2 fiber token millis))
    stores (WakeTyped.register wide.timers _ ⟨tin, declared, sub⟩) wide.waiters keys below free

/-- The store a pending Deferred's `_await` leaves: the waiter appended to the cell's wake list. -/
abbrev awaitStore (s : Stores) (cell : DeferredKey) (c : DeferredCell) (fiber : FiberId)
    (token : Nat) : Stores :=
  { s with deferreds := s.deferreds.setCell cell { c with wake := c.wake.register fiber token () } }

/-- **A Deferred's registration keeps `I`** (`DeferredStore.register`'s pending arm, decisions row
134 (b)): the waiter's key, declared at a type above the cell's columns, joins the cell's wake
list; the completion stays. -/
theorem configTyped_awaitRegister {root : ProgramSource} {rootTy : EffTy} {W : World} {M : RState}
    {q : List RCmd} (typed : ConfigTyped root rootTy W M q) {cell : DeferredKey} {c : DeferredCell}
    (hc : M.state.deferreds.cellAt cell = some c) {fiber : FiberId} {token : Nat} {tin : EffTy}
    {a e : Ty} (hcell : W.«Π» cell = some (a, e)) (declared : W.Θ fiber token = some tin)
    (demand : AwaitDemand a e tin) (below : token < M.nextToken)
    (free : requestOfR M fiber token = none) :
    W.leHost { W with state := awaitStore M.state cell c fiber token } ∧
      ConfigTyped root rootTy { W with state := awaitStore M.state cell c fiber token }
        { M with state := awaitStore M.state cell c fiber token } q := by
  have wide := typed.machine.wide
  let v : DeferredCell := { c with wake := c.wake.register fiber token () }
  let s : Stores := awaitStore M.state cell c fiber token
  have count : s.deferreds.cells.length = M.state.deferreds.cells.length := List.length_set ..
  have cellsOf : ∀ key c', s.deferreds.cellAt key = some c' →
      (c' = v ∧ cell.index = key.index) ∨ M.state.deferreds.cellAt key = some c' :=
    fun _ _ h => Guard.cellAt_setCell h
  have cells : ∀ key c', s.deferreds.cellAt key = some c' →
      ∃ c0, M.state.deferreds.cellAt key = some c0 ∧ c'.completion = c0.completion := by
    intro key c' h
    rcases cellsOf key c' h with ⟨rfl, same⟩ | old
    · refine ⟨c, ?_, rfl⟩
      rw [← deferredKey_eq same]
      exact hc
    · exact ⟨c', old, rfl⟩
  have le : M.state.le s :=
    ⟨Nat.le_refl _, Nat.le_of_eq count.symm, fun _ h => h, Nat.le_refl _, fun _ h => h,
      Nat.le_refl _⟩
  have ord : W.leHost { W with state := s } :=
    leHost_cells (by rw [wide.state]; exact le) (by rw [wide.state])
      (fun key c' h => by
        obtain ⟨c0, hc0, same⟩ := cells key c' h
        exact ⟨c0, by rw [wide.state]; exact hc0, same⟩) (by rw [wide.state])
  have stores : StoresOk (preds root) { W with state := s } Expect.root s := by
    obtain ⟨c0, c1, ⟨c2⟩, c3, c4, c5⟩ := storesOk_world ord rfl rfl rfl wide.stores
    refine ⟨c0, c1, ⟨fun i c' hc' a' e' declaredCell x hx => ?_⟩, c3, c4, c5⟩
    obtain ⟨c0', hc0, same⟩ := cells ⟨i⟩ c' hc'
    rw [same] at hx
    exact c2 i c0' hc0 a' e' declaredCell x hx
  have waiters : ∀ key cell', s.deferreds.cellAt key = some cell' → ∀ a' e',
      W.«Π» key = some (a', e') → WakeTyped W (AwaitDemand a' e') cell'.wake := by
    intro key cell' h a' e' hd
    rcases cellsOf key cell' h with ⟨rfl, same⟩ | old
    · rw [← deferredKey_eq same, hcell] at hd
      cases hd
      exact WakeTyped.register (wide.waiters cell c hc a e hcell) () ⟨tin, declared, demand⟩
    · exact wide.waiters key cell' old a' e' hd
  have keys : Guard.storeKeys s ⊆ Guard.storeKeys M.state ++ [(fiber, token)] := by
    intro k hk
    unfold Guard.storeKeys at hk ⊢
    rcases List.mem_append.mp hk with h | h
    · exact List.mem_append_left _ (List.mem_append_left _ h)
    · have sub := Guard.deferredKeys_setCell_subset M.state.deferreds cell v [(fiber, token)] (by
        intro k' hk'
        rcases (Guard.wakeKeys_register_mem c.wake fiber token () k').mp hk' with h' | rfl
        · exact List.mem_append_left _ (Guard.deferredKeys_cell hc h')
        · exact List.mem_append_right _ (List.mem_singleton_self _))
      rcases List.mem_append.mp (sub h) with h | h
      · exact List.mem_append_left _ (List.mem_append_right _ h)
      · exact List.mem_append_right _ h
  exact configTyped_register typed le rfl count cells rfl rfl
    (wf_cells wide.wf le rfl rfl rfl rfl count) stores wide.timers waiters keys below free

/-! ## The park, with or without a store edit -/

/-- **An `async` park keeps `I`**: the fiber, its stack `stk` meeting the token's type `tin`, parks on
the fresh token (`Evaluating.park_fresh`, or `Evaluating.unpark_fresh` under a deferred interrupt);
its current code makes no external request. -/
theorem Evaluating.async_parks {root : ProgramSource} {rootTy : EffTy} {w : World} {m : RState}
    {rest : List RCmd} {f : RFiber} {y : Bool} (ev : Evaluating root rootTy w m rest f y)
    {register : EffName} {request : Val} {next : ExitV → RProgram}
    (hc : f.frame.current = .vis (.inr (.async register request)) next)
    (noRequest : externalRequestR f.frame.current = none) (tin : EffTy) (stk : List ScopeFrame)
    (stack : ∀ ty, w.Γ f.id = some ty → HostStack root w (m.update f) f.id tin ty stk) :
    SettlesTyped root rootTy w f.id rest (prepareIterR
      ⟨({ m with nextToken := m.nextToken + 1 } : RState).emit [.parkedOn f.id m.nextToken],
        { f with frame := { f.frame with stack := stk }, parked := .withGuard m.nextToken,
                 pending := f.pending ++ [⟨m.nextToken, none, [], [], .void, false⟩] },
        y, .parked, []⟩) := by
  have wide := ev.typed.machine.wide
  have hmem : f ∈ (m.update f).fibers := rfiber?_mem ev.look
  have old := ev.typed.machine.fiber hmem
  let tok : Nat := m.nextToken
  let fr : RSaved := { f.frame with stack := stk }
  let p : RPending := ⟨tok, none, [], [], .void, false⟩
  obtain ⟨ty, declared⟩ := ev.declared
  obtain ⟨_, _, _, prov⟩ := ev.code (by rw [hc]; rfl) ty declared
  have ord0 : w.leHost (w.addToken f.id tok tin) :=
    addToken_leHost (valid_nextToken_fresh rootTy w (m.update f) ev.typed.machine.typed.1 f.id)
  have back : ∀ id t' ty', (w.addToken f.id tok tin).Θ id t' = some ty' → (id, t') ≠ (f.id, tok) →
      w.Θ id t' = some ty' := fun id t' ty' h ne => by rwa [addToken_Θ_other ne] at h
  have internal : ∀ k ∈ Guard.fiberKeys f, k ≠ (f.id, tok) :=
    fun k hk => key_ne_of_lt (wide.keysBelow k (fiberKeys_internal hmem hk))
  obtain ⟨_, _, _, _, ⟨c4⟩, _⟩ := runFiberOk_tok ord0 rfl back internal old.ok
  have marker : raceRegistrationR fr.current = none := by
    show raceRegistrationR f.frame.current = none
    rw [hc]
    rfl
  obtain ⟨ord, parked⟩ := ev.park_fresh tin fr f.dispatcher p stack ⟨prov.recorded, prov.deferred⟩
    rfl (fun id hid => by rcases List.mem_append.mp hid with h | h <;> cases h) noRequest marker
    (fun b hb t' ht' => (c4 b hb).c0 t' ht') (fun k hk => Or.inl (List.mem_append_right _ hk))
  let gE : RFiber := { f with frame := fr, parked := .withGuard tok, pending := f.pending ++ [p] }
  rw [prepareIterR_async (g := gE) hc]
  refine ⟨w.addToken f.id tok tin, ord, ?_⟩
  unfold settle
  dsimp only
  split
  · rename_i hd
    let gD : RFiber := { f with frame := fr, parked := .notParked, pending := [] }
    obtain ⟨_, unparked⟩ := ev.unpark_fresh tin fr stack ⟨prov.recorded, prov.deferred⟩ hd marker y
    refine configTyped_congr (m := ({ (m.update f) with nextToken := tok + 1 } : RState).update gD) ?_
      rfl rfl rfl rfl rfl rfl unparked
    have ef := congrArg RunMachine.fibers (rupdate_rupdate m (f := f) (g := gD) rfl).symm
    exact ef
  · let gP : RFiber := { f with frame := fr, dispatcher := f.dispatcher, parked := .withGuard tok,
                                pending := f.pending ++ [p], running := false }
    refine configTyped_congr (m := ({ (m.update f) with nextToken := tok + 1 } : RState).update gP) ?_
      rfl rfl rfl rfl rfl rfl parked
    have ef := congrArg RunMachine.fibers (rupdate_rupdate m (f := f) (g := gP) rfl).symm
    exact ef

/-- **An `async` park after a store edit keeps `I`**: `Evaluating.async_parks`, then the edit `s`,
typed at the world declaring the token by `edit` (`configTyped_sleep`, `configTyped_awaitRegister`)
on the machine the park leaves. -/
theorem Evaluating.async_parks_store {root : ProgramSource} {rootTy : EffTy} {w : World}
    {m : RState} {rest : List RCmd} {f : RFiber} {y : Bool} (ev : Evaluating root rootTy w m rest f y)
    {register : EffName} {request : Val} {next : ExitV → RProgram}
    (hc : f.frame.current = .vis (.inr (.async register request)) next)
    (noRequest : externalRequestR f.frame.current = none) (tin : EffTy) (stk : List ScopeFrame)
    (stack : ∀ ty, w.Γ f.id = some ty → HostStack root w (m.update f) f.id tin ty stk) (s : Stores)
    (edit : ∀ (M : RState) (q : List RCmd),
      ConfigTyped root rootTy (w.addToken f.id m.nextToken tin) M q → M.state = m.state →
      m.nextToken < M.nextToken → requestOfR M f.id m.nextToken = none →
      (w.addToken f.id m.nextToken tin).leHost { (w.addToken f.id m.nextToken tin) with state := s } ∧
        ConfigTyped root rootTy { (w.addToken f.id m.nextToken tin) with state := s }
          { M with state := s } q) :
    SettlesTyped root rootTy w f.id rest (prepareIterR
      ⟨({ m with state := s, nextToken := m.nextToken + 1 } : RState).emit [.parkedOn f.id m.nextToken],
        { f with frame := { f.frame with stack := stk }, parked := .withGuard m.nextToken,
                 pending := f.pending ++ [⟨m.nextToken, none, [], [], .void, false⟩] },
        y, .parked, []⟩) := by
  have wide := ev.typed.machine.wide
  have hmem : f ∈ (m.update f).fibers := rfiber?_mem ev.look
  have old := ev.typed.machine.fiber hmem
  let tok : Nat := m.nextToken
  let fr : RSaved := { f.frame with stack := stk }
  let p : RPending := ⟨tok, none, [], [], .void, false⟩
  obtain ⟨ty, declared⟩ := ev.declared
  obtain ⟨_, _, _, prov⟩ := ev.code (by rw [hc]; rfl) ty declared
  have ord0 : w.leHost (w.addToken f.id tok tin) :=
    addToken_leHost (valid_nextToken_fresh rootTy w (m.update f) ev.typed.machine.typed.1 f.id)
  have back : ∀ id t' ty', (w.addToken f.id tok tin).Θ id t' = some ty' → (id, t') ≠ (f.id, tok) →
      w.Θ id t' = some ty' := fun id t' ty' h ne => by rwa [addToken_Θ_other ne] at h
  have internal : ∀ k ∈ Guard.fiberKeys f, k ≠ (f.id, tok) :=
    fun k hk => key_ne_of_lt (wide.keysBelow k (fiberKeys_internal hmem hk))
  obtain ⟨_, _, _, _, ⟨c4⟩, _⟩ := runFiberOk_tok ord0 rfl back internal old.ok
  have marker : raceRegistrationR fr.current = none := by
    show raceRegistrationR f.frame.current = none
    rw [hc]
    rfl
  obtain ⟨ord, parked⟩ := ev.park_fresh tin fr f.dispatcher p stack ⟨prov.recorded, prov.deferred⟩
    rfl (fun id hid => by rcases List.mem_append.mp hid with h | h <;> cases h) noRequest marker
    (fun b hb t' ht' => (c4 b hb).c0 t' ht') (fun k hk => Or.inl (List.mem_append_right _ hk))
  let gE : RFiber := { f with frame := fr, parked := .withGuard tok, pending := f.pending ++ [p] }
  rw [prepareIterR_async (g := gE) hc]
  let gP : RFiber := { f with frame := fr, dispatcher := f.dispatcher, parked := .withGuard tok,
                              pending := f.pending ++ [p], running := false }
  let Mp : RState := ({ (m.update f) with nextToken := tok + 1 } : RState).update gP
  have lookP : Mp.fiber? f.id = some gP := rfiber?_update_self (f := f) ev.look rfl
  have editP := edit Mp _ parked rfl (Nat.lt_succ_self _) (by
    rw [requestOfR_of_parked lookP rfl]
    exact noRequest)
  refine ⟨_, leHost_trans _ _ _ ord editP.1, ?_⟩
  unfold settle
  dsimp only
  split
  · rename_i hd
    let gD : RFiber := { f with frame := fr, parked := .notParked, pending := [] }
    let Md : RState := ({ (m.update f) with nextToken := tok + 1 } : RState).update gD
    obtain ⟨_, unparked⟩ := ev.unpark_fresh tin fr stack ⟨prov.recorded, prov.deferred⟩ hd marker y
    have lookD : Md.fiber? f.id = some gD := rfiber?_update_self (f := f) ev.look rfl
    have editD := edit Md _ unparked rfl (Nat.lt_succ_self _)
      (requestOfR_of_not_parked lookD (fun h => nomatch h))
    refine configTyped_congr (m := { Md with state := s }) ?_ rfl rfl rfl rfl rfl rfl editD.2
    have ef := congrArg RunMachine.fibers (rupdate_rupdate m (f := f) (g := gD) rfl).symm
    exact ef
  · refine configTyped_congr (m := { Mp with state := s }) ?_ rfl rfl rfl rfl rfl rfl editP.2
    have ef := congrArg RunMachine.fibers (rupdate_rupdate m (f := f) (g := gP) rfl).symm
    exact ef

/-! ## The immediate answer -/

/-- **A continue that consumed a token and queued the due drain settles typed** (the `async`
arm's immediate answer, `EvaluateR.lean`): the counter bumped, the world declaring the unused token
(`configTyped_token`), then `settle_frame_ready` under `drainDue`. -/
theorem Evaluating.settle_continue_bump_drain {root : ProgramSource} {rootTy : EffTy} {w : World}
    {m : RState} {rest : List RCmd} {f : RFiber} {y y' : Bool}
    (ev : Evaluating root rootTy w m rest f y) (fr : RSaved)
    (code : ∀ ty, w.Γ f.id = some ty → CodeOk root w (m.update f) f.id ty fr) :
    SettlesTyped root rootTy w f.id rest
      (prepareIterR ⟨{ m with nextToken := m.nextToken + 1 }, { f with frame := fr }, y', .continue_,
        [.drainDue]⟩) := by
  obtain ⟨ty, declared⟩ := ev.declared
  obtain ⟨ord, bumped⟩ := configTyped_token ev.typed
    (show (w.Γ f.id).isSome = true by rw [declared]; rfl) (EffTy.pure .unit)
  let w1 := w.addToken f.id m.nextToken (EffTy.pure .unit)
  let m1 : RState := { m with nextToken := m.nextToken + 1 }
  have ev' : Evaluating root rootTy w1 m1 rest f y := ⟨bumped, ev.stale, ev.running, ev.live⟩
  have code1 : ∀ ty, w1.Γ f.id = some ty → CodeOk root w1 (m1.update f) f.id ty fr :=
    fun ty' d => codeOk_races (m := m.update f) (racesKept_of_eq fun _ => rfl)
      (codeOk_mono ord (code ty' d))
  obtain ⟨f0, hf0, _⟩ := ev'.stale
  have view := ev'.view
  let fr' : RSaved := { fr with current := prepareR m1.completedExits fr.current }
  have code' : ∀ ty, w1.Γ f.id = some ty → CodeOk root w1 (m1.update f) f.id ty fr' :=
    fun ty' d => codeOk_prepare m1.completedExits view (code1 ty' d)
  obtain ⟨_, current, _, _⟩ := code' ty declared
  have idle : prepareScopedExitR ⟨m1, { f with frame := fr' }, y', .continue_, [.drainDue]⟩ =
      ⟨m1, { f with frame := fr' }, y', .continue_, [.drainDue]⟩ := prepareScopedExitR_of_typed current
  have glue : prepareIterR ⟨m1, { f with frame := fr }, y', .continue_, [.drainDue]⟩ =
      ⟨m1, { f with frame := fr' }, y', .continue_, [.drainDue]⟩ := idle
  rw [glue]
  obtain ⟨w', ord', typed⟩ := settle_frame_ready (y' := y') ev'.typed hf0 ev'.running fr' code'
  exact ⟨w', leHost_trans _ _ _ ord ord', configTyped_cons_drainDue typed⟩

/-! ## The clause -/

/-- `interpR`'s Deferred registration, both spellings: `DeferredStore.register`, the immediate
answer's program `denoteCompletion`. -/
theorem registerAsync_await (root : ProgramSource) (C : List (FiberId × ExitV)) (s : Stores)
    (cell : DeferredKey) (fid : FiberId) (tok : Nat) :
    (interpRAt root.program C).registerAsync (.registerAwait cell) fid tok s =
        ({ s with deferreds := (s.deferreds.register cell fid tok).1 },
          (s.deferreds.register cell fid tok).2.map denoteCompletion) ∧
      (interpRAt root.program C).registerAsync (.store (.registerAwait cell)) fid tok s =
        ({ s with deferreds := (s.deferreds.register cell fid tok).1 },
          (s.deferreds.register cell fid tok).2.map denoteCompletion) :=
  ⟨rfl, rfl⟩

/-- **A host registration's park** (`.external op req`): the fiber parks on the fresh token with
its current code the host request, which `requestOfR` then names at the token; no store edit, no
cancel frame. `Evaluating.park_fresh` assumes no external request, so this branch has its own park
(`Evaluating.park_fresh_request`, seat M6B's item 3); `externalAsyncParks` proves it. -/
def ExternalAsyncParks (root : ProgramSource) (rootTy : EffTy) : Prop :=
  ∀ (op : NativeOp) (req request : Val) (origin : List Nat),
    FiberClauseKeeps root rootTy (.async (.external op req origin) request)

/-- **`async`** (`EvaluateR.lean`'s `async` arm), every registration `asyncPre` admits: a sleep
and a pending Deferred register the fiber's key, declared at the certificate, on their wake list
and park under the cancel frame (`configTyped_sleep`, `configTyped_awaitRegister`,
`Evaluating.async_parks_store`); a completed Deferred answers at once with its completion, typed
at the cell's columns below the certificate, and queues the due drain; a host slot parks
(`Evaluating.async_parks`); a host row parks with its request (`ExternalAsyncParks`). -/
theorem clause_async_of_external (root : ProgramSource) (rootTy : EffTy) (register : EffName)
    (request : Val) (external : ExternalAsyncParks root rootTy) :
    FiberClauseKeeps root rootTy (.async register request) := by
  intro w m rest f y next ev hc
  obtain ⟨ty, declared⟩ := ev.declared
  obtain ⟨tin, current, stack, prov⟩ := ev.code (by rw [hc]; rfl) ty declared
  rw [hc] at current
  obtain ⟨cert, pre, typedNext⟩ := TypedProg.fiber_inv current (fun _ h => nomatch h)
    (fun _ h => nomatch h) (fun _ h => nomatch h) (fun _ _ _ h => nomatch h)
  have same : ∀ ty', w.Γ f.id = some ty' → ty' = ty :=
    fun _ h => Option.some.inj (h.symm.trans declared)
  have answer : ∀ ty', w.Γ f.id = some ty' →
      HostStack root w (m.update f) f.id cert ty' (.answer next :: f.frame.stack) := fun ty' d => by
    rw [same ty' d]
    exact hostStack_push (answerFrame_typed (fun _ _ _ hex => hex) typedNext) stack
  have wide := ev.typed.machine.wide
  rcases asyncPre_cases pre with ⟨millis, rfl, sub⟩ | ⟨cell, a, e, hreg, hcell, ha, he⟩ |
    ⟨op, req, origin, rfl⟩ | ⟨x, rfl⟩
  · -- a sleep: the timer registration, then the park under `clearTimeout`
    have noRequest : externalRequestR f.frame.current = none := by rw [hc]; rfl
    exact ev.async_parks_store hc noRequest cert _
      (fun ty' d => hostStack_sleepCancel root f.id m.nextToken (answer ty' d))
      { m.state with timers := m.state.timers.sleep f.id m.nextToken millis }
      (fun M q typed hstate hbelow hfree => by
        have e := configTyped_sleep typed (fiber := f.id) (token := m.nextToken) millis
          addToken_Θ_self sub hbelow hfree
        rw [hstate] at e
        exact e)
  · -- a Deferred's await: the cell, declared, is live
    have live : cell.index < m.state.deferreds.cells.length :=
      (wide.promises cell).mp (by rw [hcell]; rfl)
    obtain ⟨c, hcellAt⟩ : ∃ c, m.state.deferreds.cellAt cell = some c :=
      ⟨_, List.getElem?_eq_getElem live⟩
    have declaredCell : (w.«Π» cell).isSome = true := by rw [hcell]; rfl
    have cancels := fun ty' d => hostStack_awaitCancel root declaredCell f.id m.nextToken (answer ty' d)
    cases hp : c.completion with
    | some effect =>
      -- completed: the stored effect answers at once
      have reg : m.state.deferreds.register cell f.id m.nextToken = (m.state.deferreds, some effect) := by
        simp only [DeferredStore.register, hcellAt, hp]
      have hcell' : m.state.deferreds.cells[cell.index]? = some c := hcellAt
      have strong : CompletionStrong w cert effect :=
        completionStrong_await ⟨ha, he⟩ (wide.stores.c2.c0 cell.index c hcell' a e hcell effect hp)
      have code : ∀ ty', w.Γ f.id = some ty' → CodeOk root w (m.update f) f.id ty'
          { f.frame with current := denoteCompletion effect, stack := .answer next :: f.frame.stack } :=
        fun ty' d => ⟨cert, denoteCompletion_typed root strong, answer ty' d,
          ⟨prov.recorded, prov.deferred⟩⟩
      rcases hreg with rfl | rfl
      · have hr : (interpRAt root.program m.completedExits).registerAsync (.registerAwait cell) f.id
            m.nextToken m.state = (m.state, some (denoteCompletion effect)) := by
          rw [(registerAsync_await root m.completedExits m.state cell f.id m.nextToken).1, reg]
          rfl
        simp only [evaluateFiberR, saveAnswerR, pushR, answerR, hr]
        exact ev.settle_continue_bump_drain _ code
      · have hr : (interpRAt root.program m.completedExits).registerAsync (.store (.registerAwait cell))
            f.id m.nextToken m.state = (m.state, some (denoteCompletion effect)) := by
          rw [(registerAsync_await root m.completedExits m.state cell f.id m.nextToken).2, reg]
          rfl
        simp only [evaluateFiberR, saveAnswerR, pushR, answerR, hr]
        exact ev.settle_continue_bump_drain _ code
    | none =>
      -- pending: the waiter registers, then the park under the cell's cleanup
      have reg : m.state.deferreds.register cell f.id m.nextToken =
          ((awaitStore m.state cell c f.id m.nextToken).deferreds, none) := by
        simp only [DeferredStore.register, hcellAt, hp]
      have edit : ∀ (M : RState) (q : List RCmd),
          ConfigTyped root rootTy (w.addToken f.id m.nextToken cert) M q → M.state = m.state →
          m.nextToken < M.nextToken → requestOfR M f.id m.nextToken = none →
          (w.addToken f.id m.nextToken cert).leHost
              { (w.addToken f.id m.nextToken cert) with state := awaitStore m.state cell c f.id m.nextToken } ∧
            ConfigTyped root rootTy
              { (w.addToken f.id m.nextToken cert) with state := awaitStore m.state cell c f.id m.nextToken }
              { M with state := awaitStore m.state cell c f.id m.nextToken } q := by
        intro M q typed hstate hbelow hfree
        have hc' : M.state.deferreds.cellAt cell = some c := by rw [hstate]; exact hcellAt
        have e := configTyped_awaitRegister typed hc' (fiber := f.id) (token := m.nextToken) hcell
          addToken_Θ_self ⟨ha, he⟩ hbelow hfree
        rw [hstate] at e
        exact e
      rcases hreg with rfl | rfl
      · have hr : (interpRAt root.program m.completedExits).registerAsync (.registerAwait cell) f.id
            m.nextToken m.state = (awaitStore m.state cell c f.id m.nextToken, none) := by
          rw [(registerAsync_await root m.completedExits m.state cell f.id m.nextToken).1, reg]
          rfl
        have noRequest : externalRequestR f.frame.current = none := by rw [hc]; rfl
        simp only [evaluateFiberR, saveAnswerR, pushR, RunFiber.park, hr]
        exact ev.async_parks_store hc noRequest cert _ (fun ty' d => (cancels ty' d).1) _ edit
      · have hr : (interpRAt root.program m.completedExits).registerAsync (.store (.registerAwait cell))
            f.id m.nextToken m.state = (awaitStore m.state cell c f.id m.nextToken, none) := by
          rw [(registerAsync_await root m.completedExits m.state cell f.id m.nextToken).2, reg]
          rfl
        have noRequest : externalRequestR f.frame.current = none := by rw [hc]; rfl
        simp only [evaluateFiberR, saveAnswerR, pushR, RunFiber.park, hr]
        exact ev.async_parks_store hc noRequest cert _ (fun ty' d => (cancels ty' d).2) _ edit
  · -- a host row: the open branch
    exact external op req request origin w m rest f y next ev hc
  · -- a host slot: no store edit, no cancel frame
    have noRequest : externalRequestR f.frame.current = none := by rw [hc]; rfl
    exact ev.async_parks hc noRequest cert _ answer

/-! ## A park with an external request (the host row)

A host row's fiber parks with its current code the request (`externalRequestR`), so after the park
`requestOfR` names it at the fresh key `(f.id, m.nextToken)`; every other clause of `I` is the
no-request park's. The three readers of a request are `J`'s `requestsBelow` and `requestsOwned` and
the queue's reserved keys: the fresh key is below the bumped counter, and every internal and
queued key is below the old one, so none is the fresh key. -/

/-- `machineWide_rupdate` for an edit that may add an external request at the edited fiber's key
`(g.id, token₀)`, below the counter and no internal key of the edited machine. -/
theorem machineWide_rupdate_request {root : ProgramSource} {rootTy : EffTy} {w : World} {m : RState}
    {f g : RFiber} (wide : MachineWide root rootTy w m) (hid : g.id = f.id)
    (keys : ∀ k ∈ Guard.fiberKeys g, k ∈ Guard.internalKeys m ∨
      (k.2 < m.nextToken ∧ requestOfR m k.1 k.2 = none))
    {token₀ : Nat}
    (request : ∀ token r, requestOfR (m.update g) g.id token = some r →
      requestOfR m f.id token = some r ∨ token = token₀)
    (below0 : token₀ < m.nextToken) (owned0 : (g.id, token₀) ∉ Guard.internalKeys (m.update g)) :
    MachineWide root rootTy w (m.update g) := by
  have ids : (m.update g).fibers.map (·.id) = m.fibers.map (·.id) := rupdate_ids m g
  have requests : ∀ fiber token r, requestOfR (m.update g) fiber token = some r →
      requestOfR m fiber token = some r ∨ (fiber, token) = (g.id, token₀) := by
    intro fiber token r hr
    by_cases same : fiber = g.id
    · subst same
      rcases request token r hr with h | h
      · rw [hid]
        exact Or.inl h
      · rw [h]
        exact Or.inr rfl
    · rw [requestOfR_congr (rfiber?_update_other same)] at hr
      exact Or.inl hr
  refine ⟨wide.ids.trans ids.symm, fun id => by rw [ids]; exact wide.fibers id, wide.heap,
    wide.promises, wide.tokenBound, wide.tokenTargets, wide.state, wide.wf, wide.cells,
    wide.rootDeclared,
    wide.races, wide.stores, by rw [rupdate_ids]; exact wide.fiberIds, wide.raceIds,
    wide.racesBelow, fun race hr => ?_, fun key hk => ?_,
    fun fiber token r hr => ?_, fun fiber token r hr hk => ?_, wide.services,
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
  · rcases requests fiber token r hr with h | h
    · exact wide.requestsBelow fiber token r h
    · injection h with _ ht
      rw [ht]
      exact below0
  · rcases requests fiber token r hr with before | h
    · rcases List.mem_append.mp (internalKeys_rupdate m g hk) with old | new
      · exact wide.requestsOwned fiber token r before old
      · rcases keys (fiber, token) new with old | ⟨_, none⟩
        · exact wide.requestsOwned fiber token r before old
        · rw [none] at before
          cases before
    · rw [h] at hk
      exact owned0 hk
  · have before := wide.live.dueOwners o ho owner priority mode
    rw [rfiber?_update, Option.isSome_map]
    exact before

/-- `queueOk_transport_off` for an edit that may add an external request at one key, which no
queued command holds. -/
theorem queueOk_transport_off_request {root : ProgramSource} {w : World} {m m' : RState}
    {q : List RCmd} {key : Guard.GuardKey} (queue : QueueOk root w m q) (view : ObsViewOff key m m')
    (ids : m.nextId ≤ m'.nextId)
    (off : ∀ s e o, .observe s e o ∈ q → key ∉ Guard.observerKeys o)
    (authority : ∀ c ∈ q, CommandAuthorityR m c → CommandAuthorityR m' c)
    (delivery : ∀ c ∈ q, CommandDeliveryOk root w m c → CommandDeliveryOk root w m' c)
    {key0 : Guard.GuardKey}
    (requests : ∀ fiber token r, requestOfR m' fiber token = some r →
      requestOfR m fiber token = some r ∨ (fiber, token) = key0)
    (queued0 : key0 ∉ q.flatMap Guard.commandKeys)
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
      fun fiber token r hr hk => ?_⟩,
    fun s e o ho => ⟨Nat.lt_of_lt_of_le (queue.observer s e o ho).1 ids,
      observerCommandOk_off view o (off s e o ho) (queue.observer s e o ho).2⟩,
    fun r c hc => enrollRaceOk_off view ids (queue.enroll r c hc), queue.noRaceAfterInterrupt,
    fun md sc tg ir ex hl => ?_,
    fun s e o ho r race hr => queue.raceObservers s e o ho r race ((view.races r).symm.trans hr)⟩
  · rcases requests fiber token r hr with h | h
    · exact queue.keys.disjoint fiber token r h hk
    · rw [h] at hk
      exact queued0 hk
  · obtain ⟨live, present⟩ := queue.links md sc tg ir ex hl
    exact ⟨view.scopes sc live, view.exists_ tg present⟩

/-- `configTyped_rupdate_park` for a park whose fiber's current code makes an external request at
the park's key `(g.id, token₀)`: below the counter, no internal key, no queued key. -/
theorem configTyped_rupdate_park_request {root : ProgramSource} {rootTy : EffTy} {w : World}
    {m : RState} {q : List RCmd} {f g : RFiber} (typed : ConfigTyped root rootTy w m q)
    (hf : m.fiber? f.id = some f) (hid : g.id = f.id) {token₀ : Nat}
    (pending : PendingWeakerOff token₀ f.pending g.pending)
    (storedOff : ∀ x ∈ m.fibers, ∀ o ∈ x.observers, (g.id, token₀) ∉ Guard.observerKeys o)
    (queuedOff : ∀ s e o, .observe s e o ∈ q → (g.id, token₀) ∉ Guard.observerKeys o)
    (free : f.id ∉ q.filterMap (Guard.commandOwner m))
    (keys : ∀ k ∈ Guard.fiberKeys g, k ∈ Guard.internalKeys m ∨
      (k.2 < m.nextToken ∧ requestOfR m k.1 k.2 = none))
    (request : ∀ token r, requestOfR (m.update g) g.id token = some r →
      requestOfR m f.id token = some r ∨ token = token₀)
    (below0 : token₀ < m.nextToken) (owned0 : (g.id, token₀) ∉ Guard.internalKeys (m.update g))
    (queued0 : (g.id, token₀) ∉ q.flatMap Guard.commandKeys)
    (auth : ∀ c ∈ q, CommandAuthorityR m c → CommandAuthorityR (m.update g) c)
    (readG : g.running = true → ReadsCode g.id q → raceRegistrationR g.frame.current = none →
      ∀ ty, w.Γ g.id = some ty → SavedOk (TypedProg root) ExitOk (frameProtocols root) w ty g.frame)
    (fresh : FiberTyped root w (m.update g) g) : ConfigTyped root rootTy w (m.update g) q := by
  have view : ObsViewOff (g.id, token₀) m (m.update g) := obsViewOff_rupdate hf hid pending
  obtain ⟨machine, code, queue⟩ := typed
  refine ⟨machineTyped_of (machineWide_rupdate_request machine.wide hid keys request below0 owned0)
      (fun x hx => ?_), ?_,
    queueOk_transport_off_request queue view (Nat.le_refl _) queuedOff auth
      (fun c hc h => commandDelivery_owner hid free c hc h) ?_ queued0 (Nat.le_refl _)⟩
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
      rcases request token r hr with h | h
      · rw [hid]
        exact Or.inl h
      · rw [h]
        exact Or.inr rfl
    · rw [requestOfR_congr (rfiber?_update_other same)] at hr
      exact Or.inl hr

/-- **The park on the fresh token with an external request keeps `I`** (`Evaluating.park_fresh`
for a host row): the fiber keeps its dispatcher; its current code requests at the token. -/
theorem Evaluating.park_fresh_request {root : ProgramSource} {rootTy : EffTy} {w : World}
    {m : RState} {rest : List RCmd} {f : RFiber} {y : Bool} (ev : Evaluating root rootTy w m rest f y)
    (tin : EffTy) (fr : RSaved) (p : RPending)
    (stack : ∀ ty, w.Γ f.id = some ty → HostStack root w (m.update f) f.id tin ty fr.stack)
    (prov : InterruptProvenance fr) (ptoken : p.token = m.nextToken)
    (ptargets : ∀ id ∈ p.waitingOn.toList ++ p.remaining, id.value < m.nextId)
    (marker : raceRegistrationR fr.current = none) :
    w.leHost (w.addToken f.id m.nextToken tin) ∧
      ConfigTyped root rootTy (w.addToken f.id m.nextToken tin)
        (({ (m.update f) with nextToken := m.nextToken + 1 } : RState).update
          { f with frame := fr, parked := .withGuard m.nextToken,
                   pending := f.pending ++ [p], running := false }) rest := by
  let M0 : RState := m.update f
  let tok : Nat := m.nextToken
  let M1 : RState := { M0 with nextToken := tok + 1 }
  let w1 : World := w.addToken f.id tok tin
  let g : RFiber := { f with frame := fr, parked := .withGuard tok,
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
        fun q hq => ⟨g.id, pendOk q hq⟩, c2, c3, c4, c5⟩
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
  have reqs : ∀ tok' r, requestOfR (M1.update g) g.id tok' = some r →
      requestOfR M1 f.id tok' = some r ∨ tok' = tok := by
    intro tok' r hr
    by_cases hp : g.parked = .withGuard tok'
    · exact Or.inr (tokenOf tok' hp)
    · rw [requestOfR_of_not_parked lookG hp] at hr
      cases hr
  have keysG : ∀ k ∈ Guard.fiberKeys g, k ∈ Guard.internalKeys M1 ∨
      (k.2 < M1.nextToken ∧ requestOfR M1 k.1 k.2 = none) :=
    fun k hk => Or.inl (fiberKeys_internal hmem hk)
  have owned0 : (g.id, tok) ∉ Guard.internalKeys (M1.update g) := by
    intro hk
    rcases List.mem_append.mp (internalKeys_rupdate M1 g hk) with hold | hnew
    · exact Nat.lt_irrefl _ (wide.keysBelow _ hold)
    · exact Nat.lt_irrefl _ (wide.keysBelow _ (fiberKeys_internal hmem hnew))
  have queued0 : (g.id, tok) ∉ rest.flatMap Guard.commandKeys := by
    intro hk
    obtain ⟨c, hc, hkc⟩ := List.mem_flatMap.mp hk
    exact Nat.lt_irrefl _ (ev.typed.queue.keys.below _
      (List.mem_flatMap.mpr ⟨c, List.mem_cons_of_mem _ hc, hkc⟩))
  exact ⟨ord, configTyped_rupdate_park_request (g := g) bumped hf1 rfl weakOff
    (fun x hx o ho hk => key_ne_of_lt (n := g.id) (t := tok)
      (wide.keysBelow _ (fiberKeys_internal hx (List.mem_append_left _
        (List.mem_flatMap.mpr ⟨o, ho, hk⟩)))) rfl)
    (fun s e o ho hk => key_ne_of_lt (ev.typed.queue.keys.below _
      (List.mem_flatMap.mpr ⟨.observe s e o, List.mem_cons_of_mem _ ho, hk⟩)) rfl)
    free1 keysG reqs (Nat.lt_succ_self _) owned0 queued0
    (fun c hc h => commandAuthority_unowned (g := g) hf1 rfl live free1
      bumped.queue.registration c hc h)
    (fun h => Bool.noConfusion h) fresh⟩

/-- **A host row's park keeps `I`** (`Evaluating.async_parks` with the request). -/
theorem Evaluating.async_parks_request {root : ProgramSource} {rootTy : EffTy} {w : World}
    {m : RState} {rest : List RCmd} {f : RFiber} {y : Bool} (ev : Evaluating root rootTy w m rest f y)
    {register : EffName} {request : Val} {next : ExitV → RProgram}
    (hc : f.frame.current = .vis (.inr (.async register request)) next) (tin : EffTy)
    (stk : List ScopeFrame)
    (stack : ∀ ty, w.Γ f.id = some ty → HostStack root w (m.update f) f.id tin ty stk) :
    SettlesTyped root rootTy w f.id rest (prepareIterR
      ⟨({ m with nextToken := m.nextToken + 1 } : RState).emit [.parkedOn f.id m.nextToken],
        { f with frame := { f.frame with stack := stk }, parked := .withGuard m.nextToken,
                 pending := f.pending ++ [⟨m.nextToken, none, [], [], .void, false⟩] },
        y, .parked, []⟩) := by
  let tok : Nat := m.nextToken
  let fr : RSaved := { f.frame with stack := stk }
  let p : RPending := ⟨tok, none, [], [], .void, false⟩
  obtain ⟨ty, declared⟩ := ev.declared
  obtain ⟨_, _, _, prov⟩ := ev.code (by rw [hc]; rfl) ty declared
  have marker : raceRegistrationR fr.current = none := by
    show raceRegistrationR f.frame.current = none
    rw [hc]
    rfl
  obtain ⟨ord, parked⟩ := ev.park_fresh_request tin fr p stack ⟨prov.recorded, prov.deferred⟩
    rfl (fun id hid => by rcases List.mem_append.mp hid with h | h <;> cases h) marker
  let gE : RFiber := { f with frame := fr, parked := .withGuard tok, pending := f.pending ++ [p] }
  rw [prepareIterR_async (g := gE) hc]
  refine ⟨w.addToken f.id tok tin, ord, ?_⟩
  unfold settle
  dsimp only
  split
  · rename_i hd
    let gD : RFiber := { f with frame := fr, parked := .notParked, pending := [] }
    obtain ⟨_, unparked⟩ := ev.unpark_fresh tin fr stack ⟨prov.recorded, prov.deferred⟩ hd marker y
    refine configTyped_congr (m := ({ (m.update f) with nextToken := tok + 1 } : RState).update gD) ?_
      rfl rfl rfl rfl rfl rfl unparked
    have ef := congrArg RunMachine.fibers (rupdate_rupdate m (f := f) (g := gD) rfl).symm
    exact ef
  · let gP : RFiber := { f with frame := fr, parked := .withGuard tok,
                                pending := f.pending ++ [p], running := false }
    refine configTyped_congr (m := ({ (m.update f) with nextToken := tok + 1 } : RState).update gP) ?_
      rfl rfl rfl rfl rfl rfl parked
    have ef := congrArg RunMachine.fibers (rupdate_rupdate m (f := f) (g := gP) rfl).symm
    exact ef

/-- **A host row's `async`** (`ExternalAsyncParks`): no store edit (`interpR`'s registration of a
host row is the identity), no cancel frame; the fiber parks with its request. -/
theorem externalAsyncParks (root : ProgramSource) (rootTy : EffTy) : ExternalAsyncParks root rootTy := by
  intro op req request origin w m rest f y next ev hc
  obtain ⟨ty, declared⟩ := ev.declared
  obtain ⟨tin, current, stack, _⟩ := ev.code (by rw [hc]; rfl) ty declared
  rw [hc] at current
  obtain ⟨cert, _, typedNext⟩ := TypedProg.fiber_inv current (fun _ h => nomatch h)
    (fun _ h => nomatch h) (fun _ h => nomatch h) (fun _ _ _ h => nomatch h)
  have same : ∀ ty', w.Γ f.id = some ty' → ty' = ty :=
    fun _ h => Option.some.inj (h.symm.trans declared)
  exact ev.async_parks_request hc cert _ fun ty' d => by
    rw [same ty' d]
    exact hostStack_push (answerFrame_typed (fun _ _ _ hex => hex) typedNext) stack

/-- **`async`** (`EvaluateR.lean`'s `async` arm), every registration: `clause_async_of_external` at
its host-row branch (`externalAsyncParks`). -/
theorem clause_async (root : ProgramSource) (rootTy : EffTy) (register : EffName) (request : Val) :
    FiberClauseKeeps root rootTy (.async register request) :=
  clause_async_of_external root rootTy register request (externalAsyncParks root rootTy)

end Effect4.Program.Typed
