import Effect4.Laws.Program.Typed.Commands.Clauses.Store

/-!
# Laws.Program.Typed.Commands.Clauses.StoreScope — the scope and memo rows' clauses

Concept 4 (`step-deliver-preserves`, `step-loop-preserves`): `StoreClauseKeeps` for the scope and
memo rows, over one restated-store settle (`Evaluating.store_restate`: refs, deferreds, timers and
externals unchanged, world `{ w with state := s }`), each row supplying its new scope column, memo
column and post. Drafted by seat M6G. The memo entry's build and completion allocate and complete a
Deferred cell, and are `Clauses/StoreDeferred.lean`'s.
-/

set_option autoImplicit false
namespace Effect4.Program.Typed
open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Sched

/-- A store step that keeps the heap and the timers keeps well-formedness. -/
theorem wf_step {op : SyncOp} {s s' : Stores} {ans : Val} (wf : s.WF)
    (step : syncOpStep op s = some (s', ans)) (refs : s'.refs = s.refs)
    (timers : s'.timers = s.timers) : s'.WF := by
  have le := syncOpStep_le op s s' ans step
  obtain ⟨hrefs, hscopes, hmemo, htimers⟩ := wf
  refine ⟨fun v hv => ?_, fun e he => ?_, syncOpStep_memoValid op s s' ans hmemo step, ?_⟩
  · rw [refs] at hv
    exact Val.validIn_mono le v (hrefs v hv)
  · cases hc : e.scope.closingExit? with
    | none => rfl
    | some ex =>
      obtain ⟨e₀, he₀, hex₀⟩ := syncOpStep_closingExit op s s' ans step e he ex hc
      have old := hscopes e₀ he₀
      rw [hex₀] at old
      exact Val.validIn_mono le _ old
  · rw [timers]
    exact htimers

/-- An admitted finalizer's name is typed. -/
theorem finNameOk_of_admitted {root : ProgramSource} {w : World} {e : Expect} {fin : FinName}
    (h : FinalizerAdmitted root w fin) : FinNameOk (preds root) w e fin := by
  cases fin with
  | foreign c => exact ⟨h⟩
  | _ => trivial

/-- Shared settle lemma: refs, deferreds, timers, externals unchanged; world `{ w with state := s }`. -/
theorem Evaluating.store_restate {root : ProgramSource} {rootTy : EffTy} {w : World} {m : RState}
    {rest : List RCmd} {f : RFiber} {y : Bool} (ev : Evaluating root rootTy w m rest f y)
    {op : SyncOp} {next : Val → RProgram} (hc : f.frame.current = .vis (.inl op) next)
    {s : Stores} {ans : Val} (step : syncOpStep op m.state = some (s, ans))
    (refs : s.refs = m.state.refs) (deferreds : s.deferreds = m.state.deferreds)
    (timers : s.timers = m.state.timers) (externals : s.externals = m.state.externals)
    (scopes : w.leHost { w with state := s } →
      ScopeStoreOk (preds root) { w with state := s } Expect.root m.state.scopes →
      ScopeStoreOk (preds root) { w with state := s } Expect.root s.scopes)
    (memo : w.leHost { w with state := s } →
      (∀ mm ∈ m.state.memo, MemoMapOk (preds root) { w with state := s } Expect.root mm) →
      ∀ mm ∈ s.memo, MemoMapOk (preds root) { w with state := s } Expect.root mm)
    (post : w.leHost { w with state := s } →
      ∀ cert, storePre root w op cert → storePost { w with state := s } op cert ans) :
    SettlesTyped root rootTy w f.id rest
      (prepareIterR (evaluateRawR (interpRAt root.program m.completedExits) m f y)) := by
  have wide := ev.typed.machine.wide
  have state : w.state = m.state := wide.state
  have wf0 : m.state.WF := wide.wf
  have store := storeTyped_of_typedState ev.typed.machine
  have step' : syncOpStep op w.state = some (s, ans) := by rw [state]; exact step
  obtain ⟨ord, store'⟩ := restate_world store step' (by rw [refs, state])
    (by rw [deferreds, state])
    (fun key c' h => ⟨c', by rw [state, ← deferreds]; exact h, rfl⟩) (by rw [externals, state])
  obtain ⟨c0, c1, c2, c3, c4, _⟩ := storesOk_world ord rfl rfl rfl wide.stores
  have stores : StoresOk (preds root) { w with state := s } Expect.root s := by
    refine ⟨⟨fun o ho ty declared => ?_, store'.memoTable⟩, ?_, ?_, scopes ord c3, memo ord c4,
      trivial⟩
    · rw [deferreds] at ho
      exact PromiseTableOk.due c0 o ho ty declared
    · rw [refs]
      exact c1
    · rw [deferreds]
      exact c2
  have waiters0 : ∀ key cell, m.state.deferreds.cellAt key = some cell → ∀ a e,
      w.«Π» key = some (a, e) → WakeTyped w (AwaitDemand a e) cell.wake := wide.waiters
  have due0 : ∀ o ∈ m.state.deferreds.due, ∀ owner priority, o.mode = .scheduled owner priority →
      ((m.update f).fiber? owner).isSome = true := wide.live.dueOwners
  refine ev.store_step hc step (fun o ho owner priority mode => ?_) fun cert pre =>
    ⟨_, ord, rfl, rfl, rfl, rfl, store', wf_step wf0 step refs timers, stores,
      by rw [timers]; exact wide.timers,
      fun key cell hcell a e declared =>
        waiters0 key cell (by rw [← deferreds]; exact hcell) a e declared,
      post ord cert pre⟩
  have owned := due0 o (by rw [← deferreds]; exact ho) owner priority mode
  rw [rfiber?_update, Option.isSome_map] at owned
  exact owned

theorem scopeStoreOk_make {root : ProgramSource} {w : World} {e : Expect} {st : ScopeStore}
    (h : ScopeStoreOk (preds root) w e st) (key : Nat) (strategy : FinalizerStrategy) :
    ScopeStoreOk (preds root) w e (st.make key strategy) := by
  refine ⟨fun x hx => ?_⟩
  change x ∈ st.entries ++ [⟨key, Effect4.Scope.make strategy⟩] at hx
  rcases List.mem_append.mp hx with old | new
  · exact h.c0 x old
  · rw [List.mem_singleton] at new
    subst new
    exact ⟨⟨trivial⟩⟩

/-- Scope column after `forkChild` (closed parent: child born closed at the parent's exit; open:
parent registers closeChildScope, child registers detachFromParent). -/
theorem scopeStoreOk_forkChild {root : ProgramSource} {w : World} {e : Expect} {st : ScopeStore}
    (h : ScopeStoreOk (preds root) w e st) {parent : Nat} {p : ScopeEntry}
    (hp : st.entryAt parent = some p) (child shared : Nat) (strategy : FinalizerStrategy)
    (closeOk : FinalizerAdmitted root w (.closeChildScope child))
    (detachOk : FinalizerAdmitted root w (.detachFromParent parent shared)) :
    ScopeStoreOk (preds root) w e (st.forkChild parent child shared strategy) := by
  have old := (h.c0 p (List.mem_of_find?_eq_some hp)).c0.c0
  unfold ScopeStore.forkChild
  rw [hp]
  dsimp only
  cases hexit : p.scope.closingExit? with
  | some ex =>
    have fork : Effect4.Scope.fork p.scope strategy shared (FinName.closeChildScope child)
        (FinName.detachFromParent parent shared) =
        (p.scope, { strategy := strategy, state := ScopeState.closed ex }) := by
      unfold Effect4.Scope.fork
      rw [hexit]
    rw [fork]
    dsimp only
    refine ⟨fun x hx => ?_⟩
    rcases List.mem_append.mp hx with hx | hx
    · rcases ScopeStore.mem_setEntry hx with rfl | hx
      · exact ⟨⟨old⟩⟩
      · exact h.c0 x hx
    · rw [List.mem_singleton] at hx
      subst hx
      exact ⟨⟨scopeStateOk_closed old ex hexit⟩⟩
  | none =>
    have fork : Effect4.Scope.fork p.scope strategy shared (FinName.closeChildScope child)
        (FinName.detachFromParent parent shared) =
        (p.scope.addUnsafe shared (FinName.closeChildScope child),
          (Effect4.Scope.make strategy).addUnsafe shared (FinName.detachFromParent parent shared)) := by
      unfold Effect4.Scope.fork
      rw [hexit]
    rw [fork]
    dsimp only
    refine ⟨fun x hx => ?_⟩
    rcases List.mem_append.mp hx with hx | hx
    · exact (scopeStoreOk_addUnsafe h hp shared (finNameOk_of_admitted closeOk) closeOk).c0 x hx
    · rw [List.mem_singleton] at hx
      subst hx
      refine ⟨⟨scopeStateOk_of (fun v hv => ?_) (fun v hv => ?_) (fun ex hex => ?_)⟩⟩
      · rcases entries_addUnsafe (Effect4.Scope.make strategy) shared _ v hv with hv | rfl
        · exact nomatch hv
        · exact detachOk
      · rcases entries_addUnsafe (Effect4.Scope.make strategy) shared _ v hv with hv | rfl
        · exact nomatch hv
        · trivial
      · change ((Effect4.Scope.make strategy).addUnsafe shared
          (FinName.detachFromParent parent shared)).closingExit? = some ex at hex
        rw [Effect4.Scope.closingExit_addUnsafe] at hex
        exact nomatch hex

theorem memoMapOk_updateEntry {root : ProgramSource} {w : World} {e : Expect} {memo : MemoWorld}
    (h : ∀ mm ∈ memo, MemoMapOk (preds root) w e mm) (id : MemoMapId) (layer : LayerId)
    {g : MemoEntry → MemoEntry} (keep : ∀ x, (g x).finalizer = x.finalizer) :
    ∀ mm ∈ memo.updateEntry id layer g, MemoMapOk (preds root) w e mm := by
  unfold MemoWorld.updateEntry
  split
  · exact h
  · rename_i old hold
    have hmem : old ∈ memo := List.mem_of_find?_eq_some hold
    intro mm hmm
    rcases MemoWorld.mem_setMap hmm with rfl | hmm
    · refine ⟨fun v hv => ?_⟩
      obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hv
      have prev := (h old hmem).c0 u hu
      by_cases hk : u.1 = layer
      · rw [if_pos hk]
        refine ⟨?_⟩
        show FinNameOk (preds root) w e (g u.2).finalizer
        rw [keep]
        exact prev.c0
      · rw [if_neg hk]
        exact prev
    · exact h mm hmm

theorem memoMapOk_deleteEntry {root : ProgramSource} {w : World} {e : Expect} {memo : MemoWorld}
    (h : ∀ mm ∈ memo, MemoMapOk (preds root) w e mm) (id : MemoMapId) (layer : LayerId) :
    ∀ mm ∈ memo.deleteEntry id layer, MemoMapOk (preds root) w e mm := by
  unfold MemoWorld.deleteEntry
  split
  · exact h
  · rename_i old hold
    have hmem : old ∈ memo := List.mem_of_find?_eq_some hold
    intro mm hmm
    rcases MemoWorld.mem_setMap hmm with rfl | hmm
    · exact ⟨fun v hv => (h old hmem).c0 v (List.mem_filter.mp hv).1⟩
    · exact h mm hmm

theorem memoMapOk_insertEntry {root : ProgramSource} {w : World} {e : Expect} {memo : MemoWorld}
    (h : ∀ mm ∈ memo, MemoMapOk (preds root) w e mm) (id : MemoMapId) (layer : LayerId)
    {entry : MemoEntry} (ok : FinNameOk (preds root) w e entry.finalizer) :
    ∀ mm ∈ memo.insertEntry id layer entry, MemoMapOk (preds root) w e mm := by
  unfold MemoWorld.insertEntry
  split
  · exact h
  · rename_i old hold
    have hmem : old ∈ memo := List.mem_of_find?_eq_some hold
    intro mm hmm
    rcases MemoWorld.mem_setMap hmm with rfl | hmm
    · refine ⟨fun v hv => ?_⟩
      rcases List.mem_append.mp hv with hv | hv
      · exact (h old hmem).c0 v hv
      · rw [List.mem_singleton] at hv
        subst hv
        exact ⟨ok⟩
    · exact h mm hmm

theorem clause_scopeMake (root : ProgramSource) (rootTy : EffTy) (strategy : FinalizerStrategy) :
    StoreClauseKeeps root rootTy (.scopeMake strategy) := by
  intro w m rest f y next ev hc
  exact ev.store_restate hc (syncOpStep_scopeMake m.state strategy) rfl rfl rfl rfl
    (fun _ old => scopeStoreOk_make old m.state.nextName strategy) (fun _ old => old)
    (fun _ _ _ => fits_scopeHandle _ _ (ScopeStore.entryAt_make_self _ _ _))

theorem clause_scopeAdd (root : ProgramSource) (rootTy : EffTy) (scope : Nat) (fin : FinName) :
    StoreClauseKeeps root rootTy (.scopeAdd scope fin) := by
  intro w m rest f y next ev hc
  have state : w.state = m.state := ev.typed.machine.wide.state
  have store := storeTyped_of_typedState ev.typed.machine
  obtain ⟨cert, live, admitted⟩ := ev.store_pre hc
  have live' : (m.state.scopes.entryAt scope).isSome = true := by rw [← state]; exact live
  obtain ⟨entry, hentry⟩ := Option.isSome_iff_exists.mp live'
  cases hexit : entry.scope.closingExit? with
  | some ex =>
    exact ev.store_same hc (reifyExitVal ex)
      (syncOpStep_scopeAdd_closed m.state scope fin hentry hexit)
      (fun _ _ => Or.inr ⟨ex, rfl, store.scopeExits entry
        (by rw [state]; exact List.mem_of_find?_eq_some hentry) ex hexit⟩)
  | none =>
    exact ev.store_restate hc (syncOpStep_scopeAdd_open m.state scope fin hentry hexit)
      rfl rfl rfl rfl
      (fun ord old => scopeStoreOk_addUnsafe old hentry m.state.nextName
        (finNameOk_of_admitted (finalizerAdmitted_mono root ord fin admitted))
        (finalizerAdmitted_mono root ord fin admitted))
      (fun _ old => old) (fun _ _ _ => Or.inl rfl)

theorem clause_scopeRemove (root : ProgramSource) (rootTy : EffTy) (scope key : Nat) :
    StoreClauseKeeps root rootTy (.scopeRemove scope key) := by
  intro w m rest f y next ev hc
  exact ev.store_restate hc (syncOpStep_scopeRemove m.state scope key) rfl rfl rfl rfl
    (fun _ old => scopeStoreOk_removeFinalizer old scope key) (fun _ old => old)
    (fun _ _ _ => rfl)

theorem clause_scopeIsClosed (root : ProgramSource) (rootTy : EffTy) (scope : Nat) :
    StoreClauseKeeps root rootTy (.scopeIsClosed scope) := by
  intro w m rest f y next ev hc
  have state : w.state = m.state := ev.typed.machine.wide.state
  obtain ⟨cert, live⟩ := ev.store_pre hc
  have live' : (m.state.scopes.entryAt scope).isSome = true := by rw [← state]; exact live
  obtain ⟨entry, hentry⟩ := Option.isSome_iff_exists.mp live'
  have step : syncOpStep (.scopeIsClosed scope) m.state =
      some (m.state, Val.bool entry.scope.isClosed) := by
    simp only [syncOpStep, hentry, Option.map_some]
  exact ev.store_same hc _ step (fun _ _ => ⟨_, rfl⟩)

theorem clause_scopeFork (root : ProgramSource) (rootTy : EffTy) (parent : Nat)
    (strategy : FinalizerStrategy) : StoreClauseKeeps root rootTy (.scopeFork parent strategy) := by
  intro w m rest f y next ev hc
  have state : w.state = m.state := ev.typed.machine.wide.state
  obtain ⟨cert, live⟩ := ev.store_pre hc
  have live' : (m.state.scopes.entryAt parent).isSome = true := by rw [← state]; exact live
  obtain ⟨p, hp⟩ := Option.isSome_iff_exists.mp live'
  have childLive := ScopeStore.entryAt_forkChild_child m.state.scopes parent m.state.nextName
    (m.state.nextName + 1) strategy hp
  have parentLive := ScopeStore.entryAt_forkChild_isSome m.state.scopes parent m.state.nextName
    (m.state.nextName + 1) strategy parent live'
  exact ev.store_restate hc (syncOpStep_scopeFork_some m.state parent strategy hp) rfl rfl rfl rfl
    (fun _ old => scopeStoreOk_forkChild old hp _ _ strategy childLive parentLive)
    (fun _ old => old) (fun _ _ _ => fits_scopeHandle _ _ childLive)

theorem clause_memoFork (root : ProgramSource) (rootTy : EffTy) (parent : Option MemoMapId) :
    StoreClauseKeeps root rootTy (.memoFork parent) := by
  intro w m rest f y next ev hc
  exact ev.store_restate hc (syncOpStep_memoFork m.state parent) rfl rfl rfl rfl (fun _ old => old)
    (fun _ old mm hmm => by
      rcases List.mem_append.mp hmm with hmm | hmm
      · exact old mm hmm
      · rw [List.mem_singleton] at hmm
        subst hmm
        exact ⟨fun v hv => nomatch hv⟩)
    (fun _ _ _ => ⟨_, rfl, MemoWorld.mapAt_append_self _ _⟩)

theorem clause_memoGet (root : ProgramSource) (rootTy : EffTy) (layer : LayerId)
    (memoMap : MemoMapId) : StoreClauseKeeps root rootTy (.memoGet layer memoMap) := by
  intro w m rest f y next ev hc
  have state : w.state = m.state := ev.typed.machine.wide.state
  have store := storeTyped_of_typedState ev.typed.machine
  cases hget : m.state.memo.get layer memoMap with
  | none =>
    exact ev.store_same hc Val.unit (syncOpStep_memoGet_none _ _ _ hget) (fun _ _ => Or.inl rfl)
  | some q =>
    obtain ⟨owner, entry⟩ := q
    obtain ⟨mm, hm, hid, he⟩ := MemoWorld.get_mem hget
    exact ev.store_restate hc (syncOpStep_memoGet_some m.state layer memoMap hget) rfl rfl rfl rfl
      (fun _ old => old) (fun _ old => memoMapOk_updateEntry (g := fun e =>
        { e with observers := e.observers + 1 }) old owner layer (fun _ => rfl))
      (fun ord cert pre => by
        obtain ⟨l, lt, node, checked, hcert⟩ := pre
        have declared := store.memoTable (layer, entry.deferred)
          (MemoWorld.mem_layerCells.mpr ⟨mm, by rw [state]; exact hm, (layer, entry), he, rfl⟩)
          l lt node checked
        rw [hcert] at declared
        have present : MemoLive w owner := by
          unfold MemoLive MemoWorld.mapAt
          rw [state, List.find?_isSome]
          exact ⟨mm, hm, by simp only [hid, decide_true]⟩
        exact Or.inr ⟨entry.deferred, owner, Val.memoHit?_memoHit _ _, declared,
          memoLive_mono ord.1 present⟩)

theorem clause_memoRelease (root : ProgramSource) (rootTy : EffTy) (layer : LayerId)
    (memoMap : MemoMapId) : StoreClauseKeeps root rootTy (.memoRelease layer memoMap) := by
  intro w m rest f y next ev hc
  have valid : m.state.MemoValid := ev.typed.machine.wide.wf.2.2.1
  cases hentry : m.state.memo.entryAt memoMap layer with
  | none =>
    exact ev.store_same hc Val.unit (syncOpStep_memoRelease_none _ _ _ hentry)
      (fun _ _ => Or.inl rfl)
  | some entry =>
    by_cases hobs : entry.observers ≤ 1
    · obtain ⟨mm, hm, _, hmem⟩ := MemoWorld.entryAt_mem hentry
      exact ev.store_restate hc (syncOpStep_memoRelease_last _ _ _ hentry hobs) rfl rfl rfl rfl
        (fun _ old => old) (fun _ old => memoMapOk_deleteEntry old memoMap layer)
        (fun _ _ _ => Or.inr (fits_scopeHandle _ _ (valid mm hm _ hmem).2))
    · exact ev.store_restate hc (syncOpStep_memoRelease_dec _ _ _ hentry hobs) rfl rfl rfl rfl
        (fun _ old => old) (fun _ old => memoMapOk_updateEntry (g := fun e =>
          { e with observers := e.observers - 1 }) old memoMap layer (fun _ => rfl))
        (fun _ _ _ => Or.inl rfl)

end Effect4.Program.Typed
