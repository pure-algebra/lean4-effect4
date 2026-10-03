import Effect4.Laws.Program.Typed.Commands.Evaluate

/-!
# Laws.Program.Typed.Commands.Clauses.Store — the store rows' clauses

Concept 4 of `docs/core/semantics.md` (`step-deliver-preserves`, `step-loop-preserves`): the store
clauses `StoreClauseKeeps root rootTy op` of `M6Ledger.step_deliver` / `step_loop` through
`evaluate_keeps` (`Commands/Evaluate.lean`).

The shared part (Codex's `StoreFamilyTransport` candidate, adapted to the current `J`): every store
step whose new store is typed at a later world with the same fiber and token tables keeps `I`
(`configTyped_store_step`): the fibers and queued commands move by the existing world and view
transports, the internal keys only shrink (`Guard.syncOpStep_storeKeys`), the coarse tables come
from the new store's typing. What stays per row is the new store's typing (`StoresOk`, `Stores.WF`,
the wake lists, the due owners) and the answer's post (`Evaluating.store_step`).

Not established: the rows not proved here.
-/

set_option autoImplicit false
namespace Effect4.Program.Typed
open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Sched

/-- **`J`'s machine-wide clauses after a store step**, given the new store's typing at a later
world with the same fiber and token tables. -/
theorem machineWide_store_step {root : ProgramSource} {rootTy : EffTy}
    {w w' : World} {m : RState} {op : SyncOp} {s : Stores} {ans : Val}
    (wide : MachineWide root rootTy w m)
    (step : syncOpStep op m.state = some (s, ans))
    (ord : w.leHost w') (state : w'.state = s)
    (ids : w'.ids = w.ids) (gamma : w'.Γ = w.Γ) (theta : w'.Θ = w.Θ)
    (store : StoreTyped root w')
    (wf : s.WF) (stores : StoresOk (preds root) w' Expect.root s)
    (timers : WakeTyped w' SleepDemand s.timers.wake)
    (waiters : ∀ key cell, s.deferreds.cellAt key = some cell → ∀ a e,
      w'.«Π» key = some (a, e) → WakeTyped w' (AwaitDemand a e) cell.wake)
    (due : ∀ o ∈ s.deferreds.due, ∀ owner priority, o.mode = .scheduled owner priority →
      (m.fiber? owner).isSome = true) :
    MachineWide root rootTy w' {m with state := s} := by
  have keys : Guard.internalKeys {m with state := s} ⊆ Guard.internalKeys m :=
    Guard.internalKeys_state_subset m s (Guard.syncOpStep_storeKeys step)
  have heap : ∀ key, (w'.Ρ key).isSome = true ↔ key.index < s.refs.length := by
    rw [← state]
    exact store.heap
  have promises : ∀ key, (w'.«Π» key).isSome = true ↔
      key.index < s.deferreds.cells.length := by
    rw [← state]
    exact store.promises
  have cells : HeapTable w' ∧ PromiseTable w' := by
    refine ⟨heapTable_of_fits store.values, promiseTable_of_strong ?_⟩
    rw [state]
    exact stores.c2.c0
  refine ⟨ids.trans wide.ids, fun id => ?_, heap, promises, fun id token ty declared => ?_,
    fun id token ty declared => ?_, state, wf, cells, ?_, ?_, stores,
    wide.fiberIds, wide.raceIds, wide.racesBelow, wide.raceHosts,
    (fun key hk => wide.keysBelow key (keys hk)), wide.requestsBelow,
    (fun fiber token r hr hk => wide.requestsOwned fiber token r hr (keys hk)),
    (le_serviceTy ord.1).trans wide.services, ⟨wide.live.running, due⟩,
    timers, waiters, wide.liveBelow, wide.sourceWF⟩
  · rw [gamma]
    exact wide.fibers id
  · rw [theta] at declared
    exact wide.tokenBound id token ty declared
  · rw [theta] at declared
    rw [gamma]
    exact wide.tokenTargets id token ty declared
  · rw [gamma]
    exact wide.rootDeclared
  · intro r hr
    obtain ⟨ty, payload⟩ := wide.races r hr
    exact ⟨ty, racePayload_world ord gamma theta payload⟩

/-- **A store step keeps `I`** at a later world with the same fiber and token tables, given the new
store's typing: the fibers and the queue move by the world and view transports. -/
theorem configTyped_store_step {root : ProgramSource} {rootTy : EffTy}
    {w w' : World} {m : RState} {q : List RCmd} {op : SyncOp} {s : Stores} {ans : Val}
    (typed : ConfigTyped root rootTy w m q)
    (step : syncOpStep op m.state = some (s, ans))
    (ord : w.leHost w') (state : w'.state = s)
    (ids : w'.ids = w.ids) (gamma : w'.Γ = w.Γ) (theta : w'.Θ = w.Θ)
    (store : StoreTyped root w')
    (wf : s.WF) (stores : StoresOk (preds root) w' Expect.root s)
    (timers : WakeTyped w' SleepDemand s.timers.wake)
    (waiters : ∀ key cell, s.deferreds.cellAt key = some cell → ∀ a e,
      w'.«Π» key = some (a, e) → WakeTyped w' (AwaitDemand a e) cell.wake)
    (due : ∀ o ∈ s.deferreds.due, ∀ owner priority, o.mode = .scheduled owner priority →
      (m.fiber? owner).isSome = true) :
    ConfigTyped root rootTy w' {m with state := s} q := by
  obtain ⟨machine, code, queue⟩ := typed
  have grow := syncOpStep_le op m.state s ans step
  have view : ObsView m {m with state := s} :=
    ObsView.ofLookup (fun _ => rfl) (fun _ => rfl) (fun sc h => grow.2.2.1 sc h)
  have ctl : ∀ id, (({m with state := s} : RState).fiber? id).map ctlView =
      (m.fiber? id).map ctlView := fun _ => rfl
  refine ⟨machineTyped_of
    (machineWide_store_step machine.wide step ord state ids gamma theta store wf stores timers
      waiters due)
    (fun x hx => fiberTyped_transport (fiberTyped_world ord gamma theta (machine.fiber hx))
      view (Nat.le_refl _) (Nat.le_refl _)),
    readCode_world ord gamma
      (readCode_races (m := m) rfl (racesKept_of_eq fun _ => rfl) code),
    queueOk_transport (queueOk_world ord gamma theta queue) view (Nat.le_refl _)
      (fun c _ h => commandAuthority_view ctl view.races c h)
      (fun c _ h => commandDelivery_view ctl (racesKept_of_eq view.races) c h)
      (fun _ _ _ hr => hr) (Nat.le_refl _)⟩

/-- **A store step's answered iteration settles typed** (the store arm of `evaluateRawR`): the new
store typed at a later world with the same fiber and token tables, and the answer in the row's post
there for the certificate the code carries; the continuation is typed by the code's store rule. -/
theorem Evaluating.store_step {root : ProgramSource} {rootTy : EffTy} {w w' : World} {m : RState}
    {rest : List RCmd} {f : RFiber} {y : Bool} (ev : Evaluating root rootTy w m rest f y)
    {op : SyncOp} {next : Val → RProgram} (hc : f.frame.current = .vis (.inl op) next)
    {s : Stores} {ans : Val} (step : syncOpStep op m.state = some (s, ans))
    (ord : w.leHost w') (state : w'.state = s)
    (ids : w'.ids = w.ids) (gamma : w'.Γ = w.Γ) (theta : w'.Θ = w.Θ)
    (store : StoreTyped root w')
    (wf : s.WF) (stores : StoresOk (preds root) w' Expect.root s)
    (timers : WakeTyped w' SleepDemand s.timers.wake)
    (waiters : ∀ key cell, s.deferreds.cellAt key = some cell → ∀ a e,
      w'.«Π» key = some (a, e) → WakeTyped w' (AwaitDemand a e) cell.wake)
    (due : ∀ o ∈ s.deferreds.due, ∀ owner priority, o.mode = .scheduled owner priority →
      (m.fiber? owner).isSome = true)
    (post : ∀ cert, storePre root w op cert → storePost w' op cert ans) :
    SettlesTyped root rootTy w f.id rest
      (prepareIterR (evaluateRawR (interpRAt root.program m.completedExits) m f y)) := by
  simp only [evaluateRawR, hc, step]
  have typed' : ConfigTyped root rootTy w' ({ m with state := s }.update f) (.deliver f.id y :: rest) :=
    configTyped_store_step ev.typed step ord state ids gamma theta store wf stores timers waiters
      (fun o ho owner priority mode => by
        have := due o ho owner priority mode
        rw [rfiber?_update, Option.isSome_map]
        exact this)
  have ev' : Evaluating root rootTy w' { m with state := s } rest f y :=
    ⟨typed', ev.stale, ev.running, ev.live⟩
  refine SettlesTyped.mono ord (ev'.settle_answered_drain _ fun ty declared => ?_)
  have declared0 : w.Γ f.id = some ty := by rw [← gamma]; exact declared
  obtain ⟨tin, current, stack, prov⟩ := ev.code (by rw [hc]; rfl) ty declared0
  rw [hc] at current
  obtain ⟨cert, pre, typedNext⟩ := TypedProg.store_inv current
  exact ⟨tin, typedNext w' ord ans (post cert pre),
    hostStack_mono ord (hostStack_races (m := m.update f) (m' := ({ m with state := s } : RState).update f)
      (racesKept_of_eq fun _ => rfl) stack), ⟨prov.recorded, prov.deferred⟩⟩

/-- For a ref edit, the new store's typing from the typed new heap: every other column is
untouched. -/
theorem storesOk_refs {root : ProgramSource} {w w' : World} {s s' : Stores}
    (old : StoresOk (preds root) w Expect.root s)
    (ord : w.leHost w') (theta : w'.Θ = w.Θ) (rho : w'.Ρ = w.Ρ) (pi : w'.«Π» = w.«Π»)
    (state : w'.state = s') (store : StoreTyped root w')
    (deferreds : s'.deferreds = s.deferreds) (scopes : s'.scopes = s.scopes)
    (memo : s'.memo = s.memo) :
    StoresOk (preds root) w' Expect.root s' := by
  obtain ⟨c0, c1, c2, c3, c4, c5⟩ := storesOk_world ord theta rho pi old
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · change PromiseTableOk root w' s'.deferreds.due s'.memo
    rw [deferreds, memo]
    exact c0
  · intro i v hv ty declared
    apply store.values i v _ ty declared
    rw [state]
    exact hv
  · exact deferreds.symm ▸ c2
  · exact scopes.symm ▸ c3
  · exact memo.symm ▸ c4
  · exact c5

/-- **A store step over the same declaration tables settles typed** (the ref rows): the new store
keeps every column but the heap (`storesOk_refs`), grows (`syncOpStep_le`) and stays well formed
(`syncOpStep_wf`, given the step's validity), and the answer is in the row's post at the restated
world. -/
theorem Evaluating.store_restated {root : ProgramSource} {rootTy : EffTy} {w : World} {m : RState}
    {rest : List RCmd} {f : RFiber} {y : Bool} (ev : Evaluating root rootTy w m rest f y)
    {op : SyncOp} {next : Val → RProgram} (hc : f.frame.current = .vis (.inl op) next)
    {s : Stores} {ans : Val} (step : syncOpStep op w.state = some (s, ans))
    (valid : op.validIn w.state = true)
    (store' : StoreTyped root { w with state := s }) (ord : w.leHost { w with state := s })
    (deferreds : s.deferreds = w.state.deferreds) (scopes : s.scopes = w.state.scopes)
    (memo : s.memo = w.state.memo) (timers : s.timers = w.state.timers)
    (post : ∀ cert, storePre root w op cert → storePost { w with state := s } op cert ans) :
    SettlesTyped root rootTy w f.id rest
      (prepareIterR (evaluateRawR (interpRAt root.program m.completedExits) m f y)) := by
  have wide := ev.typed.machine.wide
  have state : w.state = m.state := wide.state
  rw [state] at step valid deferreds scopes memo timers
  refine ev.store_step hc step ord rfl rfl rfl rfl store'
    (syncOpStep_wf op m.state s ans wide.wf valid step)
    (storesOk_refs wide.stores ord rfl rfl rfl rfl store' deferreds scopes memo) ?_ ?_ ?_ post
  · rw [timers]
    exact wide.timers
  · intro key cell hcell a e hpi
    rw [deferreds] at hcell
    exact wide.waiters key cell hcell a e hpi
  · intro o ho owner priority mode
    rw [deferreds] at ho
    have owned := wide.live.dueOwners o ho owner priority mode
    rw [rfiber?_update, Option.isSome_map] at owned
    exact owned

end Effect4.Program.Typed
