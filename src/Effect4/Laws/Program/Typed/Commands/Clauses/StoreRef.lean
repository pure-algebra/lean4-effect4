import Effect4.Laws.Program.Typed.Commands.Clauses.Store

/-!
# Laws.Program.Typed.Commands.Clauses.StoreRef — the ref rows' clauses

Concept 4 (`step-deliver-preserves`, `step-loop-preserves`): `StoreClauseKeeps` for the eleven ref
rows that rewrite one declared cell (`refStep`, `Machine/Stores.lean:485-493`). Each is an instance
of `Evaluating.store_restated`: the row's adequacy computation (`…_implements`,
`Typed/Adequacy.lean`) gives the step, the restated world's store typing (`poke_world`,
`restate_world`) and the post; the validity of the step is the cell's declaration (and, for a
written value, its membership, `fits_validIn`).

Not established: the other store rows.
-/

set_option autoImplicit false
namespace Effect4.Program.Typed
open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Sched

/-- A declared cell is in the heap. -/
theorem cell_live {root : ProgramSource} {w : World} {cell : RefKey} {t : Ty}
    (store : StoreTyped root w) (declared : w.Ρ cell = some t) :
    cell.index < w.state.refs.length :=
  (store.heap cell).mp (by rw [declared]; rfl)

theorem clause_refUpdate (root : ProgramSource) (rootTy : EffTy) (cell : RefKey) (f : FnName) :
    StoreClauseKeeps root rootTy (.refUpdate cell f) := by
  intro w m rest fb y next ev hc
  have store := storeTyped_of_typedState ev.typed.machine
  obtain ⟨_, t, declared⟩ := ev.store_pre hc
  obtain ⟨a, ha⟩ := cell_readable store declared
  have step : syncOpStep (.refUpdate cell f) w.state =
      some ({ w.state with refs := refPoke w.state.refs cell (f.total a) }, Val.unit) := by
    simp only [syncOpStep, refStep, refPeek, ha, Option.map_some]
  obtain ⟨ord, store'⟩ := poke_world store step rfl rfl rfl declared
    (fits_total f (store.values cell.index a ha t declared))
  exact ev.store_restated hc step (decide_eq_true (cell_live store declared)) store' ord rfl rfl rfl
    rfl fun _ _ => rfl

theorem clause_refGetAndUpdate (root : ProgramSource) (rootTy : EffTy) (cell : RefKey)
    (f : FnName) : StoreClauseKeeps root rootTy (.refGetAndUpdate cell f) := by
  intro w m rest fb y next ev hc
  have store := storeTyped_of_typedState ev.typed.machine
  obtain ⟨_, t, declared⟩ := ev.store_pre hc
  obtain ⟨a, ha⟩ := cell_readable store declared
  have old := store.values cell.index a ha t declared
  have step : syncOpStep (.refGetAndUpdate cell f) w.state =
      some ({ w.state with refs := refPoke w.state.refs cell (f.total a) }, a) := by
    simp only [syncOpStep, refStep, refPeek, ha, Option.map_some]
  obtain ⟨ord, store'⟩ := poke_world store step rfl rfl rfl declared (fits_total f old)
  exact ev.store_restated hc step (decide_eq_true (cell_live store declared)) store' ord rfl rfl rfl
    rfl fun _ _ => ⟨t, declared, fits_mono ord old⟩

theorem clause_refUpdateAndGet (root : ProgramSource) (rootTy : EffTy) (cell : RefKey)
    (f : FnName) : StoreClauseKeeps root rootTy (.refUpdateAndGet cell f) := by
  intro w m rest fb y next ev hc
  have store := storeTyped_of_typedState ev.typed.machine
  obtain ⟨_, t, declared⟩ := ev.store_pre hc
  obtain ⟨a, ha⟩ := cell_readable store declared
  have new := fits_total f (store.values cell.index a ha t declared)
  have step : syncOpStep (.refUpdateAndGet cell f) w.state =
      some ({ w.state with refs := refPoke w.state.refs cell (f.total a) }, f.total a) := by
    simp only [syncOpStep, refStep, refPeek, ha, Option.map_some]
  obtain ⟨ord, store'⟩ := poke_world store step rfl rfl rfl declared new
  exact ev.store_restated hc step (decide_eq_true (cell_live store declared)) store' ord rfl rfl rfl
    rfl fun _ _ => ⟨t, declared, fits_mono ord new⟩

theorem clause_refModify (root : ProgramSource) (rootTy : EffTy) (cell : RefKey) (f : FnName) :
    StoreClauseKeeps root rootTy (.refModify cell f) := by
  intro w m rest fb y next ev hc
  have store := storeTyped_of_typedState ev.typed.machine
  obtain ⟨_, pre⟩ := ev.store_pre hc
  obtain ⟨t, n, declared, equiv, peek⟩ := nat_cell store pre
  obtain ⟨answer, _, written⟩ := modify_nat f n
  have step : syncOpStep (.refModify cell f) w.state = some ({ w.state with
      refs := refPoke w.state.refs cell (f.modify (.nat n)).2 }, (f.modify (.nat n)).1) := by
    simp only [syncOpStep, refStep, peek, Option.map_some]
  have fits : Fits w (f.modify (.nat n)).2 t := by
    rw [written]
    exact fits_subN w equiv.2 _ trivial
  obtain ⟨ord, store'⟩ := poke_world store step rfl rfl rfl declared fits
  exact ev.store_restated hc step (decide_eq_true (cell_live store declared)) store' ord rfl rfl rfl
    rfl fun _ _ => ⟨n, answer⟩

theorem clause_refModifySome (root : ProgramSource) (rootTy : EffTy) (cell : RefKey) (f : FnName) :
    StoreClauseKeeps root rootTy (.refModifySome cell f) := by
  intro w m rest fb y next ev hc
  have store := storeTyped_of_typedState ev.typed.machine
  obtain ⟨_, pre⟩ := ev.store_pre hc
  obtain ⟨t, n, declared, equiv, peek⟩ := nat_cell store pre
  obtain ⟨answer, _, written⟩ := modifySome_nat f n
  have step : syncOpStep (.refModifySome cell f) w.state = some ({ w.state with
      refs := refPoke w.state.refs cell ((f.modifySome (.nat n)).2.getD (.nat n)) },
      (f.modifySome (.nat n)).1) := by
    simp only [syncOpStep, refStep, peek, Option.map_some]
  have fits : Fits w ((f.modifySome (.nat n)).2.getD (.nat n)) t := by
    rw [written]
    exact fits_subN w equiv.2 _ trivial
  obtain ⟨ord, store'⟩ := poke_world store step rfl rfl rfl declared fits
  exact ev.store_restated hc step (decide_eq_true (cell_live store declared)) store' ord rfl rfl rfl
    rfl fun _ _ => ⟨n, answer⟩

theorem clause_refSet (root : ProgramSource) (rootTy : EffTy) (cell : RefKey) (v : Val) :
    StoreClauseKeeps root rootTy (.refSet cell v) := by
  intro w m rest fb y next ev hc
  have store := storeTyped_of_typedState ev.typed.machine
  obtain ⟨_, t, declared, fits⟩ := ev.store_pre hc
  obtain ⟨a, ha⟩ := cell_readable store declared
  have step : syncOpStep (.refSet cell v) w.state =
      some ({ w.state with refs := refPoke w.state.refs cell v }, Val.cell cell) := by
    simp only [syncOpStep, refStep, refPeek, ha, Option.map_some]
  obtain ⟨ord, store'⟩ := poke_world store step rfl rfl rfl declared fits
  have valid : (SyncOp.refSet cell v).validIn w.state = true := by
    simp only [SyncOp.validIn, Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨cell_live store declared, fits_validIn store fits⟩
  exact ev.store_restated hc step valid store' ord rfl rfl rfl rfl fun _ _ => rfl

theorem clause_refGetAndSet (root : ProgramSource) (rootTy : EffTy) (cell : RefKey) (v : Val) :
    StoreClauseKeeps root rootTy (.refGetAndSet cell v) := by
  intro w m rest fb y next ev hc
  have store := storeTyped_of_typedState ev.typed.machine
  obtain ⟨_, t, declared, fits⟩ := ev.store_pre hc
  obtain ⟨a, ha⟩ := cell_readable store declared
  have step : syncOpStep (.refGetAndSet cell v) w.state =
      some ({ w.state with refs := refPoke w.state.refs cell v }, a) := by
    simp only [syncOpStep, refStep, refPeek, ha, Option.map_some]
  obtain ⟨ord, store'⟩ := poke_world store step rfl rfl rfl declared fits
  have valid : (SyncOp.refGetAndSet cell v).validIn w.state = true := by
    simp only [SyncOp.validIn, Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨cell_live store declared, fits_validIn store fits⟩
  exact ev.store_restated hc step valid store' ord rfl rfl rfl rfl
    fun _ _ => ⟨t, declared, fits_mono ord (store.values cell.index a ha t declared)⟩

theorem clause_refSetAndGet (root : ProgramSource) (rootTy : EffTy) (cell : RefKey) (v : Val) :
    StoreClauseKeeps root rootTy (.refSetAndGet cell v) := by
  intro w m rest fb y next ev hc
  have store := storeTyped_of_typedState ev.typed.machine
  obtain ⟨_, t, declared, fits⟩ := ev.store_pre hc
  obtain ⟨a, ha⟩ := cell_readable store declared
  have step : syncOpStep (.refSetAndGet cell v) w.state =
      some ({ w.state with refs := refPoke w.state.refs cell v }, v) := by
    simp only [syncOpStep, refStep, refPeek, ha, Option.map_some]
  obtain ⟨ord, store'⟩ := poke_world store step rfl rfl rfl declared fits
  have valid : (SyncOp.refSetAndGet cell v).validIn w.state = true := by
    simp only [SyncOp.validIn, Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨cell_live store declared, fits_validIn store fits⟩
  exact ev.store_restated hc step valid store' ord rfl rfl rfl rfl
    fun _ _ => ⟨t, declared, fits_mono ord fits⟩

/-- The rows whose partial update may decline: the store unchanged, or the cell rewritten. -/
theorem clause_refUpdateSome (root : ProgramSource) (rootTy : EffTy) (cell : RefKey) (f : FnName) :
    StoreClauseKeeps root rootTy (.refUpdateSome cell f) := by
  intro w m rest fb y next ev hc
  have store := storeTyped_of_typedState ev.typed.machine
  obtain ⟨_, t, declared⟩ := ev.store_pre hc
  obtain ⟨a, ha⟩ := cell_readable store declared
  have old := store.values cell.index a ha t declared
  have valid := decide_eq_true (cell_live store declared)
  cases hp : f.partialUpdate a with
  | none =>
    have step : syncOpStep (.refUpdateSome cell f) w.state =
        some ({ w.state with refs := w.state.refs }, Val.unit) := by
      simp only [syncOpStep, refStep, refPeek, ha, hp, Option.map_some]
    obtain ⟨ord, store'⟩ := restate_world store step rfl rfl (fun _ c' h => ⟨c', h, rfl⟩) rfl
    exact ev.store_restated hc step valid store' ord rfl rfl rfl rfl fun _ _ => rfl
  | some a' =>
    have step : syncOpStep (.refUpdateSome cell f) w.state =
        some ({ w.state with refs := refPoke w.state.refs cell a' }, Val.unit) := by
      simp only [syncOpStep, refStep, refPeek, ha, hp, Option.map_some]
    obtain ⟨ord, store'⟩ := poke_world store step rfl rfl rfl declared
      (fits_partialUpdate f old hp)
    exact ev.store_restated hc step valid store' ord rfl rfl rfl rfl fun _ _ => rfl

theorem clause_refGetAndUpdateSome (root : ProgramSource) (rootTy : EffTy) (cell : RefKey)
    (f : FnName) : StoreClauseKeeps root rootTy (.refGetAndUpdateSome cell f) := by
  intro w m rest fb y next ev hc
  have store := storeTyped_of_typedState ev.typed.machine
  obtain ⟨_, t, declared⟩ := ev.store_pre hc
  obtain ⟨a, ha⟩ := cell_readable store declared
  have old := store.values cell.index a ha t declared
  have valid := decide_eq_true (cell_live store declared)
  cases hp : f.partialUpdate a with
  | none =>
    have step : syncOpStep (.refGetAndUpdateSome cell f) w.state =
        some ({ w.state with refs := w.state.refs }, a) := by
      simp only [syncOpStep, refStep, refPeek, ha, hp, Option.map_some]
    obtain ⟨ord, store'⟩ := restate_world store step rfl rfl (fun _ c' h => ⟨c', h, rfl⟩) rfl
    exact ev.store_restated hc step valid store' ord rfl rfl rfl rfl
      fun _ _ => ⟨t, declared, fits_mono ord old⟩
  | some a' =>
    have step : syncOpStep (.refGetAndUpdateSome cell f) w.state =
        some ({ w.state with refs := refPoke w.state.refs cell a' }, a) := by
      simp only [syncOpStep, refStep, refPeek, ha, hp, Option.map_some]
    obtain ⟨ord, store'⟩ := poke_world store step rfl rfl rfl declared
      (fits_partialUpdate f old hp)
    exact ev.store_restated hc step valid store' ord rfl rfl rfl rfl
      fun _ _ => ⟨t, declared, fits_mono ord old⟩

theorem clause_refUpdateSomeAndGet (root : ProgramSource) (rootTy : EffTy) (cell : RefKey)
    (f : FnName) : StoreClauseKeeps root rootTy (.refUpdateSomeAndGet cell f) := by
  intro w m rest fb y next ev hc
  have store := storeTyped_of_typedState ev.typed.machine
  obtain ⟨_, t, declared⟩ := ev.store_pre hc
  obtain ⟨a, ha⟩ := cell_readable store declared
  have old := store.values cell.index a ha t declared
  have valid := decide_eq_true (cell_live store declared)
  cases hp : f.partialUpdate a with
  | none =>
    have step : syncOpStep (.refUpdateSomeAndGet cell f) w.state =
        some ({ w.state with refs := w.state.refs }, a) := by
      simp only [syncOpStep, refStep, refPeek, ha, hp, Option.bind_some, Option.map_some]
    obtain ⟨ord, store'⟩ := restate_world store step rfl rfl (fun _ c' h => ⟨c', h, rfl⟩) rfl
    exact ev.store_restated hc step valid store' ord rfl rfl rfl rfl
      fun _ _ => ⟨t, declared, fits_mono ord old⟩
  | some a' =>
    have live : cell.index < w.state.refs.length := (List.getElem?_eq_some_iff.mp ha).1
    have fresh : (refPoke w.state.refs cell a')[cell.index]? = some a' :=
      List.getElem?_set_self live
    have step : syncOpStep (.refUpdateSomeAndGet cell f) w.state =
        some ({ w.state with refs := refPoke w.state.refs cell a' }, a') := by
      simp only [syncOpStep, refStep, refPeek, ha, hp, Option.bind_some, fresh, Option.map_some]
    have new := fits_partialUpdate f old hp
    obtain ⟨ord, store'⟩ := poke_world store step rfl rfl rfl declared new
    exact ev.store_restated hc step valid store' ord rfl rfl rfl rfl
      fun _ _ => ⟨t, declared, fits_mono ord new⟩

/-- **`refMake`** (`Stores.lean:485`): the fresh cell declared at the code's certificate over the
grown heap (`refMake_world`), the initial value valid because it fits (`fits_validIn`); every
other column is untouched. -/
theorem clause_refMake (root : ProgramSource) (rootTy : EffTy) (initial : Val) :
    StoreClauseKeeps root rootTy (.refMake initial) := by
  intro w m rest fb y next ev hc
  have wide := ev.typed.machine.wide
  have store := storeTyped_of_typedState ev.typed.machine
  have state : w.state = m.state := wide.state
  refine ev.store_step hc (syncOpStep_refMake m.state initial) (fun o ho owner priority mode => ?_)
    fun cert pre => ?_
  · have owned := wide.live.dueOwners o ho owner priority mode
    rw [rfiber?_update, Option.isSome_map] at owned
    exact owned
  · change Ty at cert
    have fits : Fits w initial cert := pre
    have valid : (SyncOp.refMake initial).validIn m.state = true := by
      rw [← state]
      exact fits_validIn store fits
    obtain ⟨ord, store'⟩ := refMake_world root w initial cert store fits
    rw [state] at ord store'
    exact ⟨_, ord, rfl, rfl, rfl, rfl, store',
      syncOpStep_wf _ _ _ _ wide.wf valid (syncOpStep_refMake m.state initial),
      storesOk_refs wide.stores ord rfl rfl rfl store' rfl rfl rfl, wide.timers,
      fun key cell hcell a e hpi => wide.waiters key cell hcell a e hpi,
      ⟨_, rfl, insert_here _ _ _⟩⟩

end Effect4.Program.Typed
