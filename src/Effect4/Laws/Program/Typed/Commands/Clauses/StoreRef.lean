import Effect4.Laws.Program.Typed.Commands.Clauses.Store

/-!
# Laws.Program.Typed.Commands.Clauses.StoreRef — the ref rows' clauses

Concept 4 (`step-deliver-preserves`, `step-loop-preserves`): `StoreClauseKeeps` for the twelve heap
rows, one clause from their table (`clause_kernel`), and for `refMake`. A heap row reads one
declared cell and writes it back (`SyncOp.refKernel`, `Laws/Machine/RefKernel.lean`): its kernel
keeps the cell's type and answers inside the row's post at every certificate its pre admits
(`kernel_typed`, `Typed/Adequacy.lean`), and it steps to the world over the written heap
(`kernel_step`), whose fiber and token tables are the old ones. The new store's validity comes from
membership (`CellsTyped.wf_step`), not from `SyncOp.validIn`: a term row's environment is not in its
precondition (decisions row 43).

Not established: the other store rows.
-/

set_option autoImplicit false
namespace Effect4.Program.Typed
open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Sched

/-- **The twelve heap rows keep `I`**, one clause from their table: the row's kernel keeps its
cell's declared type and answers inside the row's post at every certificate the pre admits
(`kernel_typed`); the row steps to the world over the written heap (`kernel_step`), typed again
(`StoreTyped.step`); every other column is untouched; the new store is well formed by membership
(`CellsTyped.wf_step`). -/
theorem clause_kernel (root : ProgramSource) (rootTy : EffTy) {o : SyncOp} {cell : RefKey}
    {k : RefKernel} (hk : o.refKernel = some (cell, k)) : StoreClauseKeeps root rootTy o := by
  intro w m rest fb y next ev hc
  have store := storeTyped_of_typedState ev.typed.machine
  obtain ⟨cert, pre⟩ := ev.store_pre hc
  obtain ⟨t, declared, runs, keeps⟩ := kernel_typed hk pre
  obtain ⟨c, r, fc, hr, step, ord, cells'⟩ := kernel_step store.toCellsTyped hk declared runs
    fun c r hc hr => ⟨trivial, (keeps c r hc hr).2⟩
  have store' : StoreTyped root (writeWorld w cell r.2) :=
    store.step step rfl ord cells' (layerCells_of_cells_length step rfl)
  refine ev.store_kept hc step (fun wf => CellsTyped.wf_step wf step rfl cells') store' ord
    (DueKept.refl w _) (CellsKept.refl w _) rfl rfl (List.Subset.refl _) fun cert' pre' => ?_
  obtain ⟨t', declared', _, keeps'⟩ := kernel_typed hk pre'
  obtain rfl : t' = t := Option.some.inj (declared'.symm.trans declared)
  exact (keeps' c r fc hr).1 _ ord

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
