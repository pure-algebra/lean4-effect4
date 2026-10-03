import Effect4.Laws.Program.Typed.Commands.Clauses.StoreScope

/-!
# Laws.Program.Typed.Commands.Clauses.StoreDeferred — the Deferred, sleep and memo-entry rows

Concept 4 (`step-deliver-preserves`, `step-loop-preserves`): `StoreClauseKeeps` for `deferredMake`,
the two completions, the await cleanup, the sleep cancel (`Machine/Stores.lean:1099-1152`,
`Machine/Timer.lean:66`) and the memo entry's build and completion (`Stores.lean`, `memoMapBuild`).

The edits that add no declaration settle by `Evaluating.store_kept`: a cancellation removes one
waiter (`cancel_kept`, `Guard.wakeKeys_cancel_subset`); a completion stores a completion the pre
types in an empty cell, clears its waiters and owes them the completion now (`complete_kept`,
`complete_dueKept`, `CompletionDue.completion_due_typed`); `memoComplete` is the completion at the
entry's cell, declared by the memo table at the layer's columns. The two allocations declare one
fresh, empty, unwaited cell at the code's certificate (`storesOk_make`, `waiters_make`):
`deferredMake` alone (`deferredMake_world`), `memoBuild` with a fresh scope and the entry
(`memoBuild_world`, `scopeStoreOk_make`, `memoMapOk_insertEntry`).
-/

set_option autoImplicit false
namespace Effect4.Program.Typed
open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Sched

/-- `cancel` (`Stores.lean:1132-1136`) removes one waiter from one cell. -/
theorem cancel_kept (w : World) (d : DeferredStore) (cell : DeferredKey) (waiter : FiberId)
    (token : Nat) : CellsKept w (d.cancel cell waiter token) d := by
  intro key c' h
  unfold DeferredStore.cancel at h
  split at h
  · exact ⟨c', h, List.Subset.refl _, Or.inl rfl⟩
  · rename_i c0 hc0
    unfold DeferredStore.setCell DeferredStore.cellAt at h
    rw [List.getElem?_set] at h
    split at h
    · rename_i same
      split at h
      · cases h
        refine ⟨c0, ?_, Guard.wakeKeys_cancel_subset c0.wake waiter token, Or.inl rfl⟩
        unfold DeferredStore.cellAt at hc0 ⊢
        rw [← same]
        exact hc0
      · cases h
    · exact ⟨c', h, List.Subset.refl _, Or.inl rfl⟩

/-- …and keeps the due list. -/
theorem cancel_dueKept (w : World) (d : DeferredStore) (cell : DeferredKey) (waiter : FiberId)
    (token : Nat) : DueKept w (d.cancel cell waiter token) d := by
  intro o ho
  unfold DeferredStore.cancel at ho
  split at ho
  · exact Or.inl ho
  · exact Or.inl ho

/-- `complete` (`Stores.lean:1142-1152`) stores a completion in an empty cell, clearing its
waiters, and changes no other cell. -/
theorem complete_kept (w : World) (d : DeferredStore) (cell : DeferredKey)
    (effect : Completion Val Err Defect FiberId Ann)
    (strong : ∀ a e, w.«Π» cell = some (a, e) →
      CompletionStrong w ⟨a, e, Env.Requirement.empty⟩ effect) :
    CellsKept w (d.complete cell effect).1 d := by
  intro key c' h
  unfold DeferredStore.complete at h
  split at h
  · exact ⟨c', h, List.Subset.refl _, Or.inl rfl⟩
  · rename_i c0 hc0
    split at h
    · exact ⟨c', h, List.Subset.refl _, Or.inl rfl⟩
    · unfold DeferredStore.setCell DeferredStore.cellAt at h
      rw [List.getElem?_set] at h
      split at h
      · rename_i same
        split at h
        · cases h
          have hkey : key = cell := by
            cases key with
            | mk i =>
              cases cell with
              | mk c =>
                change c = i at same
                rw [same]
          refine ⟨c0, ?_, Guard.wakeKeys_wakeAll_subset c0.wake, Or.inr fun a e declared x hx => ?_⟩
          · unfold DeferredStore.cellAt at hc0 ⊢
            rw [← same]
            exact hc0
          · obtain rfl := Option.some.inj hx
            rw [hkey] at declared
            exact strong a e declared
        · cases h
      · exact ⟨c', h, List.Subset.refl _, Or.inl rfl⟩

/-- …and owes its waiters the stored completion now, typed at their tokens. -/
theorem complete_dueKept {root : ProgramSource} {rootTy : EffTy} {w : World} {m : RState}
    (wide : MachineWide root rootTy w m) (cell : DeferredKey)
    (effect : Completion Val Err Defect FiberId Ann)
    (strong : ∀ a e, w.«Π» cell = some (a, e) →
      CompletionStrong w ⟨a, e, Env.Requirement.empty⟩ effect) :
    DueKept w (m.state.deferreds.complete cell effect).1 m.state.deferreds := by
  intro o ho
  rcases CompletionDue.complete_due ho with old | ⟨_, _, _, _, _, now⟩
  · exact Or.inl old
  · exact Or.inr ⟨now, CompletionDue.completion_due_typed wide cell effect strong o ho⟩

/-- **`deferredCompleteWith`** (`Stores.lean:1142`): the completion the pre types at the cell's
columns (`complete_world`, `complete_kept`, `complete_dueKept`). -/
theorem clause_deferredCompleteWith (root : ProgramSource) (rootTy : EffTy) (key : DeferredKey)
    (completion : Completion Val Err Defect FiberId Ann) :
    StoreClauseKeeps root rootTy (.deferredCompleteWith key completion) := by
  intro w m rest fb y next ev hc
  have wide := ev.typed.machine.wide
  have state : w.state = m.state := wide.state
  have store := storeTyped_of_typedState ev.typed.machine
  obtain ⟨_, a, e, declared, pre⟩ := ev.store_pre hc
  have strong : ∀ a' e', w.«Π» key = some (a', e') →
      CompletionStrong w ⟨a', e', Env.Requirement.empty⟩ completion := by
    intro a' e' h
    rw [declared] at h
    cases h
    cases completion with
    | ofExit ex => exact pre
    | ofRefGet cell => exact pre
  have typed : ∀ types, w.«Π» key = some types → CompletionOk w types completion := by
    intro types h
    rw [declared] at h
    cases h
    cases completion with
    | ofExit ex => exact completionOk_of_fitsExit pre.1
    | ofRefGet cell => exact pre
  have step := syncOpStep_deferredCompleteWith w.state key completion
  obtain ⟨ord, store'⟩ := complete_world store step rfl rfl rfl typed
  have due : DueKept w (w.state.deferreds.complete key completion).1 w.state.deferreds := by
    rw [state]
    exact complete_dueKept wide key completion strong
  exact ev.store_kept hc step (fun h => wf_step h step rfl rfl) store' ord due
    (complete_kept w w.state.deferreds key completion strong) rfl rfl (List.Subset.refl _)
    fun _ _ => ⟨_, rfl⟩

/-- **`deferredInterruptWith`** (`Stores.lean:1142`): an interrupt failure, typed at every
column (`exitOk_interrupts`). -/
theorem clause_deferredInterruptWith (root : ProgramSource) (rootTy : EffTy) (key : DeferredKey)
    (interruptor : FiberId) :
    StoreClauseKeeps root rootTy (.deferredInterruptWith key interruptor) := by
  intro w m rest fb y next ev hc
  have wide := ev.typed.machine.wide
  have state : w.state = m.state := wide.state
  have store := storeTyped_of_typedState ev.typed.machine
  obtain ⟨_, declared⟩ := ev.store_pre hc
  have strong : ∀ a e, w.«Π» key = some (a, e) → CompletionStrong w ⟨a, e, Env.Requirement.empty⟩
      (.ofExit (.failure (Cause.interrupt (some interruptor)))) :=
    fun _ _ _ => exitOk_interrupts w _ fun r hr => by
      rw [Cause.interrupt_reasons, List.mem_singleton] at hr
      subst hr
      rfl
  have step := syncOpStep_deferredInterruptWith w.state key interruptor
  obtain ⟨ord, store'⟩ := complete_world store step rfl rfl rfl (fun _ _ => rfl)
  have due : DueKept w (w.state.deferreds.complete key
      (.ofExit (.failure (Cause.interrupt (some interruptor))))).1 w.state.deferreds := by
    rw [state]
    exact complete_dueKept wide key _ strong
  exact ev.store_kept hc step (fun h => wf_step h step rfl rfl) store' ord due
    (complete_kept w w.state.deferreds key _ strong) rfl rfl (List.Subset.refl _)
    fun _ _ => ⟨_, rfl⟩

/-- **`deferredAwaitCleanup`** (`Stores.lean:1132`): one waiter removed (`cancel_kept`). -/
theorem clause_deferredAwaitCleanup (root : ProgramSource) (rootTy : EffTy) (cell : DeferredKey)
    (waiter : FiberId) (token : Nat) :
    StoreClauseKeeps root rootTy (.deferredAwaitCleanup cell waiter token) := by
  intro w m rest fb y next ev hc
  have store := storeTyped_of_typedState ev.typed.machine
  have step := syncOpStep_deferredAwaitCleanup w.state cell waiter token
  obtain ⟨ord, store'⟩ := restate_world store step rfl (DeferredStore.cancel_cells_length _ _ _ _)
    (fun key c' h => cancel_completions _ _ _ _ key c' h) rfl
  exact ev.store_kept hc step (fun h => wf_step h step rfl rfl) store' ord
    (cancel_dueKept w w.state.deferreds cell waiter token)
    (cancel_kept w w.state.deferreds cell waiter token) rfl rfl (List.Subset.refl _) fun _ _ => rfl

/-- **`sleepCancel`** (`Timer.lean:66`): the sleep's waiter removed
(`Guard.wakeKeys_cancel_subset`). -/
theorem clause_sleepCancel (root : ProgramSource) (rootTy : EffTy) (waiter : FiberId)
    (token : Nat) : StoreClauseKeeps root rootTy (.sleepCancel waiter token) := by
  intro w m rest fb y next ev hc
  have store := storeTyped_of_typedState ev.typed.machine
  have step := syncOpStep_sleepCancel w.state waiter token
  obtain ⟨ord, store'⟩ := restate_world store step rfl rfl (fun _ c' h => ⟨c', h, rfl⟩) rfl
  exact ev.store_kept hc step (fun h => syncOpStep_wf _ _ _ _ h rfl step) store' ord
    (DueKept.refl w _) (CellsKept.refl w _) rfl rfl
    (Guard.wakeKeys_cancel_subset w.state.timers.wake waiter token) fun _ _ => rfl

/-- The store typing after one fresh, empty Deferred cell (`DeferredStore.make`) declared at a
certificate: the fresh cell has no completion, every old cell keeps its key's columns
(`insert_other`), every other column moves to the later world, through the row's new scope and
memo columns. -/
theorem storesOk_make {root : ProgramSource} {w : World} {s s' : Stores} (cert : Ty × Ty)
    (old : StoresOk (preds root) w Expect.root s) (deferreds : s'.deferreds = s.deferreds.make.2)
    (ord : w.leHost (w.addPromise s' s.deferreds.make.1 cert))
    (store : StoreTyped root (w.addPromise s' s.deferreds.make.1 cert))
    (scopes : ScopeStoreOk (preds root) (w.addPromise s' s.deferreds.make.1 cert) Expect.root
        s.scopes →
      ScopeStoreOk (preds root) (w.addPromise s' s.deferreds.make.1 cert) Expect.root s'.scopes)
    (memo : (∀ mm ∈ s.memo, MemoMapOk (preds root) (w.addPromise s' s.deferreds.make.1 cert)
        Expect.root mm) →
      ∀ mm ∈ s'.memo, MemoMapOk (preds root) (w.addPromise s' s.deferreds.make.1 cert)
        Expect.root mm) :
    StoresOk (preds root) (w.addPromise s' s.deferreds.make.1 cert) Expect.root s' := by
  obtain ⟨c0, _, ⟨c2⟩, ⟨c3⟩, c4, c5⟩ := old
  refine ⟨⟨fun o ho ty declared => ?_, store.memoTable⟩,
    fun i v hv ty declared => store.values i v hv ty declared,
    ⟨fun i cell hc a e' declared c hcomp => ?_⟩,
    scopes ⟨fun entry he => ⟨⟨scopeStateOk_world ord (c3 entry he).c0.c0⟩⟩⟩,
    memo fun mm hm => ⟨fun v0 hv => ⟨finNameOk_world ord ((c4 mm hm).c0 v0 hv).c0⟩⟩, c5⟩
  · rw [deferreds] at ho
    exact completionStrong_mono ord (PromiseTableOk.due c0 o ho ty declared)
  · have hc' : (s.deferreds.cells ++ [⟨none, WakeList.empty⟩])[i]? = some cell := by
      rw [deferreds] at hc
      exact hc
    by_cases hi : i < s.deferreds.cells.length
    · rw [List.getElem?_append_left hi] at hc'
      have hne : (⟨i⟩ : DeferredKey) ≠ ⟨s.deferreds.cells.length⟩ := fun e => by
        cases e
        exact Nat.lt_irrefl _ hi
      change tableInsert w.«Π» ⟨s.deferreds.cells.length⟩ cert ⟨i⟩ = some (a, e') at declared
      rw [insert_other _ _ _ _ hne] at declared
      exact completionStrong_mono ord (c2 i cell hc' a e' declared c hcomp)
    · rw [List.getElem?_append_right (Nat.le_of_not_lt hi)] at hc'
      cases hk : i - s.deferreds.cells.length with
      | zero =>
        rw [hk] at hc'
        cases hc'
        cases hcomp
      | succ j =>
        rw [hk] at hc'
        cases hc'

/-- The wake lists after `DeferredStore.make`: the fresh cell has no waiter, the old cells keep
their keys' columns. -/
theorem waiters_make {w : World} {d : DeferredStore} (cert : Ty × Ty) (st : Stores)
    (old : ∀ key cell, d.cellAt key = some cell → ∀ a e, w.«Π» key = some (a, e) →
      WakeTyped w (AwaitDemand a e) cell.wake) :
    ∀ key cell, d.make.2.cellAt key = some cell → ∀ a e,
      (w.addPromise st d.make.1 cert).«Π» key = some (a, e) →
      WakeTyped (w.addPromise st d.make.1 cert) (AwaitDemand a e) cell.wake := by
  intro key cell hcell a e hpi
  change (d.cells ++ [⟨none, WakeList.empty⟩])[key.index]? = some cell at hcell
  by_cases hi : key.index < d.cells.length
  · rw [List.getElem?_append_left hi] at hcell
    have hne : key ≠ ⟨d.cells.length⟩ := fun same => by
      subst same
      exact Nat.lt_irrefl _ hi
    change tableInsert w.«Π» ⟨d.cells.length⟩ cert key = some (a, e) at hpi
    rw [insert_other _ _ _ _ hne] at hpi
    exact old key cell hcell a e hpi
  · rw [List.getElem?_append_right (Nat.le_of_not_lt hi)] at hcell
    cases hk : key.index - d.cells.length with
    | zero =>
      rw [hk] at hcell
      cases hcell
      exact WakeTyped.empty _ _
    | succ j =>
      rw [hk] at hcell
      cases hcell

/-- **`deferredMake`** (`Stores.lean:1099`): the fresh cell declared at the code's certificate
(`deferredMake_world`), empty and unwaited; every other column untouched. -/
theorem clause_deferredMake (root : ProgramSource) (rootTy : EffTy) :
    StoreClauseKeeps root rootTy .deferredMake := by
  intro w m rest fb y next ev hc
  have wide := ev.typed.machine.wide
  have store := storeTyped_of_typedState ev.typed.machine
  have state : w.state = m.state := wide.state
  refine ev.store_step hc (syncOpStep_deferredMake m.state) (fun o ho owner priority mode => ?_)
    fun cert pre => ?_
  · have owned := wide.live.dueOwners o ho owner priority mode
    rw [rfiber?_update, Option.isSome_map] at owned
    exact owned
  · change Ty × Ty at cert
    obtain ⟨ord, store'⟩ := deferredMake_world root w cert store
    rw [state] at ord store'
    exact ⟨_, ord, rfl, rfl, rfl, rfl, store',
      syncOpStep_wf _ _ _ _ wide.wf rfl (syncOpStep_deferredMake m.state),
      storesOk_make cert wide.stores rfl ord store' id id, wide.timers,
      waiters_make cert _ wide.waiters, ⟨_, rfl, insert_here _ _ _⟩⟩

/-- **`memoBuild`** (`Layer.ts:396-411`): the entry's fresh cell declared at the code's
certificate, the layer's columns (`memoBuild_world`), a fresh sequential scope
(`scopeStoreOk_make`) and the entry, whose finalizer is a machine name (`memoMapOk_insertEntry`);
the answer is the fresh scope's handle. -/
theorem clause_memoBuild (root : ProgramSource) (rootTy : EffTy) (layer : LayerId)
    (memoMap : MemoMapId) : StoreClauseKeeps root rootTy (.memoBuild layer memoMap) := by
  intro w m rest fb y next ev hc
  have wide := ev.typed.machine.wide
  have store := storeTyped_of_typedState ev.typed.machine
  have state : w.state = m.state := wide.state
  have step := syncOpStep_memoBuild m.state layer memoMap
  refine ev.store_step hc step (fun o ho owner priority mode => ?_) fun cert pre => ?_
  · have owned := wide.live.dueOwners o ho owner priority mode
    rw [rfiber?_update, Option.isSome_map] at owned
    exact owned
  · change Ty × Ty at cert
    obtain ⟨ord, store'⟩ := memoBuild_world root w layer memoMap cert store pre
    rw [state] at ord store'
    exact ⟨_, ord, rfl, rfl, rfl, rfl, store', wf_step wide.wf step rfl rfl,
      storesOk_make cert wide.stores rfl ord store'
        (fun old => scopeStoreOk_make old m.state.nextName .sequential)
        (fun old => memoMapOk_insertEntry old memoMap layer trivial),
      wide.timers, waiters_make cert _ wide.waiters,
      fits_scopeHandle _ _ (ScopeStore.entryAt_make_self _ _ _)⟩

/-- **`memoComplete`** (`Layer.ts`, the build's exit): a hit completes the entry's cell, which the
memo table declares at the layer's columns, the pre's exit fitting them; a miss changes nothing. -/
theorem clause_memoComplete (root : ProgramSource) (rootTy : EffTy) (layer : LayerId)
    (memoMap : MemoMapId) (exit : ExitV) :
    StoreClauseKeeps root rootTy (.memoComplete layer memoMap exit) := by
  intro w m rest fb y next ev hc
  have wide := ev.typed.machine.wide
  have state : w.state = m.state := wide.state
  have store := storeTyped_of_typedState ev.typed.machine
  obtain ⟨_, l, lt, node, checked, fits⟩ := ev.store_pre hc
  cases hentry : w.state.memo.entryAt memoMap layer with
  | none =>
    rw [state] at hentry
    exact ev.store_same hc Val.unit (syncOpStep_memoComplete_none _ _ _ _ hentry) fun _ _ => rfl
  | some entry =>
    have step := syncOpStep_memoComplete_some w.state layer memoMap exit hentry
    obtain ⟨mm, hm, _, he⟩ := MemoWorld.entryAt_mem hentry
    have declared := store.memoTable (layer, entry.deferred)
      (MemoWorld.mem_layerCells.mpr ⟨mm, hm, (layer, entry), he, rfl⟩) l lt node checked
    have strong : ∀ a e, w.«Π» entry.deferred = some (a, e) →
        CompletionStrong w ⟨a, e, Env.Requirement.empty⟩ (.ofExit exit) := by
      intro a e h
      rw [declared] at h
      cases h
      exact fits
    obtain ⟨ord, store'⟩ := complete_world store step rfl rfl rfl fun types h => by
      rw [declared] at h
      cases h
      exact completionOk_of_fitsExit fits.1
    have due : DueKept w (w.state.deferreds.complete entry.deferred (.ofExit exit)).1
        w.state.deferreds := by
      rw [state]
      exact complete_dueKept wide entry.deferred _ strong
    exact ev.store_kept hc step (fun h => wf_step h step rfl rfl) store' ord due
      (complete_kept w w.state.deferreds entry.deferred _ strong) rfl rfl (List.Subset.refl _)
      fun _ _ => rfl

end Effect4.Program.Typed
