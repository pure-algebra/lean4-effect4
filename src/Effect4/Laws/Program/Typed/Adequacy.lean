import Effect4.Laws.Program.Typed.Residual
import Effect4.Laws.Machine.StoresLaws

/-!
# Laws.Program.Typed.Adequacy — every protocol row is fulfilled by its handler

Decisions row 136 (`E4-TYPED-CE-010`, `E4-TYPED-CE-013`). A protocol row's post is what
`TypedProg` types a continuation on, so a typed program's next step is typed only if the answer
the handler actually gives lies in the post. That is the premise of Hazel's handler rule
(de Vilhena, Def. 2.2, read through the 2026-09-05 papers review, A2, which proposed it as
`Implements`), stated here for the reference machine.

**The store rows.** `StoreImplements root op`: from a world whose store is typed
(`StoreTyped`), a request the row's pre admits steps, so the store never reaches a frontier
(`syncOpStep` answering `none`, which the evaluator answers `unit`, `EvaluateR.lean:304`), and its
answer lies in the row's post at a later world over the new store, which is typed again.
`storeStep_typed` is the handler rule for `TypedProg`'s store arm, one theorem for every row: a
typed store operation run by a handler that fulfils its row steps to a typed continuation. Each
row's fulfilment is one instance; the open ones are declared in `M3bAdequacy`.

This module proves no command preservation step: `StoreTyped` is the store half of the typed
state, which M6's `loop`/`deliver` arms supply and consume.
-/

set_option autoImplicit false
namespace Effect4.Program.Typed
open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Sched Effect4.Program.Denote
open Contracts

/-! ## The handler judgment for the store rows -/

/-- The store half of the typed state that the store rows read and keep: the world's
declarations cover exactly the allocated cells and promises (`WorldValid.heap`, `.promises`),
every stored value fits its cell's declared type (the generated `HeapCell` column), and every
closing exit a scope holds fits `Exit<unknown, unknown>` (DI-94's release type: the
`ScopeState.closed.exit` source row, which seat C un-refuses). -/
structure StoreTyped (w : World) : Prop where
  heap : ∀ key, (w.Ρ key).isSome = true ↔ key.index < w.state.refs.length
  promises : ∀ key, (w.«Π» key).isSome = true ↔ key.index < w.state.deferreds.cells.length
  values : ∀ (i : Nat) (v : Val), w.state.refs[i]? = some v → ∀ ty, w.Ρ ⟨i⟩ = some ty → Fits w v ty
  scopeExits : ∀ e ∈ w.state.scopes.entries, ∀ ex, e.scope.closingExit? = some ex →
    FitsExit w ⟨.unknown, .unknown, Env.Requirement.empty⟩ ex

/-- **The store handler fulfils row `op`** (the 2026-09-05 review's `Implements`): at a world
whose store is typed, a request the row's pre admits steps (no frontier), and its answer lies in
the row's post at a later world over the new store, which is typed again. -/
def StoreImplements (root : ProgramSource) (op : SyncOp) : Prop :=
  ∀ (w : World) (cert : StoreCert op), StoreTyped w → storePre root w op cert →
    ∃ st' ans, syncOpStep op w.state = some (st', ans) ∧
      ∃ w', w.leHost w' ∧ w'.state = st' ∧ StoreTyped w' ∧ storePost w' op cert ans

/-- **The handler rule for `TypedProg`'s store arm**, one theorem for every row: a typed store
operation run by a handler that fulfils its row steps to a typed continuation at a later world
over the new store, which is typed again. This is what the evaluator's store arm needs
(`evaluateRawR` installs `k ans` over the new store). -/
theorem storeStep_typed {root : ProgramSource} {op : SyncOp} (impl : StoreImplements root op)
    {w : World} {ty : EffTy} {k : Val → RProgram}
    (typed : TypedProg root w ty (.vis (.inl op) k)) (store : StoreTyped w) :
    ∃ st' ans, syncOpStep op w.state = some (st', ans) ∧
      ∃ w', w.leHost w' ∧ w'.state = st' ∧ StoreTyped w' ∧ TypedProg root w' ty (k ans) := by
  obtain ⟨cert, pre, next⟩ := TypedProg.store_inv typed
  obtain ⟨st', ans, step, w', ord, hstate, store', post⟩ := impl w cert store pre
  exact ⟨st', ans, step, w', ord, hstate, store', next w' ord ans post⟩

/-- A typed store operation never reaches the evaluator's frontier branch, which answers
`unit` whatever the row's post says. -/
theorem storeStep_answers {root : ProgramSource} {op : SyncOp} (impl : StoreImplements root op)
    {w : World} {ty : EffTy} {k : Val → RProgram}
    (typed : TypedProg root w ty (.vis (.inl op) k)) (store : StoreTyped w) :
    syncOpStep op w.state ≠ none := by
  obtain ⟨st', ans, step, _⟩ := storeStep_typed impl typed store
  rw [step]
  exact fun h => nomatch h

/-! ## Moving the world along a store step -/

/-- A store step that keeps the heap, the Deferred cells' completions and the external
spellings moves to the world over the new store: later in the host order, and typed. -/
theorem restate_world {w : World} {op : SyncOp} {st' : Stores} {ans : Val}
    (store : StoreTyped w) (step : syncOpStep op w.state = some (st', ans))
    (refs : st'.refs = w.state.refs)
    (cellsLength : st'.deferreds.cells.length = w.state.deferreds.cells.length)
    (completions : ∀ key c', st'.deferreds.cellAt key = some c' →
      ∃ c, w.state.deferreds.cellAt key = some c ∧ c'.completion = c.completion)
    (externals : st'.externals = w.state.externals) :
    w.leHost { w with state := st' } ∧ StoreTyped { w with state := st' } := by
  have le := syncOpStep_le op w.state st' ans step
  have ext : Extends w.state.externals.allocated st'.externals.allocated := by
    rw [externals]
    exact fun _ _ h => h
  have ord : w.leHost { w with state := st' } := by
    refine ⟨⟨⟨fun _ h => h, le⟩, fun _ _ h => h, fun _ _ h => h, fun _ _ h => h, ⟨?_, ?_⟩,
      fun _ _ _ h => h, rfl⟩, ext⟩
    · intro key ty h
      refine ⟨h.1, fun value hv => ?_⟩
      have hv' : refPeek w.state.refs key = some value := by
        change refPeek st'.refs key = some value at hv
        rw [refs] at hv
        exact hv
      exact value_transport w { w with state := st' } ty value ext (h.2 value hv')
    · intro key types h
      refine ⟨h.1, fun cell hc completion hcomp => ?_⟩
      obtain ⟨c, hc0, same⟩ := completions key cell hc
      rw [same] at hcomp
      exact completion_transport w { w with state := st' } types (fun _ _ h => h) ext completion
        (h.2 c hc0 completion hcomp)
  refine ⟨ord, ⟨?_, ?_, ?_, ?_⟩⟩
  · intro key
    change (w.Ρ key).isSome = true ↔ key.index < st'.refs.length
    rw [refs]
    exact store.heap key
  · intro key
    change (w.«Π» key).isSome = true ↔ key.index < st'.deferreds.cells.length
    rw [cellsLength]
    exact store.promises key
  · intro i v hv ty hty
    change st'.refs[i]? = some v at hv
    rw [refs] at hv
    exact fits_mono ord (store.values i v hv ty hty)
  · intro e he ex hex
    obtain ⟨e₀, he₀, hex₀⟩ := syncOpStep_closingExit op w.state st' ans step e he ex hex
    exact fitsExit_mono ord (store.scopeExits e₀ he₀ ex hex₀)

/-- A step that keeps the whole store answers at the same world. -/
theorem same_world {w : World} {op : SyncOp} {ans : Val} (store : StoreTyped w)
    {post : World → Val → Prop} (holds : post w ans)
    (step : syncOpStep op w.state = some (w.state, ans)) :
    ∃ st' ans', syncOpStep op w.state = some (st', ans') ∧
      ∃ w', w.leHost w' ∧ w'.state = st' ∧ StoreTyped w' ∧ post w' ans' :=
  ⟨w.state, ans, step, w, leHost_refl w, rfl, store, holds⟩

/-! ## Value facts the store rows read -/

/-- On a `nat` cell, `modify` answers the old value and writes a `nat`. -/
theorem modify_nat (f : FnName) (n : Nat) :
    (f.modify (.nat n)).1 = .nat n ∧ ∃ m, (f.modify (.nat n)).2 = .nat m := by
  cases f <;> exact ⟨rfl, _, rfl⟩

theorem modifySome_nat (f : FnName) (n : Nat) :
    (f.modifySome (.nat n)).1 = .nat n ∧ ∃ m, (f.modifySome (.nat n)).2.getD (.nat n) = .nat m := by
  cases f <;> exact ⟨rfl, _, rfl⟩

/-- A declared cell holds a value: reading it is not a frontier. -/
theorem cell_readable {w : World} {cell : RefKey} {t : Ty} (store : StoreTyped w)
    (declared : w.Ρ cell = some t) : ∃ a, w.state.refs[cell.index]? = some a :=
  ⟨_, List.getElem?_eq_getElem ((store.heap cell).mp (by rw [declared]; rfl))⟩

/-- A declared promise has a cell: reading it is not a frontier. -/
theorem promise_readable {w : World} {key : DeferredKey} (store : StoreTyped w)
    (declared : (w.«Π» key).isSome = true) : ∃ c, w.state.deferreds.cells[key.index]? = some c :=
  ⟨_, List.getElem?_eq_getElem ((store.promises key).mp declared)⟩

/-- The cell a `refModify`-like row names holds a `nat` at a cell declared at the native row's
cell type; reading it is not a frontier. -/
theorem nat_cell {w : World} {cell : RefKey} (store : StoreTyped w) (pre : RefDeclared w cell .nat) :
    ∃ t n, w.Ρ cell = some t ∧ Equiv t .nat ∧ refPeek w.state.refs cell = some (.nat n) := by
  obtain ⟨t, declared, equiv⟩ := pre
  have live : cell.index < w.state.refs.length := (store.heap cell).mp (by rw [declared]; rfl)
  obtain ⟨a, ha⟩ : ∃ a, w.state.refs[cell.index]? = some a :=
    ⟨_, List.getElem?_eq_getElem live⟩
  have fa : Fits w a t := store.values cell.index a ha t declared
  obtain ⟨n, rfl⟩ := fits_nat_inv (fits_subN w equiv.1 a fa)
  exact ⟨t, n, declared, equiv, ha⟩

/-- A table that covers exactly the indices below `n`, extended by the one key at index `n`,
covers exactly the indices below `n + 1`. -/
theorem insert_coverage {K A : Type} [DecidableEq K] {table : K → Option A} {index : K → Nat}
    {n : Nat} {key : K} {value : A} (keyIndex : index key = n) (inj : ∀ k, index k = n → k = key)
    (cover : ∀ k, (table k).isSome = true ↔ index k < n) :
    ∀ k, (tableInsert table key value k).isSome = true ↔ index k < n + 1 := by
  intro k
  by_cases hk : k = key
  · rw [hk, insert_here, keyIndex]
    exact ⟨fun _ => Nat.lt_succ_self n, fun _ => rfl⟩
  · rw [insert_other _ _ _ _ hk, cover k]
    have hne : index k ≠ n := fun e => hk (inj k e)
    exact ⟨Nat.lt_succ_of_lt, fun h => Nat.lt_of_le_of_ne (Nat.lt_succ_iff.mp h) hne⟩

/-- `cancel` (`Stores.lean:1132-1136`) changes a cell's waiters only. -/
theorem cancel_completions (d : DeferredStore) (cell : DeferredKey) (waiter : FiberId) (token : Nat)
    (key : DeferredKey) (c' : DeferredCell) (h : (d.cancel cell waiter token).cellAt key = some c') :
    ∃ c, d.cellAt key = some c ∧ c'.completion = c.completion := by
  unfold DeferredStore.cancel at h
  split at h
  · exact ⟨c', h, rfl⟩
  · rename_i c0 hc0
    unfold DeferredStore.setCell DeferredStore.cellAt at h
    rw [List.getElem?_set] at h
    split at h
    · rename_i same
      split at h
      · cases h
        refine ⟨c0, ?_, rfl⟩
        unfold DeferredStore.cellAt at hc0 ⊢
        rw [← same]
        exact hc0
      · cases h
    · exact ⟨c', h, rfl⟩

/-- `complete` (`Stores.lean`, `doneUnsafe`) stores a completion in an empty cell and changes no
other cell's completion. -/
theorem complete_cellAt (d : DeferredStore) (cell : DeferredKey) (effect : Completion Val Err Defect FiberId Ann)
    (key : DeferredKey) (c' : DeferredCell) (h : (d.complete cell effect).1.cellAt key = some c') :
    (∃ c, d.cellAt key = some c ∧ c'.completion = c.completion) ∨
      (key.index = cell.index ∧ c'.completion = some effect) := by
  unfold DeferredStore.complete at h
  split at h
  · exact Or.inl ⟨c', h, rfl⟩
  · rename_i c0 hc0
    split at h
    · exact Or.inl ⟨c', h, rfl⟩
    · unfold DeferredStore.setCell DeferredStore.cellAt at h
      rw [List.getElem?_set] at h
      split at h
      · rename_i same
        split at h
        · cases h
          exact Or.inr ⟨same.symm, rfl⟩
        · cases h
      · exact Or.inl ⟨c', h, rfl⟩

theorem complete_cells_length (d : DeferredStore) (cell : DeferredKey)
    (effect : Completion Val Err Defect FiberId Ann) :
    (d.complete cell effect).1.cells.length = d.cells.length := by
  unfold DeferredStore.complete
  split
  · rfl
  · split
    · rfl
    · exact List.length_set

/-! ## Moving the world along a ref write and a completion -/

/-- A store step that writes one ref cell with a value its declared type admits moves to the world
over the new store: later in the host order, and typed. -/
theorem poke_world {w : World} {op : SyncOp} {st' : Stores} {ans : Val} {cell : RefKey} {t : Ty}
    {v : Val} (store : StoreTyped w) (step : syncOpStep op w.state = some (st', ans))
    (refs : st'.refs = refPoke w.state.refs cell v) (deferreds : st'.deferreds = w.state.deferreds)
    (externals : st'.externals = w.state.externals)
    (declared : w.Ρ cell = some t) (fits : Fits w v t) :
    w.leHost { w with state := st' } ∧ StoreTyped { w with state := st' } := by
  have le := syncOpStep_le op w.state st' ans step
  have ext : Extends w.state.externals.allocated st'.externals.allocated := by
    rw [externals]
    exact fun _ _ h => h
  have written : ∀ (i : Nat) (x : Val), st'.refs[i]? = some x →
      (i = cell.index ∧ x = v) ∨ (i ≠ cell.index ∧ w.state.refs[i]? = some x) := by
    intro i x hx
    rw [refs] at hx
    unfold refPoke at hx
    rw [List.getElem?_set] at hx
    split at hx
    · rename_i same
      split at hx
      · cases hx
        exact Or.inl ⟨same.symm, rfl⟩
      · cases hx
    · rename_i other
      exact Or.inr ⟨fun h => other h.symm, hx⟩
  have ord : w.leHost { w with state := st' } := by
    refine ⟨⟨⟨fun _ h => h, le⟩, fun _ _ h => h, fun _ _ h => h, fun _ _ h => h, ⟨?_, ?_⟩,
      fun _ _ _ h => h, rfl⟩, ext⟩
    · intro key ty h
      refine ⟨h.1, fun value hv => ?_⟩
      change st'.refs[key.index]? = some value at hv
      rcases written key.index value hv with ⟨same, rfl⟩ | ⟨_, old⟩
      · have hkey : key = cell := by
          cases key with
          | mk i =>
            cases cell with
            | mk c =>
              change i = c at same
              rw [same]
        have hty := h.1
        rw [hkey, declared] at hty
        cases hty
        exact value_transport w { w with state := st' } t value ext (fits_hasTy w t value fits)
      · exact value_transport w { w with state := st' } ty value ext (h.2 value old)
    · intro key types h
      refine ⟨h.1, fun c hc completion hcomp => ?_⟩
      change st'.deferreds.cellAt key = some c at hc
      rw [deferreds] at hc
      exact completion_transport w { w with state := st' } types (fun _ _ h => h) ext completion
        (h.2 c hc completion hcomp)
  refine ⟨ord, ⟨?_, ?_, ?_, ?_⟩⟩
  · intro key
    change (w.Ρ key).isSome = true ↔ key.index < st'.refs.length
    rw [refs]
    unfold refPoke
    rw [List.length_set]
    exact store.heap key
  · intro key
    change (w.«Π» key).isSome = true ↔ key.index < st'.deferreds.cells.length
    rw [deferreds]
    exact store.promises key
  · intro i x hx ty hty
    rcases written i x hx with ⟨same, rfl⟩ | ⟨_, old⟩
    · have hkey : (⟨i⟩ : RefKey) = cell := by
        cases cell with
        | mk c =>
          change i = c at same
          rw [same]
      rw [hkey, declared] at hty
      cases hty
      exact fits_mono ord fits
    · exact fits_mono ord (store.values i x old ty hty)
  · intro e he ex hex
    obtain ⟨e₀, he₀, hex₀⟩ := syncOpStep_closingExit op w.state st' ans step e he ex hex
    exact fitsExit_mono ord (store.scopeExits e₀ he₀ ex hex₀)

/-- A store step that completes one promise with a completion its declared columns admit moves to
the world over the new store: later in the host order, and typed. -/
theorem complete_world {w : World} {op : SyncOp} {st' : Stores} {ans : Val} {cell : DeferredKey}
    {effect : Completion Val Err Defect FiberId Ann}
    (store : StoreTyped w) (step : syncOpStep op w.state = some (st', ans))
    (deferreds : st'.deferreds = (w.state.deferreds.complete cell effect).1)
    (refs : st'.refs = w.state.refs) (externals : st'.externals = w.state.externals)
    (typed : ∀ types, w.«Π» cell = some types → CompletionOk w types effect) :
    w.leHost { w with state := st' } ∧ StoreTyped { w with state := st' } := by
  have le := syncOpStep_le op w.state st' ans step
  have ext : Extends w.state.externals.allocated st'.externals.allocated := by
    rw [externals]
    exact fun _ _ h => h
  have ord : w.leHost { w with state := st' } := by
    refine ⟨⟨⟨fun _ h => h, le⟩, fun _ _ h => h, fun _ _ h => h, fun _ _ h => h, ⟨?_, ?_⟩,
      fun _ _ _ h => h, rfl⟩, ext⟩
    · intro key ty h
      refine ⟨h.1, fun value hv => ?_⟩
      have hv' : refPeek w.state.refs key = some value := by
        change refPeek st'.refs key = some value at hv
        rw [refs] at hv
        exact hv
      exact value_transport w { w with state := st' } ty value ext (h.2 value hv')
    · intro key types h
      refine ⟨h.1, fun c' hc completion hcomp => ?_⟩
      change st'.deferreds.cellAt key = some c' at hc
      rw [deferreds] at hc
      rcases complete_cellAt _ _ _ key c' hc with ⟨c, hc0, same⟩ | ⟨same, stored⟩
      · rw [same] at hcomp
        exact completion_transport w { w with state := st' } types (fun _ _ h => h) ext completion
          (h.2 c hc0 completion hcomp)
      · rw [stored] at hcomp
        cases hcomp
        have hkey : key = cell := by
          cases key with
          | mk i =>
            cases cell with
            | mk c =>
              change i = c at same
              rw [same]
        rw [hkey] at h
        exact completion_transport w { w with state := st' } types (fun _ _ h => h) ext effect
          (typed types h.1)
  refine ⟨ord, ⟨?_, ?_, ?_, ?_⟩⟩
  · intro key
    change (w.Ρ key).isSome = true ↔ key.index < st'.refs.length
    rw [refs]
    exact store.heap key
  · intro key
    change (w.«Π» key).isSome = true ↔ key.index < st'.deferreds.cells.length
    rw [deferreds, complete_cells_length]
    exact store.promises key
  · intro i v hv ty hty
    change st'.refs[i]? = some v at hv
    rw [refs] at hv
    exact fits_mono ord (store.values i v hv ty hty)
  · intro e he ex hex
    obtain ⟨e₀, he₀, hex₀⟩ := syncOpStep_closingExit op w.state st' ans step e he ex hex
    exact fitsExit_mono ord (store.scopeExits e₀ he₀ ex hex₀)

/-! ## The store rows, one instance each

Twenty-three of the thirty-one rows. The six read-modify-write rows that write `f.total a`
(`refUpdate`, `refGetAndUpdate`, `refUpdateAndGet`, `refUpdateSome`, `refGetAndUpdateSome`,
`refUpdateSomeAndGet`) need `Fits w (nat n) t → Fits w (nat m) t`, one induction over the
membership fold in `Membership.lean`; `memoGet` and `memoComplete` need a memo-table typing clause
(every entry's Deferred declared at its layer's context and error types) that no typed-state
clause states yet. Those eight are declared in `M3bAdequacy`. -/

theorem scopeRemove_implements (root : ProgramSource) (scope key : Nat) :
    StoreImplements root (.scopeRemove scope key) := by
  intro w _ store _
  obtain ⟨ord, store'⟩ := restate_world (op := .scopeRemove scope key) store rfl rfl rfl
    (fun _ c' h => ⟨c', h, rfl⟩) rfl
  exact ⟨_, _, rfl, _, ord, rfl, store', rfl⟩

theorem scopeAdd_implements (root : ProgramSource) (scope : Nat) (fin : FinName) :
    StoreImplements root (.scopeAdd scope fin) := by
  intro w cert store pre
  change (w.state.scopes.entryAt scope).isSome = true at pre
  cases hentry : w.state.scopes.entryAt scope with
  | none =>
    rw [hentry] at pre
    cases pre
  | some entry =>
    cases hexit : entry.scope.closingExit? with
    | some ex =>
      have step : syncOpStep (.scopeAdd scope fin) w.state = some (w.state, reifyExitVal ex) := by
        simp only [syncOpStep, hentry, hexit]
      exact same_world store (post := fun w' a => storePost w' (.scopeAdd scope fin) cert a)
        (Or.inr ⟨ex, rfl, store.scopeExits entry (List.mem_of_find?_eq_some hentry) ex hexit⟩) step
    | none =>
      have step : syncOpStep (.scopeAdd scope fin) w.state = some ({ w.state with
          scopes := w.state.scopes.setEntry
            { entry with scope := entry.scope.addUnsafe w.state.nextName fin }
          nextName := w.state.nextName + 1 }, Val.unit) := by
        simp only [syncOpStep, hentry, hexit]
      obtain ⟨ord, store'⟩ := restate_world store step rfl rfl (fun _ c' h => ⟨c', h, rfl⟩) rfl
      exact ⟨_, _, step, _, ord, rfl, store', Or.inl rfl⟩

theorem deferredAwaitCleanup_implements (root : ProgramSource) (cell : DeferredKey) (waiter : FiberId)
    (token : Nat) : StoreImplements root (.deferredAwaitCleanup cell waiter token) := by
  intro w _ store _
  obtain ⟨ord, store'⟩ := restate_world (op := .deferredAwaitCleanup cell waiter token) store rfl rfl
    (DeferredStore.cancel_cells_length _ _ _ _) (fun key c' h => cancel_completions _ _ _ _ key c' h) rfl
  exact ⟨_, _, rfl, _, ord, rfl, store', rfl⟩

theorem memoRelease_implements (root : ProgramSource) (layer : LayerId) (memoMap : MemoMapId) :
    StoreImplements root (.memoRelease layer memoMap) := by
  intro w cert store _
  cases hentry : w.state.memo.entryAt memoMap layer with
  | none =>
    exact same_world store (post := fun w' a => storePost w' (.memoRelease layer memoMap) cert a)
      (Or.inl rfl) (syncOpStep_memoRelease_none _ _ _ hentry)
  | some entry =>
    by_cases hobs : entry.observers ≤ 1
    · have step := syncOpStep_memoRelease_last _ _ _ hentry hobs
      obtain ⟨ord, store'⟩ := restate_world store step rfl rfl (fun _ c' h => ⟨c', h, rfl⟩) rfl
      exact ⟨_, _, step, _, ord, rfl, store', Or.inr ⟨_, rfl⟩⟩
    · have step := syncOpStep_memoRelease_dec _ _ _ hentry hobs
      obtain ⟨ord, store'⟩ := restate_world store step rfl rfl (fun _ c' h => ⟨c', h, rfl⟩) rfl
      exact ⟨_, _, step, _, ord, rfl, store', Or.inl rfl⟩

theorem refModify_implements (root : ProgramSource) (cell : RefKey) (f : FnName) :
    StoreImplements root (.refModify cell f) := by
  intro w _ store pre
  obtain ⟨t, n, declared, equiv, peek⟩ := nat_cell store pre
  obtain ⟨answer, m, written⟩ := modify_nat f n
  have step : syncOpStep (.refModify cell f) w.state = some ({ w.state with
      refs := refPoke w.state.refs cell (f.modify (.nat n)).2 }, (f.modify (.nat n)).1) := by
    simp only [syncOpStep, refStep, peek, Option.map_some]
  have fits : Fits w (f.modify (.nat n)).2 t := by
    rw [written]
    exact fits_subN w equiv.2 _ trivial
  obtain ⟨ord, store'⟩ := poke_world store step rfl rfl rfl declared fits
  exact ⟨_, _, step, _, ord, rfl, store', ⟨n, answer⟩⟩

theorem refModifySome_implements (root : ProgramSource) (cell : RefKey) (f : FnName) :
    StoreImplements root (.refModifySome cell f) := by
  intro w _ store pre
  obtain ⟨t, n, declared, equiv, peek⟩ := nat_cell store pre
  obtain ⟨answer, m, written⟩ := modifySome_nat f n
  have step : syncOpStep (.refModifySome cell f) w.state = some ({ w.state with
      refs := refPoke w.state.refs cell ((f.modifySome (.nat n)).2.getD (.nat n)) },
      (f.modifySome (.nat n)).1) := by
    simp only [syncOpStep, refStep, peek, Option.map_some]
  have fits : Fits w ((f.modifySome (.nat n)).2.getD (.nat n)) t := by
    rw [written]
    exact fits_subN w equiv.2 _ trivial
  obtain ⟨ord, store'⟩ := poke_world store step rfl rfl rfl declared fits
  exact ⟨_, _, step, _, ord, rfl, store', ⟨n, answer⟩⟩

theorem refMake_implements (root : ProgramSource) (initial : Val) :
    StoreImplements root (.refMake initial) := by
  intro w cert store pre
  change Ty at cert
  obtain ⟨_, fits⟩ := pre
  have fresh : w.Ρ ⟨w.state.refs.length⟩ = none := by
    cases h : w.Ρ ⟨w.state.refs.length⟩ with
    | none => rfl
    | some t =>
      have := (store.heap ⟨w.state.refs.length⟩).mp (by rw [h]; rfl)
      exact absurd this (Nat.lt_irrefl _)
  have step := syncOpStep_refMake w.state initial
  obtain ⟨le, _⟩ := refMake_extension w initial cert _ _ step fresh (fits_hasTy w cert initial fits)
  have ord : w.leHost (w.addRef { w.state with refs := w.state.refs ++ [initial] }
      ⟨w.state.refs.length⟩ cert) := ⟨le, fun _ _ h => h⟩
  refine ⟨_, _, step, _, ord, rfl, ⟨?_, ?_, ?_, ?_⟩, ⟨_, rfl, insert_here _ _ _⟩⟩
  · change ∀ k, (tableInsert w.Ρ ⟨w.state.refs.length⟩ cert k).isSome = true ↔
      k.index < (w.state.refs ++ [initial]).length
    rw [List.length_append, List.length_singleton]
    exact insert_coverage (index := RefKey.index) rfl
      (fun k e => by cases k; cases e; rfl) store.heap
  · exact store.promises
  · intro i v hv ty hty
    change (w.state.refs ++ [initial])[i]? = some v at hv
    change tableInsert w.Ρ ⟨w.state.refs.length⟩ cert ⟨i⟩ = some ty at hty
    by_cases hi : i < w.state.refs.length
    · rw [List.getElem?_append_left hi] at hv
      have hne : (⟨i⟩ : RefKey) ≠ ⟨w.state.refs.length⟩ := fun e => by
        cases e
        exact Nat.lt_irrefl _ hi
      rw [insert_other _ _ _ _ hne] at hty
      exact fits_mono ord (store.values i v hv ty hty)
    · rw [List.getElem?_append_right (Nat.le_of_not_lt hi)] at hv
      have hlast : i = w.state.refs.length := by
        cases hk : i - w.state.refs.length with
        | zero => exact Nat.le_antisymm (Nat.sub_eq_zero_iff_le.mp hk) (Nat.le_of_not_lt hi)
        | succ j =>
          rw [hk] at hv
          cases hv
      subst hlast
      rw [Nat.sub_self] at hv
      cases hv
      rw [insert_here] at hty
      cases hty
      exact fits_mono ord fits
  · intro e he ex hex
    obtain ⟨e₀, he₀, hex₀⟩ := syncOpStep_closingExit _ w.state _ _ step e he ex hex
    exact fitsExit_mono ord (store.scopeExits e₀ he₀ ex hex₀)

theorem refGet_implements (root : ProgramSource) (cell : RefKey) :
    StoreImplements root (.refGet cell) := by
  intro w cert store pre
  obtain ⟨t, declared⟩ := pre
  obtain ⟨a, ha⟩ := cell_readable store declared
  have step : syncOpStep (.refGet cell) w.state = some (w.state, a) := by
    simp only [syncOpStep, refStep, refPeek, ha, Option.map_some]
  exact same_world store (post := fun w' x => storePost w' (.refGet cell) cert x)
    ⟨t, declared, store.values cell.index a ha t declared⟩ step

theorem refSet_implements (root : ProgramSource) (cell : RefKey) (v : Val) :
    StoreImplements root (.refSet cell v) := by
  intro w _ store pre
  obtain ⟨t, declared, fits⟩ := pre
  obtain ⟨a, ha⟩ := cell_readable store declared
  have step : syncOpStep (.refSet cell v) w.state =
      some ({ w.state with refs := refPoke w.state.refs cell v }, Val.cell cell) := by
    simp only [syncOpStep, refStep, refPeek, ha, Option.map_some]
  obtain ⟨ord, store'⟩ := poke_world store step rfl rfl rfl declared fits
  exact ⟨_, _, step, _, ord, rfl, store', rfl⟩

theorem refGetAndSet_implements (root : ProgramSource) (cell : RefKey) (v : Val) :
    StoreImplements root (.refGetAndSet cell v) := by
  intro w _ store pre
  obtain ⟨t, declared, fits⟩ := pre
  obtain ⟨a, ha⟩ := cell_readable store declared
  have step : syncOpStep (.refGetAndSet cell v) w.state =
      some ({ w.state with refs := refPoke w.state.refs cell v }, a) := by
    simp only [syncOpStep, refStep, refPeek, ha, Option.map_some]
  obtain ⟨ord, store'⟩ := poke_world store step rfl rfl rfl declared fits
  exact ⟨_, _, step, _, ord, rfl, store',
    ⟨t, declared, fits_mono ord (store.values cell.index a ha t declared)⟩⟩

theorem refSetAndGet_implements (root : ProgramSource) (cell : RefKey) (v : Val) :
    StoreImplements root (.refSetAndGet cell v) := by
  intro w _ store pre
  obtain ⟨t, declared, fits⟩ := pre
  obtain ⟨a, ha⟩ := cell_readable store declared
  have step : syncOpStep (.refSetAndGet cell v) w.state =
      some ({ w.state with refs := refPoke w.state.refs cell v }, v) := by
    simp only [syncOpStep, refStep, refPeek, ha, Option.map_some]
  obtain ⟨ord, store'⟩ := poke_world store step rfl rfl rfl declared fits
  exact ⟨_, _, step, _, ord, rfl, store', ⟨t, declared, fits_mono ord fits⟩⟩

theorem deferredMake_implements (root : ProgramSource) : StoreImplements root .deferredMake := by
  intro w cert store _
  change Ty × Ty at cert
  have fresh : w.«Π» w.state.deferreds.make.1 = none := by
    cases h : w.«Π» w.state.deferreds.make.1 with
    | none => rfl
    | some t =>
      have := (store.promises w.state.deferreds.make.1).mp (by rw [h]; rfl)
      exact absurd this (Nat.lt_irrefl _)
  have step := syncOpStep_deferredMake w.state
  obtain ⟨le, _⟩ := deferredMake_extension w cert _ _ step fresh
  have ord : w.leHost (w.addPromise { w.state with deferreds := w.state.deferreds.make.2 }
      w.state.deferreds.make.1 cert) := ⟨le, fun _ _ h => h⟩
  refine ⟨_, _, step, _, ord, rfl, ⟨?_, ?_, ?_, ?_⟩, ⟨_, rfl, insert_here _ _ _⟩⟩
  · exact store.heap
  · change ∀ k, (tableInsert w.«Π» w.state.deferreds.make.1 cert k).isSome = true ↔
      k.index < w.state.deferreds.make.2.cells.length
    have hlen : w.state.deferreds.make.2.cells.length = w.state.deferreds.cells.length + 1 := by
      simp only [DeferredStore.make, List.length_append, List.length_singleton]
    rw [hlen]
    exact insert_coverage (index := DeferredKey.index) rfl
      (fun k e => by cases k; cases e; rfl) store.promises
  · intro i v hv ty hty
    exact fits_mono ord (store.values i v hv ty hty)
  · intro e he ex hex
    obtain ⟨e₀, he₀, hex₀⟩ := syncOpStep_closingExit _ w.state _ _ step e he ex hex
    exact fitsExit_mono ord (store.scopeExits e₀ he₀ ex hex₀)

theorem deferredIsDone_implements (root : ProgramSource) (key : DeferredKey) :
    StoreImplements root (.deferredIsDone key) := by
  intro w cert store pre
  obtain ⟨c, hc⟩ := promise_readable store pre
  have step : syncOpStep (.deferredIsDone key) w.state =
      some (w.state, Val.bool c.completion.isSome) := by
    simp only [syncOpStep, DeferredStore.isDone, DeferredStore.cellAt, hc, Option.map_some]
  exact same_world store (post := fun w' x => storePost w' (.deferredIsDone key) cert x) ⟨_, rfl⟩ step

theorem deferredPoll_implements (root : ProgramSource) (key : DeferredKey) :
    StoreImplements root (.deferredPoll key) := by
  intro w cert store pre
  obtain ⟨c, hc⟩ := promise_readable store pre
  have step : syncOpStep (.deferredPoll key) w.state =
      some (w.state, Val.bool c.completion.isSome) := by
    simp only [syncOpStep, DeferredStore.poll, DeferredStore.cellAt, hc, Option.map_some]
  exact same_world store (post := fun w' x => storePost w' (.deferredPoll key) cert x) ⟨_, rfl⟩ step

theorem deferredCompleteWith_implements (root : ProgramSource) (key : DeferredKey)
    (completion : Completion Val Err Defect FiberId Ann) :
    StoreImplements root (.deferredCompleteWith key completion) := by
  intro w _ store pre
  obtain ⟨a, e, declared, strong⟩ := pre
  have typed : ∀ types, w.«Π» key = some types → CompletionOk w types completion := by
    intro types h
    rw [declared] at h
    cases h
    cases completion with
    | ofExit ex => exact completionOk_of_fitsExit strong.1
    | ofRefGet cell => exact strong
  obtain ⟨ord, store'⟩ := complete_world (op := .deferredCompleteWith key completion)
    store rfl rfl rfl rfl typed
  exact ⟨_, _, rfl, _, ord, rfl, store', ⟨_, rfl⟩⟩

theorem deferredInterruptWith_implements (root : ProgramSource) (key : DeferredKey)
    (interruptor : FiberId) : StoreImplements root (.deferredInterruptWith key interruptor) := by
  intro w _ store _
  obtain ⟨ord, store'⟩ := complete_world (op := .deferredInterruptWith key interruptor)
    (cell := key) (effect := .ofExit (.failure (Cause.interrupt (some interruptor))))
    store rfl rfl rfl rfl (fun _ _ => rfl)
  exact ⟨_, _, rfl, _, ord, rfl, store', ⟨_, rfl⟩⟩

theorem clockNow_implements (root : ProgramSource) : StoreImplements root .clockNow := by
  intro w cert store _
  exact same_world store (post := fun w' x => storePost w' .clockNow cert x) ⟨_, rfl⟩ rfl

theorem sleepCancel_implements (root : ProgramSource) (waiter : FiberId) (token : Nat) :
    StoreImplements root (.sleepCancel waiter token) := by
  intro w _ store _
  obtain ⟨ord, store'⟩ := restate_world (op := .sleepCancel waiter token) store rfl rfl rfl
    (fun _ c' h => ⟨c', h, rfl⟩) rfl
  exact ⟨_, _, rfl, _, ord, rfl, store', rfl⟩

theorem scopeMake_implements (root : ProgramSource) (strategy : FinalizerStrategy) :
    StoreImplements root (.scopeMake strategy) := by
  intro w _ store _
  obtain ⟨ord, store'⟩ := restate_world (op := .scopeMake strategy) store rfl rfl rfl
    (fun _ c' h => ⟨c', h, rfl⟩) rfl
  exact ⟨_, _, rfl, _, ord, rfl, store', ⟨_, rfl⟩⟩

theorem scopeIsClosed_implements (root : ProgramSource) (scope : Nat) :
    StoreImplements root (.scopeIsClosed scope) := by
  intro w cert store pre
  change (w.state.scopes.entryAt scope).isSome = true at pre
  cases hentry : w.state.scopes.entryAt scope with
  | none =>
    rw [hentry] at pre
    cases pre
  | some entry =>
    have step : syncOpStep (.scopeIsClosed scope) w.state =
        some (w.state, Val.bool entry.scope.isClosed) := by
      simp only [syncOpStep, hentry, Option.map_some]
    exact same_world store (post := fun w' x => storePost w' (.scopeIsClosed scope) cert x)
      ⟨_, rfl⟩ step

theorem scopeFork_implements (root : ProgramSource) (parent : Nat) (strategy : FinalizerStrategy) :
    StoreImplements root (.scopeFork parent strategy) := by
  intro w _ store pre
  change (w.state.scopes.entryAt parent).isSome = true at pre
  cases hentry : w.state.scopes.entryAt parent with
  | none =>
    rw [hentry] at pre
    cases pre
  | some entry =>
    have step : syncOpStep (.scopeFork parent strategy) w.state = some ({ w.state with
        scopes := w.state.scopes.forkChild parent w.state.nextName (w.state.nextName + 1) strategy
        nextName := w.state.nextName + 2 }, Val.scopeHandle w.state.nextName) := by
      simp only [syncOpStep, hentry]
    obtain ⟨ord, store'⟩ := restate_world store step rfl rfl (fun _ c' h => ⟨c', h, rfl⟩) rfl
    exact ⟨_, _, step, _, ord, rfl, store', ⟨_, rfl⟩⟩

theorem memoFork_implements (root : ProgramSource) (parent : Option MemoMapId) :
    StoreImplements root (.memoFork parent) := by
  intro w _ store _
  obtain ⟨ord, store'⟩ := restate_world (op := .memoFork parent) store rfl rfl rfl
    (fun _ c' h => ⟨c', h, rfl⟩) rfl
  exact ⟨_, _, rfl, _, ord, rfl, store', ⟨_, rfl⟩⟩

theorem memoBuild_implements (root : ProgramSource) (layer : LayerId) (memoMap : MemoMapId) :
    StoreImplements root (.memoBuild layer memoMap) := by
  intro w cert store _
  change Ty × Ty at cert
  have fresh : w.«Π» w.state.deferreds.make.1 = none := by
    cases h : w.«Π» w.state.deferreds.make.1 with
    | none => rfl
    | some t =>
      have := (store.promises w.state.deferreds.make.1).mp (by rw [h]; rfl)
      exact absurd this (Nat.lt_irrefl _)
  have step := syncOpStep_memoBuild w.state layer memoMap
  obtain ⟨le, _⟩ := memoBuild_extension w cert _ layer memoMap _ step fresh
  refine ⟨_, _, step, _, ⟨le, fun _ _ h => h⟩, rfl, ⟨?_, ?_, ?_, ?_⟩, ⟨_, rfl⟩⟩
  · exact store.heap
  · change ∀ k, (tableInsert w.«Π» w.state.deferreds.make.1 cert k).isSome = true ↔
      k.index < w.state.deferreds.make.2.cells.length
    have hlen : w.state.deferreds.make.2.cells.length = w.state.deferreds.cells.length + 1 := by
      simp only [DeferredStore.make, List.length_append, List.length_singleton]
    rw [hlen]
    exact insert_coverage (index := DeferredKey.index) rfl
      (fun k e => by cases k; cases e; rfl) store.promises
  · intro i v hv ty hty
    exact fits_mono ⟨le, fun _ _ h => h⟩ (store.values i v hv ty hty)
  · intro e he ex hex
    obtain ⟨e₀, he₀, hex₀⟩ := syncOpStep_closingExit _ w.state _ _ step e he ex hex
    exact fitsExit_mono ⟨le, fun _ _ h => h⟩ (store.scopeExits e₀ he₀ ex hex₀)

/-! ## The fiber rows

The fiber rows are answered by the scheduler, not by one store step. Some are answered at once:
a `FiberAction` helper installs `next a` for a value `a` (`getId`, `getContext`, `fork`, …).
The others are answered through the frame the evaluator saves over the continuation
(`saveAnswerR f next`, or `seqR next` for a value continuation) when the code it installs, or the
fiber it parks, finishes. The handler rule for those rows is one theorem: the saved frame accepts
every exit the row's post admits (`answerFrame_typed`, `seqFrame_typed`). What the code installs
is the row's own obligation (`closeScope_installs`; the body, generator, loop and race codes are
M5's and the race and registration payloads seat C's). -/

/-- **The answer frame accepts what the post admits.** -/
theorem answerFrame_typed {root : ProgramSource} {w : World} {outer tin : EffTy}
    {post : World → ExitV → Prop} {next : ExitV → RProgram}
    (admits : ∀ w', w.leHost w' → ∀ ex, ExitOk w' tin ex → post w' ex)
    (typed : ∀ w', w.leHost w' → ∀ ex, post w' ex → TypedProg root w' outer (next ex)) :
    FrameAccepts (TypedProg root) ExitOk (frameProtocols root) w tin outer (.answer next) :=
  .answer next fun w' ord ex hex => typed w' ord ex (admits w' ord ex hex)

theorem seqFrame_typed {root : ProgramSource} {w : World} {outer tin : EffTy}
    {post : World → Val → Prop} {next : Val → RProgram} (never : tin.error = .never)
    (admits : ∀ w', w.leHost w' → ∀ v, Fits w' v tin.answer → post w' v)
    (typed : ∀ w', w.leHost w' → ∀ v, post w' v → TypedProg root w' outer (next v)) :
    FrameAccepts (TypedProg root) ExitOk (frameProtocols root) w tin outer
      (.answer (seqR next)) := by
  refine .answer _ fun w' ord ex hex => ?_
  cases ex with
  | success v =>
    exact typed w' ord v (admits w' ord v ((fitsExit_success_iff w' tin v).mp hex.1))
  | failure c =>
    exact TypedProg.pure
      (strongExit_of_clean w' outer c (cleanExit_of_never_fits w' tin c never hex.1) hex.2)

theorem closeScope_frame {root : ProgramSource} {w : World} {outer : EffTy} {scope : Nat}
    {exit : ExitV} {next : ExitV → RProgram}
    (h : TypedProg root w outer (.vis (.inr (.closeScope scope exit)) next)) :
    FrameAccepts (TypedProg root) ExitOk (frameProtocols root) w (EffTy.pure .unit) outer
      (.answer next) := by
  obtain ⟨_, _, typed⟩ := TypedProg.fiber_inv h (fun _ h => nomatch h) (fun _ h => nomatch h)
    (fun _ h => nomatch h) (fun _ _ _ h => nomatch h)
  exact answerFrame_typed (fun _ _ _ hex => hex) typed

theorem closeIter_frame {root : ProgramSource} {w : World} {outer : EffTy}
    {strategy : FinalizerStrategy} {order : List FinName} {exit : ExitV} {next : ExitV → RProgram}
    (h : TypedProg root w outer (.vis (.inr (.closeIter strategy order exit)) next)) :
    FrameAccepts (TypedProg root) ExitOk (frameProtocols root) w (EffTy.pure .unit) outer
      (.answer next) := by
  obtain ⟨_, _, typed⟩ := TypedProg.fiber_inv h (fun _ h => nomatch h) (fun _ h => nomatch h)
    (fun _ h => nomatch h) (fun _ _ _ h => nomatch h)
  exact answerFrame_typed (fun _ _ _ hex => hex) typed

theorem awaitValue_frame {root : ProgramSource} {w : World} {outer ty : EffTy} {target : FiberId}
    {next : Val → RProgram} (declared : w.Γ target = some ty)
    (h : TypedProg root w outer (.vis (.inr (.await target .awaitValue)) next)) :
    FrameAccepts (TypedProg root) ExitOk (frameProtocols root) w
      (EffTy.pure (.exitOf ty.answer ty.error)) outer (.answer (seqR next)) := by
  obtain ⟨_, _, typed⟩ := TypedProg.fiber_inv h (fun _ h => nomatch h) (fun _ h => nomatch h)
    (fun _ h => nomatch h) (fun _ _ _ h => nomatch h)
  exact seqFrame_typed rfl (fun w' ord v hv => ⟨ty, ord.1.2.1 _ _ declared, hv⟩) typed

theorem awaitValue_delivered {w : World} {target : FiberId} {ty : EffTy} {ex : ExitV}
    (cert : FiberCert (.await target .awaitValue)) (declared : w.Γ target = some ty)
    (typed : FitsExit w ty ex) :
    fiberPost w (.await target .awaitValue) cert (reifyExitVal ex) :=
  ⟨ty, declared, typed⟩

theorem joinEffect_frame {root : ProgramSource} {w : World} {outer ty : EffTy} {target : FiberId}
    {next : ExitV → RProgram} (declared : w.Γ target = some ty)
    (h : TypedProg root w outer (.vis (.inr (.await target .joinEffect)) next)) :
    FrameAccepts (TypedProg root) ExitOk (frameProtocols root) w ty outer (.answer next) := by
  obtain ⟨_, _, typed⟩ := TypedProg.fiber_inv h (fun _ h => nomatch h) (fun _ h => nomatch h)
    (fun _ h => nomatch h) (fun _ _ _ h => nomatch h)
  exact answerFrame_typed (fun w' ord ex hex => ⟨ty, ord.1.2.1 _ _ declared, hex⟩) typed

theorem joinEffect_delivered {w : World} {target : FiberId} {ty : EffTy} {ex : ExitV}
    (cert : FiberCert (.await target .joinEffect)) (declared : w.Γ target = some ty)
    (typed : ExitOk w ty ex) : fiberPost w (.await target .joinEffect) cert ex :=
  ⟨ty, declared, typed⟩

/-! The rows answered with the exit of the code they install or the registration they wait on,
at their certificate. -/

theorem mask_frame {root : ProgramSource} {w : World} {outer : EffTy} {flag : Bool} {body : Body}
    {next : ExitV → RProgram} (h : TypedProg root w outer (.vis (.inr (.mask flag body)) next)) :
    ∃ cert : EffTy, FrameAccepts (TypedProg root) ExitOk (frameProtocols root) w cert outer
      (.answer next) := by
  obtain ⟨cert, _, typed⟩ := TypedProg.fiber_inv h (fun _ h => nomatch h) (fun _ h => nomatch h)
    (fun _ h => nomatch h) (fun _ _ _ h => nomatch h)
  exact ⟨cert, answerFrame_typed (fun _ _ _ hex => hex) typed⟩

theorem scoped_frame {root : ProgramSource} {w : World} {outer : EffTy} {body : Point}
    {next : ExitV → RProgram} (h : TypedProg root w outer (.vis (.inr (.scoped body)) next)) :
    ∃ cert : EffTy, FrameAccepts (TypedProg root) ExitOk (frameProtocols root) w cert outer
      (.answer next) := by
  obtain ⟨cert, _, typed⟩ := TypedProg.fiber_inv h (fun _ h => nomatch h) (fun _ h => nomatch h)
    (fun _ h => nomatch h) (fun _ _ _ h => nomatch h)
  exact ⟨cert, answerFrame_typed (fun _ _ _ hex => hex) typed⟩

theorem gen_frame {root : ProgramSource} {w : World} {outer : EffTy} {p : Point}
    {next : ExitV → RProgram} (h : TypedProg root w outer (.vis (.inr (.gen p)) next)) :
    ∃ cert : EffTy, FrameAccepts (TypedProg root) ExitOk (frameProtocols root) w cert outer
      (.answer next) := by
  obtain ⟨cert, _, typed⟩ := TypedProg.fiber_inv h (fun _ h => nomatch h) (fun _ h => nomatch h)
    (fun _ h => nomatch h) (fun _ _ _ h => nomatch h)
  exact ⟨cert, answerFrame_typed (fun _ _ _ hex => hex) typed⟩

theorem loop_frame {root : ProgramSource} {w : World} {outer : EffTy} {p : Point} {cursor : Val}
    {next : ExitV → RProgram} (h : TypedProg root w outer (.vis (.inr (.loop p cursor)) next)) :
    ∃ cert : EffTy, FrameAccepts (TypedProg root) ExitOk (frameProtocols root) w cert outer
      (.answer next) := by
  obtain ⟨cert, _, typed⟩ := TypedProg.fiber_inv h (fun _ h => nomatch h) (fun _ h => nomatch h)
    (fun _ h => nomatch h) (fun _ _ _ h => nomatch h)
  exact ⟨cert, answerFrame_typed (fun _ _ _ hex => hex) typed⟩

theorem raceAll_frame {root : ProgramSource} {w : World} {outer : EffTy} {entrants : List Point} {site : List Nat}
    {next : ExitV → RProgram} (h : TypedProg root w outer (.vis (.inr (.raceAll entrants site)) next)) :
    ∃ cert : EffTy, FrameAccepts (TypedProg root) ExitOk (frameProtocols root) w cert outer
      (.answer next) := by
  obtain ⟨cert, _, typed⟩ := TypedProg.fiber_inv h (fun _ h => nomatch h) (fun _ h => nomatch h)
    (fun _ h => nomatch h) (fun _ _ _ h => nomatch h)
  exact ⟨cert, answerFrame_typed (fun _ _ _ hex => hex) typed⟩

theorem raceRegister_frame {root : ProgramSource} {w : World} {outer : EffTy} {race : Nat}
    {next : ExitV → RProgram} (h : TypedProg root w outer (.vis (.inr (.raceRegister race)) next)) :
    ∃ cert : EffTy, FrameAccepts (TypedProg root) ExitOk (frameProtocols root) w cert outer
      (.answer next) := by
  obtain ⟨cert, _, typed⟩ := TypedProg.fiber_inv h (fun _ h => nomatch h) (fun _ h => nomatch h)
    (fun _ h => nomatch h) (fun _ _ _ h => nomatch h)
  exact ⟨cert, answerFrame_typed (fun _ _ _ hex => hex) typed⟩

theorem async_frame {root : ProgramSource} {w : World} {outer : EffTy} {register : EffName} {request : Val}
    {next : ExitV → RProgram} (h : TypedProg root w outer (.vis (.inr (.async register request)) next)) :
    ∃ cert : EffTy, FrameAccepts (TypedProg root) ExitOk (frameProtocols root) w cert outer
      (.answer next) := by
  obtain ⟨cert, _, typed⟩ := TypedProg.fiber_inv h (fun _ h => nomatch h) (fun _ h => nomatch h)
    (fun _ h => nomatch h) (fun _ _ _ h => nomatch h)
  exact ⟨cert, answerFrame_typed (fun _ _ _ hex => hex) typed⟩

/-! The rows whose continuation reads `void` through `seqR`: the saved frame accepts `⟨unit,
never⟩`. -/

theorem yieldNow_frame {root : ProgramSource} {w : World} {outer : EffTy} {priority : Nat}
    {next : Val → RProgram} (h : TypedProg root w outer (.vis (.inr (.yieldNow priority)) next)) :
    FrameAccepts (TypedProg root) ExitOk (frameProtocols root) w (EffTy.pure .unit) outer
      (.answer (seqR next)) := by
  obtain ⟨_, _, typed⟩ := TypedProg.fiber_inv h (fun _ h => nomatch h) (fun _ h => nomatch h)
    (fun _ h => nomatch h) (fun _ _ _ h => nomatch h)
  exact seqFrame_typed rfl (fun _ _ v hv => fits_unit_inv hv) typed

theorem interrupt_frame {root : ProgramSource} {w : World} {outer : EffTy} {target : FiberId}
    {next : Val → RProgram} (h : TypedProg root w outer (.vis (.inr (.interrupt target)) next)) :
    FrameAccepts (TypedProg root) ExitOk (frameProtocols root) w (EffTy.pure .unit) outer
      (.answer (seqR next)) := by
  obtain ⟨_, _, typed⟩ := TypedProg.fiber_inv h (fun _ h => nomatch h) (fun _ h => nomatch h)
    (fun _ h => nomatch h) (fun _ _ _ h => nomatch h)
  exact seqFrame_typed rfl (fun _ _ v hv => fits_unit_inv hv) typed

theorem interruptAs_frame {root : ProgramSource} {w : World} {outer : EffTy} {target who : FiberId}
    {next : Val → RProgram} (h : TypedProg root w outer (.vis (.inr (.interruptAs target who)) next)) :
    FrameAccepts (TypedProg root) ExitOk (frameProtocols root) w (EffTy.pure .unit) outer
      (.answer (seqR next)) := by
  obtain ⟨_, _, typed⟩ := TypedProg.fiber_inv h (fun _ h => nomatch h) (fun _ h => nomatch h)
    (fun _ h => nomatch h) (fun _ _ _ h => nomatch h)
  exact seqFrame_typed rfl (fun _ _ v hv => fits_unit_inv hv) typed

theorem interruptScoped_frame {root : ProgramSource} {w : World} {outer : EffTy} {target : FiberId}
    {next : Val → RProgram} (h : TypedProg root w outer (.vis (.inr (.interruptScoped target)) next)) :
    FrameAccepts (TypedProg root) ExitOk (frameProtocols root) w (EffTy.pure .unit) outer
      (.answer (seqR next)) := by
  obtain ⟨_, _, typed⟩ := TypedProg.fiber_inv h (fun _ h => nomatch h) (fun _ h => nomatch h)
    (fun _ h => nomatch h) (fun _ _ _ h => nomatch h)
  exact seqFrame_typed rfl (fun _ _ v hv => fits_unit_inv hv) typed

theorem interruptAll_frame {root : ProgramSource} {w : World} {outer : EffTy} {targets : List FiberId} {who : Option FiberId}
    {next : Val → RProgram} (h : TypedProg root w outer (.vis (.inr (.interruptAll targets who)) next)) :
    FrameAccepts (TypedProg root) ExitOk (frameProtocols root) w (EffTy.pure .unit) outer
      (.answer (seqR next)) := by
  obtain ⟨_, _, typed⟩ := TypedProg.fiber_inv h (fun _ h => nomatch h) (fun _ h => nomatch h)
    (fun _ h => nomatch h) (fun _ _ _ h => nomatch h)
  exact seqFrame_typed rfl (fun _ _ v hv => fits_unit_inv hv) typed

theorem cancelRace_frame {root : ProgramSource} {w : World} {outer : EffTy} {race : Nat}
    {next : Val → RProgram} (h : TypedProg root w outer (.vis (.inr (.cancelRace race)) next)) :
    FrameAccepts (TypedProg root) ExitOk (frameProtocols root) w (EffTy.pure .unit) outer
      (.answer (seqR next)) := by
  obtain ⟨_, _, typed⟩ := TypedProg.fiber_inv h (fun _ h => nomatch h) (fun _ h => nomatch h)
    (fun _ h => nomatch h) (fun _ _ _ h => nomatch h)
  exact seqFrame_typed rfl (fun _ _ v hv => fits_unit_inv hv) typed

theorem awaitNewChildren_frame {root : ProgramSource} {w : World} {outer : EffTy} {snapshot : List FiberId}
    {next : Val → RProgram} (h : TypedProg root w outer (.vis (.inr (.awaitNewChildren snapshot)) next)) :
    FrameAccepts (TypedProg root) ExitOk (frameProtocols root) w (EffTy.pure .unit) outer
      (.answer (seqR next)) := by
  obtain ⟨_, _, typed⟩ := TypedProg.fiber_inv h (fun _ h => nomatch h) (fun _ h => nomatch h)
    (fun _ h => nomatch h) (fun _ _ _ h => nomatch h)
  exact seqFrame_typed rfl (fun _ _ v hv => fits_unit_inv hv) typed

/-! The join-all rows: the saved frame accepts the list of exits the certificate names. -/

theorem awaitAll_frame {root : ProgramSource} {w : World} {outer : EffTy} {targets : List FiberId}
    {next : Val → RProgram} (h : TypedProg root w outer (.vis (.inr (.awaitAll targets)) next)) :
    ∃ cert : Ty, FrameAccepts (TypedProg root) ExitOk (frameProtocols root) w (EffTy.pure cert)
      outer (.answer (seqR next)) := by
  obtain ⟨cert, _, typed⟩ := TypedProg.fiber_inv h (fun _ h => nomatch h) (fun _ h => nomatch h)
    (fun _ h => nomatch h) (fun _ _ _ h => nomatch h)
  exact ⟨cert, seqFrame_typed rfl (fun _ _ _ hv => hv) typed⟩

theorem awaitAllFailFast_frame {root : ProgramSource} {w : World} {outer : EffTy}
    {targets : List FiberId} {next : Val → RProgram}
    (h : TypedProg root w outer (.vis (.inr (.awaitAllFailFast targets)) next)) :
    ∃ cert : Ty, FrameAccepts (TypedProg root) ExitOk (frameProtocols root) w (EffTy.pure cert)
      outer (.answer (seqR next)) := by
  obtain ⟨cert, _, typed⟩ := TypedProg.fiber_inv h (fun _ h => nomatch h) (fun _ h => nomatch h)
    (fun _ h => nomatch h) (fun _ _ _ h => nomatch h)
  exact ⟨cert, seqFrame_typed rfl (fun _ _ _ hv => hv) typed⟩

/-- The exits a join-all delivers (`exitsVal`, the reference's `exitsValue`) fit the
certificate's list of exits when each fits the columns the pre bounds the targets by. -/
theorem awaitAll_delivered {w : World} {targets : List FiberId} {a e : Ty} {exits : List ExitV}
    (typed : ∀ ex ∈ exits, FitsExit w ⟨a, e, Env.Requirement.empty⟩ ex) :
    fiberPost w (.awaitAll targets) (.list (.exitOf a e)) (exitsVal exits) := by
  intro x hx
  obtain ⟨ex, hex, rfl⟩ := List.mem_map.mp hx
  exact typed ex hex

theorem awaitAllFailFast_delivered {w : World} {targets : List FiberId} {a e : Ty}
    {exits : List ExitV} (typed : ∀ ex ∈ exits, FitsExit w ⟨a, e, Env.Requirement.empty⟩ ex) :
    fiberPost w (.awaitAllFailFast targets) (.list (.exitOf a e)) (exitsVal exits) := by
  intro x hx
  obtain ⟨ex, hex, rfl⟩ := List.mem_map.mp hx
  exact typed ex hex

/-! The rows answered at once, through the reference interpreter's value hooks. -/

theorem getId_answers (root : ProgramSource) (w : World) (id : FiberId) :
    fiberPost w .getId () ((interpR root.program).fiberIdValue id) := ⟨id, rfl⟩

theorem sync_answers (w : World) (v : Val) : fiberPost w (.sync v) () v := rfl

theorem ambientScope_answers (root : ProgramSource) (w : World) (scope : Nat) :
    fiberPost w .ambientScope () ((interpR root.program).scopeValue scope) := ⟨scope, rfl⟩

theorem setContext_answers (root : ProgramSource) (w : World) (ctx : Ctx) :
    fiberPost w (.setContext ctx) () (interpR root.program).voidValue := rfl

theorem fork_answers {w : World} {id : FiberId} {cert : EffTy} (root : ProgramSource)
    (body : Body) (options : Supervision.ForkOptions) (site : List Nat) (fresh : w.Γ id = none) :
    w.leHost (w.addFiber id cert) ∧
      fiberPost (w.addFiber id cert) (.fork body options site) cert
        ((interpR root.program).fiberValue id) := by
  obtain ⟨le, here, _⟩ := fork_extension w id cert fresh
  exact ⟨⟨le, fun _ _ h => h⟩, id, rfl, here⟩

theorem forkIn_answers {w : World} {id : FiberId} {cert : EffTy} (root : ProgramSource)
    (child : Point) (options : Supervision.ForkOptions) (scope : Nat) (site : List Nat)
    (fresh : w.Γ id = none) :
    w.leHost (w.addFiber id cert) ∧
      fiberPost (w.addFiber id cert) (.forkIn child options scope site) cert
        ((interpR root.program).fiberValue id) := by
  obtain ⟨le, here, _⟩ := fork_extension w id cert fresh
  exact ⟨⟨le, fun _ _ h => h⟩, id, rfl, here⟩

theorem forkScoped_answers {w : World} {id : FiberId} {cert : EffTy} (root : ProgramSource)
    (child : Point) (options : Supervision.ForkOptions) (site : List Nat) (fresh : w.Γ id = none) :
    w.leHost (w.addFiber id cert) ∧
      fiberPost (w.addFiber id cert) (.forkScoped child options site) cert
        (.success ((interpR root.program).fiberValue id)) := by
  obtain ⟨le, here, _⟩ := fork_extension w id cert fresh
  exact ⟨⟨le, fun _ _ h => h⟩, id, rfl, here⟩

/-- The context read: the fiber's context, whose services the state types and whose handles
are declared, fits the context handle. -/
theorem getContext_answers (root : ProgramSource) (w : World) (ctx : Ctx)
    (services : ServicesFit w ctx.services) (live : Live w (Val.context ctx)) :
    fiberPost w .getContext (.handle Ty.contextTarget) ((interpR root.program).contextValue ctx) :=
  ⟨rfl, ctx, Val.context?_context ctx, services, live⟩

theorem runIn_answers (root : ProgramSource) (w : World) (target : FiberId) (scope : Nat) :
    fiberPost w (.runIn target scope) () (interpR root.program).voidValue := rfl

theorem dropObservers_answers (root : ProgramSource) (w : World) (token : Nat) :
    fiberPost w (.dropObservers token) () (interpR root.program).voidValue := rfl

theorem closeWalk_answers (w : World) (strategy : FinalizerStrategy) (order : List FinName)
    (exit : ExitV) : fiberPost w (.closeWalk strategy order exit) () Val.unit := rfl

theorem foreignRelease_answers (w : World) (c : Capture) (exit : ExitV) :
    fiberPost w (.foreignRelease c exit) () Val.unit := rfl

/-- A child snapshot fits the list of fibers at `(unknown, unknown)` when each child is declared. -/
theorem snapshotChildren_answers (root : ProgramSource) (w : World) (children : List FiberId)
    (declared : ∀ c ∈ children, (w.Γ c).isSome = true) :
    fiberPost w .snapshotChildren (.list (.fiberOf .unknown .unknown))
      ((interpR root.program).fibersValue children) := by
  change Fits w (Val.fibers children) (.list (.fiberOf .unknown .unknown))
  rw [fits_list_iff]
  have view : Val.asList? (Val.fibers children) = some (children.map Val.fiber) := by
    simp only [Val.asList?, Val.snapshot?_fibers, Option.map_some]
  refine ⟨children.map Val.fiber, view, fun x hx => ?_⟩
  obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hx
  obtain ⟨fty, hfty⟩ := Option.isSome_iff_exists.mp (declared c hc)
  exact ⟨fty, hfty, Ty.sub_unknown _, Ty.sub_unknown _⟩

/-! ## What the close-scope row installs -/

/-- The multi-finalizer close: the counted suspend, then the walk, each answered within its
post, so the close is typed at `⟨unit, never⟩` whatever the finalizers are. -/
theorem closeWalk_typed (root : ProgramSource) (w : World) (strategy : FinalizerStrategy)
    (order : List FinName) (exit : ExitV) :
    TypedProg root w (EffTy.pure .unit) (closeWalkR strategy order exit) := by
  refine TypedProg.fiber (fun _ h => nomatch h) (fun _ h => nomatch h) (fun _ h => nomatch h)
    (fun _ _ _ h => nomatch h) () trivial ?_
  intro w' _ _ _
  exact TypedProg.fiber (fun _ h => nomatch h) (fun _ h => nomatch h) (fun _ h => nomatch h)
    (fun _ _ _ h => nomatch h) () trivial (fun _ _ ans post => TypedProg.pure post)

/-- **`Scope.close`'s installed program is typed at `⟨unit, never⟩`** when the scope's lone
finalizer, if it has exactly one, is. -/
theorem closeScope_installs (root : ProgramSource) (w : World) (scope : Nat) (exit : ExitV)
    (flag : Bool) (st st' : Stores) (code : RProgram)
    (lone : ∀ state strategy fin, scopeCloseSnapshot scope exit st = some (state, strategy, [fin]) →
      TypedProg root w (EffTy.pure .unit) (denoteFin fin exit))
    (h : closeScopeR scope exit flag st = some (st', code)) :
    TypedProg root w (EffTy.pure .unit) code := by
  unfold closeScopeR closeScopeUnsafeR at h
  cases hs : scopeCloseSnapshot scope exit st with
  | none =>
    rw [hs] at h
    cases h
  | some snapshot =>
    obtain ⟨state, strategy, order⟩ := snapshot
    rw [hs] at h
    simp only at h
    obtain ⟨_, rfl⟩ := h
    match order, hs with
    | [], _ => exact TypedProg.pure ⟨trivial, trivial⟩
    | [fin], hs => exact lone state strategy fin hs
    | _ :: _ :: _, _ => exact closeWalk_typed root w strategy _ exit

/-! ## The ledger: the handler side of decisions row 136

One goal per row the evaluator answers, beside the eighteen command goals (`M6Ledger`), with the
two generic rules: the store rows through `syncOpStep` (`StoreImplements`), the fiber rows
through the frame the evaluator saves and the answers their helpers give. Wave 2 consumes them
in M6's `loop` and `deliver` arms. Proved here: the three generic rules, 23 store rows and 40
fiber instances (the guard row's through `TypedProg.guard_frame`); declared: the 8 store rows
named above. -/

namespace M3bAdequacy

theorem refMake_implements (root : ProgramSource) (initial : Val) :
    ProofGraph.Obligation (StoreImplements root (.refMake initial)) := ⟨⟩

theorem refGet_implements (root : ProgramSource) (cell : RefKey) :
    ProofGraph.Obligation (StoreImplements root (.refGet cell)) := ⟨⟩

theorem refSet_implements (root : ProgramSource) (cell : RefKey) (v : Val) :
    ProofGraph.Obligation (StoreImplements root (.refSet cell v)) := ⟨⟩

theorem refGetAndSet_implements (root : ProgramSource) (cell : RefKey) (v : Val) :
    ProofGraph.Obligation (StoreImplements root (.refGetAndSet cell v)) := ⟨⟩

theorem refSetAndGet_implements (root : ProgramSource) (cell : RefKey) (v : Val) :
    ProofGraph.Obligation (StoreImplements root (.refSetAndGet cell v)) := ⟨⟩

theorem refUpdate_implements (root : ProgramSource) (cell : RefKey) (f : FnName) :
    ProofGraph.Obligation (StoreImplements root (.refUpdate cell f)) := ⟨⟩

theorem refGetAndUpdate_implements (root : ProgramSource) (cell : RefKey) (f : FnName) :
    ProofGraph.Obligation (StoreImplements root (.refGetAndUpdate cell f)) := ⟨⟩

theorem refUpdateAndGet_implements (root : ProgramSource) (cell : RefKey) (f : FnName) :
    ProofGraph.Obligation (StoreImplements root (.refUpdateAndGet cell f)) := ⟨⟩

theorem refUpdateSome_implements (root : ProgramSource) (cell : RefKey) (f : FnName) :
    ProofGraph.Obligation (StoreImplements root (.refUpdateSome cell f)) := ⟨⟩

theorem refGetAndUpdateSome_implements (root : ProgramSource) (cell : RefKey) (f : FnName) :
    ProofGraph.Obligation (StoreImplements root (.refGetAndUpdateSome cell f)) := ⟨⟩

theorem refUpdateSomeAndGet_implements (root : ProgramSource) (cell : RefKey) (f : FnName) :
    ProofGraph.Obligation (StoreImplements root (.refUpdateSomeAndGet cell f)) := ⟨⟩

theorem refModify_implements (root : ProgramSource) (cell : RefKey) (f : FnName) :
    ProofGraph.Obligation (StoreImplements root (.refModify cell f)) := ⟨⟩

theorem refModifySome_implements (root : ProgramSource) (cell : RefKey) (f : FnName) :
    ProofGraph.Obligation (StoreImplements root (.refModifySome cell f)) := ⟨⟩

theorem deferredMake_implements (root : ProgramSource) :
    ProofGraph.Obligation (StoreImplements root (.deferredMake)) := ⟨⟩

theorem deferredIsDone_implements (root : ProgramSource) (key : DeferredKey) :
    ProofGraph.Obligation (StoreImplements root (.deferredIsDone key)) := ⟨⟩

theorem deferredPoll_implements (root : ProgramSource) (key : DeferredKey) :
    ProofGraph.Obligation (StoreImplements root (.deferredPoll key)) := ⟨⟩

theorem deferredCompleteWith_implements (root : ProgramSource) (key : DeferredKey) (completion : Completion Val Err Defect FiberId Ann) :
    ProofGraph.Obligation (StoreImplements root (.deferredCompleteWith key completion)) := ⟨⟩

theorem deferredInterruptWith_implements (root : ProgramSource) (key : DeferredKey) (interruptor : FiberId) :
    ProofGraph.Obligation (StoreImplements root (.deferredInterruptWith key interruptor)) := ⟨⟩

theorem deferredAwaitCleanup_implements (root : ProgramSource) (cell : DeferredKey) (waiter : FiberId) (token : Nat) :
    ProofGraph.Obligation (StoreImplements root (.deferredAwaitCleanup cell waiter token)) := ⟨⟩

theorem clockNow_implements (root : ProgramSource) :
    ProofGraph.Obligation (StoreImplements root (.clockNow)) := ⟨⟩

theorem sleepCancel_implements (root : ProgramSource) (waiter : FiberId) (token : Nat) :
    ProofGraph.Obligation (StoreImplements root (.sleepCancel waiter token)) := ⟨⟩

theorem scopeMake_implements (root : ProgramSource) (strategy : FinalizerStrategy) :
    ProofGraph.Obligation (StoreImplements root (.scopeMake strategy)) := ⟨⟩

theorem scopeAdd_implements (root : ProgramSource) (scope : Nat) (fin : FinName) :
    ProofGraph.Obligation (StoreImplements root (.scopeAdd scope fin)) := ⟨⟩

theorem scopeRemove_implements (root : ProgramSource) (scope key : Nat) :
    ProofGraph.Obligation (StoreImplements root (.scopeRemove scope key)) := ⟨⟩

theorem scopeIsClosed_implements (root : ProgramSource) (scope : Nat) :
    ProofGraph.Obligation (StoreImplements root (.scopeIsClosed scope)) := ⟨⟩

theorem scopeFork_implements (root : ProgramSource) (parent : Nat) (strategy : FinalizerStrategy) :
    ProofGraph.Obligation (StoreImplements root (.scopeFork parent strategy)) := ⟨⟩

theorem memoFork_implements (root : ProgramSource) (parent : Option MemoMapId) :
    ProofGraph.Obligation (StoreImplements root (.memoFork parent)) := ⟨⟩

theorem memoGet_implements (root : ProgramSource) (layer : LayerId) (memoMap : MemoMapId) :
    ProofGraph.Obligation (StoreImplements root (.memoGet layer memoMap)) := ⟨⟩

theorem memoBuild_implements (root : ProgramSource) (layer : LayerId) (memoMap : MemoMapId) :
    ProofGraph.Obligation (StoreImplements root (.memoBuild layer memoMap)) := ⟨⟩

theorem memoComplete_implements (root : ProgramSource) (layer : LayerId) (memoMap : MemoMapId) (exit : ExitV) :
    ProofGraph.Obligation (StoreImplements root (.memoComplete layer memoMap exit)) := ⟨⟩

theorem memoRelease_implements (root : ProgramSource) (layer : LayerId) (memoMap : MemoMapId) :
    ProofGraph.Obligation (StoreImplements root (.memoRelease layer memoMap)) := ⟨⟩

theorem storeStep_typed (root : ProgramSource) (op : SyncOp) : ProofGraph.Obligation
    (StoreImplements root op → ∀ (w : World) (ty : EffTy) (k : Val → RProgram),
      TypedProg root w ty (.vis (.inl op) k) → StoreTyped w →
      ∃ st' ans, syncOpStep op w.state = some (st', ans) ∧
        ∃ w', w.leHost w' ∧ w'.state = st' ∧ StoreTyped w' ∧ TypedProg root w' ty (k ans)) := ⟨⟩

theorem answerFrame_typed (root : ProgramSource) (w : World) (outer tin : EffTy) (post : World → ExitV → Prop)
    (next : ExitV → RProgram) : ProofGraph.Obligation
    ((∀ w', w.leHost w' → ∀ ex, ExitOk w' tin ex → post w' ex) →
      (∀ w', w.leHost w' → ∀ ex, post w' ex → TypedProg root w' outer (next ex)) →
      FrameAccepts (TypedProg root) ExitOk (frameProtocols root) w tin outer (.answer next)) := ⟨⟩

theorem seqFrame_typed (root : ProgramSource) (w : World) (outer tin : EffTy) (post : World → Val → Prop)
    (next : Val → RProgram) : ProofGraph.Obligation
    (tin.error = .never → (∀ w', w.leHost w' → ∀ v, Fits w' v tin.answer → post w' v) →
      (∀ w', w.leHost w' → ∀ v, post w' v → TypedProg root w' outer (next v)) →
      FrameAccepts (TypedProg root) ExitOk (frameProtocols root) w tin outer (.answer (seqR next))) := ⟨⟩

theorem closeScope_frame (root : ProgramSource) (w : World) (outer : EffTy) (scope : Nat) (exit : ExitV)
    (next : ExitV → RProgram) : ProofGraph.Obligation
    (TypedProg root w outer (.vis (.inr (.closeScope scope exit)) next) →
      FrameAccepts (TypedProg root) ExitOk (frameProtocols root) w (EffTy.pure .unit) outer (.answer next)) := ⟨⟩

theorem closeIter_frame (root : ProgramSource) (w : World) (outer : EffTy) (strategy : FinalizerStrategy)
    (order : List FinName) (exit : ExitV) (next : ExitV → RProgram) : ProofGraph.Obligation
    (TypedProg root w outer (.vis (.inr (.closeIter strategy order exit)) next) →
      FrameAccepts (TypedProg root) ExitOk (frameProtocols root) w (EffTy.pure .unit) outer (.answer next)) := ⟨⟩

theorem awaitValue_frame (root : ProgramSource) (w : World) (outer ty : EffTy) (target : FiberId)
    (next : Val → RProgram) : ProofGraph.Obligation
    (w.Γ target = some ty → TypedProg root w outer (.vis (.inr (.await target .awaitValue)) next) →
      FrameAccepts (TypedProg root) ExitOk (frameProtocols root) w (EffTy.pure (.exitOf ty.answer ty.error)) outer (.answer (seqR next))) := ⟨⟩

theorem awaitValue_delivered (w : World) (target : FiberId) (ty : EffTy) (ex : ExitV)
    (cert : FiberCert (.await target .awaitValue)) : ProofGraph.Obligation
    (w.Γ target = some ty → FitsExit w ty ex →
      fiberPost w (.await target .awaitValue) cert (reifyExitVal ex)) := ⟨⟩

theorem joinEffect_frame (root : ProgramSource) (w : World) (outer ty : EffTy) (target : FiberId)
    (next : ExitV → RProgram) : ProofGraph.Obligation
    (w.Γ target = some ty → TypedProg root w outer (.vis (.inr (.await target .joinEffect)) next) →
      FrameAccepts (TypedProg root) ExitOk (frameProtocols root) w ty outer (.answer next)) := ⟨⟩

theorem joinEffect_delivered (w : World) (target : FiberId) (ty : EffTy) (ex : ExitV)
    (cert : FiberCert (.await target .joinEffect)) : ProofGraph.Obligation
    (w.Γ target = some ty → ExitOk w ty ex → fiberPost w (.await target .joinEffect) cert ex) := ⟨⟩

theorem mask_frame (root : ProgramSource) (w : World) (outer : EffTy) (flag : Bool) (body : Body)
    (next : ExitV → RProgram) : ProofGraph.Obligation
    (TypedProg root w outer (.vis (.inr (.mask flag body)) next) →
      ∃ cert : EffTy, FrameAccepts (TypedProg root) ExitOk (frameProtocols root) w cert outer (.answer next)) := ⟨⟩

theorem scoped_frame (root : ProgramSource) (w : World) (outer : EffTy) (body : Point)
    (next : ExitV → RProgram) : ProofGraph.Obligation
    (TypedProg root w outer (.vis (.inr (.scoped body)) next) →
      ∃ cert : EffTy, FrameAccepts (TypedProg root) ExitOk (frameProtocols root) w cert outer (.answer next)) := ⟨⟩

theorem gen_frame (root : ProgramSource) (w : World) (outer : EffTy) (p : Point)
    (next : ExitV → RProgram) : ProofGraph.Obligation
    (TypedProg root w outer (.vis (.inr (.gen p)) next) →
      ∃ cert : EffTy, FrameAccepts (TypedProg root) ExitOk (frameProtocols root) w cert outer (.answer next)) := ⟨⟩

theorem loop_frame (root : ProgramSource) (w : World) (outer : EffTy) (p : Point) (cursor : Val)
    (next : ExitV → RProgram) : ProofGraph.Obligation
    (TypedProg root w outer (.vis (.inr (.loop p cursor)) next) →
      ∃ cert : EffTy, FrameAccepts (TypedProg root) ExitOk (frameProtocols root) w cert outer (.answer next)) := ⟨⟩

theorem raceAll_frame (root : ProgramSource) (w : World) (outer : EffTy) (entrants : List Point) (site : List Nat)
    (next : ExitV → RProgram) : ProofGraph.Obligation
    (TypedProg root w outer (.vis (.inr (.raceAll entrants site)) next) →
      ∃ cert : EffTy, FrameAccepts (TypedProg root) ExitOk (frameProtocols root) w cert outer (.answer next)) := ⟨⟩

theorem raceRegister_frame (root : ProgramSource) (w : World) (outer : EffTy) (race : Nat)
    (next : ExitV → RProgram) : ProofGraph.Obligation
    (TypedProg root w outer (.vis (.inr (.raceRegister race)) next) →
      ∃ cert : EffTy, FrameAccepts (TypedProg root) ExitOk (frameProtocols root) w cert outer (.answer next)) := ⟨⟩

theorem async_frame (root : ProgramSource) (w : World) (outer : EffTy) (register : EffName) (request : Val)
    (next : ExitV → RProgram) : ProofGraph.Obligation
    (TypedProg root w outer (.vis (.inr (.async register request)) next) →
      ∃ cert : EffTy, FrameAccepts (TypedProg root) ExitOk (frameProtocols root) w cert outer (.answer next)) := ⟨⟩

theorem yieldNow_frame (root : ProgramSource) (w : World) (outer : EffTy) (priority : Nat)
    (next : Val → RProgram) : ProofGraph.Obligation
    (TypedProg root w outer (.vis (.inr (.yieldNow priority)) next) →
      FrameAccepts (TypedProg root) ExitOk (frameProtocols root) w (EffTy.pure .unit) outer (.answer (seqR next))) := ⟨⟩

theorem interrupt_frame (root : ProgramSource) (w : World) (outer : EffTy) (target : FiberId)
    (next : Val → RProgram) : ProofGraph.Obligation
    (TypedProg root w outer (.vis (.inr (.interrupt target)) next) →
      FrameAccepts (TypedProg root) ExitOk (frameProtocols root) w (EffTy.pure .unit) outer (.answer (seqR next))) := ⟨⟩

theorem interruptAs_frame (root : ProgramSource) (w : World) (outer : EffTy) (target who : FiberId)
    (next : Val → RProgram) : ProofGraph.Obligation
    (TypedProg root w outer (.vis (.inr (.interruptAs target who)) next) →
      FrameAccepts (TypedProg root) ExitOk (frameProtocols root) w (EffTy.pure .unit) outer (.answer (seqR next))) := ⟨⟩

theorem interruptScoped_frame (root : ProgramSource) (w : World) (outer : EffTy) (target : FiberId)
    (next : Val → RProgram) : ProofGraph.Obligation
    (TypedProg root w outer (.vis (.inr (.interruptScoped target)) next) →
      FrameAccepts (TypedProg root) ExitOk (frameProtocols root) w (EffTy.pure .unit) outer (.answer (seqR next))) := ⟨⟩

theorem interruptAll_frame (root : ProgramSource) (w : World) (outer : EffTy) (targets : List FiberId) (who : Option FiberId)
    (next : Val → RProgram) : ProofGraph.Obligation
    (TypedProg root w outer (.vis (.inr (.interruptAll targets who)) next) →
      FrameAccepts (TypedProg root) ExitOk (frameProtocols root) w (EffTy.pure .unit) outer (.answer (seqR next))) := ⟨⟩

theorem cancelRace_frame (root : ProgramSource) (w : World) (outer : EffTy) (race : Nat)
    (next : Val → RProgram) : ProofGraph.Obligation
    (TypedProg root w outer (.vis (.inr (.cancelRace race)) next) →
      FrameAccepts (TypedProg root) ExitOk (frameProtocols root) w (EffTy.pure .unit) outer (.answer (seqR next))) := ⟨⟩

theorem awaitNewChildren_frame (root : ProgramSource) (w : World) (outer : EffTy) (snapshot : List FiberId)
    (next : Val → RProgram) : ProofGraph.Obligation
    (TypedProg root w outer (.vis (.inr (.awaitNewChildren snapshot)) next) →
      FrameAccepts (TypedProg root) ExitOk (frameProtocols root) w (EffTy.pure .unit) outer (.answer (seqR next))) := ⟨⟩

theorem awaitAll_frame (root : ProgramSource) (w : World) (outer : EffTy) (targets : List FiberId)
    (next : Val → RProgram) : ProofGraph.Obligation
    (TypedProg root w outer (.vis (.inr (.awaitAll targets)) next) →
      ∃ cert : Ty, FrameAccepts (TypedProg root) ExitOk (frameProtocols root) w (EffTy.pure cert) outer (.answer (seqR next))) := ⟨⟩

theorem awaitAll_delivered (w : World) (targets : List FiberId) (a e : Ty) (exits : List ExitV) : ProofGraph.Obligation
    ((∀ ex ∈ exits, FitsExit w ⟨a, e, Env.Requirement.empty⟩ ex) →
      fiberPost w (.awaitAll targets) (.list (.exitOf a e)) (exitsVal exits)) := ⟨⟩

theorem awaitAllFailFast_frame (root : ProgramSource) (w : World) (outer : EffTy) (targets : List FiberId)
    (next : Val → RProgram) : ProofGraph.Obligation
    (TypedProg root w outer (.vis (.inr (.awaitAllFailFast targets)) next) →
      ∃ cert : Ty, FrameAccepts (TypedProg root) ExitOk (frameProtocols root) w (EffTy.pure cert) outer (.answer (seqR next))) := ⟨⟩

theorem awaitAllFailFast_delivered (w : World) (targets : List FiberId) (a e : Ty) (exits : List ExitV) : ProofGraph.Obligation
    ((∀ ex ∈ exits, FitsExit w ⟨a, e, Env.Requirement.empty⟩ ex) →
      fiberPost w (.awaitAllFailFast targets) (.list (.exitOf a e)) (exitsVal exits)) := ⟨⟩

theorem getId_answers (root : ProgramSource) (w : World) (id : FiberId) : ProofGraph.Obligation
    (fiberPost w .getId () ((interpR root.program).fiberIdValue id)) := ⟨⟩

theorem sync_answers (w : World) (v : Val) : ProofGraph.Obligation
    (fiberPost w (.sync v) () v) := ⟨⟩

theorem ambientScope_answers (root : ProgramSource) (w : World) (scope : Nat) : ProofGraph.Obligation
    (fiberPost w .ambientScope () ((interpR root.program).scopeValue scope)) := ⟨⟩

theorem setContext_answers (root : ProgramSource) (w : World) (ctx : Ctx) : ProofGraph.Obligation
    (fiberPost w (.setContext ctx) () (interpR root.program).voidValue) := ⟨⟩

theorem fork_answers (w : World) (id : FiberId) (cert : EffTy) (root : ProgramSource) (body : Body)
    (options : Supervision.ForkOptions) (site : List Nat) : ProofGraph.Obligation
    (w.Γ id = none → w.leHost (w.addFiber id cert) ∧
      fiberPost (w.addFiber id cert) (.fork body options site) cert ((interpR root.program).fiberValue id)) := ⟨⟩

theorem forkIn_answers (w : World) (id : FiberId) (cert : EffTy) (root : ProgramSource) (child : Point)
    (options : Supervision.ForkOptions) (scope : Nat) (site : List Nat) : ProofGraph.Obligation
    (w.Γ id = none → w.leHost (w.addFiber id cert) ∧
      fiberPost (w.addFiber id cert) (.forkIn child options scope site) cert
        ((interpR root.program).fiberValue id)) := ⟨⟩

theorem forkScoped_answers (w : World) (id : FiberId) (cert : EffTy) (root : ProgramSource) (child : Point)
    (options : Supervision.ForkOptions) (site : List Nat) : ProofGraph.Obligation
    (w.Γ id = none → w.leHost (w.addFiber id cert) ∧
      fiberPost (w.addFiber id cert) (.forkScoped child options site) cert
        (.success ((interpR root.program).fiberValue id))) := ⟨⟩

theorem getContext_answers (root : ProgramSource) (w : World) (ctx : Ctx) : ProofGraph.Obligation
    (ServicesFit w ctx.services → Live w (Val.context ctx) →
      fiberPost w .getContext (.handle Ty.contextTarget) ((interpR root.program).contextValue ctx)) := ⟨⟩

theorem runIn_answers (root : ProgramSource) (w : World) (target : FiberId) (scope : Nat) : ProofGraph.Obligation
    (fiberPost w (.runIn target scope) () (interpR root.program).voidValue) := ⟨⟩

theorem dropObservers_answers (root : ProgramSource) (w : World) (token : Nat) : ProofGraph.Obligation
    (fiberPost w (.dropObservers token) () (interpR root.program).voidValue) := ⟨⟩

theorem closeWalk_answers (w : World) (strategy : FinalizerStrategy) (order : List FinName) (exit : ExitV) : ProofGraph.Obligation
    (fiberPost w (.closeWalk strategy order exit) () Val.unit) := ⟨⟩

theorem foreignRelease_answers (w : World) (c : Capture) (exit : ExitV) : ProofGraph.Obligation
    (fiberPost w (.foreignRelease c exit) () Val.unit) := ⟨⟩

theorem snapshotChildren_answers (root : ProgramSource) (w : World) (children : List FiberId) : ProofGraph.Obligation
    ((∀ c ∈ children, (w.Γ c).isSome = true) →
      fiberPost w .snapshotChildren (.list (.fiberOf .unknown .unknown))
        ((interpR root.program).fibersValue children)) := ⟨⟩

theorem closeWalk_typed (root : ProgramSource) (w : World) (strategy : FinalizerStrategy) (order : List FinName)
    (exit : ExitV) : ProofGraph.Obligation
    (TypedProg root w (EffTy.pure .unit) (closeWalkR strategy order exit)) := ⟨⟩

theorem closeScope_installs (root : ProgramSource) (w : World) (scope : Nat) (exit : ExitV) (flag : Bool)
    (st st' : Stores) (code : RProgram) : ProofGraph.Obligation
    ((∀ state strategy fin, scopeCloseSnapshot scope exit st = some (state, strategy, [fin]) →
        TypedProg root w (EffTy.pure .unit) (denoteFin fin exit)) →
      closeScopeR scope exit flag st = some (st', code) → TypedProg root w (EffTy.pure .unit) code) := ⟨⟩

/-- The guard row: its typing is the arrow of the frame the evaluator saves
(`TypedProg.guard_frame`, `Typed/Residual.lean`). -/
theorem guard_frame (root : ProgramSource) (w : World) (ty : EffTy) (kind : GuardKind)
    (k : Option ExitV → RProgram) : ProofGraph.Obligation
    (TypedProg root w ty (.vis (.inr (.guard_ kind)) k) →
      ∃ mid : EffTy, TypedProg root w mid (k none) ∧
        FrameAccepts (TypedProg root) ExitOk (frameProtocols root) w mid ty
          (.resume kind fun ex => k (some ex))) := ⟨⟩

end M3bAdequacy

end Effect4.Program.Typed

#obligation_proved Effect4.Program.Typed.M3bAdequacy.refMake_implements :=
  @Effect4.Program.Typed.refMake_implements
#obligation_proved Effect4.Program.Typed.M3bAdequacy.refGet_implements :=
  @Effect4.Program.Typed.refGet_implements
#obligation_proved Effect4.Program.Typed.M3bAdequacy.refSet_implements :=
  @Effect4.Program.Typed.refSet_implements
#obligation_proved Effect4.Program.Typed.M3bAdequacy.refGetAndSet_implements :=
  @Effect4.Program.Typed.refGetAndSet_implements
#obligation_proved Effect4.Program.Typed.M3bAdequacy.refSetAndGet_implements :=
  @Effect4.Program.Typed.refSetAndGet_implements
#obligation_proved Effect4.Program.Typed.M3bAdequacy.refModify_implements :=
  @Effect4.Program.Typed.refModify_implements
#obligation_proved Effect4.Program.Typed.M3bAdequacy.refModifySome_implements :=
  @Effect4.Program.Typed.refModifySome_implements
#obligation_proved Effect4.Program.Typed.M3bAdequacy.deferredMake_implements :=
  @Effect4.Program.Typed.deferredMake_implements
#obligation_proved Effect4.Program.Typed.M3bAdequacy.deferredIsDone_implements :=
  @Effect4.Program.Typed.deferredIsDone_implements
#obligation_proved Effect4.Program.Typed.M3bAdequacy.deferredPoll_implements :=
  @Effect4.Program.Typed.deferredPoll_implements
#obligation_proved Effect4.Program.Typed.M3bAdequacy.deferredCompleteWith_implements :=
  @Effect4.Program.Typed.deferredCompleteWith_implements
#obligation_proved Effect4.Program.Typed.M3bAdequacy.deferredInterruptWith_implements :=
  @Effect4.Program.Typed.deferredInterruptWith_implements
#obligation_proved Effect4.Program.Typed.M3bAdequacy.deferredAwaitCleanup_implements :=
  @Effect4.Program.Typed.deferredAwaitCleanup_implements
#obligation_proved Effect4.Program.Typed.M3bAdequacy.clockNow_implements :=
  @Effect4.Program.Typed.clockNow_implements
#obligation_proved Effect4.Program.Typed.M3bAdequacy.sleepCancel_implements :=
  @Effect4.Program.Typed.sleepCancel_implements
#obligation_proved Effect4.Program.Typed.M3bAdequacy.scopeMake_implements :=
  @Effect4.Program.Typed.scopeMake_implements
#obligation_proved Effect4.Program.Typed.M3bAdequacy.scopeAdd_implements :=
  @Effect4.Program.Typed.scopeAdd_implements
#obligation_proved Effect4.Program.Typed.M3bAdequacy.scopeRemove_implements :=
  @Effect4.Program.Typed.scopeRemove_implements
#obligation_proved Effect4.Program.Typed.M3bAdequacy.scopeIsClosed_implements :=
  @Effect4.Program.Typed.scopeIsClosed_implements
#obligation_proved Effect4.Program.Typed.M3bAdequacy.scopeFork_implements :=
  @Effect4.Program.Typed.scopeFork_implements
#obligation_proved Effect4.Program.Typed.M3bAdequacy.memoFork_implements :=
  @Effect4.Program.Typed.memoFork_implements
#obligation_proved Effect4.Program.Typed.M3bAdequacy.memoBuild_implements :=
  @Effect4.Program.Typed.memoBuild_implements
#obligation_proved Effect4.Program.Typed.M3bAdequacy.memoRelease_implements :=
  @Effect4.Program.Typed.memoRelease_implements
#obligation_proved Effect4.Program.Typed.M3bAdequacy.storeStep_typed :=
  @Effect4.Program.Typed.storeStep_typed
#obligation_proved Effect4.Program.Typed.M3bAdequacy.answerFrame_typed :=
  @Effect4.Program.Typed.answerFrame_typed
#obligation_proved Effect4.Program.Typed.M3bAdequacy.seqFrame_typed :=
  @Effect4.Program.Typed.seqFrame_typed
#obligation_proved Effect4.Program.Typed.M3bAdequacy.closeScope_frame :=
  @Effect4.Program.Typed.closeScope_frame
#obligation_proved Effect4.Program.Typed.M3bAdequacy.closeIter_frame :=
  @Effect4.Program.Typed.closeIter_frame
#obligation_proved Effect4.Program.Typed.M3bAdequacy.awaitValue_frame :=
  @Effect4.Program.Typed.awaitValue_frame
#obligation_proved Effect4.Program.Typed.M3bAdequacy.awaitValue_delivered :=
  @Effect4.Program.Typed.awaitValue_delivered
#obligation_proved Effect4.Program.Typed.M3bAdequacy.joinEffect_frame :=
  @Effect4.Program.Typed.joinEffect_frame
#obligation_proved Effect4.Program.Typed.M3bAdequacy.joinEffect_delivered :=
  @Effect4.Program.Typed.joinEffect_delivered
#obligation_proved Effect4.Program.Typed.M3bAdequacy.mask_frame :=
  @Effect4.Program.Typed.mask_frame
#obligation_proved Effect4.Program.Typed.M3bAdequacy.scoped_frame :=
  @Effect4.Program.Typed.scoped_frame
#obligation_proved Effect4.Program.Typed.M3bAdequacy.gen_frame :=
  @Effect4.Program.Typed.gen_frame
#obligation_proved Effect4.Program.Typed.M3bAdequacy.loop_frame :=
  @Effect4.Program.Typed.loop_frame
#obligation_proved Effect4.Program.Typed.M3bAdequacy.raceAll_frame :=
  @Effect4.Program.Typed.raceAll_frame
#obligation_proved Effect4.Program.Typed.M3bAdequacy.raceRegister_frame :=
  @Effect4.Program.Typed.raceRegister_frame
#obligation_proved Effect4.Program.Typed.M3bAdequacy.async_frame :=
  @Effect4.Program.Typed.async_frame
#obligation_proved Effect4.Program.Typed.M3bAdequacy.yieldNow_frame :=
  @Effect4.Program.Typed.yieldNow_frame
#obligation_proved Effect4.Program.Typed.M3bAdequacy.interrupt_frame :=
  @Effect4.Program.Typed.interrupt_frame
#obligation_proved Effect4.Program.Typed.M3bAdequacy.interruptAs_frame :=
  @Effect4.Program.Typed.interruptAs_frame
#obligation_proved Effect4.Program.Typed.M3bAdequacy.interruptScoped_frame :=
  @Effect4.Program.Typed.interruptScoped_frame
#obligation_proved Effect4.Program.Typed.M3bAdequacy.interruptAll_frame :=
  @Effect4.Program.Typed.interruptAll_frame
#obligation_proved Effect4.Program.Typed.M3bAdequacy.cancelRace_frame :=
  @Effect4.Program.Typed.cancelRace_frame
#obligation_proved Effect4.Program.Typed.M3bAdequacy.awaitNewChildren_frame :=
  @Effect4.Program.Typed.awaitNewChildren_frame
#obligation_proved Effect4.Program.Typed.M3bAdequacy.awaitAll_frame :=
  @Effect4.Program.Typed.awaitAll_frame
#obligation_proved Effect4.Program.Typed.M3bAdequacy.awaitAll_delivered :=
  @Effect4.Program.Typed.awaitAll_delivered
#obligation_proved Effect4.Program.Typed.M3bAdequacy.awaitAllFailFast_frame :=
  @Effect4.Program.Typed.awaitAllFailFast_frame
#obligation_proved Effect4.Program.Typed.M3bAdequacy.awaitAllFailFast_delivered :=
  @Effect4.Program.Typed.awaitAllFailFast_delivered
#obligation_proved Effect4.Program.Typed.M3bAdequacy.getId_answers :=
  @Effect4.Program.Typed.getId_answers
#obligation_proved Effect4.Program.Typed.M3bAdequacy.sync_answers :=
  @Effect4.Program.Typed.sync_answers
#obligation_proved Effect4.Program.Typed.M3bAdequacy.ambientScope_answers :=
  @Effect4.Program.Typed.ambientScope_answers
#obligation_proved Effect4.Program.Typed.M3bAdequacy.setContext_answers :=
  @Effect4.Program.Typed.setContext_answers
#obligation_proved Effect4.Program.Typed.M3bAdequacy.fork_answers :=
  @Effect4.Program.Typed.fork_answers
#obligation_proved Effect4.Program.Typed.M3bAdequacy.forkIn_answers :=
  @Effect4.Program.Typed.forkIn_answers
#obligation_proved Effect4.Program.Typed.M3bAdequacy.forkScoped_answers :=
  @Effect4.Program.Typed.forkScoped_answers
#obligation_proved Effect4.Program.Typed.M3bAdequacy.getContext_answers :=
  @Effect4.Program.Typed.getContext_answers
#obligation_proved Effect4.Program.Typed.M3bAdequacy.runIn_answers :=
  @Effect4.Program.Typed.runIn_answers
#obligation_proved Effect4.Program.Typed.M3bAdequacy.dropObservers_answers :=
  @Effect4.Program.Typed.dropObservers_answers
#obligation_proved Effect4.Program.Typed.M3bAdequacy.closeWalk_answers :=
  @Effect4.Program.Typed.closeWalk_answers
#obligation_proved Effect4.Program.Typed.M3bAdequacy.foreignRelease_answers :=
  @Effect4.Program.Typed.foreignRelease_answers
#obligation_proved Effect4.Program.Typed.M3bAdequacy.snapshotChildren_answers :=
  @Effect4.Program.Typed.snapshotChildren_answers
#obligation_proved Effect4.Program.Typed.M3bAdequacy.closeWalk_typed :=
  @Effect4.Program.Typed.closeWalk_typed
#obligation_proved Effect4.Program.Typed.M3bAdequacy.closeScope_installs :=
  @Effect4.Program.Typed.closeScope_installs
#proof_wanted Effect4.Program.Typed.M3bAdequacy.refUpdate_implements
#proof_wanted Effect4.Program.Typed.M3bAdequacy.refGetAndUpdate_implements
#proof_wanted Effect4.Program.Typed.M3bAdequacy.refUpdateAndGet_implements
#proof_wanted Effect4.Program.Typed.M3bAdequacy.refUpdateSome_implements
#proof_wanted Effect4.Program.Typed.M3bAdequacy.refGetAndUpdateSome_implements
#proof_wanted Effect4.Program.Typed.M3bAdequacy.refUpdateSomeAndGet_implements
#proof_wanted Effect4.Program.Typed.M3bAdequacy.memoGet_implements
#proof_wanted Effect4.Program.Typed.M3bAdequacy.memoComplete_implements
#obligation_proved Effect4.Program.Typed.M3bAdequacy.guard_frame :=
  fun _ _ _ _ _ h => Effect4.Program.Typed.TypedProg.guard_frame h
#obligation_audit Effect4.Program.Typed.M3bAdequacy
#typed_state_obligations Effect4.Program.Typed.M3bAdequacy ceiling 8
  using aesop (rule_sets := [Effect4.TypedState])
