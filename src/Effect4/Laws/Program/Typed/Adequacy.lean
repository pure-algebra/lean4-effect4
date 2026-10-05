import Effect4.Laws.Program.Typed.Residual
import Effect4.Laws.Program.Typed.Seq
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

**The cell columns** (decisions row 209). `CellsTyped` is the cell half of `StoreTyped`, shared
with the meaning layer's `Denote.StoreFits` (`Laws/Program/Progress.lean`), so the columns are
defined once. `CellImplements root op` is `StoreImplements` on the cell columns alone. Each native
`sync` row has one instance; the heap kernels are one theorem (`kernel_step`) over one table
(`kernel_typed`), whose eight term rows are one lemma (`termKernel_typed`): the row's term maps
the cell's type into the row's result type (`TermMaps`, decisions row 43), and the row's decoder
reads every member of that type. `CellImplements.implements` reads an instance on the typed state,
so a native row is proved once, and the meaning layer's `progress` reads the same instances.

This module proves no command preservation step: `StoreTyped` is the store half of the typed
state, which M6's `loop`/`deliver` arms supply and consume.
-/

set_option autoImplicit false
namespace Effect4.Program.Typed
open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Sched Effect4.Program.Denote
open Contracts

/-! ## The handler judgment for the store rows -/

/-! ## The memo table (decisions row 187 (c)) -/

/-- A memo entry's cell at its layer: declared at the built context and the layer's own checked
error type, the certificate `memoBuild`'s row declares it at (`storePre`) and the columns
`memoComplete`'s exit fits. A path that is no checked layer constrains nothing. -/
def LayerCellTyped (root : ProgramSource) (w : World) (layer : LayerId) (cell : DeferredKey) :
    Prop :=
  ∀ l lt, Node.at_ (.eff root.program) layer = some (.layer l) →
    Checker.checkLayer root.signature layer (LayerTerm.expandIn root.program l) = .ok lt →
      w.«Π» cell = some (.handle Ty.contextTarget, lt.error)

/-- **The memo table**: every entry's cell is typed at its layer, read through the memo world's
one view of its cells (`MemoWorld.layerCells`). The promise table's `memoBuild` row
(`Typed/Vocabulary.lean`: `Π` declares a built cell at its layer's type). -/
def MemoTableTyped (root : ProgramSource) (w : World) (memo : MemoWorld) : Prop :=
  ∀ p ∈ memo.layerCells, LayerCellTyped root w p.1 p.2

/-- Declarations are kept along the host order (`World.le`'s `Π` extension). -/
theorem MemoTableTyped.mono {root : ProgramSource} {w w' : World} (ord : w.leHost w')
    {memo : MemoWorld} (h : MemoTableTyped root w memo) : MemoTableTyped root w' memo :=
  fun p hp l lt node checked => ord.1.2.2.1 _ _ (h p hp l lt node checked)

/-- A memo world whose cells are among a typed one's is typed at every later world. -/
theorem memoTable_step {root : ProgramSource} {w w' : World} {memo memo' : MemoWorld}
    (ord : w.leHost w') (h : MemoTableTyped root w memo)
    (keep : ∀ p ∈ memo'.layerCells, p ∈ memo.layerCells) : MemoTableTyped root w' memo' :=
  fun p hp => MemoTableTyped.mono ord h p (keep p hp)

/-- A step that is no build adds no memo cell (`syncOpStep_layerCells`). -/
theorem layerCells_of_not_build {op : SyncOp} {s s' : Stores} {ans : Val}
    (step : syncOpStep op s = some (s', ans))
    (notBuild : ∀ layer memoMap, op ≠ .memoBuild layer memoMap) :
    ∀ p ∈ s'.memo.layerCells, p ∈ s.memo.layerCells := by
  intro p hp
  rcases syncOpStep_layerCells op s s' ans step p hp with old | ⟨⟨memoMap, build⟩, _, _⟩
  · exact old
  · exact absurd build (notBuild _ _)

/-- A step that keeps the Deferred cells' count adds no memo cell: a build allocates one. -/
theorem layerCells_of_cells_length {op : SyncOp} {s s' : Stores} {ans : Val}
    (step : syncOpStep op s = some (s', ans))
    (len : s'.deferreds.cells.length = s.deferreds.cells.length) :
    ∀ p ∈ s'.memo.layerCells, p ∈ s.memo.layerCells := by
  intro p hp
  rcases syncOpStep_layerCells op s s' ans step p hp with old | ⟨_, _, grown⟩
  · exact old
  · rw [grown] at len
    simp only [DeferredStore.make, List.length_append, List.length_singleton] at len
    omega

/-- **The cell columns**, the store typing both store halves share (decisions row 209): the
world's declarations cover exactly the allocated cells and Deferred cells (`WorldValid.heap`,
`.promises`), and every stored value fits its cell's declared type (the generated heap column at
the strong leaf, `(preds root).HeapCell`; `heapTable_of_fits` gives the coarse `HeapTable`).
`StoreTyped` adds the scope and memo clauses the typed state reads; the meaning layer's
`Denote.StoreFits` (`Laws/Program/Progress.lean`) adds `Stores.WF`. -/
structure CellsTyped (w : World) : Prop where
  heap : ∀ key, (w.Ρ key).isSome = true ↔ key.index < w.state.refs.length
  promises : ∀ key, (w.«Π» key).isSome = true ↔ key.index < w.state.deferreds.cells.length
  values : ∀ (i : Nat) (v : Val), w.state.refs[i]? = some v → ∀ ty, w.Ρ ⟨i⟩ = some ty → Fits w v ty

/-- The store half of the typed state that the store rows read and keep: the cell columns
(`CellsTyped`), every closing exit a scope holds fits `Exit<unknown, unknown>` (DI-94's release
type: the `ScopeState.closed.exit` source row, which seat C un-refuses), and every memo entry's
Deferred and layer scope exist (`Stores.MemoValid`, the memo clause of `WorldValid.wf`), which
`memoRelease`'s post reads when it answers the layer scope (decisions row 156), and every memo
entry's cell is declared at its layer's columns (`MemoTableTyped`, decisions row 187 (c)), which
`memoGet`'s post and `memoComplete`'s completion read. -/
structure StoreTyped (root : ProgramSource) (w : World) : Prop extends CellsTyped w where
  scopeExits : ∀ e ∈ w.state.scopes.entries, ∀ ex, e.scope.closingExit? = some ex →
    FitsExit w ⟨.unknown, .unknown, Env.Requirement.empty⟩ ex
  memo : w.state.MemoValid
  memoTable : MemoTableTyped root w w.state.memo

/-- **The store handler fulfils row `op`** (the 2026-09-05 review's `Implements`): at a world
whose store is typed, a request the row's pre admits steps (no frontier), and its answer lies in
the row's post at a later world over the new store, which is typed again. -/
def StoreImplements (root : ProgramSource) (op : SyncOp) : Prop :=
  ∀ (w : World) (cert : StoreCert op), StoreTyped root w → storePre root w op cert →
    ∃ st' ans, syncOpStep op w.state = some (st', ans) ∧
      ∃ w', w.leHost w' ∧ w'.state = st' ∧ StoreTyped root w' ∧ storePost w' op cert ans

/-- **The store handler fulfils row `op` on the cell columns**: the cell half of `StoreImplements`.
At a world whose cell columns are typed, a request the row's pre admits steps (no frontier), and
its answer lies in the row's post at a later world over the new store, whose cell columns are typed
again. One instance per row of the native `sync` table (`kernel_cellImplements` for the heap
kernels); the meaning layer's `progress` (`Laws/Program/Progress.lean`) reads them. -/
def CellImplements (root : ProgramSource) (op : SyncOp) : Prop :=
  ∀ (w : World) (cert : StoreCert op), CellsTyped w → storePre root w op cert →
    ∃ st' ans, syncOpStep op w.state = some (st', ans) ∧
      ∃ w', w.leHost w' ∧ w'.state = st' ∧ CellsTyped w' ∧ storePost w' op cert ans

/-- **Membership is the store's validity** (finding F-WF, owner's ruling 2026-10-02): at a world
whose cell columns are typed, a value that fits any type is valid in the store (`Val.validIn`, what
`Stores.WF` asks of every stored value and closing exit): `fits_live` gives capability membership,
and the columns' forward bounds (`CellsTyped.heap`, `.promises`) make it validity
(`live_validIn`). -/
theorem CellsTyped.fits_validIn {w : World} (cells : CellsTyped w) {ty : Ty} {v : Val}
    (h : Fits w v ty) : v.validIn w.state = true :=
  live_validIn (fun k => (cells.heap k).mp) (fun k => (cells.promises k).mp) (fits_live w ty v h)

/-- `CellsTyped.fits_validIn` at the typed state's store half. -/
theorem fits_validIn {root : ProgramSource} {w : World} (store : StoreTyped root w) {ty : Ty} {v : Val}
    (h : Fits w v ty) : v.validIn w.state = true :=
  store.toCellsTyped.fits_validIn h

/-- **The store's validity moves along a step by membership** (finding F-WF): at a world over the
new store whose cell columns are typed, every heap value fits its declared type and so is valid
(`CellsTyped.fits_validIn`); the scope, memo and timer clauses move by the step. A term row's
environment is not in its precondition, so its new heap's validity is read here, not off
`SyncOp.validIn`. -/
theorem CellsTyped.wf_step {w w' : World} {o : SyncOp} {st' : Stores} {a : Val}
    (wf : w.state.WF) (step : syncOpStep o w.state = some (st', a)) (hstate : w'.state = st')
    (cells : CellsTyped w') : st'.WF := by
  subst hstate
  refine ⟨fun v hv => ?_, syncOpStep_closingValid o w.state _ a wf step,
    syncOpStep_memoValid o w.state _ a wf.2.2.1 step,
    syncOpStep_timers_wf o w.state _ a wf.2.2.2 step⟩
  obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hv
  obtain ⟨ty, hty⟩ := Option.isSome_iff_exists.mp
    ((cells.heap ⟨i⟩).mpr (List.getElem?_eq_some_iff.mp hi).1)
  exact cells.fits_validIn (cells.values i v hi ty hty)

/-- **The handler rule for `TypedProg`'s store arm**, one theorem for every row: a typed store
operation run by a handler that fulfils its row steps to a typed continuation at a later world
over the new store, which is typed again. This is what the evaluator's store arm needs
(`evaluateRawR` installs `k ans` over the new store). -/
theorem storeStep_typed {root : ProgramSource} {op : SyncOp} (impl : StoreImplements root op)
    {w : World} {ty : EffTy} {k : Val → RProgram}
    (typed : TypedProg root w ty (.vis (.inl op) k)) (store : StoreTyped root w) :
    ∃ st' ans, syncOpStep op w.state = some (st', ans) ∧
      ∃ w', w.leHost w' ∧ w'.state = st' ∧ StoreTyped root w' ∧ TypedProg root w' ty (k ans) := by
  obtain ⟨cert, pre, next⟩ := TypedProg.store_inv typed
  obtain ⟨st', ans, step, w', ord, hstate, store', post⟩ := impl w cert store pre
  exact ⟨st', ans, step, w', ord, hstate, store', next w' ord ans post⟩

/-- A typed store operation never reaches the evaluator's frontier branch, which answers
`unit` whatever the row's post says. -/
theorem storeStep_answers {root : ProgramSource} {op : SyncOp} (impl : StoreImplements root op)
    {w : World} {ty : EffTy} {k : Val → RProgram}
    (typed : TypedProg root w ty (.vis (.inl op) k)) (store : StoreTyped root w) :
    syncOpStep op w.state ≠ none := by
  obtain ⟨st', ans, step, _⟩ := storeStep_typed impl typed store
  rw [step]
  exact fun h => nomatch h

/-! ## Moving the world along a store step

The cell columns move once (`CellsTyped.restate`, `CellsTyped.addRef`, `CellsTyped.addPromise`);
the typed state's own clauses move once (`StoreTyped.step`); each `…_world` lemma below is one of
each. -/

/-- **The cell columns move along a store step that keeps the declarations**: the new heap typed at
the old declarations, every completion of the new Deferred cells old or admitted at its cell's
columns, the lengths and the external spellings kept. The world over the new store is then later
in the host order, and its cell columns are typed. -/
theorem CellsTyped.restate {w : World} {op : SyncOp} {st' : Stores} {ans : Val}
    (cells : CellsTyped w) (step : syncOpStep op w.state = some (st', ans))
    (refsLength : st'.refs.length = w.state.refs.length)
    (values : ∀ (i : Nat) (v : Val), st'.refs[i]? = some v → ∀ ty, w.Ρ ⟨i⟩ = some ty → Fits w v ty)
    (cellsLength : st'.deferreds.cells.length = w.state.deferreds.cells.length)
    (completions : ∀ key c', st'.deferreds.cellAt key = some c' → ∀ completion,
      c'.completion = some completion →
        (∃ c, w.state.deferreds.cellAt key = some c ∧ c.completion = some completion) ∨
          ∀ types, w.«Π» key = some types → CompletionOk w types completion)
    (externals : st'.externals = w.state.externals) :
    w.leHost { w with state := st' } ∧ CellsTyped { w with state := st' } := by
  have alloc : Extends w.state.externals.allocated st'.externals.allocated := by
    rw [externals]
    exact fun _ _ h => h
  have ord : w.leHost { w with state := st' } := by
    refine ⟨⟨⟨fun _ h => h, syncOpStep_le op w.state st' ans step⟩, fun _ _ h => h,
      fun _ _ h => h, fun _ _ h => h, ⟨?_, ?_⟩, fun _ _ _ h => h, rfl⟩, alloc⟩
    · intro key ty h
      refine ⟨h.1, fun value hv => ?_⟩
      exact value_transport w { w with state := st' } ty value alloc
        (fits_hasTy w ty value (values key.index value hv ty h.1))
    · intro key types h
      refine ⟨h.1, fun c' hc completion hcomp => ?_⟩
      rcases completions key c' hc completion hcomp with ⟨c, hc0, same⟩ | fresh
      · exact completion_transport w { w with state := st' } types (fun _ _ h => h) alloc
          completion (h.2 c hc0 completion same)
      · exact completion_transport w { w with state := st' } types (fun _ _ h => h) alloc
          completion (fresh types h.1)
  refine ⟨ord, ⟨?_, ?_, ?_⟩⟩
  · intro key
    change (w.Ρ key).isSome = true ↔ key.index < st'.refs.length
    rw [refsLength]
    exact cells.heap key
  · intro key
    change (w.«Π» key).isSome = true ↔ key.index < st'.deferreds.cells.length
    rw [cellsLength]
    exact cells.promises key
  · intro i v hv ty hty
    exact fits_mono ord (values i v hv ty hty)

/-- **The typed state's own clauses move along a store step that adds no memo layer cell**: the
closing exits by `fitsExit_mono`, the memo entries by the step (`syncOpStep_memoValid`), the memo
table by the order (`memoTable_step`). With the cell columns typed at the later world, its store
half is typed. -/
theorem StoreTyped.step {root : ProgramSource} {w w' : World} {op : SyncOp} {st' : Stores}
    {ans : Val} (store : StoreTyped root w) (step : syncOpStep op w.state = some (st', ans))
    (hstate : w'.state = st') (ord : w.leHost w') (cells : CellsTyped w')
    (keep : ∀ p ∈ st'.memo.layerCells, p ∈ w.state.memo.layerCells) : StoreTyped root w' := by
  subst hstate
  refine ⟨cells, fun e he ex hex => ?_, syncOpStep_memoValid _ _ _ _ store.memo step,
    memoTable_step ord store.memoTable keep⟩
  obtain ⟨e₀, he₀, hex₀⟩ := syncOpStep_closingExit op w.state _ ans step e he ex hex
  exact fitsExit_mono ord (store.scopeExits e₀ he₀ ex hex₀)

/-- A store step that keeps the heap, the Deferred cells' completions and the external
spellings moves to the world over the new store: later in the host order, and typed. -/
theorem restate_world {root : ProgramSource} {w : World} {op : SyncOp} {st' : Stores} {ans : Val}
    (store : StoreTyped root w) (step : syncOpStep op w.state = some (st', ans))
    (refs : st'.refs = w.state.refs)
    (cellsLength : st'.deferreds.cells.length = w.state.deferreds.cells.length)
    (completions : ∀ key c', st'.deferreds.cellAt key = some c' →
      ∃ c, w.state.deferreds.cellAt key = some c ∧ c'.completion = c.completion)
    (externals : st'.externals = w.state.externals) :
    w.leHost { w with state := st' } ∧ StoreTyped root { w with state := st' } := by
  obtain ⟨ord, cells⟩ := store.toCellsTyped.restate step (by rw [refs])
    (fun i v hv ty hty => store.values i v (by rw [← refs]; exact hv) ty hty) cellsLength
    (fun key c' hc completion hcomp => by
      obtain ⟨c, hc0, same⟩ := completions key c' hc
      exact .inl ⟨c, hc0, by rw [← same]; exact hcomp⟩)
    externals
  exact ⟨ord, store.step step rfl ord cells (layerCells_of_cells_length step cellsLength)⟩

/-- A step that keeps the whole store answers at the same world. -/
theorem same_world {root : ProgramSource} {w : World} {op : SyncOp} {ans : Val}
    (store : StoreTyped root w)
    {post : World → Val → Prop} (holds : post w ans)
    (step : syncOpStep op w.state = some (w.state, ans)) :
    ∃ st' ans', syncOpStep op w.state = some (st', ans') ∧
      ∃ w', w.leHost w' ∧ w'.state = st' ∧ StoreTyped root w' ∧ post w' ans' :=
  ⟨w.state, ans, step, w, leHost_refl w, rfl, store, holds⟩

/-! ## Value facts the store rows read -/

/-- A declared promise has a cell: reading it is not a frontier. -/
theorem promise_readable {root : ProgramSource} {w : World} {key : DeferredKey}
    (store : StoreTyped root w)
    (declared : (w.«Π» key).isSome = true) : ∃ c, w.state.deferreds.cells[key.index]? = some c :=
  ⟨_, List.getElem?_eq_getElem ((store.promises key).mp declared)⟩

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

/-! ## Moving the world along a completion -/

/-- **The cell columns move along a completion**: a store step that completes one Deferred cell
with a completion its declared columns admit, keeping the heap and the external spellings. -/
theorem CellsTyped.complete {w : World} {op : SyncOp} {st' : Stores} {ans : Val} {cell : DeferredKey}
    {effect : Completion Val Err Defect FiberId Ann}
    (cells : CellsTyped w) (step : syncOpStep op w.state = some (st', ans))
    (deferreds : st'.deferreds = (w.state.deferreds.complete cell effect).1)
    (refs : st'.refs = w.state.refs) (externals : st'.externals = w.state.externals)
    (typed : ∀ types, w.«Π» cell = some types → CompletionOk w types effect) :
    w.leHost { w with state := st' } ∧ CellsTyped { w with state := st' } :=
  cells.restate step (by rw [refs])
    (fun i v hv ty hty => cells.values i v (by rw [← refs]; exact hv) ty hty)
    (by rw [deferreds, complete_cells_length])
    (fun key c' hc completion hcomp => by
      rw [deferreds] at hc
      rcases complete_cellAt _ _ _ key c' hc with ⟨c, hc0, same⟩ | ⟨same, stored⟩
      · exact .inl ⟨c, hc0, by rw [← same]; exact hcomp⟩
      · rw [stored] at hcomp
        cases hcomp
        have hkey : key = cell := by
          cases key with
          | mk i =>
            cases cell with
            | mk c =>
              change i = c at same
              rw [same]
        subst hkey
        exact .inr typed)
    externals

/-- A store step that completes one promise with a completion its declared columns admit moves to
the world over the new store: later in the host order, and typed. -/
theorem complete_world {root : ProgramSource} {w : World} {op : SyncOp} {st' : Stores} {ans : Val} {cell : DeferredKey}
    {effect : Completion Val Err Defect FiberId Ann}
    (store : StoreTyped root w) (step : syncOpStep op w.state = some (st', ans))
    (deferreds : st'.deferreds = (w.state.deferreds.complete cell effect).1)
    (refs : st'.refs = w.state.refs) (externals : st'.externals = w.state.externals)
    (typed : ∀ types, w.«Π» cell = some types → CompletionOk w types effect) :
    w.leHost { w with state := st' } ∧ StoreTyped root { w with state := st' } := by
  obtain ⟨ord, cells⟩ := store.toCellsTyped.complete step deferreds refs externals typed
  exact ⟨ord, store.step step rfl ord cells
    (layerCells_of_cells_length step (by rw [deferreds, complete_cells_length]))⟩

/-! ## The native store rows on the cell columns

The cell half of each native `sync` row's adequacy, stated over `CellsTyped` so that both store
typings read it: the typed state's `StoreTyped` and the meaning layer's `Denote.StoreFits`
(`Laws/Program/Progress.lean`, whose `progress` dispatches here). The heap kernels are one theorem
(`kernel_step`) over one table (`kernel_typed`, the cases of `SyncOp.refKernel`); the allocations
are `CellsTyped.addRef` and `CellsTyped.addPromise`; every other native row keeps the
declarations (`CellsTyped.restate`). -/

/-- **The cell columns move along `refMake`**: the fresh cell declared at `ty` over the grown heap,
holding the initial value, which fits `ty`; every old cell keeps its declaration and its value. -/
theorem CellsTyped.addRef {w : World} (cells : CellsTyped w) (initial : Val) (ty : Ty)
    (fits : Fits w initial ty) :
    w.leHost (w.addRef { w.state with refs := w.state.refs ++ [initial] } ⟨w.state.refs.length⟩ ty) ∧
      CellsTyped
        (w.addRef { w.state with refs := w.state.refs ++ [initial] } ⟨w.state.refs.length⟩ ty) := by
  have fresh : w.Ρ ⟨w.state.refs.length⟩ = none := by
    cases h : w.Ρ ⟨w.state.refs.length⟩ with
    | none => rfl
    | some t =>
      have := (cells.heap ⟨w.state.refs.length⟩).mp (by rw [h]; rfl)
      exact absurd this (Nat.lt_irrefl _)
  obtain ⟨le, _⟩ := refMake_extension w initial ty _ _ (syncOpStep_refMake w.state initial) fresh
    (fits_hasTy w ty initial fits)
  have ord : w.leHost (w.addRef { w.state with refs := w.state.refs ++ [initial] }
      ⟨w.state.refs.length⟩ ty) := ⟨le, fun _ _ h => h⟩
  refine ⟨ord, ⟨?_, cells.promises, ?_⟩⟩
  · change ∀ k, (tableInsert w.Ρ ⟨w.state.refs.length⟩ ty k).isSome = true ↔
      k.index < (w.state.refs ++ [initial]).length
    rw [List.length_append, List.length_singleton]
    exact insert_coverage (index := RefKey.index) rfl
      (fun k e => by cases k; cases e; rfl) cells.heap
  · intro i v hv t hty
    change (w.state.refs ++ [initial])[i]? = some v at hv
    change tableInsert w.Ρ ⟨w.state.refs.length⟩ ty ⟨i⟩ = some t at hty
    by_cases hi : i < w.state.refs.length
    · rw [List.getElem?_append_left hi] at hv
      have hne : (⟨i⟩ : RefKey) ≠ ⟨w.state.refs.length⟩ := fun e => by
        cases e
        exact Nat.lt_irrefl _ hi
      rw [insert_other _ _ _ _ hne] at hty
      exact fits_mono ord (cells.values i v hv t hty)
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

/-- The next Deferred cell is undeclared at a world whose cell columns are typed. -/
theorem CellsTyped.promise_fresh {w : World} (cells : CellsTyped w) :
    w.«Π» ⟨w.state.deferreds.cells.length⟩ = none := by
  cases h : w.«Π» ⟨w.state.deferreds.cells.length⟩ with
  | none => rfl
  | some t =>
    have := (cells.promises ⟨w.state.deferreds.cells.length⟩).mp (by rw [h]; rfl)
    exact absurd this (Nat.lt_irrefl _)

/-- **The cell columns move along a Deferred allocation**: a store whose Deferred cells grew by one
empty cell, with the heap and the external spellings kept, at the world that declares the fresh
cell at `types`, given the allocation's world order (`deferredMake_extension`,
`memoBuild_extension`). `deferredMake` and `memoBuild` allocate this way. -/
theorem CellsTyped.addPromise {w : World} (cells : CellsTyped w) (types : Ty × Ty) (state : Stores)
    (hrefs : state.refs = w.state.refs)
    (hcells : state.deferreds =
      ⟨w.state.deferreds.cells ++ [⟨none, WakeList.empty⟩], w.state.deferreds.due⟩)
    (hext : state.externals = w.state.externals)
    (le : w.le (w.addPromise state ⟨w.state.deferreds.cells.length⟩ types)) :
    w.leHost (w.addPromise state ⟨w.state.deferreds.cells.length⟩ types) ∧
      CellsTyped (w.addPromise state ⟨w.state.deferreds.cells.length⟩ types) := by
  have alloc : Extends w.state.externals.allocated state.externals.allocated := by
    rw [hext]
    exact fun _ _ h => h
  have ord : w.leHost (w.addPromise state ⟨w.state.deferreds.cells.length⟩ types) := ⟨le, alloc⟩
  refine ⟨ord, ⟨?_, ?_, ?_⟩⟩
  · intro key
    change (w.Ρ key).isSome = true ↔ key.index < state.refs.length
    rw [hrefs]
    exact cells.heap key
  · change ∀ k, (tableInsert w.«Π» ⟨w.state.deferreds.cells.length⟩ types k).isSome = true ↔
      k.index < state.deferreds.cells.length
    rw [hcells, List.length_append, List.length_singleton]
    exact insert_coverage (index := DeferredKey.index) rfl
      (fun k e => by cases k; cases e; rfl) cells.promises
  · intro i v hv t hty
    change state.refs[i]? = some v at hv
    rw [hrefs] at hv
    exact fits_mono ord (cells.values i v hv t hty)

/-- The world over a heap with one cell written back (`refWriteBack`): every other column and every
declaration table as it was. A heap-kernel row steps to it (`kernel_step`). -/
def writeWorld (w : World) (cell : RefKey) (next : Option Val) : World :=
  { w with state := { w.state with refs := refWriteBack w.state.refs cell next } }

/-- **A heap-kernel row on the cell columns** (one theorem for every kernel row): at a cell declared
at `t`, a kernel that answers on every value fitting `t` and writes only values fitting `t` steps
(no frontier) to the world over the written heap (`writeWorld`). That world is later in the host
order and its cell columns are typed; the value read fits `t`, and the step answers what the
kernel answers on it. Every other cell keeps its value (`indexed_ref_step_preserves`, FR-03's
index-aware adapter). -/
theorem kernel_step {w : World} {o : SyncOp} {cell : RefKey} {k : RefKernel} {t : Ty}
    (cells : CellsTyped w) (hk : o.refKernel = some (cell, k)) (declared : w.Ρ cell = some t)
    (runs : ∀ c, Fits w c t → (k c).isSome = true)
    (writes : RefKernel.Keeps (Fits w · t) (fun _ => True) k) :
    ∃ c r, Fits w c t ∧ k c = some r ∧
      syncOpStep o w.state = some ((writeWorld w cell r.2).state, r.1) ∧
      w.leHost (writeWorld w cell r.2) ∧ CellsTyped (writeWorld w cell r.2) := by
  obtain ⟨c, hc⟩ : ∃ c, refPeek w.state.refs cell = some c :=
    ⟨_, List.getElem?_eq_getElem ((cells.heap cell).mp (by rw [declared]; rfl))⟩
  have fc := cells.values cell.index c hc t declared
  obtain ⟨r, hr⟩ := Option.isSome_iff_exists.mp (runs c fc)
  have hstepOf : refStepOf cell k w.state.refs = some (r.1, refWriteBack w.state.refs cell r.2) := by
    simp only [refStepOf, hc, Option.bind_some, hr, Option.map_some]
  have step : syncOpStep o w.state = some ((writeWorld w cell r.2).state, r.1) := by
    rw [syncOpStep_eq_refStepOf hk, hstepOf, Option.map_some]
    rfl
  have hrs : refStep o w.state.refs = some (r.1, refWriteBack w.state.refs cell r.2) := by
    rw [refStep_eq_refStepOf hk]
    exact hstepOf
  have cellKeeps : RefKernel.Keeps
      ((fun i x => ∀ ty, w.Ρ ⟨i⟩ = some ty → Fits w x ty) cell.index) (fun _ => True) k := by
    intro c' r' hc' hkr
    obtain ⟨_, hw⟩ := writes c' r' (hc' t declared) hkr
    refine ⟨trivial, fun next hn ty hty => ?_⟩
    have same : ty = t := Option.some.inj (hty.symm.trans declared)
    subst same
    exact hw next hn
  obtain ⟨_, typed, len, _⟩ := indexed_ref_step_preserves
    (fun i x => ∀ ty, w.Ρ ⟨i⟩ = some ty → Fits w x ty) (fun _ => True) o cell k w.state.refs _ r.1
    hk (fun i v hv ty hty => cells.values i v hv ty hty) cellKeeps hrs
  obtain ⟨ord, cells'⟩ := cells.restate step len (fun i v hv ty hty => typed i v hv ty hty) rfl
    (fun key c' hc' completion hcomp => .inl ⟨c', hc', hcomp⟩) rfl
  exact ⟨c, r, fc, hr, step, ord, cells'⟩

/-- **A term kernel under its row's demand** (one lemma for the eight term rows): when the term
maps the cell's type `t` into the row's result type `R` at every later world (`TermMaps`), the
row's decoder reads every member of `R` as a good part, and the row's arrangement of a member of
`t` and a good part answers in `Q` and writes members of `t`, the kernel answers on every member
of `t` and keeps `t` in the cell. -/
theorem termKernel_typed {D : Type} {decode : Val → Option D}
    {arrange : Val → D → Val × Option Val} {w : World} {f : Term} {env : List Val}
    {t R : Ty} {Good : D → Prop} {Q : Val → Prop} (maps : TermMaps w f env t R)
    (hdecode : ∀ r, Fits w r R → ∃ d, decode r = some d ∧ Good d)
    (harrange : ∀ a d, Fits w a t → Good d →
      Q (arrange a d).1 ∧ ∀ next, (arrange a d).2 = some next → Fits w next t) :
    (∀ c, Fits w c t → (termKernel decode arrange f env c).isSome = true) ∧
      RefKernel.Keeps (Fits w · t) Q (termKernel decode arrange f env) := by
  have run : ∀ c, Fits w c t →
      ∃ d, termKernel decode arrange f env c = some (arrange c d) ∧ Good d := by
    intro c hc
    obtain ⟨r, hr, hfit⟩ := maps w (leHost_refl w) c hc
    obtain ⟨d, hd, good⟩ := hdecode r hfit
    exact ⟨d, by simp only [termKernel, hr, Option.bind_some, hd, Option.map_some], good⟩
  refine ⟨fun c hc => ?_, fun c p hc hp => ?_⟩
  · obtain ⟨d, hk, _⟩ := run c hc
    rw [hk]
    rfl
  · obtain ⟨d, hk, good⟩ := run c hc
    rw [hk] at hp
    cases hp
    exact harrange c d hc good

/-- The exact option image reads every member of `Option<t>`, as a member of `t` or nothing. -/
theorem decode_option {w : World} {t : Ty} (r : Val) (h : Fits w r (.option t)) :
    ∃ o, Store.Image.ofOption Store.Image.ident r = some o ∧ ∀ a, o = some a → Fits w a t := by
  rcases fits_option_inv h with rfl | ⟨x, rfl, hx⟩
  · exact ⟨none, rfl, fun _ h => nomatch h⟩
  · exact ⟨some x, rfl, fun a h => by cases h; exact hx⟩

/-- The exact pair image reads every member of `[b, t]` as its two members. -/
theorem decode_pair {w : World} {b t : Ty} (r : Val) (h : Fits w r (.prod b t)) :
    ∃ p, Store.Image.ofTuple2 Store.Image.ident Store.Image.ident r = some p ∧
      Fits w p.1 b ∧ Fits w p.2 t := by
  obtain ⟨x, y, rfl, hx, hy⟩ := (fits_prod_iff _ _ _ _).mp h
  exact ⟨(x, y), rfl, hx, hy⟩

/-- The exact pair image over the option image reads every member of `[b, Option<t>]`. -/
theorem decode_pairOption {w : World} {b t : Ty} (r : Val) (h : Fits w r (.prod b (.option t))) :
    ∃ p, Store.Image.ofTuple2 Store.Image.ident (Store.Image.option Store.Image.ident) r = some p ∧
      Fits w p.1 b ∧ ∀ a, p.2 = some a → Fits w a t := by
  obtain ⟨x, y, rfl, hx, hy⟩ := (fits_prod_iff _ _ _ _).mp h
  obtain ⟨o, ho, good⟩ := decode_option y hy
  obtain rfl : y = (Store.Image.option Store.Image.ident).toVal o :=
    (Store.Image.option Store.Image.ident).ofVal_exact ho
  exact ⟨(x, o),
    (Store.Image.tuple2 Store.Image.ident (Store.Image.option Store.Image.ident)).ofVal_toVal (x, o),
    hx, good⟩

/-- **The heap kernels under the store pre** (one table, the cases of `SyncOp.refKernel`): the row's
cell is declared at some `t`; its kernel answers on every value that fits `t`, writes only values
that fit `t`, and answers inside the row's post at every later world. A term row reads its term's
demand (`TermMaps`, decisions row 43) through `termKernel_typed`, with its shape's decoder:
the value itself, `decode_option`, `decode_pair` or `decode_pairOption`. -/
theorem kernel_typed {root : ProgramSource} {w : World} {o : SyncOp} {cert : StoreCert o}
    {cell : RefKey} {k : RefKernel} (hk : o.refKernel = some (cell, k))
    (pre : storePre root w o cert) :
    ∃ t, w.Ρ cell = some t ∧ (∀ c, Fits w c t → (k c).isSome = true) ∧
      RefKernel.Keeps (Fits w · t) (fun a => ∀ w', w.leHost w' → storePost w' o cert a) k := by
  -- a value read from the cell, or written to it, answers at every later world
  have read : ∀ {t : Ty} {a : Val}, w.Ρ cell = some t → Fits w a t → ∀ w', w.leHost w' →
      ∃ ty, w'.Ρ cell = some ty ∧ Fits w' a ty :=
    fun declared ha w' ord => ⟨_, ord.1.2.2.2.1 cell _ declared, fits_mono ord ha⟩
  cases o <;> cases hk
  case refGet =>
    obtain ⟨t, declared⟩ := pre
    refine ⟨t, declared, fun _ _ => rfl, fun c r hc hr => ?_⟩
    cases hr
    exact ⟨read declared hc, fun _ h => nomatch h⟩
  case refSet v =>
    obtain ⟨t, declared, fits⟩ := pre
    refine ⟨t, declared, fun _ _ => rfl, fun c r hc hr => ?_⟩
    cases hr
    exact ⟨fun _ _ => rfl, fun _ h => by cases h; exact fits⟩
  case refGetAndSet v =>
    obtain ⟨t, declared, fits⟩ := pre
    refine ⟨t, declared, fun _ _ => rfl, fun c r hc hr => ?_⟩
    cases hr
    exact ⟨read declared hc, fun _ h => by cases h; exact fits⟩
  case refSetAndGet v =>
    obtain ⟨t, declared, fits⟩ := pre
    refine ⟨t, declared, fun _ _ => rfl, fun c r hc hr => ?_⟩
    cases hr
    exact ⟨read declared fits, fun _ h => by cases h; exact fits⟩
  case refUpdate f env =>
    obtain ⟨t, declared, maps⟩ := pre
    exact ⟨t, declared, termKernel_typed maps (fun r hr => ⟨r, rfl, hr⟩)
      fun _ _ _ hd => ⟨fun _ _ => rfl, fun _ h => by cases h; exact hd⟩⟩
  case refGetAndUpdate f env =>
    obtain ⟨t, declared, maps⟩ := pre
    exact ⟨t, declared, termKernel_typed maps (fun r hr => ⟨r, rfl, hr⟩)
      fun _ _ ha hd => ⟨read declared ha, fun _ h => by cases h; exact hd⟩⟩
  case refUpdateAndGet f env =>
    obtain ⟨t, declared, maps⟩ := pre
    exact ⟨t, declared, termKernel_typed maps (fun r hr => ⟨r, rfl, hr⟩)
      fun _ _ _ hd => ⟨read declared hd, fun _ h => by cases h; exact hd⟩⟩
  case refUpdateSome f env =>
    obtain ⟨t, declared, maps⟩ := pre
    exact ⟨t, declared, termKernel_typed maps decode_option
      fun _ _ _ good => ⟨fun _ _ => rfl, good⟩⟩
  case refGetAndUpdateSome f env =>
    obtain ⟨t, declared, maps⟩ := pre
    exact ⟨t, declared, termKernel_typed maps decode_option
      fun _ _ ha good => ⟨read declared ha, good⟩⟩
  case refUpdateSomeAndGet f env =>
    obtain ⟨t, declared, maps⟩ := pre
    exact ⟨t, declared, termKernel_typed maps decode_option
      fun _ _ ha good => ⟨read declared (RefKernel.getD_keeps good ha), good⟩⟩
  case refModify f env =>
    obtain ⟨t, declared, maps⟩ := pre
    exact ⟨t, declared, termKernel_typed maps decode_pair
      fun _ _ _ good => ⟨fun _ ord => fits_mono ord good.1,
        fun _ h => by cases h; exact good.2⟩⟩
  case refModifySome f env =>
    obtain ⟨t, declared, maps⟩ := pre
    exact ⟨t, declared, termKernel_typed maps decode_pairOption
      fun _ _ ha good => ⟨fun _ ord => fits_mono ord good.1,
        fun _ h => by cases h; exact RefKernel.getD_keeps good.2 ha⟩⟩

/-- The heap kernels fulfil their rows on the cell columns: `kernel_typed`'s table run by
`kernel_step`. -/
theorem kernel_cellImplements (root : ProgramSource) {o : SyncOp} {cell : RefKey}
    {k : RefKernel} (hk : o.refKernel = some (cell, k)) : CellImplements root o := by
  intro w cert cells pre
  obtain ⟨t, declared, runs, keeps⟩ := kernel_typed hk pre
  obtain ⟨c, r, hc, hr, step, ord, cells'⟩ := kernel_step cells hk declared runs
    fun c r hc hr => ⟨trivial, (keeps c r hc hr).2⟩
  exact ⟨_, r.1, step, _, ord, rfl, cells', (keeps c r hc hr).1 _ ord⟩

theorem refMake_cellImplements (root : ProgramSource) (initial : Val) :
    CellImplements root (.refMake initial) := by
  intro w cert cells pre
  change Ty at cert
  obtain ⟨ord, cells'⟩ := cells.addRef initial cert pre
  exact ⟨_, _, syncOpStep_refMake w.state initial, _, ord, rfl, cells', ⟨_, rfl, insert_here _ _ _⟩⟩

theorem deferredMake_cellImplements (root : ProgramSource) : CellImplements root .deferredMake := by
  intro w cert cells _
  change Ty × Ty at cert
  have step := syncOpStep_deferredMake w.state
  obtain ⟨le, _⟩ := deferredMake_extension w cert _ _ step cells.promise_fresh
  obtain ⟨ord, cells'⟩ := cells.addPromise cert { w.state with deferreds := w.state.deferreds.make.2 }
    rfl rfl rfl le
  exact ⟨_, _, step, _, ord, rfl, cells', ⟨_, rfl, insert_here _ _ _⟩⟩

theorem deferredIsDone_cellImplements (root : ProgramSource) (key : DeferredKey) :
    CellImplements root (.deferredIsDone key) := by
  intro w cert cells pre
  obtain ⟨c, hc⟩ : ∃ c, w.state.deferreds.cells[key.index]? = some c :=
    ⟨_, List.getElem?_eq_getElem ((cells.promises key).mp pre)⟩
  have step : syncOpStep (.deferredIsDone key) w.state =
      some (w.state, Val.bool c.completion.isSome) := by
    simp only [syncOpStep, DeferredStore.isDone, DeferredStore.cellAt, hc, Option.map_some]
  exact ⟨_, _, step, w, leHost_refl w, rfl, cells, ⟨_, rfl⟩⟩

theorem deferredPoll_cellImplements (root : ProgramSource) (key : DeferredKey) :
    CellImplements root (.deferredPoll key) := by
  intro w cert cells pre
  obtain ⟨c, hc⟩ : ∃ c, w.state.deferreds.cells[key.index]? = some c :=
    ⟨_, List.getElem?_eq_getElem ((cells.promises key).mp pre)⟩
  have step : syncOpStep (.deferredPoll key) w.state =
      some (w.state, Val.bool c.completion.isSome) := by
    simp only [syncOpStep, DeferredStore.poll, DeferredStore.cellAt, hc, Option.map_some]
  exact ⟨_, _, step, w, leHost_refl w, rfl, cells, ⟨_, rfl⟩⟩

theorem deferredCompleteWith_cellImplements (root : ProgramSource) (key : DeferredKey)
    (completion : Completion Val Err Defect FiberId Ann) :
    CellImplements root (.deferredCompleteWith key completion) := by
  intro w _ cells pre
  obtain ⟨a, e, declared, strong⟩ := pre
  have typed : ∀ types, w.«Π» key = some types → CompletionOk w types completion := by
    intro types h
    rw [declared] at h
    cases h
    cases completion with
    | ofExit ex => exact completionOk_of_fitsExit strong.1
    | ofRefGet cell => exact strong
  obtain ⟨ord, cells'⟩ := cells.complete (op := .deferredCompleteWith key completion) rfl rfl rfl rfl
    typed
  exact ⟨_, _, rfl, _, ord, rfl, cells', ⟨_, rfl⟩⟩

/-- The allocation installs the scope it answers (`ScopeStore.entryAt_make_self`), so the handle
fits `Ty.scope` at the answer world (decisions row 156). -/
theorem scopeMake_cellImplements (root : ProgramSource) (strategy : FinalizerStrategy) :
    CellImplements root (.scopeMake strategy) := by
  intro w _ cells _
  have step := syncOpStep_scopeMake w.state strategy
  obtain ⟨ord, cells'⟩ := cells.restate step rfl (fun i v hv ty hty => cells.values i v hv ty hty)
    rfl (fun _ c' hc _ hcomp => .inl ⟨c', hc, hcomp⟩) rfl
  exact ⟨_, _, step, _, ord, rfl, cells', fits_scopeHandle _ _ (ScopeStore.entryAt_make_self _ _ _)⟩

theorem clockNow_cellImplements (root : ProgramSource) : CellImplements root .clockNow := by
  intro w cert cells _
  exact ⟨_, _, syncOpStep_clockNow w.state, w, leHost_refl w, rfl, cells, ⟨_, rfl⟩⟩

/-! ## The store rows, one instance each

Twenty-nine of the thirty-one rows. Each native `sync` row is its cell-level instance read on the
typed state (`CellImplements.implements`), so a row is proved once, on the cell columns. The eight
read-modify-write rows read their term's demand (`TermMaps`) through `termKernel_typed`
(`kernel_typed`), at any cell type; `memoGet` and `memoComplete` read the memo table (`MemoTableTyped`: every entry's Deferred declared at its
layer's context and error types, decisions row 187 (c)), which `memoBuild` establishes and every
other row keeps (`syncOpStep_layerCells`). -/

/-- **A row fulfilled on the cell columns is fulfilled on the typed state** when its step adds no
memo layer cell: the cell columns move by the row (`CellImplements`), the typed state's own clauses
by `StoreTyped.step`. -/
theorem CellImplements.implements {root : ProgramSource} {op : SyncOp}
    (cell : CellImplements root op) (notBuild : ∀ layer memoMap, op ≠ .memoBuild layer memoMap) :
    StoreImplements root op := by
  intro w cert store pre
  obtain ⟨st', ans, step, w', ord, hstate, cells, post⟩ := cell w cert store.toCellsTyped pre
  exact ⟨st', ans, step, w', ord, hstate,
    store.step step hstate ord cells (layerCells_of_not_build step notBuild), post⟩

theorem scopeRemove_implements (root : ProgramSource) (scope key : Nat) :
    StoreImplements root (.scopeRemove scope key) := by
  intro w _ store _
  obtain ⟨ord, store'⟩ := restate_world (op := .scopeRemove scope key) store rfl rfl rfl
    (fun _ c' h => ⟨c', h, rfl⟩) rfl
  exact ⟨_, _, rfl, _, ord, rfl, store', rfl⟩

theorem scopeAdd_implements (root : ProgramSource) (scope : Nat) (fin : FinName) :
    StoreImplements root (.scopeAdd scope fin) := by
  intro w cert store pre
  -- the finalizer's admission (decisions row 151 (a″)) is the scope store's typing, not the
  -- store's: the handler needs the scope's presence only
  replace pre : (w.state.scopes.entryAt scope).isSome = true := pre.1
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
      obtain ⟨m, hm, _, hmem⟩ := MemoWorld.entryAt_mem hentry
      exact ⟨_, _, step, _, ord, rfl, store',
        Or.inr (fits_scopeHandle _ _ (store.memo m hm _ hmem).2)⟩
    · have step := syncOpStep_memoRelease_dec _ _ _ hentry hobs
      obtain ⟨ord, store'⟩ := restate_world store step rfl rfl (fun _ c' h => ⟨c', h, rfl⟩) rfl
      exact ⟨_, _, step, _, ord, rfl, store', Or.inl rfl⟩

theorem refModify_implements (root : ProgramSource) (cell : RefKey) (f : Term) (env : List Val) :
    StoreImplements root (.refModify cell f env) :=
  CellImplements.implements (kernel_cellImplements root rfl) fun _ _ h => nomatch h

theorem refModifySome_implements (root : ProgramSource) (cell : RefKey) (f : Term)
    (env : List Val) : StoreImplements root (.refModifySome cell f env) :=
  CellImplements.implements (kernel_cellImplements root rfl) fun _ _ h => nomatch h

/-- The six rows whose term answers the cell's new value or an option of it: the cell holds a value
of its declared type, the term maps it to one (`TermMaps`), and the answer is the old value, the
new value or `unit` as the row says (`kernel_typed`). -/
theorem refUpdate_implements (root : ProgramSource) (cell : RefKey) (f : Term) (env : List Val) :
    StoreImplements root (.refUpdate cell f env) :=
  CellImplements.implements (kernel_cellImplements root rfl) fun _ _ h => nomatch h

theorem refGetAndUpdate_implements (root : ProgramSource) (cell : RefKey) (f : Term)
    (env : List Val) : StoreImplements root (.refGetAndUpdate cell f env) :=
  CellImplements.implements (kernel_cellImplements root rfl) fun _ _ h => nomatch h

theorem refUpdateAndGet_implements (root : ProgramSource) (cell : RefKey) (f : Term)
    (env : List Val) : StoreImplements root (.refUpdateAndGet cell f env) :=
  CellImplements.implements (kernel_cellImplements root rfl) fun _ _ h => nomatch h

theorem refUpdateSome_implements (root : ProgramSource) (cell : RefKey) (f : Term)
    (env : List Val) : StoreImplements root (.refUpdateSome cell f env) :=
  CellImplements.implements (kernel_cellImplements root rfl) fun _ _ h => nomatch h

theorem refGetAndUpdateSome_implements (root : ProgramSource) (cell : RefKey) (f : Term)
    (env : List Val) : StoreImplements root (.refGetAndUpdateSome cell f env) :=
  CellImplements.implements (kernel_cellImplements root rfl) fun _ _ h => nomatch h

theorem refUpdateSomeAndGet_implements (root : ProgramSource) (cell : RefKey) (f : Term)
    (env : List Val) : StoreImplements root (.refUpdateSomeAndGet cell f env) :=
  CellImplements.implements (kernel_cellImplements root rfl) fun _ _ h => nomatch h

/-- `refMake`'s world: the fresh cell declared at the certificate over the grown heap, typed. -/
theorem refMake_world (root : ProgramSource) (w : World) (initial : Val) (cert : Ty)
    (store : StoreTyped root w) (fits : Fits w initial cert) :
    w.leHost (w.addRef { w.state with refs := w.state.refs ++ [initial] } ⟨w.state.refs.length⟩ cert) ∧
      StoreTyped root
        (w.addRef { w.state with refs := w.state.refs ++ [initial] } ⟨w.state.refs.length⟩ cert) := by
  have step := syncOpStep_refMake w.state initial
  obtain ⟨ord, cells⟩ := store.toCellsTyped.addRef initial cert fits
  exact ⟨ord, store.step step rfl ord cells (layerCells_of_not_build step (fun _ _ h => nomatch h))⟩

theorem refMake_implements (root : ProgramSource) (initial : Val) :
    StoreImplements root (.refMake initial) :=
  CellImplements.implements (refMake_cellImplements root initial) fun _ _ h => nomatch h

theorem refGet_implements (root : ProgramSource) (cell : RefKey) :
    StoreImplements root (.refGet cell) :=
  CellImplements.implements (kernel_cellImplements root rfl) fun _ _ h => nomatch h

theorem refSet_implements (root : ProgramSource) (cell : RefKey) (v : Val) :
    StoreImplements root (.refSet cell v) :=
  CellImplements.implements (kernel_cellImplements root rfl) fun _ _ h => nomatch h

theorem refGetAndSet_implements (root : ProgramSource) (cell : RefKey) (v : Val) :
    StoreImplements root (.refGetAndSet cell v) :=
  CellImplements.implements (kernel_cellImplements root rfl) fun _ _ h => nomatch h

theorem refSetAndGet_implements (root : ProgramSource) (cell : RefKey) (v : Val) :
    StoreImplements root (.refSetAndGet cell v) :=
  CellImplements.implements (kernel_cellImplements root rfl) fun _ _ h => nomatch h

/-- `deferredMake`'s world: the fresh cell declared at the certificate over the grown cells, typed. -/
theorem deferredMake_world (root : ProgramSource) (w : World) (cert : Ty × Ty)
    (store : StoreTyped root w) :
    w.leHost (w.addPromise { w.state with deferreds := w.state.deferreds.make.2 }
      w.state.deferreds.make.1 cert) ∧
      StoreTyped root (w.addPromise { w.state with deferreds := w.state.deferreds.make.2 }
        w.state.deferreds.make.1 cert) := by
  have step := syncOpStep_deferredMake w.state
  obtain ⟨le, _⟩ := deferredMake_extension w cert _ _ step store.toCellsTyped.promise_fresh
  obtain ⟨ord, cells⟩ := store.toCellsTyped.addPromise cert
    { w.state with deferreds := w.state.deferreds.make.2 } rfl rfl rfl le
  exact ⟨ord, store.step step rfl ord cells (layerCells_of_not_build step (fun _ _ h => nomatch h))⟩

theorem deferredMake_implements (root : ProgramSource) : StoreImplements root .deferredMake :=
  CellImplements.implements (deferredMake_cellImplements root) fun _ _ h => nomatch h

theorem deferredIsDone_implements (root : ProgramSource) (key : DeferredKey) :
    StoreImplements root (.deferredIsDone key) :=
  CellImplements.implements (deferredIsDone_cellImplements root key) fun _ _ h => nomatch h

theorem deferredPoll_implements (root : ProgramSource) (key : DeferredKey) :
    StoreImplements root (.deferredPoll key) :=
  CellImplements.implements (deferredPoll_cellImplements root key) fun _ _ h => nomatch h

theorem deferredCompleteWith_implements (root : ProgramSource) (key : DeferredKey)
    (completion : Completion Val Err Defect FiberId Ann) :
    StoreImplements root (.deferredCompleteWith key completion) :=
  CellImplements.implements (deferredCompleteWith_cellImplements root key completion)
    fun _ _ h => nomatch h

theorem deferredInterruptWith_implements (root : ProgramSource) (key : DeferredKey)
    (interruptor : FiberId) : StoreImplements root (.deferredInterruptWith key interruptor) := by
  intro w _ store _
  obtain ⟨ord, store'⟩ := complete_world (op := .deferredInterruptWith key interruptor)
    (cell := key) (effect := .ofExit (.failure (Cause.interrupt (some interruptor))))
    store rfl rfl rfl rfl (fun _ _ => rfl)
  exact ⟨_, _, rfl, _, ord, rfl, store', ⟨_, rfl⟩⟩

theorem clockNow_implements (root : ProgramSource) : StoreImplements root .clockNow :=
  CellImplements.implements (clockNow_cellImplements root) fun _ _ h => nomatch h

theorem sleepCancel_implements (root : ProgramSource) (waiter : FiberId) (token : Nat) :
    StoreImplements root (.sleepCancel waiter token) := by
  intro w _ store _
  obtain ⟨ord, store'⟩ := restate_world (op := .sleepCancel waiter token) store rfl rfl rfl
    (fun _ c' h => ⟨c', h, rfl⟩) rfl
  exact ⟨_, _, rfl, _, ord, rfl, store', rfl⟩

/-- The allocation installs the scope it answers (`ScopeStore.entryAt_make_self`), so the
handle fits `Ty.scope` at the answer world (decisions row 156). -/
theorem scopeMake_implements (root : ProgramSource) (strategy : FinalizerStrategy) :
    StoreImplements root (.scopeMake strategy) :=
  CellImplements.implements (scopeMake_cellImplements root strategy) fun _ _ h => nomatch h

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
    exact ⟨_, _, step, _, ord, rfl, store',
      fits_scopeHandle _ _ (ScopeStore.entryAt_forkChild_child _ _ _ _ _ hentry)⟩

theorem memoFork_implements (root : ProgramSource) (parent : Option MemoMapId) :
    StoreImplements root (.memoFork parent) := by
  intro w _ store _
  obtain ⟨ord, store'⟩ := restate_world (op := .memoFork parent) store rfl rfl rfl
    (fun _ c' h => ⟨c', h, rfl⟩) rfl
  exact ⟨_, _, rfl, _, ord, rfl, store', ⟨_, rfl, MemoWorld.mapAt_append_self _ _⟩⟩

/-- `memoBuild`'s world: the entry's fresh cell declared at the certificate over the new store,
typed; the memo table declares it at the layer's columns (the pre). -/
theorem memoBuild_world (root : ProgramSource) (w : World) (layer : LayerId) (memoMap : MemoMapId)
    (cert : Ty × Ty) (store : StoreTyped root w)
    (pre : storePre root w (.memoBuild layer memoMap) cert) :
    w.leHost (w.addPromise { w.state with
        scopes := w.state.scopes.make w.state.nextName FinalizerStrategy.sequential
        deferreds := w.state.deferreds.make.2
        memo := w.state.memo.insertEntry memoMap layer
          ⟨1, w.state.nextName, w.state.deferreds.make.1, FinName.memoEntry layer memoMap⟩
        nextName := w.state.nextName + 1 } w.state.deferreds.make.1 cert) ∧
      StoreTyped root (w.addPromise { w.state with
        scopes := w.state.scopes.make w.state.nextName FinalizerStrategy.sequential
        deferreds := w.state.deferreds.make.2
        memo := w.state.memo.insertEntry memoMap layer
          ⟨1, w.state.nextName, w.state.deferreds.make.1, FinName.memoEntry layer memoMap⟩
        nextName := w.state.nextName + 1 } w.state.deferreds.make.1 cert) := by
  have step := syncOpStep_memoBuild w.state layer memoMap
  obtain ⟨le, _⟩ := memoBuild_extension w cert _ layer memoMap _ step store.toCellsTyped.promise_fresh
  obtain ⟨ord, cells⟩ := store.toCellsTyped.addPromise cert { w.state with
      scopes := w.state.scopes.make w.state.nextName FinalizerStrategy.sequential
      deferreds := w.state.deferreds.make.2
      memo := w.state.memo.insertEntry memoMap layer
        ⟨1, w.state.nextName, w.state.deferreds.make.1, FinName.memoEntry layer memoMap⟩
      nextName := w.state.nextName + 1 } rfl rfl rfl le
  refine ⟨ord, ⟨cells, fun e he ex hex => ?_, syncOpStep_memoValid _ _ _ _ store.memo step, ?_⟩⟩
  · obtain ⟨e₀, he₀, hex₀⟩ := syncOpStep_closingExit _ w.state _ _ step e he ex hex
    exact fitsExit_mono ord (store.scopeExits e₀ he₀ ex hex₀)
  · intro q hq
    rcases syncOpStep_layerCells _ w.state _ _ step q hq with old | ⟨⟨mm, build⟩, cell, _⟩
    · exact MemoTableTyped.mono ord store.memoTable q old
    · injection build with same
      intro l lt node checked
      obtain ⟨l', lt', node', checked', hcert⟩ := pre
      rw [same, node] at node'
      cases node'
      rw [same, checked] at checked'
      cases checked'
      rw [cell]
      change tableInsert w.«Π» w.state.deferreds.make.1 cert w.state.deferreds.make.1 = _
      rw [insert_here, hcert]

theorem memoBuild_implements (root : ProgramSource) (layer : LayerId) (memoMap : MemoMapId) :
    StoreImplements root (.memoBuild layer memoMap) := by
  intro w cert store pre
  change Ty × Ty at cert
  obtain ⟨ord, store'⟩ := memoBuild_world root w layer memoMap cert store pre
  exact ⟨_, _, syncOpStep_memoBuild w.state layer memoMap, _, ord, rfl, store',
    fits_scopeHandle _ _ (ScopeStore.entryAt_make_self _ _ _)⟩

/-- **`memoGet` fulfils its row** (decisions row 187): a hit answers the entry's cell and its map,
and the memo table declares the cell at the asked layer's columns, the built context and the
error type the row's certificate names; a miss answers `unit`. -/
theorem memoGet_implements (root : ProgramSource) (layer : LayerId) (memoMap : MemoMapId) :
    StoreImplements root (.memoGet layer memoMap) := by
  intro w cert store pre
  change Ty at cert
  obtain ⟨l, lt, node, checked, hcert⟩ := pre
  cases hget : w.state.memo.get layer memoMap with
  | none =>
    exact same_world store (post := fun w' a => storePost w' (.memoGet layer memoMap) cert a)
      (Or.inl rfl) (syncOpStep_memoGet_none _ _ _ hget)
  | some q =>
    obtain ⟨owner, entry⟩ := q
    have step := syncOpStep_memoGet_some w.state layer memoMap hget
    obtain ⟨ord, store'⟩ := restate_world store step rfl rfl (fun _ c' h => ⟨c', h, rfl⟩) rfl
    obtain ⟨m, hm, hid, he⟩ := MemoWorld.get_mem hget
    have declared := store.memoTable (layer, entry.deferred)
      (MemoWorld.mem_layerCells.mpr ⟨m, hm, (layer, entry), he, rfl⟩) l lt node checked
    rw [hcert] at declared
    -- the owner holds the entry, so it is present, and memo maps are never removed
    have present : MemoLive w owner := by
      unfold MemoLive MemoWorld.mapAt
      rw [List.find?_isSome]
      exact ⟨m, hm, by simp only [hid, decide_true]⟩
    exact ⟨_, _, step, _, ord, rfl, store',
      Or.inr ⟨entry.deferred, owner, Val.memoHit?_memoHit _ _, declared, memoLive_mono ord.1 present⟩⟩

/-- **`memoComplete` fulfils its row** (decisions row 187): the memo table declares the entry's
cell at the layer's columns, which the row's exit fits, so the completed cell stays typed; an
absent entry changes nothing. -/
theorem memoComplete_implements (root : ProgramSource) (layer : LayerId) (memoMap : MemoMapId)
    (exit : ExitV) : StoreImplements root (.memoComplete layer memoMap exit) := by
  intro w cert store pre
  obtain ⟨l, lt, node, checked, fits⟩ := pre
  cases hentry : w.state.memo.entryAt memoMap layer with
  | none =>
    exact same_world store (post := fun w' a => storePost w' (.memoComplete layer memoMap exit) cert a)
      rfl (syncOpStep_memoComplete_none _ _ _ _ hentry)
  | some entry =>
    have step := syncOpStep_memoComplete_some w.state layer memoMap exit hentry
    obtain ⟨m, hm, _, he⟩ := MemoWorld.entryAt_mem hentry
    have declared := store.memoTable (layer, entry.deferred)
      (MemoWorld.mem_layerCells.mpr ⟨m, hm, (layer, entry), he, rfl⟩) l lt node checked
    obtain ⟨ord, store'⟩ := complete_world store step rfl rfl rfl fun types h => by
      rw [declared] at h
      cases h
      exact completionOk_of_fitsExit fits.1
    exact ⟨_, _, step, _, ord, rfl, store', rfl⟩

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

/-- The ambient-scope read answers the context's scope handle (`FiberAction.ambientScope`,
`Machine/Fibers.lean:1491-1498`); it lies in the post when the scope is present, which `J`
supplies for every fiber's context (`ambientScope_live`, `ambientScope_answers_of_typed` in
`Assembly.lean`; decisions row 156). -/
theorem ambientScope_answers (root : ProgramSource) (w : World) (scope : Nat)
    (live : ScopeLive w scope) :
    fiberPost w .ambientScope () ((interpR root.program).scopeValue scope) :=
  fits_scopeHandle w scope live

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
    (order : List FinName) (exit : ExitV) (fins : ∀ fin ∈ order, FinalizerAdmitted root w fin)
    (exitFits : FitsExit w ⟨.unknown, .unknown, Env.Requirement.empty⟩ exit) :
    TypedProg root w (EffTy.pure .unit) (closeWalkR strategy order exit) := by
  refine TypedProg.fiber (fun _ h => nomatch h) (fun _ h => nomatch h) (fun _ h => nomatch h)
    (fun _ _ _ h => nomatch h) () trivial ?_
  intro w' o _ _
  exact TypedProg.fiber (fun _ h => nomatch h) (fun _ h => nomatch h) (fun _ h => nomatch h)
    (fun _ _ _ h => nomatch h) ()
    ⟨fun fin hf => finalizerAdmitted_mono root o fin (fins fin hf), fitsExit_mono o exitFits⟩
    (fun _ _ ans post => TypedProg.pure post)

/-- **A registered finalizer is typed** (decisions row 151 (a″)): at every later world and every
closing exit that fits rc.112's release parameter type `Exit<unknown, unknown>`
(`internal/effect.ts:3973`; DI-94, the type the closed-scope row gives a scope's closing exit,
`ScopeExitOk`), its program is typed at `⟨unknown, never⟩`, rc.112's finalizer type
`Effect<unknown>` (`:3849`). The exit premise is what the close needs and no more: a foreign
finalizer's release reads its exit at that type (`capture_lookup`), so it has no typing at an exit
outside it. The generated bundle's `FinalizerOk` is this (`preds`, `Typed/Assembly.lean`), read at
every finalizer a scope holds (`Typed/Sources.lean`'s `each` rows). -/
def FinalizerTyped (root : ProgramSource) (w : World) (fin : FinName) : Prop :=
  ∀ w', w.leHost w' → ∀ ex, FitsExit w' ⟨.unknown, .unknown, Env.Requirement.empty⟩ ex →
    TypedProg root w' ⟨.unknown, .never, Env.Requirement.empty⟩ (denoteFin fin ex)

/-- The finalizer typing transports along the host order (row 87's monotonicity of the bundle's
owner predicates, for its `FinalizerOk`). -/
theorem finalizerTyped_mono (root : ProgramSource) (w w' : World) (fin : FinName)
    (ord : w.leHost w') (h : FinalizerTyped root w fin) : FinalizerTyped root w' fin :=
  fun w'' o => h w'' (leHost_trans _ _ _ ord o)

/-- **A lone finalizer's close is typed at `⟨unit, never⟩`** when the finalizer is typed at
`⟨unknown, never⟩` (rc.112's finalizer type `Effect<unknown>`, `internal/effect.ts:3849`): the
close runs it, then answers `void` (decisions row 151 (a″), `closeScopeR`), so its answer
is irrelevant and its failures are those of a `never` error column (`seq_typed`). -/
theorem voidedClose_typed (root : ProgramSource) {w : World} {fin : FinName} {exit : ExitV}
    (h : TypedProg root w ⟨.unknown, .never, Env.Requirement.empty⟩ (denoteFin fin exit)) :
    TypedProg root w (EffTy.pure .unit)
      ((guardR .onSuccess (denoteFin fin exit)).bind (seqR fun _ => .pure (.success .unit))) :=
  seq_typed root h (fun _ _ _ _ => TypedProg.pure ⟨trivial, trivial⟩) rfl

/-- Every finalizer a close snapshot captures is one a scope of the store holds. -/
theorem mem_of_snapshot {scope : Nat} {exit : ExitV} {st state : Stores}
    {strategy : FinalizerStrategy} {order : List FinName}
    (hs : scopeCloseSnapshot scope exit st = some (state, strategy, order)) :
    ∃ entry ∈ st.scopes.entries, order = entry.scope.closeOrder := by
  unfold scopeCloseSnapshot at hs
  obtain ⟨entry, hentry, hs⟩ := Option.bind_eq_some_iff.mp hs
  change some _ = some (state, strategy, order) at hs
  simp only [Option.some.injEq, Prod.mk.injEq] at hs
  exact ⟨entry, List.mem_of_find?_eq_some hentry, hs.2.2.symm⟩

/-- A lone-finalizer snapshot reads the finalizer off a scope the store holds. -/
theorem lone_of_snapshot {scope : Nat} {exit : ExitV} {st state : Stores}
    {strategy : FinalizerStrategy} {fin : FinName}
    (hs : scopeCloseSnapshot scope exit st = some (state, strategy, [fin])) :
    ∃ entry ∈ st.scopes.entries, fin ∈ entry.scope.closeOrder := by
  unfold scopeCloseSnapshot at hs
  obtain ⟨entry, hentry, hs⟩ := Option.bind_eq_some_iff.mp hs
  change some _ = some (state, strategy, [fin]) at hs
  simp only [Option.some.injEq, Prod.mk.injEq] at hs
  refine ⟨entry, List.mem_of_find?_eq_some hentry, ?_⟩
  rw [hs.2.2]
  exact List.mem_singleton_self fin

/-- **`Scope.close`'s installed program is typed at `⟨unit, never⟩`** at every close (decisions
rows 136 and 151 (a″)): void for no finalizer, the walk for two or more (`closeWalk_typed`), and a
lone finalizer voided (`voidedClose_typed`), typed by the scope store's typing (`fins`, what the
generated bundle's `FinalizerOk` states at every finalizer a scope holds) at the closing exit. The
one premise beside the store's typing is the closing exit's fit at `Exit<unknown, unknown>`: the
lone finalizer's typing reads it, as the closed-scope row reads the closing exit (`ScopeExitOk`),
and the close-scope row's pre gives it (finding F-CLOSE, `closeScope_pre_refuses_unfit_exit`). -/
theorem closeScope_installs (root : ProgramSource) (w : World) (scope : Nat) (exit : ExitV)
    (flag : Bool) (st st' : Stores) (code : RProgram)
    (fins : ∀ entry ∈ st.scopes.entries, ∀ fin ∈ entry.scope.closeOrder, FinalizerTyped root w fin)
    (admitted : ∀ entry ∈ st.scopes.entries, ∀ fin ∈ entry.scope.closeOrder,
      FinalizerAdmitted root w fin)
    (exitFits : FitsExit w ⟨.unknown, .unknown, Env.Requirement.empty⟩ exit)
    (h : closeScopeR scope exit flag st = some (st', code)) :
    TypedProg root w (EffTy.pure .unit) code := by
  unfold closeScopeR at h
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
    | [fin], hs =>
      obtain ⟨entry, hentry, hfin⟩ := lone_of_snapshot hs
      exact voidedClose_typed root (fins entry hentry fin hfin w (leHost_refl w) exit exitFits)
    | _ :: _ :: _, hs =>
      obtain ⟨entry, hentry, horder⟩ := mem_of_snapshot hs
      exact closeWalk_typed root w strategy _ exit
        (fun fin hf => admitted entry hentry fin (horder ▸ hf)) exitFits

/-- **The unsafe close's program is typed at rc.112's finalizer type `⟨unknown, never⟩`**: the lone
finalizer by the scope store's typing at the closing exit, the walk at `⟨unit, never⟩` widened. It
is what the scoped exit's close runs under the finalizer boundary (`prepareScopedExitR`,
`internal/effect.ts:3944-3947`), with the same premises as `closeScope_installs`. -/
theorem closeScopeUnsafe_installs (root : ProgramSource) (w : World) (scope : Nat) (exit : ExitV)
    (flag : Bool) (st st' : Stores) (program : Option RProgram)
    (fins : ∀ entry ∈ st.scopes.entries, ∀ fin ∈ entry.scope.closeOrder, FinalizerTyped root w fin)
    (admitted : ∀ entry ∈ st.scopes.entries, ∀ fin ∈ entry.scope.closeOrder,
      FinalizerAdmitted root w fin)
    (exitFits : FitsExit w ⟨.unknown, .unknown, Env.Requirement.empty⟩ exit)
    (h : closeScopeUnsafeR scope exit flag st = some (st', program)) :
    ∀ code, program = some code → TypedProg root w ⟨.unknown, .never, Env.Requirement.empty⟩ code := by
  unfold closeScopeUnsafeR at h
  cases hs : scopeCloseSnapshot scope exit st with
  | none =>
    rw [hs] at h
    cases h
  | some snapshot =>
    obtain ⟨state, strategy, order⟩ := snapshot
    rw [hs] at h
    simp only at h
    obtain ⟨_, rfl⟩ := h
    intro code hcode
    match order, hs, hcode with
    | [], _, hcode => cases hcode
    | [fin], hs, hcode =>
      cases hcode
      obtain ⟨entry, hentry, hfin⟩ := lone_of_snapshot hs
      exact fins entry hentry fin hfin w (leHost_refl w) exit exitFits
    | _ :: _ :: _, hs, hcode =>
      cases hcode
      obtain ⟨entry, hentry, horder⟩ := mem_of_snapshot hs
      refine typedProg_widen root (T := EffTy.pure .unit) ?_ (Ty.subN_refl _)
        (closeWalk_typed root w strategy _ exit
          (fun fin hf => admitted entry hentry fin (horder ▸ hf)) exitFits)
      exact Ty.sub_unknown _

/-! ## The ledger: the handler side of decisions row 136

One goal per row the evaluator answers, beside the eighteen command goals (`M6Ledger`), with the
two generic rules: the store rows through `syncOpStep` (`StoreImplements`), the fiber rows
through the frame the evaluator saves and the answers their helpers give. Wave 2 consumes them
in M6's `loop` and `deliver` arms. Proved here: the three generic rules, the 31 store rows (`memoGet`
and `memoComplete` through the memo table, decisions row 187) and 40 fiber instances (the guard
row's through `TypedProg.guard_frame`). -/

/-! Row 87: the bundle's `FinalizerOk` (decisions row 151 (a″)) transports along the host order,
beside `M3bWorld`'s other laws (`Typed/Residual.lean`, `Typed/Assembly.lean`, whose foot runs the
scope's report). -/

end Effect4.Program.Typed
