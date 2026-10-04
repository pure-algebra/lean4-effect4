import Test.Program.LayerDenotation

/-!
# Test.Program.MemoTable — the memo table (decisions row 187 (c))

The store typing's memo row (`MemoTableTyped`, `Typed/Adequacy.lean`; in `J` the promise table's
memo row, `PromiseTableOk.memo`): every memo entry's Deferred is declared at its layer's columns,
the built context and the layer's own checked error type. `memoBuild` establishes it at the cell it
allocates, every other row keeps it (`syncOpStep_layerCells`), and `memoGet` and `memoComplete`
read it (`memoGet_implements`, `memoComplete_implements`).

The controls run the leaf of `Test.Program.LayerDenotation` (`memoSrc`: the layer at `[0]` binds
`K`, its checked error `never`) through the actual store steps:

* **the build** (`built`): from the forked store, `memoBuild` answers a scope and the typed store
  after it declares the entry's cell at `(Ty.context, never)`;
* **a real hit** (`hit`): `memoGet` on the built store answers the entry's cell and map, and the
  row's post types that cell at the leaf's columns;
* **a real completion** (`completed`): `memoComplete` with the built context completes the cell,
  and the store stays typed;
* **the wrong error column is refused**: a world declaring the entry's cell at `string` is no typed
  store (`wrong_column_refused`), and a `memoGet` request certified at `string` is refused by the
  row's pre (`wrong_certificate_refused`).
-/

set_option autoImplicit false

namespace Test.Program.MemoTable

open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Sched Effect4.Program.Typed
open Test.Program.TypedDenotation Test.Program.LayerDenotation

/-- The store after `memoFork none`: one memo map, id 0, no entry. -/
def s0 : Stores := { Stores.empty with memo := [⟨⟨0⟩, none, []⟩], nextName := 1 }

theorem forked : syncOpStep (.memoFork none) Stores.empty = some (s0, Val.memoMap ⟨0⟩) := rfl

/-- The world over the forked store: nothing declared. -/
def w0 : W :=
  { wHit with state := s0, «Π» := fun _ => none }

theorem store0 : StoreTyped memoSrc w0 :=
  ⟨⟨fun _ => ⟨(fun h => nomatch h), (fun h => absurd h (Nat.not_lt_zero _))⟩,
    fun _ => ⟨(fun h => nomatch h), (fun h => absurd h (Nat.not_lt_zero _))⟩,
    (fun _ _ h => nomatch h)⟩, (fun _ h => nomatch h),
    (fun m hm e he => by
      change m ∈ [_] at hm
      rw [List.mem_singleton] at hm
      subst hm
      cases he),
    (fun _ hp => nomatch hp)⟩

/-! ## The build -/

/-- `memoBuild`'s certificate: the leaf's columns. -/
theorem build_pre : storePre memoSrc w0 (.memoBuild [0] ⟨0⟩) (.handle Ty.contextTarget, .never) :=
  ⟨memoLayer, _, memo_layer_node, memo_layer_check, rfl⟩

/-- The store after the build: map 0 holds the leaf's entry, at cell 0 and layer scope 1. -/
def s1 : Stores := (syncOpStep (.memoBuild [0] ⟨0⟩) s0).map Prod.fst |>.getD Stores.empty

theorem built_step : syncOpStep (.memoBuild [0] ⟨0⟩) s0 = some (s1, Val.scopeHandle 1) := rfl

theorem s1_cells : s1.memo.layerCells = [([0], ⟨0⟩)] := rfl

/-- **The build establishes the memo row**: the typed store after it declares the entry's cell at
the leaf's columns. -/
theorem built : ∃ w1, w0.leHost w1 ∧ w1.state = s1 ∧ StoreTyped memoSrc w1 ∧
    w1.«Π» ⟨0⟩ = some (.handle Ty.contextTarget, .never) := by
  obtain ⟨st, ans, step, w1, ord, hst, store1, _⟩ :=
    memoBuild_implements memoSrc [0] ⟨0⟩ w0 _ store0 build_pre
  rw [show w0.state = s0 from rfl, built_step] at step
  cases step
  refine ⟨w1, ord, hst, store1, ?_⟩
  have mem : ([0], (⟨0⟩ : DeferredKey)) ∈ w1.state.memo.layerCells := by
    rw [hst, s1_cells]
    exact List.mem_singleton_self _
  exact store1.memoTable _ mem memoLayer _ memo_layer_node memo_layer_check

/-! ## A real hit -/

/-- `memoGet` on the built store hits: it answers the entry's cell and its map. -/
theorem hit_step :
    (syncOpStep (.memoGet [0] ⟨0⟩) s1).map Prod.snd = some (Val.memoHit ⟨0⟩ ⟨0⟩) := rfl

/-- **A real hit, typed**: the answer `memoGet` gives on the built store is the hit, and the row's
post declares its cell at the leaf's columns. -/
theorem hit : ∃ (w2 : W) (cell : DeferredKey) (owner : MemoMapId), Val.memoHit? (Val.memoHit ⟨0⟩ ⟨0⟩) = some (cell, owner) ∧
    w2.«Π» cell = some (.handle Ty.contextTarget, .never) := by
  obtain ⟨w1, _, hst, store1, _⟩ := built
  obtain ⟨st, ans, step, w2, _, _, _, post⟩ :=
    memoGet_implements memoSrc [0] ⟨0⟩ w1 Ty.never store1
      ⟨memoLayer, _, memo_layer_node, memo_layer_check, rfl⟩
  have answer : ans = Val.memoHit ⟨0⟩ ⟨0⟩ := by
    have h := hit_step
    rw [← hst, step] at h
    exact Option.some.inj h
  subst answer
  rcases post with unit | ⟨cell, owner, read, declared, _⟩
  · cases unit
  · exact ⟨w2, cell, owner, read, declared⟩

/-! ## A real completion -/

/-- The exit the build completes the entry with: the built context. -/
def builtExit : ExitV := .success (Val.context emptyCtx)

/-- `memoComplete` on the built store completes cell 0 with the built context. -/
theorem completed_step :
    ((syncOpStep (.memoComplete [0] ⟨0⟩ builtExit) s1).map Prod.fst).bind
        (fun s => (s.deferreds.cellAt ⟨0⟩).bind (·.completion)) =
      some (.ofExit builtExit) := rfl

theorem completed_store :
    syncOpStep (.memoComplete [0] ⟨0⟩ builtExit) s1 =
      some ({ s1 with deferreds := (s1.deferreds.complete ⟨0⟩ (.ofExit builtExit)).1 }, Val.unit) :=
  rfl

/-- **A real completion, typed**: the store after it is typed again. -/
theorem completed : ∃ w3, StoreTyped memoSrc w3 ∧
    w3.state.deferreds.cellAt ⟨0⟩ = (s1.deferreds.complete ⟨0⟩ (.ofExit builtExit)).1.cellAt ⟨0⟩ := by
  obtain ⟨w1, _, hst, store1, _⟩ := built
  obtain ⟨st, ans, step, w3, _, hst3, store3, _⟩ :=
    memoComplete_implements memoSrc [0] ⟨0⟩ builtExit w1 PUnit.unit store1
      ⟨memoLayer, _, memo_layer_node, memo_layer_check, ⟨emptyCtx_fits w1, trivial⟩⟩
  rw [hst, completed_store] at step
  cases step
  exact ⟨w3, store3, by rw [hst3]⟩

/-! ## The wrong error column is refused -/

/-- The built store at a world that declares the entry's cell at `string`. -/
def wBad : W :=
  { wHit with
    state := s1
    «Π» := fun k => if k = ⟨0⟩ then some (.handle Ty.contextTarget, .string) else none }

/-- **Refused**: the memo row reads the leaf's checked error, `never`, and the world says
`string`. -/
theorem wrong_column_refused : ¬ StoreTyped memoSrc wBad := by
  intro store
  have mem : ([0], (⟨0⟩ : DeferredKey)) ∈ wBad.state.memo.layerCells := by
    change ([0], (⟨0⟩ : DeferredKey)) ∈ s1.memo.layerCells
    rw [s1_cells]
    exact List.mem_singleton_self _
  have declared := store.memoTable _ mem memoLayer _ memo_layer_node memo_layer_check
  change (if (⟨0⟩ : DeferredKey) = ⟨0⟩ then some (Ty.handle Ty.contextTarget, Ty.string)
    else none) = _ at declared
  rw [if_pos rfl] at declared
  cases declared

/-- **Refused**: a `memoGet` request certified at `string` is not admitted; the row's certificate
is the looked-up layer's own checked error. -/
theorem wrong_certificate_refused (w : W) :
    ¬ storePre memoSrc w (.memoGet [0] ⟨0⟩) Ty.string := by
  rintro ⟨l, lt, node, checked, err⟩
  rw [memo_layer_node] at node
  cases node
  rw [memo_layer_check] at checked
  cases checked
  cases err

end Test.Program.MemoTable
