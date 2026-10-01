import Test.Program.TypedCorpus

/-! Registry seat, task 5: what creation evidence cells and deferreds would need.

Research evidence outside the Test root. Base `be15b062`. Finite checks, not proofs.

Today a native cell holds a number and a deferred completes with numbers
(`Program/Native.lean:90`, `:98`). The pattern that works for fibers is: the creating
transition records the creation site, and the declared type is the checker's type at that
site, in `staticEnvAt`'s environment. This probe shows what the stores record today, and what
the template rows of decisions rows 42 and 43 would give at a creation site. -/

set_option autoImplicit false
set_option maxRecDepth 8192

namespace Research.Pass.Registry.Cells
open Effect4 Effect4.Machine Effect4.Program

abbrev E := Eff NativeOp
def n (i : Nat) : Term := .lit (.nat i)
def u : Term := .lit .unit

/-! ## 1. The stores keep values and completions, not creation sites -/

/-- Two cells made at two sites, then a deferred made. -/
def twoCells : E :=
  .bind (.perform .refMake (n 1))
    (.bind (.perform .refMake (n 2))
      (.bind (.perform .deferredMake u) (.succeed u)))

def finalStores : Stores := (Api.run twoCells 1000).machine.state

-- The heap is the values in allocation order (`RefHeap := List Val`, `Machine/Stores.lean:841`):
-- the cell key is the index, and nothing names the `perform` that made it.
#guard finalStores.refs = [.nat 1, .nat 2]
#guard finalStores.deferreds.cells.length = 1
-- The compile drops the site when it builds the store operation: `perform` at point `p` becomes
-- `Prim.sync (EffThunk.op operation)` (`Program/Compile.lean:574-586`); `SyncOp.refMake`
-- carries the initial value only.
#guard (Api.compile (.perform .refMake (n 1)) 10) = Prim.sync (EffThunk.op (SyncOp.refMake (.nat 1)))

/-! ## 2. Memo deferreds already record their creating layer -/

def key : ServiceKey := ⟨⟨4⟩, ⟨4⟩⟩

/-- The body sleeps, so the layer is still provided, and its memo entry alive, when the tape
stops: the entry is deleted when the last observer releases it at scope close. -/
def memoProgram : E :=
  .scoped (.provideLayer (.effect key (.succeed (n 1))) false
    (.bind (.perform .sleep (n 5)) (.service key)))

def memoWorld : MemoWorld :=
  (Api.replay memoProgram 1000 [Api.evaluate, Api.flush]).machine.state.memo

-- Every memo entry is keyed by its layer's path (`LayerId`, `SyncOp.memoBuild q.path`,
-- `Compile.lean:1141`) and holds its deferred's key; the path names a layer node of the
-- program, whose checked signature gives the deferred's error column.
#guard (memoWorld.flatMap (·.entries)).length = 1
#guard (memoWorld.flatMap (·.entries)).all fun (layer, _) =>
  match Node.at_ (.eff memoProgram) layer with
  | some (.layer l) => (Checker.checkLayer (nativeSignature []) layer l).toOption.isSome
  | _ => false

/-! ## 3. The template rows of decisions rows 42-43 at a creation site -/

/-- `Ref.make : A → Ref<A>`, as a template row. -/
def refMakeRow : Row :=
  { name := "refMake", spelling := "Ref.make", kind := .sync, request := .var 0,
    answer := .refOf (.var 0), cite := "research probe" }

/-- `Deferred.make<A, E>() : Deferred<A, E>`, as a template row: the request is `void`. -/
def deferredMakeRow : Row :=
  { name := "deferredMake", spelling := "Deferred.make", kind := .sync, request := .unit,
    answer := .deferredOf (.var 0) (.var 1), cite := "research probe" }

-- A cell's type is fixed by its initial value's static type at the site: the site's
-- environment (`staticEnvAt`) and the request term give it.
#guard (rowTy refMakeRow .string).map (·.answer) = some (.refOf .string)
#guard (rowTy refMakeRow (.option .nat)).map (·.answer) = some (.refOf (.option .nat))
-- A deferred's types are not in its request: the template's parameters stay unbound and
-- instantiate to `never` (`Ty.instantiate`, `Program/Ty.lean:474-495`). The creation site must
-- carry them, as `refUpdate` carries its `FnName` in the operation today.
#guard (rowTy deferredMakeRow .unit).map (·.answer) = some (.deferredOf .never .never)

/-! ## 4. Why a cell's declaration is compared exactly

A cell is written and read at one type: `refOf` is invariant (decisions row 55). So the boundary
check a registry would make for a cell handle compares the declaration exactly, where a fiber's
compares by subtyping. Today's shape check accepts any cell handle at any `refOf`. -/

#guard Val.hasTy (Val.cell ⟨0⟩) (.refOf .string)
#guard Val.hasTy (Val.cell ⟨0⟩) (.refOf .nat)

#eval IO.println "Cells probe: all guards passed."

end Research.Pass.Registry.Cells
