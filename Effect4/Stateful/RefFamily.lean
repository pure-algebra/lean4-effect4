import Effect4.Meta.Derive

/-!
# Stateful.RefFamily

`Refs`: a traced family over **every** rc.112 `Ref` operation that is an
`Effect`, with the Lean handler that is the *projection of the Ref heap* —
spike S2's `RefHeap` (`docs/research/2026-09-03-spike-s2-stores-witnesses.md`
§1.2) at this family's alphabet, where a cell holds a number.

Twelve rows, one per rc.112 entry point, each cited by `path:line`:

| row | rc.112 | answer |
| --- | --- | --- |
| `make` | `Ref.ts:173` | the new `Ref` |
| `get` | `Ref.ts:200` | `A` |
| `set` | `Ref.ts:307` | **the `MutableRef`**, i.e. the cell |
| `getAndSet` | `Ref.ts:399-404` | the value before the write |
| `setAndGet` | `Ref.ts:747` | the assignment expression's value |
| `update` | `Ref.ts:1273-1276` | `undefined` (a block arrow) |
| `getAndUpdate` | `Ref.ts:496-501` | the value before the write |
| `updateAndGet` | `Ref.ts:1368` | the new value |
| `modify` | `Ref.ts:896-901` | `B` |
| `getAndUpdateSome` | `Ref.ts:635-643` | the value read before the write |
| `updateSomeAndGet` | `Ref.ts:1639-1646` | **a fresh read after the write** |
| `modifySome` | `Ref.ts:1159-1163` | `B`; `None` writes back the read value |

Two rc.112 entry points are deliberately not rowed: `updateSome`
(`Ref.ts:1502-1508`) answers `undefined` like `update` and no census clause
separates the two, and `getUnsafe` (`Ref.ts:1672`) is not an `Effect` at all,
so it has no service method to lower.

## What changed against the previous six rows, and why

Both changes are cases of *the row was wrong against rc.112*
(`docs/research/2026-09-03-deep-state-models.md` §4.3), not of taste:

* **`set` answers the cell, not `Unit`.** `MutableRef.set` is
  `(self, value) => { self.current = value; return self }`
  (`MutableRef.ts:1067-1070`) and `Ref.set` is an *expression* arrow over it
  (`Ref.ts:307`), so the success value is the `MutableRef`. The declaration is
  `Effect<void>`, and the previous row read the declaration; census row
  `ref.set-void-returns-cell` is about the runtime value, and no `void`
  spelling can carry it. `Handle "Ref.Ref<number>"` can, so the row answers it
  and `E4-SEM-CE-009`'s "declared `void`, answers the cell" is now a *row*
  rather than a comment. `Ref.update` stays unit: its arrow is a *block*
  (`Ref.ts:1273-1276`), so it really does answer `undefined`, and the pair is
  the whole content of the census row.
* **The read-modify-write rows take a function, not an amount.** rc.112's
  `update`, `getAndUpdate`, `updateAndGet`, `modify`, `getAndUpdateSome`,
  `updateSomeAndGet` and `modifySome` all take an arbitrary function; the
  previous rows took a `Nat` and added it, which is one function of one
  family. DB-02 (`docs/DESIGN-BASIS.md`) forbids a Lean function in canonical
  content, so the function is a **name**: `Handle "RefFn"`, minted by the named
  atoms of `RefFns` below, interpreted on the Lean side by `RefFn.total`,
  `RefFn.partialUpdate`, `RefFn.modify` and `RefFn.modifySome`, and on the host
  by the table `harness/trace/ref-fns.ts` exports. A program names one with a
  `PureTerm.app` (`Refs.update(r, fnIncr 0)`), never with a closure.

The goldens under `generated/traces/ref/` are therefore owed a regeneration:
every row whose request or answer moved changes the log it produces. That
regeneration belongs to the harness lane; nothing in this module runs it.

## The handler is a projection

`refStep` is S2's `refStep` (`workshop/Deep/Stores.lean`) restricted to the ref
fragment of its `SyncOp` alphabet and to `Val := Nat`: every arm is one
`Effect.sync` thunk, so a read-modify-write's read and write happen with no
intervening runtime step, and `none` is a **frontier** — a key no allocation of
this heap minted — never a typed error (`AGENTS.md`). `refsLive` is that step
composed with the answer projection `refAnswerOf`, which is what
`refsLive_is_refStep` says, by `rfl`.

The join is *forgetful* in exactly one direction: S2's heap is `List Val` over
the machine's whole value alphabet and this one is `List Nat`, because every
cell of this family holds a number. Nothing else is dropped.

## Refusals

- **Atomicity is not observable from this lane.** A `Ref` is fiber-safe and the
  point of `modify` is an atomic transformation under contention. Every program
  here is single-fiber, so `modify` is traced as an ordinary answer and nothing
  about atomicity is claimed. Two fibers over one ref belong to the `Fibers`
  lane, which has the tape to order them.
- **The handle index is per-family here and global on the host**
  (`harness/trace/tracer.ts` `nextHandleIndex`). A tail that branded two handle
  types and interleaved their allocation would diverge from a per-family store.
  `E4-SEM-CE-014`.
- **A `RefFn` handle is a *table index*, not a first-seen object index.** The
  host tail must map `RefFn` back through the same declared table
  (`RefFn.ofHandle` below), because a function reaching the host as an ordinary
  object would be numbered in first-seen order and the two faces would disagree
  the first time a program used the functions out of declaration order.

This module declares the projection lemmas and nothing else about the host. The
receipts are `Effect4Test/Flow/RefsContract.lean` and the attacks
`Effect4Test/Counterexamples/Runtime/Refs.lean`; the host comparison is
`scripts/check-trace-host.sh`'s `ref` section, which is evidence and never a
theorem.
-/

set_option linter.unusedVariables false

namespace Effect4.RefFamily

open Effects Effect4 Effect4.Meta Effect4.Target.EffectV4

/-- The one pure atom the ref scripts call on a number. `harness/trace/atoms.ts`
carries its host body, the same one the `Cell` scripts use. -/
def succ (n : Nat) : Nat := n + 1

/-! ## The named functions

DB-02 forbids a Lean function in canonical content, so rc.112's `(a: A) => A`
and `(a: A) => Option<A>` arguments are *names*. `RefFn` is the declared table;
`RefFns` below is the same table on both faces, as `effect_atoms` requires. -/

/-- The functions the ref corpus names, in table order. The alphabet is spike
S2's `FnName` (`workshop/Deep/Stores.lean`). -/
inductive RefFn
  /-- `a => a + 1`. -/
  | incr
  /-- `a => a * 2`. -/
  | double
  /-- `a => [a, a + 1]` under `modify`: take the old value and bump. -/
  | takeAndBump
  /-- `a => Option.none`: the partial update that never fires. -/
  | noChange
  /-- `a => a > 0 ? Option.some(0) : Option.none`. -/
  | zeroWhenPositive
deriving DecidableEq, Repr, Inhabited

/-- The host handle a named function crosses the wire as: the index into the
table, and nothing else. -/
abbrev RefFnHandle := Handle "RefFn"

/-- The cell handle: rc.112's own opaque `Ref.Ref<number>`. -/
abbrev RefHandle := Handle "Ref.Ref<number>"

namespace RefFn

/-- The table position of a function. -/
def index : RefFn → Nat
  | .incr => 0
  | .double => 1
  | .takeAndBump => 2
  | .noChange => 3
  | .zeroWhenPositive => 4

/-- The function a handle names. An index outside the table reads as
`noChange`, the identity of the partial family: a frontier of the *name*
alphabet, never a new function. -/
def ofHandle : RefFnHandle → RefFn
  | ⟨0⟩ => .incr
  | ⟨1⟩ => .double
  | ⟨2⟩ => .takeAndBump
  | ⟨3⟩ => .noChange
  | ⟨4⟩ => .zeroWhenPositive
  | _ => .noChange

/-- `a ↦ f(a)` for the total read-modify-write operations. -/
def total : RefFn → Nat → Nat
  | .incr, n => n + 1
  | .double, n => n * 2
  | .takeAndBump, n => n + 1
  | .noChange, n => n
  | .zeroWhenPositive, n => n

/-- `a ↦ pf(a)` for the `Some`/`None` read-modify-write operations. -/
def partialUpdate : RefFn → Nat → Option Nat
  | .noChange, _ => Option.none
  | .zeroWhenPositive, Nat.succ _ => Option.some 0
  | .zeroWhenPositive, 0 => Option.none
  | f, value => Option.some (f.total value)

/-- `a ↦ [b, a']` (`Ref.ts:898`). -/
def modify : RefFn → Nat → Nat × Nat
  | .takeAndBump, n => (n, n + 1)
  | f, value => (value, f.total value)

/-- `a ↦ [b, Option a']` (`Ref.ts:1161`). -/
def modifySome : RefFn → Nat → Nat × Option Nat
  | .noChange, value => (value, Option.none)
  | f, value => ((f.modify value).1, Option.some (f.modify value).2)

/-- The handle of a function is its table position, and reading it back is the
identity on the table. -/
theorem ofHandle_index (f : RefFn) : ofHandle ⟨f.index⟩ = f := by
  cases f <;> rfl

end RefFn

/-! The named function atoms. One declaration, every face: the Lean body is the
handle, the host body is the same index, and `RefFns.source` is the generated
module. The binder is a tag both faces ignore — `effect_atoms` has no nullary
former — and the *name* is what a program's `PureTerm.app` carries. -/

effect_atoms RefFns importing handles [RefFn] from "./ref-fns.ts" where
  | fnIncr (tag : Nat) : Handle "RefFn" ⟪ "0" ⟫ := ⟨0⟩
  | fnDouble (tag : Nat) : Handle "RefFn" ⟪ "1" ⟫ := ⟨1⟩
  | fnTakeAndBump (tag : Nat) : Handle "RefFn" ⟪ "2" ⟫ := ⟨2⟩
  | fnNoChange (tag : Nat) : Handle "RefFn" ⟪ "3" ⟫ := ⟨3⟩
  | fnZeroWhenPositive (tag : Nat) : Handle "RefFn" ⟪ "4" ⟫ := ⟨4⟩

/-! ## The signature -/

effect_signature Refs where
  | make (initial : Nat) : Handle "Ref.Ref<number>"
      ⟪ "allocate a ref", "a new reference holding the value" ⟫
  | get (ref : Handle "Ref.Ref<number>") : Nat ⟪ "read the ref", "current value" ⟫
  | set (ref : Handle "Ref.Ref<number>") (value : Nat) : Handle "Ref.Ref<number>"
      ⟪ "write the ref", "store", "declared void, answers the mutable cell" ⟫
  | getAndSet (ref : Handle "Ref.Ref<number>") (value : Nat) : Nat
      ⟪ "write the ref and answer the value it held before" ⟫
  | setAndGet (ref : Handle "Ref.Ref<number>") (value : Nat) : Nat
      ⟪ "write the ref and answer the assignment's value" ⟫
  | update (ref : Handle "Ref.Ref<number>") (f : Handle "RefFn") : Unit
      ⟪ "transform the ref in place", "answers undefined" ⟫
  | getAndUpdate (ref : Handle "Ref.Ref<number>") (f : Handle "RefFn") : Nat
      ⟪ "transform the ref and answer the value it held before" ⟫
  | updateAndGet (ref : Handle "Ref.Ref<number>") (f : Handle "RefFn") : Nat
      ⟪ "transform the ref and answer the new value" ⟫
  | modify (ref : Handle "Ref.Ref<number>") (f : Handle "RefFn") : Nat
      ⟪ "transform the ref and answer the function's first component" ⟫
  | getAndUpdateSome (ref : Handle "Ref.Ref<number>") (pf : Handle "RefFn") : Nat
      ⟪ "transform the ref where the partial function is defined",
        "the value read before the write" ⟫
  | updateSomeAndGet (ref : Handle "Ref.Ref<number>") (pf : Handle "RefFn") : Nat
      ⟪ "transform the ref where the partial function is defined",
        "a fresh read after the write" ⟫
  | modifySome (ref : Handle "Ref.Ref<number>") (pf : Handle "RefFn") : Nat
      ⟪ "transform the ref where the partial function is defined",
        "None writes back the value already read" ⟫

/-! ## The Ref heap, and the step over it

Spike S2's `RefHeap` at this family's alphabet. -/

/-- Every live cell, in creation order; a `Handle` indexes into it. The host
tail has no counterpart: it hands rc.112's own `Ref` objects straight through
and the tracer numbers them. -/
abbrev RefStore := List Nat

/-- `self.ref.current` (`Ref.ts:200`); a dangling key is a frontier. -/
def refPeek? (store : RefStore) (handle : RefHandle) : Option Nat := store[handle.index]?

/-- The total reading, for the places a handler has to answer something. -/
def refPeek (store : RefStore) (handle : RefHandle) : Nat := (refPeek? store handle).getD 0

/-- `self.ref.current = value` (`MutableRef.ts:1068`). -/
def refPoke (store : RefStore) (handle : RefHandle) (value : Nat) : RefStore :=
  store.set handle.index value

/-- The store operations of the ref fragment: one arm per rc.112 entry point,
the ref arms of S2's `SyncOp`. -/
inductive RefOp
  | make (initial : Nat)
  | get (cell : RefHandle)
  | set (cell : RefHandle) (value : Nat)
  | getAndSet (cell : RefHandle) (value : Nat)
  | setAndGet (cell : RefHandle) (value : Nat)
  | update (cell : RefHandle) (f : RefFn)
  | getAndUpdate (cell : RefHandle) (f : RefFn)
  | updateAndGet (cell : RefHandle) (f : RefFn)
  | getAndUpdateSome (cell : RefHandle) (pf : RefFn)
  | updateSomeAndGet (cell : RefHandle) (pf : RefFn)
  | modify (cell : RefHandle) (f : RefFn)
  | modifySome (cell : RefHandle) (pf : RefFn)
deriving DecidableEq, Repr

/-- The values a ref step answers: S2's `Val` restricted to the ref fragment. -/
inductive RefVal
  | unit
  | nat (n : Nat)
  | cell (ref : RefHandle)
deriving DecidableEq, Repr, Inhabited

/-- One step of the Ref heap. `none` is a frontier: a key no allocation of this
heap minted. Every arm is one `Effect.sync` thunk, so the read and the write of
a read-modify-write happen with no intervening runtime step
(`Ref.ts:400-404`). -/
def refStep : RefOp → RefStore → Option (RefVal × RefStore)
  | .make initial, store => Option.some (.cell ⟨store.length⟩, store ++ [initial])
  | .get cell, store => (refPeek? store cell).map (fun a => (.nat a, store))
  | .set cell value, store =>
      (refPeek? store cell).map (fun _ => (.cell cell, refPoke store cell value))
  | .getAndSet cell value, store =>
      (refPeek? store cell).map (fun a => (.nat a, refPoke store cell value))
  | .setAndGet cell value, store =>
      (refPeek? store cell).map (fun _ => (.nat value, refPoke store cell value))
  | .update cell f, store =>
      (refPeek? store cell).map (fun a => (.unit, refPoke store cell (f.total a)))
  | .getAndUpdate cell f, store =>
      (refPeek? store cell).map (fun a => (.nat a, refPoke store cell (f.total a)))
  | .updateAndGet cell f, store =>
      (refPeek? store cell).map (fun a => (.nat (f.total a), refPoke store cell (f.total a)))
  | .getAndUpdateSome cell pf, store =>
      (refPeek? store cell).map (fun a =>
        (.nat a,
          match pf.partialUpdate a with
          | Option.some a' => refPoke store cell a'
          | Option.none => store))
  | .updateSomeAndGet cell pf, store =>
      (refPeek? store cell).bind (fun a =>
        match pf.partialUpdate a with
        | Option.some a' =>
            (refPeek? (refPoke store cell a') cell).map
              (fun fresh => (RefVal.nat fresh, refPoke store cell a'))
        | Option.none => Option.some (RefVal.nat a, store))
  | .modify cell f, store =>
      (refPeek? store cell).map (fun a =>
        (.nat (f.modify a).1, refPoke store cell (f.modify a).2))
  | .modifySome cell pf, store =>
      (refPeek? store cell).map (fun a =>
        (.nat (pf.modifySome a).1, refPoke store cell ((pf.modifySome a).2.getD a)))

/-- The total reading of the step: a frontier leaves the heap alone and answers
`unit`, which is the only thing a first-order handler can do with a key no
allocation minted. -/
def refRun (op : RefOp) (store : RefStore) : RefVal × RefStore :=
  (refStep op store).getD (RefVal.unit, store)

/-! ## The handler, as the projection of the heap -/

/-- The store operation a request names. -/
def refOpOf : (name : Refs.Name) → Refs.Param name → RefOp
  | .make, initial => .make initial
  | .get, cell => .get cell
  | .set, (cell, value) => .set cell value
  | .getAndSet, (cell, value) => .getAndSet cell value
  | .setAndGet, (cell, value) => .setAndGet cell value
  | .update, (cell, f) => .update cell (RefFn.ofHandle f)
  | .getAndUpdate, (cell, f) => .getAndUpdate cell (RefFn.ofHandle f)
  | .updateAndGet, (cell, f) => .updateAndGet cell (RefFn.ofHandle f)
  | .modify, (cell, f) => .modify cell (RefFn.ofHandle f)
  | .getAndUpdateSome, (cell, pf) => .getAndUpdateSome cell (RefFn.ofHandle pf)
  | .updateSomeAndGet, (cell, pf) => .updateSomeAndGet cell (RefFn.ofHandle pf)
  | .modifySome, (cell, pf) => .modifySome cell (RefFn.ofHandle pf)

/-- The number a step's value carries. -/
def refNat : RefVal → Nat
  | .nat n => n
  | .cell ref => ref.index
  | .unit => 0

/-- The cell a step's value carries. -/
def refCell : RefVal → RefHandle
  | .cell ref => ref
  | _ => ⟨0⟩

/-- The family answer a step's value projects to, per operation. -/
def refAnswerOf : (name : Refs.Name) → RefVal → Refs.Answer name
  | .make, value => refCell value
  | .get, value => refNat value
  | .set, value => refCell value
  | .getAndSet, value => refNat value
  | .setAndGet, value => refNat value
  | .update, _ => ()
  | .getAndUpdate, value => refNat value
  | .updateAndGet, value => refNat value
  | .modify, value => refNat value
  | .getAndUpdateSome, value => refNat value
  | .updateSomeAndGet, value => refNat value
  | .modifySome, value => refNat value

/-- The Lean handler `ref-tail.ts` mirrors, operation for operation: the heap
step, and the answer projection over it. -/
def refsLive : Refs.Service (StateT RefStore Id) := fun name param => do
  let store ← get
  let step := refRun (refOpOf name param) store
  set step.2
  pure (refAnswerOf name step.1)

/-! ### The projection lemma

The whole content of "the handler is a projection of the heap", in one
equation, by `rfl`. Every clause of `refStep` is therefore a clause of the
handler, and the goldens this module emits are checks on the heap. -/

/-- `refsLive` is `refStep` under `refOpOf` and `refAnswerOf`. -/
theorem refsLive_is_refStep (name : Refs.Name) (param : Refs.Param name) (store : RefStore) :
    refsLive name param store =
      (refAnswerOf name (refRun (refOpOf name param) store).1,
        (refRun (refOpOf name param) store).2) := rfl

/-- On a live handle the frontier arm is not taken, so the handler answers the
step's own value and reaches the step's own heap. -/
theorem refsLive_of_step {name : Refs.Name} {param : Refs.Param name}
    {store store' : RefStore} {value : RefVal}
    (h : refStep (refOpOf name param) store = Option.some (value, store')) :
    refsLive name param store = (refAnswerOf name value, store') := by
  rw [refsLive_is_refStep]
  simp [refRun, h]

/-! ### The clauses the census rows name

Each is `rfl` at the step, so the handler carries it through
`refsLive_is_refStep`. -/

/-- `ref.make`: the single field is a fresh cell, appended in allocation order.
census: ref.make -/
theorem refStep_make (store : RefStore) (initial : Nat) :
    refStep (.make initial) store = Option.some (.cell ⟨store.length⟩, store ++ [initial]) := rfl

/-- `ref.set-void-returns-cell` and `ref.cell-set-returns-self`: `Ref.set`
answers the very cell it was given (`Ref.ts:307`, `MutableRef.ts:1067-1070`).
census: ref.set-void-returns-cell -/
theorem refStep_set (store : RefStore) (cell : RefHandle) (value a : Nat)
    (h : refPeek? store cell = Option.some a) :
    refStep (.set cell value) store = Option.some (.cell cell, refPoke store cell value) := by
  simp [refStep, h]

/-- `ref.update`: the block arrow answers `undefined`, and that is a different
answer from `set`'s. census: ref.update -/
theorem refStep_update (store : RefStore) (cell : RefHandle) (f : RefFn) (a : Nat)
    (h : refPeek? store cell = Option.some a) :
    refStep (.update cell f) store = Option.some (.unit, refPoke store cell (f.total a)) := by
  simp [refStep, h]

/-- The two `void`-declared operations do not answer the same thing. This is
the separation `E4-SEM-CE-009` is about, now inside the alphabet. -/
theorem set_answer_ne_update_answer (store : RefStore) (cell : RefHandle) (f : RefFn)
    (value a : Nat) (h : refPeek? store cell = Option.some a) :
    ((refStep (.set cell value) store).map Prod.fst) ≠
      ((refStep (.update cell f) store).map Prod.fst) := by
  simp [refStep, h]

/-- `ref.set-and-get-assignment`: `setAndGet` succeeds with the assignment
expression, so it never reads the cell a second time (`Ref.ts:747`).
census: ref.set-and-get-assignment -/
theorem refStep_setAndGet (store : RefStore) (cell : RefHandle) (value a : Nat)
    (h : refPeek? store cell = Option.some a) :
    refStep (.setAndGet cell value) store =
      Option.some (.nat value, refPoke store cell value) := by
  simp [refStep, h]

/-- `ref.modify-some-no-reread`: on `None`, `modifySome` writes back the value
`modify` already read, never a re-read (`Ref.ts:1160-1162`).
census: ref.modify-some-no-reread -/
theorem refStep_modifySome_none (store : RefStore) (cell : RefHandle) (a : Nat)
    (h : refPeek? store cell = Option.some a) :
    refStep (.modifySome cell RefFn.noChange) store =
      Option.some (.nat a, refPoke store cell a) := by
  simp [refStep, RefFn.modifySome, h]

/-- `ref.update-some-and-get-reread`: where the partial function is undefined,
`updateSomeAndGet` answers the value it read and writes nothing
(`Ref.ts:1639-1646`). census: ref.update-some-and-get-reread -/
theorem refStep_updateSomeAndGet_none (store : RefStore) (cell : RefHandle) (a : Nat)
    (h : refPeek? store cell = Option.some a) :
    refStep (.updateSomeAndGet cell RefFn.noChange) store = Option.some (.nat a, store) := by
  simp [refStep, RefFn.partialUpdate, h]

/-- `getAndUpdateSome` answers the value read *before* the write and
`updateSomeAndGet` a fresh read *after* it; on a cell the partial function
changes, the two differ. census: ref.update-some-and-get-reread -/
theorem updateSomeAndGet_ne_getAndUpdateSome :
    ((refStep (.updateSomeAndGet ⟨0⟩ RefFn.zeroWhenPositive) [3]).map Prod.fst) ≠
      ((refStep (.getAndUpdateSome ⟨0⟩ RefFn.zeroWhenPositive) [3]).map Prod.fst) := by
  decide

/-! ## The programs

`n` is the parameter every `effect_program` takes; the corpus instantiates it
at the value each golden is generated with. -/

-- The handle a `make` answers is the one every later operation names.
effect_program refMakeGet (n : Nat) over Refs : Nat :=
  let r ← Refs.make(n)
  let v ← Refs.get(r)
  return v

-- `set` answers the cell it wrote, and the read after it sees the write.
effect_program refSetGet (n : Nat) over Refs : Nat :=
  let r ← Refs.make(n)
  let _ ← Refs.set(r, 9)
  let v ← Refs.get(r)
  return v

-- Two identical requests, two identical unit answers, and a read that shows
-- both landed. The function is named, not a closure.
effect_program refUpdateTwice (n : Nat) over Refs : Nat :=
  let r ← Refs.make(n)
  let _ ← Refs.update(r, fnIncr 0)
  let _ ← Refs.update(r, fnIncr 0)
  let v ← Refs.get(r)
  return v

-- `modify` answers the function's first component and the read after it shows
-- the second: `takeAndBump` is `a ↦ [a, a + 1]` (E4-SEM-CE-015).
effect_program refModifyOld (n : Nat) over Refs : Nat :=
  let r ← Refs.make(n)
  let before ← Refs.modify(r, fnTakeAndBump 0)
  let _ ← Refs.get(r)
  return before

effect_program refGetAndSetOld (n : Nat) over Refs : Nat :=
  let r ← Refs.make(n)
  let before ← Refs.getAndSet(r, 100)
  let _ ← Refs.get(r)
  return before

-- `setAndGet` answers the assignment expression, so its answer is the value
-- written and not the value read.
effect_program refSetAndGet (n : Nat) over Refs : Nat :=
  let r ← Refs.make(n)
  let after ← Refs.setAndGet(r, 9)
  let _ ← Refs.get(r)
  return after

-- The `getAndUpdate` / `updateAndGet` pair: one answers before the write, the
-- other after it, on the same function.
effect_program refUpdateAndGet (n : Nat) over Refs : Nat :=
  let r ← Refs.make(n)
  let _ ← Refs.getAndUpdate(r, fnIncr 0)
  let after ← Refs.updateAndGet(r, fnIncr 0)
  return after

-- The partial pair: `getAndUpdateSome` answers the value it read, and
-- `updateSomeAndGet` on an undefined point answers that same value and writes
-- nothing.
effect_program refSomeContrast (n : Nat) over Refs : Nat :=
  let r ← Refs.make(n)
  let before ← Refs.getAndUpdateSome(r, fnZeroWhenPositive 0)
  let after ← Refs.updateSomeAndGet(r, fnZeroWhenPositive 0)
  return after

-- `modifySome` on `None` writes back the value it already read, so the cell is
-- unchanged and the answer is that value.
effect_program refModifySomeNoReread (n : Nat) over Refs : Nat :=
  let r ← Refs.make(n)
  let answer ← Refs.modifySome(r, fnNoChange 0)
  let _ ← Refs.get(r)
  return answer

-- Two handles, allocated in order: a write through the first is invisible
-- through the second.
effect_program refTwoRefs (n : Nat) over Refs : Nat :=
  let a ← Refs.make(n)
  let b ← Refs.make(succ n)
  let _ ← Refs.set(a, 0)
  let _ ← Refs.get(b)
  let _ ← Refs.update(b, fnIncr 0)
  let _ ← Refs.get(a)
  let z ← Refs.get(b)
  return z

/-! ### A failing operation over the same handles

`tryTake` subtracts, and refuses rather than underflowing. The refusal is an
answer, not an abort: the program continues and the read after it is
unaffected, which is the whole claim. It is also the contrasting half of
`E4-SEM-CE-015` — here `Ref.modify`'s two tuple components have *different*
types, so the compiler does pin their order, and only the same-typed `modify`
above needs a golden to separate them. -/

effect_signature ERefs where
  | make (initial : Nat) : Handle "Ref.Ref<number>"
      ⟪ "allocate a ref", "a new reference holding the value" ⟫
  | tryTake (ref : Handle "Ref.Ref<number>") (amount : Nat) : Except String Nat
      ⟪ "subtract from the ref", "the value left, or a refusal that changed nothing" ⟫
  | get (ref : Handle "Ref.Ref<number>") : Nat ⟪ "read the ref", "current value" ⟫

def erefsLive : ERefs.Service (StateT RefStore Id) := fun name =>
  match name with
  | .make => fun initial => do
      let store ← get
      set (store ++ [initial])
      pure ⟨store.length⟩
  | .tryTake => fun (handle, amount) => do
      let store ← get
      let before := refPeek store handle
      if amount ≤ before then
        set (refPoke store handle (before - amount))
        pure (.ok (before - amount))
      else
        pure (.error "underflow")
  | .get => fun handle => do
      let store ← get
      pure (refPeek store handle)

-- A take that succeeds, a take that refuses, and a read that shows the refusal
-- left the cell exactly where the successful one did.
effect_program refTakeUnderflow (n : Nat) over ERefs : Nat :=
  let r ← ERefs.make(n)
  let _ ← ERefs.tryTake(r, 2)
  let _ ← ERefs.tryTake(r, 9)
  let v ← ERefs.get(r)
  return v

example : ((interpret refsLive.toHandler (refMakeGet 7)).run [] : Nat × RefStore) = (7, [7]) := rfl
example : ((interpret refsLive.toHandler (refSetGet 7)).run [] : Nat × RefStore) = (9, [9]) := rfl
example : ((interpret refsLive.toHandler (refUpdateTwice 7)).run [] : Nat × RefStore) = (9, [9]) := rfl
example : ((interpret refsLive.toHandler (refModifyOld 7)).run [] : Nat × RefStore) = (7, [8]) := rfl
example : ((interpret refsLive.toHandler (refGetAndSetOld 7)).run [] : Nat × RefStore) = (7, [100]) := rfl
example : ((interpret refsLive.toHandler (refSetAndGet 7)).run [] : Nat × RefStore) = (9, [9]) := rfl
example : ((interpret refsLive.toHandler (refUpdateAndGet 7)).run [] : Nat × RefStore) = (9, [9]) := rfl
example : ((interpret refsLive.toHandler (refSomeContrast 3)).run [] : Nat × RefStore) = (0, [0]) := rfl
example :
    ((interpret refsLive.toHandler (refModifySomeNoReread 1)).run [] : Nat × RefStore) = (1, [1]) :=
  rfl
example : ((interpret refsLive.toHandler (refTwoRefs 7)).run [] : Nat × RefStore) = (9, [0, 9]) := rfl
example : ((interpret erefsLive.toHandler (refTakeUnderflow 7)).run [] : Nat × RefStore) = (5, [5]) := rfl

/-- The traced run of a ref program from an empty store, with its outcome
appended. A ref family allocates what it reads, so there is no ambient initial
cell for the two faces to disagree about. -/
def refGoldenLog {α : Type} [Effects.Trace.ToVal α] (program : Program Refs.Sig α) :
    Effect4.Trace.Log :=
  let result : (α × Effect4.Trace.Log) × RefStore :=
    ((interpret (Refs.traced refsLive).toHandler program).run []).run []
  result.1.2 ++ [.done (.success (Effects.Trace.ToVal.toVal result.1.1))]

def erefGoldenLog {α : Type} [Effects.Trace.ToVal α] (program : Program ERefs.Sig α) :
    Effect4.Trace.Log :=
  let result : (α × Effect4.Trace.Log) × RefStore :=
    ((interpret (ERefs.traced erefsLive).toHandler program).run []).run []
  result.1.2 ++ [.done (.success (Effects.Trace.ToVal.toVal result.1.1))]

/-- One ref program: its family's rows, its script, and its golden log. -/
structure RefEntry where
  name : String
  rows : ServiceRow
  script : Script
  log : Effect4.Trace.Log

def refPrograms : List RefEntry :=
  [ { name := "makeGet", rows := Refs.rows, script := refMakeGet.script,
      log := refGoldenLog (refMakeGet 7) }
  , { name := "setGet", rows := Refs.rows, script := refSetGet.script,
      log := refGoldenLog (refSetGet 7) }
  , { name := "updateTwice", rows := Refs.rows, script := refUpdateTwice.script,
      log := refGoldenLog (refUpdateTwice 7) }
  , { name := "modifyOld", rows := Refs.rows, script := refModifyOld.script,
      log := refGoldenLog (refModifyOld 7) }
  , { name := "getAndSetOld", rows := Refs.rows, script := refGetAndSetOld.script,
      log := refGoldenLog (refGetAndSetOld 7) }
  , { name := "setAndGet", rows := Refs.rows, script := refSetAndGet.script,
      log := refGoldenLog (refSetAndGet 7) }
  , { name := "updateAndGet", rows := Refs.rows, script := refUpdateAndGet.script,
      log := refGoldenLog (refUpdateAndGet 7) }
  , { name := "someContrast", rows := Refs.rows, script := refSomeContrast.script,
      log := refGoldenLog (refSomeContrast 3) }
  , { name := "modifySomeNoReread", rows := Refs.rows, script := refModifySomeNoReread.script,
      log := refGoldenLog (refModifySomeNoReread 1) }
  , { name := "twoRefs", rows := Refs.rows, script := refTwoRefs.script,
      log := refGoldenLog (refTwoRefs 7) }
  , { name := "takeUnderflow", rows := ERefs.rows, script := refTakeUnderflow.script,
      log := erefGoldenLog (refTakeUnderflow 7) } ]

/-- The families of the ref module, each with its scripts. -/
def refFamilies : List (ServiceRow × List Script) :=
  [ (Refs.rows, [refMakeGet.script, refSetGet.script, refUpdateTwice.script, refModifyOld.script,
      refGetAndSetOld.script, refSetAndGet.script, refUpdateAndGet.script, refSomeContrast.script,
      refModifySomeNoReread.script, refTwoRefs.script])
  , (ERefs.rows, [refTakeUnderflow.script]) ]

end Effect4.RefFamily

