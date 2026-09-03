import Effect4.Meta.Derive

/-!
# Stateful.RefFamily

`Refs`: a traced family over rc.112's `Ref.make` / `Ref.get` / `Ref.set` /
`Ref.update` / `Ref.modify` / `Ref.getAndSet`, with the Lean handler
`harness/trace/ref-tail.ts` mirrors operation for operation.

The second family over an opaque host handle (after M1's `Scopes`), and the one
where the handle is the *only* thing the family owns. `Handle "Ref.Ref<number>"`
prints rc.112's own `Ref.Ref<number>`, so the host tail is a thin wrapper: it
keeps no store, hands the ref objects straight through, and the tracer indexes
them. The Lean face keeps a `List Nat` and names cells `0, 1, 2, …` in creation
order; the host tracer indexes the objects it is handed in first-seen order.
The two agree because a ref only ever leaves the host as the answer of the
`make` that produced it, and because this tail brands exactly one handle type
(`E4-SEM-CE-014`).

## What the goldens are stated against

The reading of record is the census (`generated/effect-runtime-census.tsv`
rows `ref.*`); `harness/trace/ref-probe.mjs` executes it on the pin.

- `set` and `update` are declared `Effect<void>` and rc.112 disagrees with
  itself about what they hand back. `Ref.set` answers the mutable cell
  (`ref.set-void-returns-cell`, `ref.cell-set-returns-self`; `E4-SEM-CE-009`)
  and `Ref.update` answers `undefined` (`ref.update`). Both rows are unit here,
  read off the declared spelling and off neither runtime value — which is the
  point: no rule over runtime values covers both.
- `modify` and `getAndSet` answer the value *before* the write. Both goldens use
  a non-zero amount and read the cell afterwards, so the answer and the new
  state are separate rows: when the two share a type nothing else separates them
  (`E4-SEM-CE-015`).

## Refusals

- **Atomicity is not observable from this lane.** A `Ref` is fiber-safe and the
  point of `modify` is an atomic transformation under contention. Every program
  here is single-fiber, so `modify` is traced as an ordinary answer and nothing
  about atomicity is claimed. Two fibers over one ref belong to the `Fibers`
  lane, which has the tape to order them.
- **The handle index is per-family here and global on the host**
  (`harness/trace/tracer.ts` `nextHandleIndex`). A tail that branded two handle
  types and interleaved their allocation would diverge from a per-family store.
  `ref-tail.ts` brands one. `E4-SEM-CE-014`.

This module declares no theorem. The receipts are `Effect4Test/Flow/RefsContract.lean`
and the attacks `Effect4Test/Counterexamples/Runtime/Refs.lean`; the host
comparison is `scripts/check-trace-host.sh`'s `ref` section, which is evidence
and never a theorem.
-/

namespace Effect4.RefFamily

open Effects Effect4 Effect4.Meta Effect4.Target.EffectV4

/-- The one pure atom the ref scripts call. `harness/trace/atoms.ts` carries its
host body, the same one the `Cell` scripts use. -/
def succ (n : Nat) : Nat := n + 1

effect_signature Refs where
  | make (initial : Nat) : Handle "Ref.Ref<number>"
      ⟪ "allocate a ref", "a new reference holding the value" ⟫
  | get (ref : Handle "Ref.Ref<number>") : Nat ⟪ "read the ref", "current value" ⟫
  | set (ref : Handle "Ref.Ref<number>") (value : Nat) : Unit ⟪ "write the ref", "store" ⟫
  | update (ref : Handle "Ref.Ref<number>") (amount : Nat) : Unit
      ⟪ "add to the ref", "transform in place" ⟫
  | modify (ref : Handle "Ref.Ref<number>") (amount : Nat) : Nat
      ⟪ "add to the ref and answer the value it held before" ⟫
  | getAndSet (ref : Handle "Ref.Ref<number>") (value : Nat) : Nat
      ⟪ "write the ref and answer the value it held before" ⟫

/-- Every live cell, in creation order; a `Handle` indexes into it. The host
tail has no counterpart: it hands rc.112's own `Ref` objects straight through
and the tracer numbers them. -/
abbrev RefStore := List Nat

def refPeek (store : RefStore) (handle : Handle "Ref.Ref<number>") : Nat :=
  (store[handle.index]?).getD 0

def refPoke (store : RefStore) (handle : Handle "Ref.Ref<number>") (value : Nat) : RefStore :=
  store.set handle.index value

/-- The Lean handler `ref-tail.ts` mirrors, operation for operation. -/
def refsLive : Refs.Service (StateT RefStore Id) := fun name =>
  match name with
  | .make => fun initial => do
      let store ← get
      set (store ++ [initial])
      pure ⟨store.length⟩
  | .get => fun handle => do
      let store ← get
      pure (refPeek store handle)
  | .set => fun (handle, value) => do
      modify fun store => refPoke store handle value
  | .update => fun (handle, amount) => do
      let store ← get
      set (refPoke store handle (refPeek store handle + amount))
  | .modify => fun (handle, amount) => do
      let store ← get
      let before := refPeek store handle
      set (refPoke store handle (before + amount))
      pure before
  | .getAndSet => fun (handle, value) => do
      let store ← get
      let before := refPeek store handle
      set (refPoke store handle value)
      pure before

-- The handle a `make` answers is the one every later operation names.
effect_program refMakeGet (n : Nat) over Refs : Nat :=
  let r ← Refs.make(n)
  let v ← Refs.get(r)
  return v

-- A `void` answer is unit whatever rc.112's `Ref.set` hands back.
effect_program refSetGet (n : Nat) over Refs : Nat :=
  let r ← Refs.make(n)
  let _ ← Refs.set(r, 9)
  let v ← Refs.get(r)
  return v

-- Two identical requests, two identical unit answers, and a read that shows
-- both landed.
effect_program refUpdateTwice (n : Nat) over Refs : Nat :=
  let r ← Refs.make(n)
  let _ ← Refs.update(r, 1)
  let _ ← Refs.update(r, 1)
  let v ← Refs.get(r)
  return v

-- `modify` answers 7 and the read after it answers 12: the amount is non-zero
-- on purpose (E4-SEM-CE-015).
effect_program refModifyOld (n : Nat) over Refs : Nat :=
  let r ← Refs.make(n)
  let before ← Refs.modify(r, 5)
  let _ ← Refs.get(r)
  return before

effect_program refGetAndSetOld (n : Nat) over Refs : Nat :=
  let r ← Refs.make(n)
  let before ← Refs.getAndSet(r, 100)
  let _ ← Refs.get(r)
  return before

-- Two handles, allocated in order: a write through the first is invisible
-- through the second.
effect_program refTwoRefs (n : Nat) over Refs : Nat :=
  let a ← Refs.make(n)
  let b ← Refs.make(succ n)
  let _ ← Refs.set(a, 0)
  let _ ← Refs.get(b)
  let _ ← Refs.update(b, 1)
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
      let before := (store[handle.index]?).getD 0
      if amount ≤ before then
        set (store.set handle.index (before - amount))
        pure (.ok (before - amount))
      else
        pure (.error "underflow")
  | .get => fun handle => do
      let store ← get
      pure ((store[handle.index]?).getD 0)

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
example : ((interpret refsLive.toHandler (refModifyOld 7)).run [] : Nat × RefStore) = (7, [12]) := rfl
example : ((interpret refsLive.toHandler (refGetAndSetOld 7)).run [] : Nat × RefStore) = (7, [100]) := rfl
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
  , { name := "twoRefs", rows := Refs.rows, script := refTwoRefs.script,
      log := refGoldenLog (refTwoRefs 7) }
  , { name := "takeUnderflow", rows := ERefs.rows, script := refTakeUnderflow.script,
      log := erefGoldenLog (refTakeUnderflow 7) } ]

/-- The families of the ref module, each with its scripts. -/
def refFamilies : List (ServiceRow × List Script) :=
  [ (Refs.rows, [refMakeGet.script, refSetGet.script, refUpdateTwice.script, refModifyOld.script,
      refGetAndSetOld.script, refTwoRefs.script])
  , (ERefs.rows, [refTakeUnderflow.script]) ]


end Effect4.RefFamily
