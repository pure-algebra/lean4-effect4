/-
Counterexamples for the `Refs` family (`test/counterexamples/REGISTER.md`,
`E4-SEM-CE-012` and `E4-SEM-CE-013`).

Both attacks are about a *host* fact that the Lean face cannot state, so each is
recorded in two halves: the rc.112 observation, executed by
`harness/trace/ref-probe.mjs`, and the Lean witness below, which shows that the
committed golden rejects the attack and — the half that is easy to lose — that
the golden it would have been natural to write instead does not.

Pinned host: `effect@4.0.0-rc.112` (`harness/trace/host-pin.json`).
Doc comments cannot precede `#guard`, so the receipts carry line comments.
-/

import Effect4.Stateful.RefFamily
import Effect4.Semantics.Observation

namespace Effect4Test.Counterexamples.Runtime.Refs

open Effects Effect4 Effect4.Meta
open Effect4.RefFamily

/-! ## E4-SEM-CE-012: the handle index is the same counter on both faces

Attack: read `harness/trace/tracer.ts`'s first-seen indexing as *the* meaning of
a handle, and let a tail brand as many handle types as it likes.

It is one counter. `nextHandleIndex` is a single module-global running number
over every branded object, while the Lean face numbers each family's handles
from `0` within its own store. `ref-probe.mjs` prints, after branding both
rc.112's `Ref` and its `Scope`:

    first scope   -> host handle index 1
    next  ref     -> host handle index 2
    a per-family Lean store would name that ref 0, not 2

So the agreement `harness/trace/ref-tail.ts` relies on is not a property of the
tracer. It holds because that tail brands exactly one handle type, so first-seen
order and creation order coincide within it.

The Lean half of the row is the shape of the claim: each family's store starts
at `0` and knows nothing of any other family's allocations. -/

/-- Two families' handles are named independently: the first cell either one
allocates is `0`, whatever the other has done. -/
def firstHandleOf (log : Effect4.Trace.Log) : Option Effects.Trace.Val :=
  (log.find? fun event => match event with | .answer "make" _ => true | _ => false).bind
    fun event => match event with | .answer _ value => some value | _ => none

-- The `Refs` face names its first cell 0 …
#guard firstHandleOf (refGoldenLog (refMakeGet 7)) = some (.nat 0)

-- … and so does the `ERefs` face, from its own store, with no counter shared
-- between them. A host that indexed both families from one counter would put a
-- different number in the second of these rows.
#guard firstHandleOf (erefGoldenLog (refTakeUnderflow 7)) = some (.nat 0)

-- Within one family the names are creation order, and distinct cells get
-- distinct names: `twoRefs` allocates two and names them 0 and 1.
#guard (refGoldenLog (refTwoRefs 7)).filterMap
    (fun event => match event with | .answer "make" value => some value | _ => none)
  = [.nat 0, .nat 1]

-- A handle crosses the wire as a bare index, so nothing about the host object
-- it names is describable, and nothing else has to agree for the two faces to.
#guard Refs.encodeAnswer .make ⟨0⟩ = Effects.Trace.Val.nat 0

example (left right : Handle "Ref.Ref<number>")
    (equal : Refs.encodeAnswer .make left = Refs.encodeAnswer .make right) : left = right := by
  have index : left.index = right.index := by injection equal
  cases left; cases right; simp_all

/-! ## E4-SEM-CE-013: a `modify` answer is pinned by its type

Attack: rc.112's `Ref.modify(self, f)` takes `f : (a) => readonly [B, A]`, and
`Refs.modify` declares `Handle × Nat → Nat`. Read the declaration as fixing
which component is the answer.

It does not, when `B = A`. A tail that answers the *new* value and stores the
*old* one typechecks under the pinned unpatched compiler (`tsc.original`, exit
0) and draws no `effect-tsgo` diagnostic; only a golden separates them.

Repair: `refModifyOld` adds a non-zero amount and reads the cell afterwards, so
the answer (7) and the new state (12) are two rows in the order the family
fixes. `ERefs.tryTake` is the contrasting half: its two tuple components have
different types, so there the compiler does pin the order and no golden is
carrying the claim alone. -/

/-- The attack as a handler: `modify` answers the value after the write. Every
other operation is `refsLive`, so the mutation is exactly one arm. -/
def refsModifyAnswersNew : Refs.Service (StateT RefStore Id) := fun name =>
  match name with
  | .modify => fun (handle, amount) => do
      let store ← get
      let after := refPeek store handle + amount
      set (refPoke store handle after)
      pure after
  | other => refsLive other

def attackLog {α : Type} [Effects.Trace.ToVal α] (program : Program Refs.Sig α) :
    Effect4.Trace.Log :=
  let result : (α × Effect4.Trace.Log) × RefStore :=
    ((interpret (Refs.traced refsModifyAnswersNew).toHandler program).run []).run []
  result.1.2 ++ [.done (.success (Effects.Trace.ToVal.toVal result.1.1))]

-- The committed golden rejects the attack, at the answer row and at the outcome.
#guard (attackLog (refModifyOld 7) == refGoldenLog (refModifyOld 7)) = false

#guard attackLog (refModifyOld 7) =
  [ .op "make" (.nat 7), .answer "make" (.nat 0)
  , .op "modify" (.pair (.nat 0) (.nat 5)), .answer "modify" (.nat 12)
  , .op "get" (.nat 0), .answer "get" (.nat 12)
  , .done (.success (.nat 12)) ]

-- It is rejected under every registered mask, including the coarsest.
#guard Effect4.Trace.maskTable.all (fun mask =>
  Effect4.Trace.agree mask.2 (attackLog (refModifyOld 7)) (refGoldenLog (refModifyOld 7))) = false

/-- The golden that would not have caught it: the same program with a zero
amount. The answer and the new state coincide, so the attacked and repaired
handlers are indistinguishable — every row, every mask. -/
def modifyZero : Program Refs.Sig Nat :=
  Refs.make 7 >>= fun handle =>
    Refs.modify handle 0 >>= fun before =>
      Refs.get handle >>= fun _ => pure before

#guard attackLog modifyZero = refGoldenLog modifyZero

#guard Effect4.Trace.maskTable.all (fun mask =>
  Effect4.Trace.agree mask.2 (attackLog modifyZero) (refGoldenLog modifyZero))

-- What separates them is a row carrying the old value beside the new one, which
-- only a non-zero amount produces.
#guard refGoldenLog modifyZero =
  [ .op "make" (.nat 7), .answer "make" (.nat 0)
  , .op "modify" (.pair (.nat 0) (.nat 0)), .answer "modify" (.nat 7)
  , .op "get" (.nat 0), .answer "get" (.nat 7)
  , .done (.success (.nat 7)) ]

/-! ### `getAndSet` has the same shape and is separated the same way -/

def refsGetAndSetAnswersNew : Refs.Service (StateT RefStore Id) := fun name =>
  match name with
  | .getAndSet => fun (handle, value) => do
      let store ← get
      set (refPoke store handle value)
      pure value
  | other => refsLive other

def getAndSetAttackLog {α : Type} [Effects.Trace.ToVal α] (program : Program Refs.Sig α) :
    Effect4.Trace.Log :=
  let result : (α × Effect4.Trace.Log) × RefStore :=
    ((interpret (Refs.traced refsGetAndSetAnswersNew).toHandler program).run []).run []
  result.1.2 ++ [.done (.success (Effects.Trace.ToVal.toVal result.1.1))]

#guard (getAndSetAttackLog (refGetAndSetOld 7) == refGoldenLog (refGetAndSetOld 7)) = false

/-! ### The contrasting half: differently-typed components are pinned

`tryTake` answers `Except String Nat` while its new state is a `Nat`, so the
same swap is not even expressible: there is no tuple order to get wrong. The
`takeUnderflow` golden carries a claim about the *values*, not about which
component is which. -/

#guard (ERefs.rows.row? "tryTake").map (·.tsAnswer) = some "Result.Result<number, string>"

#guard (Refs.rows.row? "modify").map (·.tsAnswer) = some "number"

-- And the refusal leaves the cell alone: the read after it answers what the
-- successful take left, which is the other thing that golden is for.
#guard (erefGoldenLog (refTakeUnderflow 7)).filterMap
    (fun event => match event with | .answer "get" value => some value | _ => none)
  = [.nat 5]

end Effect4Test.Counterexamples.Runtime.Refs
