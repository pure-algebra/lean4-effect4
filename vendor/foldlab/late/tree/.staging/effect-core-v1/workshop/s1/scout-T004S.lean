import Cas.Lang.Ops
import Cas.Lang.Roots
import Cas.Lang.Worded
import Cas.Schema.Described

/-!
# `EC1-T004S` scout probe — the answer bridge is a well-formedness field, not a theorem

Row under scout (`../../PROOF-DAG.md:194`):

> `EC1-T004S` PENDING THEOREM
> `alphabet_answer_bridge : (op : a.toSig.Op) -> Value (lookup a op).answerTy ≃ a.toSig.Ans op`

Stage: `lean-formalization-strategy` **Pass B** (declaration validation; the
row proposes a public declaration and the question is whether it can be
elaborated and frozen). Written 2026-08-31, Lean `leanprover/lean4:v4.33.1`,
against `library/cas` at the working tree.

Outside every lake target, exactly like `../exhibits.lean` and
`../counterexamples/Nondeterminism.lean`. Adds nothing to `Cas`, moves no
byte, promotes no name.

Run it from `library/cas`:

```
lake env lean ../../.staging/effect-core-v1/workshop/s1/scout-T004S.lean
```

## What this file settles

`ValueTy`, `Value`, `Alphabet`, `OpDesc` and `lookup` do not exist — every
`formal/effect-core-v1/EffectCore/Foundation/*.lean` is an empty stub. So the
row cannot be elaborated as written. What CAN be settled today is what the
statement will run into once those carriers land, and that is decided by the
shipped signatures (`Cas/Lang/Ops.lean`, `Roots.lean`, `Worded.lean`) and the
shipped schema universe (`Cas/Schema/El.lean`, `Described/Instances.lean`),
both of which are frozen library facts.

Five findings, each a theorem below:

1. §1 `Ans` factors through the operation HEADER for every shipped signature.
   This is the fact that makes a header-indexed `answerTy` well-typed at all.
2. §2 `CasSig.Op` is not finitely enumerable — `Nat` injects into it. So
   "a finite canonical enumeration of that signature's `Sig.Op`"
   (`ALGEBRA.md` §2.2) is false for the shipped `CasSig`; the enumeration is
   of headers.
3. §3 the bridge for `put` is CONSTRUCTIBLE but NOT CANONICAL: 256 distinct
   codes denote `Addr32` equally well, so an `≃`-shaped row cannot pin
   `answerTy`.
4. §4 the bridge for `fail` FORCES an empty code: no inhabited code can carry
   `CasE.Ans (.fail r) = Empty`. The only WF codes that denote `Empty` are the
   estate's declared "no carrier yet" arms.
5. §5 the row is FALSE for a general alphabet: an author may write a wrong
   `answerTy` and nothing refutes it. The row is an `AlphabetWF` clause.

## Axiom receipt

Every theorem carries a `#print axioms` line at the foot. Fourteen are
`[propext]` or axiom-free. Three carry `[propext, Classical.choice,
Quot.sound]`, and the reason is a LIBRARY fact, not a modelling choice here:
`Cas.Schema.Ast.WF` is a mutual definition compiled by well-founded recursion,
so any term that unfolds it inherits `WellFounded.fix`'s axioms. Confirmed
directly — `theorem susp_wf : (Ast.susp .null).WF := trivial` alone reports
`[propext, Classical.choice, Quot.sound]`. The three affected results are the
ones whose statements mention a `Described` value, whose `wf` field is an
`Ast.WF` proof. `two_codes_one_answer_shape` restates the §3 finding without
that field and reports `[propext]`, so the finding does not rest on choice.
-/

set_option warn.classDefReducibility false

namespace ScoutT004S

open Cas.Lang
open Cas.Schema
open Cas (Addr32 Node Word)

/-! ## §1 — answer types factor through the operation header

`Sig.Ans : Op → Type` may in general depend on the operation's PAYLOAD. If it
did, no header-indexed `answerTy : OpId → ValueTy` table could type-check
against it, and `EC1-T004S` would be unstatable before it was unprovable.

Every shipped signature is payload-independent. Each of these is `rfl`; that
is the point — the fact is definitional and free, and it is a premise the
restated row should carry explicitly for signatures that are not shipped. -/

theorem put_ans_ignores_payload (n m : Node) :
    CasE.Ans (.put n) = CasE.Ans (.put m) := rfl

theorem load_ans_ignores_payload (a b : Addr32) :
    CasE.Ans (.load a) = CasE.Ans (.load b) := rfl

theorem fail_ans_ignores_payload (r s : String) :
    CasE.Ans (.fail r) = CasE.Ans (.fail s) := rfl

theorem publish_ans_ignores_payload (a b : Addr32) :
    RootE.Ans (.publish a) = RootE.Ans (.publish b) := rfl

theorem since_ans_ignores_payload (m n : Nat) :
    WordE.Ans (.since m) = WordE.Ans (.since n) := rfl

theorem infer_ans_ignores_payload (p q : String) :
    LlmE.Ans (.infer p) = LlmE.Ans (.infer q) := rfl

/-- The seven answer types the alphabet must bridge, spelled out. Each is
`rfl`; the value of the list is the inventory, not the proof. -/
theorem shipped_answer_inventory :
    CasE.Ans (.put ⟨0, 0, [], []⟩) = Addr32
    ∧ CasE.Ans (.load ⟨List.replicate 32 0, by simp⟩) = Node
    ∧ CasE.Ans (.fail "r") = Empty
    ∧ RootE.Ans (.publish ⟨List.replicate 32 0, by simp⟩) = Unit
    ∧ RootE.Ans .listRoots = List Addr32
    ∧ WordE.Ans (.since 0) = Word
    ∧ LlmE.Ans (.infer "p") = String :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-! ## §2 — `CasSig.Op` is infinite, so the enumeration is of headers

`ALGEBRA.md` §2.2 describes the alphabet as carrying "a finite canonical
enumeration of that signature's `Sig.Op`". `CasSig.Op` is `CasE`, and `CasE`
is payload-indexed by `Node`, `Addr32` and `String`. `Nat` injects into it. -/

/-- A `Nat`-indexed family of pairwise distinct store operations. -/
def opOfNat (n : Nat) : CasSig.Op := CasE.put ⟨0, 0, List.replicate n 0, []⟩

theorem opOfNat_injective {m n : Nat} (h : opOfNat m = opOfNat n) : m = n := by
  injection h with hnode
  injection hnode with _ _ hpayload _
  have hlen := congrArg List.length hpayload
  simpa using hlen

/-- Two of them, concretely distinct — the injectivity above is not vacuous. -/
theorem opOfNat_zero_ne_one : opOfNat 0 ≠ opOfNat 1 := by
  intro h; exact absurd (opOfNat_injective h) (by decide)

/-! ## §3 — the `put` bridge exists but is not canonical

The estate's own spelling of "type `α` is the denotation of a code" is
`Cas.Schema.Described` (`Cas/Schema/Described/Core.lean:16`): a bundled
`toEl`/`ofEl` pair with BOTH round trips. That is the `≃` the row wants, and
it already exists — no new equivalence type is needed.

`Addr32` has no `Described` instance (the complete instance set is `Unit`,
`Bool`, `SafeInt`, `String`, `StoreRef tag`, `List α` —
`Cas/Schema/Described/Instances.lean`), but one is CONSTRUCTIBLE, because
`El (.ref t) = StoreRef t` is a one-field wrapper around `Addr32`.

The problem is that it is constructible in 256 ways. -/

/-- A bridge witnessing `Value (.ref t) ≃ Addr32`, for every tag. -/
def describedAddr32 (t : UInt8) : Described Addr32 where
  code := .ref t
  wf := trivial
  toEl := fun a => ⟨a⟩
  ofEl := fun r => r.addr
  ofEl_toEl := fun _ => rfl
  toEl_ofEl := fun _ => rfl

/-- **The non-determination.** Two bridges for the SAME answer type carry two
DIFFERENT codes. An `≃`-shaped row therefore cannot pin `answerTy`: it is
satisfied by either choice, so it is not the functionality obligation the
packet needs at this node. The tag is semantic (the kind expected at the
target) and `Sig` does not carry it. -/
theorem answerTy_not_determined_by_the_bridge :
    (describedAddr32 0).code ≠ (describedAddr32 1).code := by
  intro h
  injection h with htag
  exact absurd htag (by decide)

/-- The same non-determination stated WITHOUT touching `Ast.WF`, so the
receipt is `[propext]` alone: two distinct codes, whose denotations are the
same one-field wrapper around `Addr32` at two different tags. -/
theorem two_codes_one_answer_shape :
    (Ast.ref 0 : Ast) ≠ Ast.ref 1
    ∧ El (Ast.ref 0) = StoreRef 0
    ∧ El (Ast.ref 1) = StoreRef 1 := by
  refine ⟨?_, rfl, rfl⟩
  intro h
  injection h with htag
  exact absurd htag (by decide)

/-- Both bridges are real: each round-trips in both directions. The
non-determination is between two CORRECT bridges, not a correct and a broken
one. -/
theorem describedAddr32_roundtrips (t : UInt8) (a : Addr32) (r : StoreRef t) :
    (describedAddr32 t).ofEl ((describedAddr32 t).toEl a) = a
    ∧ (describedAddr32 t).toEl ((describedAddr32 t).ofEl r) = r :=
  ⟨rfl, rfl⟩

/-! ## §4 — the `fail` bridge forces an empty code

`CasE.Ans (.fail r)` is `Empty` — `Cas/Lang/Ops.lean:29` states the reason:
"a refused program has no continuation, by type". So the alphabet's
`answerTy` for `fail` must be a code that denotes NOTHING.

There is no way around it: any inhabited code kills the forward half of the
bridge outright. -/

theorem fail_answer_is_empty (r : String) : CasE.Ans (.fail r) = Empty := rfl

/-- **No inhabited code can carry `fail`'s answer.** One inhabitant of the
code's denotation is enough to refute the forward map — no round trips
required, no `Classical.choice`. -/
theorem inhabited_code_cannot_bridge_fail
    {a : Ast} (x : El a) (r : String) :
    (El a → CasE.Ans (CasE.fail r)) → False :=
  fun f => (f x).elim

/-- Concretely, at the four inhabited primitive codes. -/
theorem primitives_cannot_bridge_fail (r : String) :
    ((El .null → CasE.Ans (CasE.fail r)) → False)
    ∧ ((El .bool → CasE.Ans (CasE.fail r)) → False)
    ∧ ((El .str → CasE.Ans (CasE.fail r)) → False)
    ∧ ((El (.ref 0) → CasE.Ans (CasE.fail r)) → False)
    ∧ ((El (.arr .bool) → CasE.Ans (CasE.fail r)) → False) :=
  ⟨inhabited_code_cannot_bridge_fail (a := .null) () r,
   inhabited_code_cannot_bridge_fail (a := .bool) true r,
   inhabited_code_cannot_bridge_fail (a := .str) "" r,
   inhabited_code_cannot_bridge_fail (a := .ref 0)
     (⟨⟨List.replicate 32 0, by simp⟩⟩ : StoreRef 0) r,
   inhabited_code_cannot_bridge_fail (a := .arr .bool) ([] : List Bool) r⟩

/-- An empty code that is nonetheless WELL-FORMED does exist, so the bridge is
not impossible — but it lands on `.susp`, one of the arms `Cas/Schema/El.lean`
declares to denote no Lean values YET. Reading a suspension code as "this
operation has no continuation" is a category error the packet should refuse
explicitly rather than discover in an emitter. -/
theorem an_empty_wf_code_exists :
    (Ast.susp .null).WF ∧ El (Ast.susp .null) = Empty :=
  ⟨trivial, rfl⟩

/-- And a bridge really does exist at that code — which is exactly why the
`≃` form is not enough on its own to refuse the category error. -/
def describedFailAnswer (r : String) : Described (CasE.Ans (CasE.fail r)) where
  code := .susp .null
  wf := trivial
  toEl := fun e => e.elim
  ofEl := fun e => e.elim
  ofEl_toEl := fun e => e.elim
  toEl_ofEl := fun e => e.elim

/-! ## §5 — the row is false for a general alphabet

Strip the packet vocabulary to its skeleton: an alphabet is a signature plus a
per-header `answerTy` table. Nothing in that data forces the table to be
right. Here is a table that is wrong, and the refutation. -/

/-- A minimal stand-in for the proposed `Alphabet`: the shipped signature,
plus the metadata table the packet adds. `sig` is a FIELD, matching
`ALGEBRA.md` §2.2 — "`Alphabet.toSig` returns this existing semantic
signature". -/
structure ToyAlphabet where
  sig : Sig
  answerTy : sig.Op → Ast

/-- The bridge the row asks for, spelled in the estate's own vocabulary
(`Described`) instead of an unminted `≃`. -/
def AnswerBridge (a : ToyAlphabet) : Type :=
  (op : a.sig.Op) → Described (a.sig.Ans op)

/-- A wrong table: it claims `fail` answers a Boolean. Nothing in
`ToyAlphabet` refuses it. -/
def badAlphabet : ToyAlphabet where
  sig := CasSig
  answerTy
    | .put _ => .ref 0
    | .load _ => .str
    | .fail _ => .bool

/-- **The refutation.** For `badAlphabet` there is no forward map at the
`fail` operation, hence no bridge of any shape. So

```text
∀ (a : Alphabet) (op : a.toSig.Op), Value (lookup a op).answerTy ≃ a.toSig.Ans op
```

is FALSE as a universally quantified theorem. It is a well-formedness clause
on `Alphabet` — either a field of `OpDesc` or a premise `AlphabetWF a`. -/
theorem badAlphabet_has_no_bridge :
    (El (badAlphabet.answerTy (CasE.fail "r")) →
      badAlphabet.sig.Ans (CasE.fail "r")) → False :=
  fun f => (f true).elim

/-- The same statement in the form the row is written in: there is an alphabet
and an operation for which the claimed equivalence has no forward half. -/
theorem answer_bridge_is_not_a_theorem :
    ∃ (a : ToyAlphabet) (op : a.sig.Op),
      (El (a.answerTy op) → a.sig.Ans op) → False :=
  ⟨badAlphabet, CasE.fail "r", badAlphabet_has_no_bridge⟩

/-! ## §6 — the shape that IS a theorem

Once the bridge is DATA rather than a proposition, there is a real obligation
left over, and it is the one the packet actually wants: that the data can be
supplied for the shipped signature. Here is that obligation discharged for the
three shipped arms whose answer types the current schema universe can carry
exactly — and note which arms are missing, because that is the finding. -/

/-- `publish` answers `Unit`; `Described Unit` is shipped. -/
def describedPublishAnswer (a : Addr32) : Described (RootE.Ans (.publish a)) :=
  inferInstanceAs (Described Unit)

/-- `infer` answers `String`; `Described String` is shipped. -/
def describedInferAnswer (p : String) : Described (LlmE.Ans (.infer p)) :=
  inferInstanceAs (Described String)

/-- `put` answers `Addr32`, which needs the constructed bridge of §3 and its
arbitrary tag. -/
def describedPutAnswer (n : Node) (t : UInt8) : Described (CasE.Ans (.put n)) :=
  describedAddr32 t

/-- `listRoots` answers `List Addr32`, which inherits the same arbitrary tag
through the shipped `List` instance. -/
def describedListRootsAnswer (t : UInt8) : Described (RootE.Ans .listRoots) :=
  @instDescribedList _ (describedAddr32 t)

/-- **What is NOT here, and why.** `load` answers `Node` and `since` answers
`Word = List Binding`, and `Binding` contains a `Node`. `Node` carries two
`UInt8` fields and a `payload : Bytes = List UInt8`. The schema universe has
no `UInt8` code — `El .int` is `SafeInt`, a subtype of `Int`, not a byte — and
no bytes code. The complete `Described` instance set is six instances and
contains neither. So `Described Node` cannot be constructed today.

This paragraph is an INVENTORY finding, verified by reading
`Cas/Schema/El.lean:178-207` and the whole of
`Cas/Schema/Described/Instances.lean` (73 lines, six instances). It is NOT a
Lean theorem: this file does not prove that no `Ast` denotes `Node`, and no
such non-existence proof was attempted. What IS proved below is the weaker,
checkable half — that the obvious candidate fails. -/
theorem int_code_is_not_a_byte : El .int = SafeInt := rfl

end ScoutT004S

#print axioms ScoutT004S.put_ans_ignores_payload
#print axioms ScoutT004S.load_ans_ignores_payload
#print axioms ScoutT004S.fail_ans_ignores_payload
#print axioms ScoutT004S.publish_ans_ignores_payload
#print axioms ScoutT004S.since_ans_ignores_payload
#print axioms ScoutT004S.infer_ans_ignores_payload
#print axioms ScoutT004S.shipped_answer_inventory
#print axioms ScoutT004S.opOfNat_injective
#print axioms ScoutT004S.opOfNat_zero_ne_one
#print axioms ScoutT004S.answerTy_not_determined_by_the_bridge
#print axioms ScoutT004S.two_codes_one_answer_shape
#print axioms ScoutT004S.describedAddr32_roundtrips
#print axioms ScoutT004S.fail_answer_is_empty
#print axioms ScoutT004S.inhabited_code_cannot_bridge_fail
#print axioms ScoutT004S.primitives_cannot_bridge_fail
#print axioms ScoutT004S.an_empty_wf_code_exists
#print axioms ScoutT004S.badAlphabet_has_no_bridge
#print axioms ScoutT004S.answer_bridge_is_not_a_theorem
#print axioms ScoutT004S.int_code_is_not_a_byte
