import Cas.Lang.Ops
import Cas.Lang.Roots
import Cas.Lang.Worded
import Cas.Schema.Described

/-!
# `EC1-T004S` — the answer bridge is a well-formedness FIELD, not a theorem

Row under implementation (`.staging/effect-core-v1/PROOF-DAG.md:194`):

> `EC1-T004S` PENDING THEOREM
> `alphabet_answer_bridge : (op : a.toSig.Op) -> Value (lookup a op).answerTy ≃ a.toSig.Ans op`
> Depends on `T004`; existing `Sig` answer indexing.

**Outcome: REFUTED.** As a universally quantified theorem over alphabets the
row is FALSE, and it is false twice over — once at the degenerate `fail` arm
and once at an ordinary inhabited arm with a well-formed code, so the failure
is not an artifact of `Empty`. §3 shows every repair-by-premise collapses into
the tautology family `PROOF-DAG.md:207` has already deleted twice. §4 proves
the nearest true statements: the header factorization that makes a
header-indexed `answerTy` table well-typed at all, the constructibility
obligation discharged on a named admitted fragment of the shipped signatures,
and the non-determination result showing an `≃`-shaped row cannot pin
`answerTy` even where it holds.

Skill stage: `lean-model-invariants` (the row is about representation — which
facts live in the type, which in a validator, and which are erased). The
inventory it asks for is in §1: `answerTy`-denotes-`Sig.Ans` is a
REPRESENTATION invariant with a global lifetime, undecidable as stated (it
quantifies over types), and therefore it must be carried as a WITNESS on the
checked carrier rather than validated after the fact. That is the whole
finding, and §2/§3 are its proof.

Written 2026-08-31, Lean `leanprover/lean4:v4.33.1`, against `library/cas` at
the working tree. Outside every lake target, exactly like `../exhibits.lean`
and `../counterexamples/Nondeterminism.lean`. Adds nothing to `Cas`, moves no
byte, promotes no name.

Run it from `library/cas`:

```
lake env lean ../../.staging/effect-core-v1/workshop/s1/T004S.lean
```

## Reuse, never mint

The row's `≃` is spelled with `Cas.Schema.Described`
(`Cas/Schema/Described/Core.lean:16`), which is already `α ≃ El code` with
`Ast.WF` as a field and both round trips as laws. No second equivalence type is
minted. `library/cas` has no Mathlib (`lake-manifest.json` lists
`"packages": []`, toolchain `leanprover/lean4:v4.33.1`) and no TYPE
equivalence: the corpus's only `Equiv` is `Cas/Core/Canonicalize.lean:81`, a
relation on VALUES at one fixed type. The schematic signature's `≃` is
therefore not spellable as written, which is itself part of the finding. `Sig`, `CasSig`, `RootSig`, `WordSig`,
`LlmSig`, `El`, `Ast` and the six shipped `Described` instances are all reused
verbatim. Nothing here touches `Prog` — this is effect-free work on first-order
data, per `EFFECTS-BACKEND.md` R14a.

## Axiom receipt

Every theorem carries a `#print axioms` line at the foot. `Classical.choice`
appears exactly where a statement mentions a `Described` value, whose `wf`
field is an `Ast.WF` proof; `Ast.WF` is a mutual definition compiled by
well-founded recursion, so any term unfolding it inherits `WellFounded.fix`'s
axioms. This is a LIBRARY fact, not a modelling choice here: shipped
`Cas.Schema.Described.decode_encode` reports the same triple. Each such result
that has a choice-free restatement is given one.

No `sorry`, no `axiom`, no `native_decide`, no `#eval` carrying a claim.
-/

set_option warn.classDefReducibility false

namespace EC1T004S

open Cas.Lang
open Cas.Schema
open Cas (Addr32 Node Word Binding)

/-! ## §0 — the row's `≃`, in the estate's own vocabulary

`Cas.Schema.Described α` is a bundled `code : Ast`, a proof `code.WF`, and an
inverse pair `toEl`/`ofEl` with both round trips. That IS the equivalence
`EC1-T004S` asks for, and it already exists. Two consequences of the round
trips carry every refutation below. -/

/-- Local alias, so the prose and the Lean agree on what `≃` means here. It is
`Cas.Schema.Described` and nothing else. -/
abbrev Bridge (α : Type) := Cas.Schema.Described α

/-- The forward half of an equivalence is injective. This is the only content
of `Described` the refutations use. -/
theorem bridge_toEl_injective {α : Type} (d : Bridge α) {x y : α}
    (h : d.toEl x = d.toEl y) : x = y := by
  rw [← d.ofEl_toEl x, ← d.ofEl_toEl y, h]

/-- A bridge at a code that denotes a SUBSINGLETON forces the answer type to be
a subsingleton. -/
theorem bridge_at_subsingleton_code {α : Type} (d : Bridge α)
    (hs : ∀ x y : El d.code, x = y) (x y : α) : x = y :=
  bridge_toEl_injective d (hs _ _)

/-- `El .null` is `Unit`; structure eta makes its subsingleton law `rfl`. -/
theorem el_null_subsingleton (x y : El Ast.null) : x = y := rfl

/-! ## §1 — the carrier, and the representation question underneath the row

`ValueTy`, `Value`, `Alphabet`, `OpDesc` and `lookup` do not exist: every
`formal/effect-core-v1/EffectCore/Foundation/*.lean` is an empty stub, and
`PROOF-DAG.md` §17 conditions 1, 13 and 14 are all OPEN. So the row cannot be
elaborated as written, and what follows is a MINIMAL STAND-IN whose only job is
to decide the statement's shape.

The stand-in is deliberately MORE generous than the packet's proposal: it
indexes `answerTy` by the operation itself rather than by a header, so a
payload-dependent answer code is permitted. Refuting the most generous reading
refutes every narrower one. `sig` is a FIELD, matching `ALGEBRA.md:166` —
"`Alphabet.toSig` returns this existing semantic signature". -/

/-- A minimal stand-in for `EC1-D010 Alphabet`: an existing semantic signature
plus the per-operation answer-code table `EC1-A07 OpDesc` contributes. -/
structure ToyAlphabet where
  sig : Sig
  answerTy : sig.Op → Ast

/-- The row's claim at one operation, with the code PINNED. The pin is not
decoration: §4.4 proves an unpinned `≃` leaves `answerTy` free, so without it
the row says nothing about the table it is supposed to be about. -/
def AnswerBridge (a : ToyAlphabet) (op : a.sig.Op) : Type :=
  { d : Bridge (a.sig.Ans op) // d.code = a.answerTy op }

/-- `EC1-T004S` as the DAG writes it, with the alphabet universally quantified
as the schematic signature's free variable `a` requires. -/
def RowAsWritten : Prop :=
  ∀ (a : ToyAlphabet) (op : a.sig.Op), Nonempty (AnswerBridge a op)

/-! ## §2 — the refutation

Nothing in "signature plus metadata table" forces the table to be right. An
author may write a wrong `answerTy`, and the resulting alphabet is a perfectly
good inhabitant of the carrier. -/

/-- **Witness A — the degenerate arm.** A table claiming `fail` answers a
Boolean. `CasE.Ans (.fail r) = Empty` (`Cas/Lang/Ops.lean:29`: "a refused
program has no continuation, by type"). -/
def failAlphabet : ToyAlphabet where
  sig := CasSig
  answerTy
    | .put _ => .ref 0
    | .load _ => .str
    | .fail _ => .bool

theorem failAlphabet_answer_is_empty :
    failAlphabet.sig.Ans (CasE.fail "boom") = Empty := rfl

/-- No bridge exists: the backward map would produce an inhabitant of `Empty`
out of `true`. -/
theorem failAlphabet_has_no_bridge
    (b : AnswerBridge failAlphabet (CasE.fail "boom")) : False := by
  obtain ⟨d, hcode⟩ := b
  have hx : El d.code := by rw [hcode]; exact (true : Bool)
  exact (d.ofEl hx : Empty).elim

/-- A 32-byte address, so the inhabited-arm witness has two distinct values to
separate. -/
def addrZero : Addr32 := ⟨List.replicate 32 0, by simp⟩

/-- **Witness B — an ordinary inhabited arm, well-formed code.** A table
claiming `listRoots` answers `null`. `RootE.Ans .listRoots = List Addr32`
(`Cas/Lang/Roots.lean:34`), `Ast.null` is WF, and `El .null = Unit` is
inhabited — so nothing degenerate is in play. The row still fails. -/
def unitAlphabet : ToyAlphabet where
  sig := RootSig
  answerTy := fun _ => .null

theorem unitAlphabet_answer_is_a_list :
    unitAlphabet.sig.Ans RootE.listRoots = List Addr32 := rfl

theorem unitAlphabet_code_is_wf_and_inhabited :
    (unitAlphabet.answerTy RootE.listRoots).WF
    ∧ Nonempty (El (unitAlphabet.answerTy RootE.listRoots)) :=
  ⟨trivial, ⟨()⟩⟩

/-- No bridge exists: a one-element denotation cannot separate `[]` from
`[addrZero]`. -/
theorem unitAlphabet_has_no_bridge
    (b : AnswerBridge unitAlphabet RootE.listRoots) : False := by
  obtain ⟨d, hcode⟩ := b
  have hs : ∀ x y : El d.code, x = y := by
    rw [hcode]; exact el_null_subsingleton
  have h : ([] : List Addr32) = [addrZero] :=
    bridge_at_subsingleton_code d hs ([] : List Addr32) [addrZero]
  exact absurd h (by simp)

/-- **`EC1-T004S` IS FALSE.** -/
theorem answer_bridge_is_not_a_theorem : ¬ RowAsWritten := fun h =>
  (h unitAlphabet RootE.listRoots).elim unitAlphabet_has_no_bridge

/-- And it is false at two independent arms — so excluding `fail`'s `Empty`
answer, or excluding empty codes, does not rescue it. Witness B's answer type
is inhabited, its claimed code is inhabited, and its claimed code is `Ast.WF`. -/
theorem false_at_two_independent_arms :
    ¬ Nonempty (AnswerBridge failAlphabet (CasE.fail "boom"))
    ∧ ¬ Nonempty (AnswerBridge unitAlphabet RootE.listRoots) :=
  ⟨fun h => h.elim failAlphabet_has_no_bridge,
   fun h => h.elim unitAlphabet_has_no_bridge⟩

/-! ### §2.1 — the choice-free core of the refutation

Both refutations above report `Classical.choice`, and the reason is
bookkeeping rather than mathematics: they mention a `Bridge`, whose `wf` field
has type `Ast.WF code`, and `Ast.WF` is a mutual definition compiled by
well-founded recursion. Stripped to the two maps and one round trip — the whole
of what `≃` asserts — each witness is refuted with `[propext]` alone. -/

/-- Witness A's core: `El .bool` is inhabited and `CasE.Ans (.fail r)` is not,
so no map out of the code's denotation exists. `failAlphabet.answerTy` sends
`fail` to `.bool`, so this is that arm. -/
theorem no_map_at_the_fail_arm (r : String)
    (f : El (failAlphabet.answerTy (CasE.fail r)) → CasE.Ans (CasE.fail r)) :
    False :=
  (f (true : Bool)).elim

/-- Witness B's core: one round trip through a one-element denotation collapses
`[]` and `[addrZero]`. `unitAlphabet.answerTy` sends every operation to
`.null`, so this is that arm. -/
theorem no_round_trip_at_the_listRoots_arm
    (toEl : List Addr32 → El (unitAlphabet.answerTy RootE.listRoots))
    (ofEl : El (unitAlphabet.answerTy RootE.listRoots) → List Addr32)
    (h : ∀ x, ofEl (toEl x) = x) : False := by
  have heq : toEl [] = toEl [addrZero] :=
    el_null_subsingleton (toEl []) (toEl [addrZero])
  have hc : ([] : List Addr32) = [addrZero] :=
    calc ([] : List Addr32) = ofEl (toEl []) := (h []).symm
      _ = ofEl (toEl [addrZero]) := by rw [heq]
      _ = [addrZero] := h [addrZero]
  exact absurd hc (by simp)

/-! ## §3 — every repair-by-premise collapses

The obvious fix is to add a well-formedness premise. It does not work: the
premise IS the conclusion, which is the vacuity `PROOF-DAG.md:207` used to
delete `exists! v, evalPure e env = v` and the same-input function-equality
form. -/

/-- The only premise that discharges the row is the row. -/
def AlphabetWF (a : ToyAlphabet) : Prop :=
  ∀ op : a.sig.Op, Nonempty (AnswerBridge a op)

/-- **Repair (a) is the identity function.** The proof term is its own
hypothesis, applied. -/
theorem premise_repair_is_the_identity (a : ToyAlphabet) (h : AlphabetWF a)
    (op : a.sig.Op) : Nonempty (AnswerBridge a op) := h op

/-- The premise is not vacuous — it genuinely excludes the §2 witnesses. So the
content is real; it has simply moved out of the theorem and into the premise,
where it is a well-formedness clause and not a proof obligation. -/
theorem alphabetWF_is_not_vacuous : ¬ AlphabetWF unitAlphabet := fun h =>
  (h RootE.listRoots).elim unitAlphabet_has_no_bridge

/-- **Repair (b) — the one `ALGEBRA.md` §2.2 already specifies**: "`OpDesc op`
records metadata for the existing operation AND PROVES that `answerTy` denotes
`Sig.Ans op`". Carry the bridge as a field and the row is a projection, closed
by `rfl`. This is the recommended shape, and it is why the row should not be a
theorem row at all. -/
structure BridgedAlphabet where
  sig : Sig
  bridge : (op : sig.Op) → Bridge (sig.Ans op)

theorem field_repair_is_a_projection (a : BridgedAlphabet) (op : a.sig.Op) :
    ∃ d : Bridge (a.sig.Ans op), d.code = (a.bridge op).code :=
  ⟨a.bridge op, rfl⟩

/-- **Repair (c) — derive the answers from the code table.** Then the bridge is
the identity and the row is `rfl`. It is available, and it is refused for a
reason outside this file: the resulting signature is no longer the shipped one,
which `ALGEBRA.md:166` requires and `EC1-T004RW` depends on. Recorded so the
horn is on the record rather than rediscovered in an emitter. -/
def derivedSig (Header : Type) (code : Header → Ast) : Sig :=
  ⟨Header, fun h => El (code h)⟩

def derivedBridge {Header : Type} (code : Header → Ast) (h : Header)
    (wf : (code h).WF) : Bridge ((derivedSig Header code).Ans h) where
  code := code h
  wf := wf
  toEl := id
  ofEl := id
  ofEl_toEl := fun _ => rfl
  toEl_ofEl := fun _ => rfl

theorem derived_repair_is_rfl {Header : Type} (code : Header → Ast)
    (h : Header) (wf : (code h).WF) :
    (derivedBridge code h wf).code = code h := rfl

/-! ## §4 — the nearest true statements

The row is not salvageable as written. What IS provable, and what the packet
needs in its place, is four things: the factorization that makes a
header-indexed answer table well-typed at all (§4.1–4.2), the exclusion that
`fail`'s `Empty` answer forces (§4.3), the non-determination that stops an
`≃`-shaped row from pinning `answerTy` even where it holds (§4.4), and the
constructibility obligation discharged on a NAMED fragment of the shipped
signatures (§4.5).

### §4.1 — the enumeration must be of headers, because `Sig.Op` is infinite

`ALGEBRA.md` §2.2 describes the alphabet as carrying "a finite canonical
enumeration of that signature's `Sig.Op`". For the shipped `CasSig` that is
false: `CasSig.Op` is `CasE`, payload-indexed by `Node`, and `Nat` injects into
it. The finite enumeration is of HEADERS, and the header indirection is forced
rather than convenient. -/

/-- A `Nat`-indexed family of pairwise distinct store operations. -/
def opOfNat (n : Nat) : CasE := .put ⟨0, 0, List.replicate n 0, []⟩

theorem opOfNat_injective {m n : Nat} (h : opOfNat m = opOfNat n) : m = n := by
  injection h with hnode
  injection hnode with _ _ hpayload _
  have hlen := congrArg List.length hpayload
  simpa using hlen

/-- The header enumeration, in the estate's shipped closed-registry shape
(`Cas/Schema/Declarations.lean:202,276`): a closed inductive with a complete
`all` list and a duplicate-free guard. -/
inductive CasHeader where
  | put | load | fail
  deriving DecidableEq, Repr

def CasHeader.all : List CasHeader := [.put, .load, .fail]

theorem CasHeader.all_complete (h : CasHeader) : h ∈ CasHeader.all := by
  cases h <;> simp [CasHeader.all]

theorem CasHeader.all_nodup : CasHeader.all.Nodup := by decide

def casHeader : CasE → CasHeader
  | .put _ => .put
  | .load _ => .load
  | .fail _ => .fail

def CasHeader.ans : CasHeader → Type
  | .put => Addr32
  | .load => Node
  | .fail => Empty

/-- **The forced shape.** The operation universe is infinite; the header
universe is finite and complete. Any `answerTy` table the alphabet can write
down is indexed by the second. -/
theorem enumeration_must_be_of_headers :
    (∀ h : CasHeader, h ∈ CasHeader.all)
    ∧ CasHeader.all.length = 3
    ∧ (∀ m n : Nat, opOfNat m = opOfNat n → m = n) :=
  ⟨CasHeader.all_complete, rfl, fun _ _ h => opOfNat_injective h⟩

/-! ### §4.2 — payload independence, the premise that makes the table well-typed

`Sig.Ans : Op → Type` may in general depend on an operation's PAYLOAD. If it
did, no header-indexed `answerTy` could type-check against it and `EC1-T004S`
would be unstatable before it was unprovable. Every shipped signature is
payload-independent; no `Sig` is, so the clause must be carried explicitly in
`AlphabetWF` rather than assumed. -/

/-- The answer assignment factors through a header. -/
def PayloadIndependent (S : Sig) {Header : Type} (hd : S.Op → Header)
    (ans : Header → Type) : Prop :=
  ∀ op : S.Op, S.Ans op = ans (hd op)

theorem casSig_ans_factors (op : CasE) : CasSig.Ans op = (casHeader op).ans := by
  cases op <;> rfl

inductive RootHeader where
  | publish | listRoots
  deriving DecidableEq, Repr

def rootHeader : RootE → RootHeader
  | .publish _ => .publish
  | .listRoots => .listRoots

def RootHeader.ans : RootHeader → Type
  | .publish => Unit
  | .listRoots => List Addr32

theorem rootSig_ans_factors (op : RootE) : RootSig.Ans op = (rootHeader op).ans := by
  cases op <;> rfl

inductive WordHeader where
  | since
  deriving DecidableEq, Repr

def wordHeader : WordE → WordHeader
  | .since _ => .since

def WordHeader.ans : WordHeader → Type
  | .since => Word

theorem wordSig_ans_factors (op : WordE) : WordSig.Ans op = (wordHeader op).ans := by
  cases op <;> rfl

inductive LlmHeader where
  | infer
  deriving DecidableEq, Repr

def llmHeader : LlmE → LlmHeader
  | .infer _ => .infer

def LlmHeader.ans : LlmHeader → Type
  | .infer => String

theorem llmSig_ans_factors (op : LlmE) : LlmSig.Ans op = (llmHeader op).ans := by
  cases op <;> rfl

/-- **All four shipped signatures factor.** -/
theorem shipped_signatures_are_payload_independent :
    PayloadIndependent CasSig casHeader CasHeader.ans
    ∧ PayloadIndependent RootSig rootHeader RootHeader.ans
    ∧ PayloadIndependent WordSig wordHeader WordHeader.ans
    ∧ PayloadIndependent LlmSig llmHeader LlmHeader.ans :=
  ⟨casSig_ans_factors, rootSig_ans_factors, wordSig_ans_factors, llmSig_ans_factors⟩

/-- ADVERSARY (scratch, promoted nowhere): a signature whose answer type
depends on the payload. -/
def payloadDependentSig : Sig := ⟨Bool, fun b => cond b Unit Empty⟩

/-- **Payload independence is not free.** It is a fact about the SHIPPED
signatures, so `AlphabetWF` must state it rather than inherit it. -/
theorem payload_independence_is_not_free :
    ¬ ∃ ans : Unit → Type,
        ∀ op : payloadDependentSig.Op, payloadDependentSig.Ans op = ans () := by
  rintro ⟨ans, h⟩
  have hUE : Unit = Empty := (h true).trans (h false).symm
  exact (cast hUE ()).elim

/-! ### §4.3 — `fail` forces a code outside the populated fragment

`CasE.Ans (.fail r) = Empty`. Any code whose denotation has an inhabitant kills
the bridge outright, in either direction. This generalizes the per-primitive
check to the whole first-order fragment of `Ast` by exhibiting an inhabitant
constructively. -/

/-- The codes this file exhibits an inhabitant of. Deliberately a `Type`, so
the witness is data rather than an existential. -/
inductive Populated : Ast → Type where
  | null : Populated .null
  | bool : Populated .bool
  | int : Populated .int
  | str : Populated .str
  | lit (v : LitVal) : Populated (.lit v)
  | arr (a : Ast) : Populated (.arr a)
  | ref (t : UInt8) : Populated (.ref t)
  | structNil : Populated (.struct [])

def Populated.witness : {a : Ast} → Populated a → El a
  | _, .null => ()
  | _, .bool => true
  | _, .int => ⟨0, by simp⟩
  | _, .str => ""
  | _, .lit _ => ()
  | _, .arr _ => []
  | _, .ref _ => ⟨addrZero⟩
  | _, .structNil => ()

/-- **No populated code can carry `fail`'s answer.** No round trips are
required and no `Classical.choice` is reached: one inhabitant refutes the
forward map. -/
theorem populated_cannot_bridge_fail {a : Ast} (p : Populated a) (r : String)
    (f : El a → CasE.Ans (CasE.fail r)) : False :=
  (f p.witness).elim

/-- The remaining WF codes that denote `Empty` are exactly `El`'s declared
"no carrier yet" arms. One exists, so the bridge is not impossible — but
reading a suspension code as "this operation has no continuation" is a category
error, and `Ast.union_nil_not_wf`/`Ast.enum_nil_not_wf` already record that
`Never` is not an admitted code. -/
theorem an_empty_wf_code_exists :
    (Ast.susp .null).WF ∧ El (Ast.susp .null) = Empty :=
  ⟨trivial, rfl⟩

/-! ### §4.4 — the `≃` does not determine `answerTy`

`El` is not injective on the fragment the alphabet needs, so a bridge-existence
claim leaves the code free. Determination is a SEPARATE obligation, and the
estate already ships its shape as a surjectivity/injectivity pair
(`Cas/Schema/Declarations.lean:288,297`). `EC1-T004S` has no analogue of it. -/

/-- A bridge witnessing `El (.ref t) ≃ Addr32`, for every tag. `Addr32` has no
shipped `Described` instance; this constructs one, and the tag is free. -/
def describedAddr32 (t : UInt8) : Bridge Addr32 where
  code := .ref t
  wf := trivial
  toEl := fun a => ⟨a⟩
  ofEl := fun r => r.addr
  ofEl_toEl := fun _ => rfl
  toEl_ofEl := fun _ => rfl

/-- Both bridges are genuine: each round-trips in both directions. The
non-determination below is between two CORRECT bridges, not a correct and a
broken one. -/
theorem describedAddr32_roundtrips (t : UInt8) (a : Addr32) (r : StoreRef t) :
    (describedAddr32 t).ofEl ((describedAddr32 t).toEl a) = a
    ∧ (describedAddr32 t).toEl ((describedAddr32 t).ofEl r) = r :=
  ⟨rfl, rfl⟩

/-- **The non-determination.** `∃ d : Bridge Addr32, d.code = .ref t` holds at
EVERY tag `t`, and those codes are pairwise distinct. An `≃`-shaped row is
satisfied by any of them, so it does not pin `answerTy`. The tag is semantic —
the kind expected at the target — and `Sig` does not carry it.

Note this also corrects a statement the scouting pass proposed: a determination
theorem cannot compare `d.toEl x` with `e.toEl x` for bridges at different
codes, because those live in different types. The obligation has to be phrased
on the code table, as here. -/
theorem answerTy_is_not_determined_by_the_bridge {t t' : UInt8} (h : t ≠ t') :
    (∃ d : Bridge Addr32, d.code = .ref t)
    ∧ (∃ d : Bridge Addr32, d.code = .ref t')
    ∧ (Ast.ref t ≠ Ast.ref t') :=
  ⟨⟨describedAddr32 t, rfl⟩, ⟨describedAddr32 t', rfl⟩, by
    intro he
    injection he with ht
    exact h ht⟩

/-- The same finding without touching `Ast.WF`, so the receipt is choice-free:
two distinct codes whose denotations are the same one-field wrapper around
`Addr32` at two different tags. -/
theorem two_codes_one_answer_shape :
    (Ast.ref 0 : Ast) ≠ Ast.ref 1
    ∧ El (Ast.ref 0) = StoreRef 0
    ∧ El (Ast.ref 1) = StoreRef 1 := by
  refine ⟨?_, rfl, rfl⟩
  intro he
  injection he with ht
  exact absurd ht (by decide)

/-! ### §4.5 — where the row IS a theorem: the admitted fragment

Once the bridge is data rather than a proposition there is a real obligation
left: that it CAN be supplied. Here that obligation is discharged for the four
shipped arms the current schema universe carries exactly, and the alphabet
built from them satisfies the §3 well-formedness clause the general row could
not. This is the non-vacuity control for everything above. -/

inductive AdmittedHeader where
  | put | listRoots | publish | infer
  deriving DecidableEq, Repr

def AdmittedHeader.all : List AdmittedHeader := [.put, .listRoots, .publish, .infer]

theorem AdmittedHeader.all_complete (h : AdmittedHeader) : h ∈ AdmittedHeader.all := by
  cases h <;> simp [AdmittedHeader.all]

def AdmittedHeader.ans : AdmittedHeader → Type
  | .put => Addr32
  | .listRoots => List Addr32
  | .publish => Unit
  | .infer => String

def AdmittedHeader.answerTy (t : UInt8) : AdmittedHeader → Ast
  | .put => .ref t
  | .listRoots => .arr (.ref t)
  | .publish => .null
  | .infer => .str

/-- The bridge, constructed per admitted header, with its code pinned to the
table. Two arms are shipped instances (`Unit`, `String`); two are built from
the constructed `Addr32` bridge and the shipped `List` instance. -/
def admittedBridge (t : UInt8) :
    (h : AdmittedHeader) → { d : Bridge h.ans // d.code = AdmittedHeader.answerTy t h }
  | .put => ⟨describedAddr32 t, rfl⟩
  | .listRoots => ⟨@instDescribedList _ (describedAddr32 t), rfl⟩
  | .publish => ⟨inferInstanceAs (Described Unit), rfl⟩
  | .infer => ⟨inferInstanceAs (Described String), rfl⟩

/-- **`EC1-T004S`, restated where it is true.** For every admitted header the
bridge exists and its code is exactly the table's. -/
theorem admitted_answer_bridge (t : UInt8) (h : AdmittedHeader) :
    ∃ d : Bridge h.ans, d.code = AdmittedHeader.answerTy t h :=
  ⟨(admittedBridge t h).1, (admittedBridge t h).2⟩

/-- The admitted headers really are answering the SHIPPED signatures'
operations; nothing has been renamed into agreement. -/
theorem admitted_headers_are_shipped_answers (n : Node) (a : Addr32) (p : String) :
    CasSig.Ans (.put n) = AdmittedHeader.put.ans
    ∧ RootSig.Ans .listRoots = AdmittedHeader.listRoots.ans
    ∧ RootSig.Ans (.publish a) = AdmittedHeader.publish.ans
    ∧ LlmSig.Ans (.infer p) = AdmittedHeader.infer.ans :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- The alphabet over the admitted fragment. -/
def admittedAlphabet (t : UInt8) : ToyAlphabet where
  sig := ⟨AdmittedHeader, AdmittedHeader.ans⟩
  answerTy := AdmittedHeader.answerTy t

/-- **NON-VACUITY CONTROL.** `AlphabetWF` is satisfiable: the §2 refutation is
about the quantifier, not about an unsatisfiable clause. -/
theorem admittedAlphabet_satisfies_the_row (t : UInt8) : AlphabetWF (admittedAlphabet t) :=
  fun op => ⟨admittedBridge t op⟩

/-- The shipped arms that are NOT in the admitted fragment, and their answer
types. `load` answers `Node`, whose `payload` is `Bytes = List UInt8`; `since`
answers `Word = List Binding`, and `Binding` carries a `Node`. The schema
universe has no byte code — `El .int` is a bounded `Int` subtype — and the six
shipped `Described` instances contain neither.

This is an INVENTORY finding, and the theorem below states only its checkable
half. This file does NOT prove that no `Ast` denotes `Node`; no such
non-existence proof was attempted. -/
theorem blocked_arms_answer_node_and_word (a : Addr32) (m : Nat) :
    CasSig.Ans (.load a) = Node
    ∧ WordSig.Ans (.since m) = Word
    ∧ (Word = List Binding) :=
  ⟨rfl, rfl, rfl⟩

theorem int_code_is_not_a_byte : El .int = SafeInt := rfl

/-! ### §4.6 — `EC1-T004` and `EC1-T004S` disagree about `lookup`'s codomain

`EC1-T004` fixes `lookup a op : Option OpDesc` (`exists! d, lookup a op =
some d`). `EC1-T004S` then writes `(lookup a op).answerTy`, projecting a field
off an `Option`, which does not elaborate: the `some` is never discharged. The
two rows must be re-spelled together.

The repair is the one `scout-T004` was independently forced into: refine the
operation universe by the `isSome` evidence, after which the projection is
definitional and `Sig`'s total `Ans : Op → Type` is honored without modifying
`Sig`. -/

structure OptAlphabet where
  Header : Type
  lookup : Header → Option Ast

/-- The refined operation universe: headers the table actually declares. -/
def OptAlphabet.Op (a : OptAlphabet) : Type :=
  { h : a.Header // (a.lookup h).isSome = true }

def OptAlphabet.answerTy (a : OptAlphabet) (op : a.Op) : Ast :=
  (a.lookup op.1).get op.2

/-- With the `some` discharged by the refinement, the projection the row wants
is definitional. -/
theorem lookup_projection_is_definitional (a : OptAlphabet) (op : a.Op) :
    a.answerTy op = (a.lookup op.1).get op.2 := rfl

/-- And the derived signature over that refinement answers exactly the table's
codes, by `rfl` — the shape `EC1-T004`'s restatement already needs. -/
theorem opt_derived_answer_is_definitional (a : OptAlphabet) (op : a.Op) :
    (derivedSig a.Op a.answerTy).Ans op = El ((a.lookup op.1).get op.2) := rfl

end EC1T004S

/-! ## Axiom receipts

`Classical.choice` and `Quot.sound` appear in exactly the results whose
statement mentions a `Bridge` (= `Cas.Schema.Described`), whose `wf` field has
type `Ast.WF code`; `Ast.WF` is a mutual definition compiled by well-founded
recursion, so any term unfolding it inherits `WellFounded.fix`'s axioms. This
is the ESTATE's ceiling, not a modelling choice here: shipped
`Cas.Schema.Described.decode_encode` reports the identical triple.

The load-bearing results all have a choice-free form:

- the refutation's core — `no_map_at_the_fail_arm`,
  `no_round_trip_at_the_listRoots_arm`, `populated_cannot_bridge_fail`, all
  `[propext]`;
- the non-determination — `two_codes_one_answer_shape`, `[propext]`;
- the header factorization and payload independence —
  `casSig_ans_factors`, `rootSig_ans_factors`, `wordSig_ans_factors`,
  `llmSig_ans_factors`, `shipped_signatures_are_payload_independent`,
  `payload_independence_is_not_free`, all axiom-free.

So no conclusion in this file rests on choice.

## Checks omitted, stated

- It is NOT proved that no `Ast` denotes `Node` or `Word`. §4.5's blocked-arm
  paragraph is an inventory finding read off `Cas/Schema/El.lean:178-207` and
  the complete `Described/Instances.lean`; the theorem beside it states only
  the checkable half. A non-existence proof over the whole code universe was
  not attempted.
- `Populated` covers the first-order arms this file exhibits an inhabitant of.
  It does NOT cover `.struct` with fields, or the discriminated `.union`, so
  §4.3 does not claim to enumerate every inhabited code.
- The `ToyAlphabet`/`OptAlphabet`/`BridgedAlphabet` carriers are stand-ins that
  settle statement SHAPE only. They are not proposed for `EC1-D010`/`EC1-D011`
  and they settle nothing about the real alphabet's representation, which
  freeze conditions 3 and 14 still own.
- `payloadDependentSig` is a scratch adversary, promoted nowhere.
- Nothing here bears on `EC1-T004X`'s `Sig.sum` reindexing, `EC1-T004RW`'s
  Root/Word import laws, or `EC1-T003E`'s `toAst?` fragment. `Ast.WF`
  decidability and the question of whether `ValueTy` should simply BE `Ast`
  were not probed.
- No host/TypeScript evidence was gathered, and no `lake build` was run: this
  file is outside every lake target and touches no library byte. -/

#print axioms EC1T004S.bridge_toEl_injective
#print axioms EC1T004S.bridge_at_subsingleton_code
#print axioms EC1T004S.el_null_subsingleton
#print axioms EC1T004S.failAlphabet_answer_is_empty
#print axioms EC1T004S.failAlphabet_has_no_bridge
#print axioms EC1T004S.unitAlphabet_answer_is_a_list
#print axioms EC1T004S.unitAlphabet_code_is_wf_and_inhabited
#print axioms EC1T004S.unitAlphabet_has_no_bridge
#print axioms EC1T004S.answer_bridge_is_not_a_theorem
#print axioms EC1T004S.false_at_two_independent_arms
#print axioms EC1T004S.no_map_at_the_fail_arm
#print axioms EC1T004S.no_round_trip_at_the_listRoots_arm
#print axioms EC1T004S.premise_repair_is_the_identity
#print axioms EC1T004S.alphabetWF_is_not_vacuous
#print axioms EC1T004S.field_repair_is_a_projection
#print axioms EC1T004S.derived_repair_is_rfl
#print axioms EC1T004S.opOfNat_injective
#print axioms EC1T004S.CasHeader.all_complete
#print axioms EC1T004S.CasHeader.all_nodup
#print axioms EC1T004S.enumeration_must_be_of_headers
#print axioms EC1T004S.casSig_ans_factors
#print axioms EC1T004S.rootSig_ans_factors
#print axioms EC1T004S.wordSig_ans_factors
#print axioms EC1T004S.llmSig_ans_factors
#print axioms EC1T004S.shipped_signatures_are_payload_independent
#print axioms EC1T004S.payload_independence_is_not_free
#print axioms EC1T004S.populated_cannot_bridge_fail
#print axioms EC1T004S.an_empty_wf_code_exists
#print axioms EC1T004S.describedAddr32_roundtrips
#print axioms EC1T004S.answerTy_is_not_determined_by_the_bridge
#print axioms EC1T004S.two_codes_one_answer_shape
#print axioms EC1T004S.AdmittedHeader.all_complete
#print axioms EC1T004S.admitted_answer_bridge
#print axioms EC1T004S.admitted_headers_are_shipped_answers
#print axioms EC1T004S.admittedAlphabet_satisfies_the_row
#print axioms EC1T004S.blocked_arms_answer_node_and_word
#print axioms EC1T004S.int_code_is_not_a_byte
#print axioms EC1T004S.lookup_projection_is_definitional
#print axioms EC1T004S.opt_derived_answer_is_definitional
