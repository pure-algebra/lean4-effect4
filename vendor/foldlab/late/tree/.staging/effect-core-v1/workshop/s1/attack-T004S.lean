import Cas.Lang.Ops
import Cas.Lang.Roots
import Cas.Lang.Worded
import Cas.Schema.Described

/-!
# Breaker attack on `EC1-T004S`

Adversarial companion to `T004S.lean`. Nothing here is proposed for the
library; every declaration is scratch. Run it from `library/cas`:

```
lake env lean ../../.staging/effect-core-v1/workshop/s1/attack-T004S.lean
```

`T004S.lean` is not a module in any lake target, so it cannot be imported.
§0 below RESTATES the definitions under attack verbatim, with the line of
`T004S.lean` each was copied from, so the attacks bite on the same objects.

No `sorry`, no `axiom`, no `native_decide`, no `#eval`. `#print axioms` on
every theorem, at the foot.
-/

set_option warn.classDefReducibility false

namespace AttackT004S

open Cas.Lang
open Cas.Schema
open Cas (Addr32 Node Word Binding)

/-! ## §0 — the objects under attack, copied verbatim from `T004S.lean` -/

/-- `T004S.lean:89`. -/
abbrev Bridge (α : Type) := Cas.Schema.Described α

/-- `T004S.lean:93-95`. -/
theorem bridge_toEl_injective {α : Type} (d : Bridge α) {x y : α}
    (h : d.toEl x = d.toEl y) : x = y := by
  rw [← d.ofEl_toEl x, ← d.ofEl_toEl y, h]

/-- `T004S.lean:99-101`. -/
theorem bridge_at_subsingleton_code {α : Type} (d : Bridge α)
    (hs : ∀ x y : El d.code, x = y) (x y : α) : x = y :=
  bridge_toEl_injective d (hs _ _)

/-- `T004S.lean:104`. -/
theorem el_null_subsingleton (x y : El Ast.null) : x = y := rfl

/-- `T004S.lean:122-124`. -/
structure ToyAlphabet where
  sig : Sig
  answerTy : sig.Op → Ast

/-- `T004S.lean:129-130`. -/
def AnswerBridge (a : ToyAlphabet) (op : a.sig.Op) : Type :=
  { d : Bridge (a.sig.Ans op) // d.code = a.answerTy op }

/-- `T004S.lean:134-135`. -/
def RowAsWritten : Prop :=
  ∀ (a : ToyAlphabet) (op : a.sig.Op), Nonempty (AnswerBridge a op)

/-- `T004S.lean:166`. -/
def addrZero : Addr32 := ⟨List.replicate 32 0, by simp⟩

/-- `T004S.lean:172-174`. -/
def unitAlphabet : ToyAlphabet where
  sig := RootSig
  answerTy := fun _ => .null

/-- `T004S.lean:186-193`. -/
theorem unitAlphabet_has_no_bridge
    (b : AnswerBridge unitAlphabet RootE.listRoots) : False := by
  obtain ⟨d, hcode⟩ := b
  have hs : ∀ x y : El d.code, x = y := by
    rw [hcode]; exact el_null_subsingleton
  have h : ([] : List Addr32) = [addrZero] :=
    bridge_at_subsingleton_code d hs ([] : List Addr32) [addrZero]
  exact absurd h (by simp)

/-- `T004S.lean:196-197`. -/
theorem answer_bridge_is_not_a_theorem : ¬ RowAsWritten := fun h =>
  (h unitAlphabet RootE.listRoots).elim unitAlphabet_has_no_bridge

/-- `T004S.lean:266-268`. -/
structure BridgedAlphabet where
  sig : Sig
  bridge : (op : sig.Op) → Bridge (sig.Ans op)

/-- `T004S.lean:270-272`, verbatim, statement AND proof. -/
theorem field_repair_is_a_projection (a : BridgedAlphabet) (op : a.sig.Op) :
    ∃ d : Bridge (a.sig.Ans op), d.code = (a.bridge op).code :=
  ⟨a.bridge op, rfl⟩

/-- `T004S.lean:314`. -/
def opOfNat (n : Nat) : CasE := .put ⟨0, 0, List.replicate n 0, []⟩

/-- `T004S.lean:487-493`. -/
def describedAddr32 (t : UInt8) : Bridge Addr32 where
  code := .ref t
  wf := trivial
  toEl := fun a => ⟨a⟩
  ofEl := fun r => r.addr
  ofEl_toEl := fun _ => rfl
  toEl_ofEl := fun _ => rfl

/-- `T004S.lean:541-543`. -/
inductive AdmittedHeader where
  | put | listRoots | publish | infer
  deriving DecidableEq, Repr

/-- `T004S.lean:550-554`. -/
def AdmittedHeader.ans : AdmittedHeader → Type
  | .put => Addr32
  | .listRoots => List Addr32
  | .publish => Unit
  | .infer => String

/-- `T004S.lean:556-560`. -/
def AdmittedHeader.answerTy (t : UInt8) : AdmittedHeader → Ast
  | .put => .ref t
  | .listRoots => .arr (.ref t)
  | .publish => .null
  | .infer => .str

/-- `T004S.lean:565-570`. -/
def admittedBridge (t : UInt8) :
    (h : AdmittedHeader) → { d : Bridge h.ans // d.code = AdmittedHeader.answerTy t h }
  | .put => ⟨describedAddr32 t, rfl⟩
  | .listRoots => ⟨@instDescribedList _ (describedAddr32 t), rfl⟩
  | .publish => ⟨inferInstanceAs (Described Unit), rfl⟩
  | .infer => ⟨inferInstanceAs (Described String), rfl⟩

/-- `T004S.lean:588-590`. -/
def admittedAlphabet (t : UInt8) : ToyAlphabet where
  sig := ⟨AdmittedHeader, AdmittedHeader.ans⟩
  answerTy := AdmittedHeader.answerTy t

/-- `T004S.lean:247-248`. -/
def AlphabetWF (a : ToyAlphabet) : Prop :=
  ∀ op : a.sig.Op, Nonempty (AnswerBridge a op)

/-- `T004S.lean:594-595`. -/
theorem admittedAlphabet_satisfies_the_row (t : UInt8) : AlphabetWF (admittedAlphabet t) :=
  fun op => ⟨admittedBridge t op⟩

/-! ## §A1 — the licensing lemma is invalid, and `T004S.lean` refutes it itself

`T004S.lean:114-117` licenses the transfer from the stand-in to the packet's
real carrier with:

> "The stand-in is deliberately MORE generous than the packet's proposal ...
> Refuting the most generous reading refutes every narrower one."

For a UNIVERSALLY quantified row that inference runs backwards. Enlarging the
domain STRENGTHENS `∀`, and refuting a strictly stronger statement leaves the
weaker one open. -/

/-- The valid direction: generosity implies narrowness, never the converse. -/
theorem generosity_runs_one_way (N : ToyAlphabet → Prop) (h : RowAsWritten) :
    ∀ a : ToyAlphabet, N a → ∀ op : a.sig.Op, Nonempty (AnswerBridge a op) :=
  fun a _ op => h a op

/-- A narrower class, built out of `T004S.lean`'s OWN non-vacuity control. -/
def IsAdmitted (a : ToyAlphabet) : Prop := ∃ t : UInt8, a = admittedAlphabet t

theorem admitted_class_is_inhabited : IsAdmitted (admittedAlphabet 0) := ⟨0, rfl⟩

theorem row_holds_on_the_narrower_class (a : ToyAlphabet) (h : IsAdmitted a) :
    ∀ op : a.sig.Op, Nonempty (AnswerBridge a op) := by
  obtain ⟨t, rfl⟩ := h
  exact admittedAlphabet_satisfies_the_row t

/-- **In the file's favour.** The specific narrowing `T004S.lean:114-117`
names — indexing `answerTy` by a header rather than by the operation — does
NOT rescue the row: witness B's table is constant, hence factors through any
header map, and it is still refuted. So the conclusion survives that narrowing;
it is the stated justification for the transfer, not the conclusion, that
fails. -/
theorem witness_B_survives_the_header_narrowing :
    (∀ op : RootSig.Op, unitAlphabet.answerTy op = (fun _ : Unit => Ast.null) ())
    ∧ ¬ Nonempty (AnswerBridge unitAlphabet RootE.listRoots) :=
  ⟨fun _ => rfl, fun h => h.elim unitAlphabet_has_no_bridge⟩

/-- **The licensing lemma is FALSE.** A narrower class on which the row HOLDS,
inhabited, sitting inside the generous class on which it fails. So
"refuting the most generous reading refutes every narrower one" is exhibited
false by the very objects `T004S.lean` §4.5 constructs. -/
theorem generosity_inference_is_invalid :
    (∃ a : ToyAlphabet, IsAdmitted a)
    ∧ (∀ a : ToyAlphabet, IsAdmitted a → ∀ op : a.sig.Op, Nonempty (AnswerBridge a op))
    ∧ ¬ RowAsWritten :=
  ⟨⟨admittedAlphabet 0, admitted_class_is_inhabited⟩,
   row_holds_on_the_narrower_class,
   answer_bridge_is_not_a_theorem⟩

/-! ## §A2 — on the carrier the packet actually specifies, the row is TRUE

`ALGEBRA.md:131-135` (§2.2) defines the Lean-side candidate for `EC1-A06
Alphabet` as a signature plus "a sorted dependent table of `EC1-A07 OpDesc`
records", where

> "`OpDesc op` records metadata for the existing operation AND PROVES THAT
> `answerTy` DENOTES `Sig.Ans op`."

`PROOF-DAG.md:84` types that as `EC1-D011 OpDesc : (a : Alphabet) -> a.toSig.Op
-> Type` — a TYPE per operation, i.e. data that may carry the proof. The row's
free `a` therefore ranges over alphabets whose descriptor table already
supplies the bridge. `ToyAlphabet` (`T004S.lean:121-123`) has no such field,
so it is not that carrier. -/

/-- The packet's carrier, transcribed. The `desc` field is the `OpDesc` clause
`ALGEBRA.md:134-135` names: it PROVES that `answerTy` denotes `Sig.Ans op`. -/
structure SpecAlphabet where
  sig : Sig
  answerTy : sig.Op → Ast
  desc : (op : sig.Op) → { d : Bridge (sig.Ans op) // d.code = answerTy op }

def SpecRowAsWritten : Prop :=
  ∀ (a : SpecAlphabet) (op : a.sig.Op),
    Nonempty { d : Bridge (a.sig.Ans op) // d.code = a.answerTy op }

/-- **The row HOLDS on the packet's own carrier.** Universally quantified,
no premise, no restriction of the operation universe. -/
theorem spec_row_holds : SpecRowAsWritten := fun a op => ⟨a.desc op⟩

/-- Non-vacuity, over a SHIPPED signature and a SHIPPED `Described` instance —
no minted `Sig`, no constructed bridge, no erased tag. `LlmSig` is
`Cas/Lang/Ops.lean:44`; `Described String` is
`Cas/Schema/Described/Instances.lean:37`. -/
def llmSpecAlphabet : SpecAlphabet where
  sig := LlmSig
  answerTy := fun _ => .str
  desc := fun _ => ⟨inferInstanceAs (Described String), rfl⟩

theorem llmSpecAlphabet_is_over_a_shipped_signature :
    llmSpecAlphabet.sig = LlmSig := rfl

theorem spec_row_is_not_vacuous : Nonempty SpecAlphabet := ⟨llmSpecAlphabet⟩

/-- **The dichotomy that is actually supported.** Not "the row is FALSE": the
row is false on a carrier that DROPS the descriptor clause and true — and
content-free — on the carrier that keeps it. Which of the two the DAG row
means is a packet question, not a Lean one, and `ALGEBRA.md:134-135` answers
it in favour of the second. -/
theorem the_supported_dichotomy :
    ¬ RowAsWritten ∧ SpecRowAsWritten ∧ Nonempty SpecAlphabet :=
  ⟨answer_bridge_is_not_a_theorem, spec_row_holds, spec_row_is_not_vacuous⟩

/-! ## §A3 — `field_repair_is_a_projection` pins the code to itself

`T004S.lean:266-272` offers `BridgedAlphabet` as the RECOMMENDED REPLACEMENT
and proves "with the bridge as a field the row is `rfl`". But `BridgedAlphabet`
has NO `answerTy` field, so the theorem's conclusion `d.code = (a.bridge
op).code` pins the code to its own bridge. The row is about a SEPARATE table;
this statement cannot mention one. -/

/-- The whole content, with no alphabet in sight: it holds of an arbitrary
family of bridges, correct or not. -/
theorem field_repair_needs_no_alphabet {S : Sig}
    (b : (op : S.Op) → Bridge (S.Ans op)) (op : S.Op) :
    ∃ d : Bridge (S.Ans op), d.code = (b op).code :=
  ⟨b op, rfl⟩

/-- Sharper: it holds of a single bridge value, with no signature either. -/
theorem code_pinned_to_itself_is_a_tautology {α : Type} (d : Bridge α) :
    ∃ e : Bridge α, e.code = d.code :=
  ⟨d, rfl⟩

/-- A `BridgedAlphabet` over the very signature §2's witness B refutes. Its
bridge's code is `.arr (.ref t)`. -/
def rootBridged (t : UInt8) : BridgedAlphabet where
  sig := RootSig
  bridge := fun op => match op with
    | .publish _ => inferInstanceAs (Described Unit)
    | .listRoots => @instDescribedList _ (describedAddr32 t)

/-- **The repair does not detect the error it was offered against.** The
`unitAlphabet` table is still refuted, and `field_repair_is_a_projection`
holds over the same signature regardless, because it never looks at a table. -/
theorem field_repair_does_not_detect_the_refuted_table (t : UInt8) :
    (∀ op : RootSig.Op, unitAlphabet.answerTy op = Ast.null)
    ∧ (∃ d : Bridge (RootSig.Ans RootE.listRoots),
          d.code = ((rootBridged t).bridge RootE.listRoots).code)
    ∧ ¬ Nonempty (AnswerBridge unitAlphabet RootE.listRoots) :=
  ⟨fun _ => rfl,
   field_repair_is_a_projection (rootBridged t) RootE.listRoots,
   fun h => h.elim unitAlphabet_has_no_bridge⟩

/-- The honest form of the repair: keep the table, and PIN the bridge to it.
Then the row is a projection ABOUT `answerTy`, which is what §2.2 asks for. -/
structure PinnedAlphabet where
  sig : Sig
  answerTy : sig.Op → Ast
  bridge : (op : sig.Op) → Bridge (sig.Ans op)
  pinned : ∀ op, (bridge op).code = answerTy op

theorem honest_field_repair_is_a_projection (a : PinnedAlphabet) (op : a.sig.Op) :
    ∃ d : Bridge (a.sig.Ans op), d.code = a.answerTy op :=
  ⟨a.bridge op, a.pinned op⟩

/-! ## §A4 — `enumeration_must_be_of_headers` states no "must"

`T004S.lean:349-354` proves
`(∀ h : CasHeader, h ∈ CasHeader.all) ∧ CasHeader.all.length = 3 ∧
 (∀ m n, opOfNat m = opOfNat n → m = n)`.
Two of the three conjuncts are facts about a locally minted inductive; the
third is injectivity of one family. Nothing in the statement says `CasSig.Op`
admits no finite enumeration, which is the fact the name asserts. It is
provable, and here it is. -/

def casSize : CasE → Nat
  | .put n => n.payload.length
  | _ => 0

theorem casSize_opOfNat (n : Nat) : casSize (opOfNat n) = n := by
  simp [casSize, opOfNat]

def maxOf : List Nat → Nat
  | [] => 0
  | x :: xs => Nat.max x (maxOf xs)

theorem le_maxOf : ∀ {l : List Nat} {x : Nat}, x ∈ l → x ≤ maxOf l
  | _ :: _, _, List.Mem.head _ => Nat.le_max_left _ _
  | _ :: _, _, List.Mem.tail _ h => Nat.le_trans (le_maxOf h) (Nat.le_max_right _ _)

/-- **The missing statement.** No list enumerates `CasSig.Op`, so the finite
canonical enumeration `ALGEBRA.md:132-133` asks for cannot be of operations.
This is the "must" the shipped theorem's name claims and its statement omits. -/
theorem casSig_op_has_no_finite_enumeration (l : List CasSig.Op) :
    ∃ op : CasSig.Op, op ∉ l := by
  refine ⟨opOfNat (maxOf (l.map casSize) + 1), fun hmem => ?_⟩
  have hmap : casSize (opOfNat (maxOf (l.map casSize) + 1)) ∈ l.map casSize :=
    List.mem_map_of_mem hmem
  rw [casSize_opOfNat] at hmap
  have hle := le_maxOf hmap
  omega

/-! ## §A5 — the admitted fragment leaves `put`'s code free, and its `Addr32`
bridge erases the tag `Cas/Schema/El.lean` says must be retained

`T004S.lean:541-586` discharges the constructibility obligation for four arms.
Two of them — `put` and `listRoots` — are built from `describedAddr32`
(`T004S.lean:487`), a `Described Addr32` at code `.ref t` for an arbitrary tag.
`Cas/Schema/El.lean:16-18` says of `StoreRef`:

> "A typed store reference that RETAINS the kind it expects ... Erasing the
> tag would make every reference code denote one type and lose the refinement."

The shipped carrier for `.ref t` is `StoreRef t`
(`Cas/Schema/Described/Instances.lean:45`). `describedAddr32` puts the untagged
`Addr32` at the same codes, for every tag at once. -/

/-- The shipped carrier keeps the tag. -/
theorem shipped_ref_carrier_is_tagged (t : UInt8) :
    (inferInstance : Described (StoreRef t)).code = Ast.ref t
    ∧ El (Ast.ref t) = StoreRef t :=
  ⟨rfl, rfl⟩

/-- The constructed carrier does not: one `Addr32` sits at every `.ref` code. -/
theorem addr32_bridge_erases_the_tag (t : UInt8) :
    (describedAddr32 t).code = Ast.ref t :=
  rfl

/-- **The consequence for §4.5.** `admitted_answer_bridge` holds for the
`answerTy` table at tag `0` and, simultaneously, for the DIFFERENT table at
tag `1`. So the constructibility discharge identifies no canonical `answerTy`
for `put`; §4.4's non-determination applies to §4.5's positive result too. -/
theorem admitted_bridge_leaves_put_free :
    AdmittedHeader.answerTy 0 .put ≠ AdmittedHeader.answerTy 1 .put
    ∧ (∃ d : Bridge AdmittedHeader.put.ans, d.code = AdmittedHeader.answerTy 0 .put)
    ∧ (∃ d : Bridge AdmittedHeader.put.ans, d.code = AdmittedHeader.answerTy 1 .put) :=
  ⟨by intro he; injection he with ht; exact absurd ht (by decide),
   ⟨(admittedBridge 0 .put).1, (admittedBridge 0 .put).2⟩,
   ⟨(admittedBridge 1 .put).1, (admittedBridge 1 .put).2⟩⟩

/-- And the same for `listRoots`, since its code is built from `put`'s. -/
theorem admitted_bridge_leaves_listRoots_free :
    AdmittedHeader.answerTy 0 .listRoots ≠ AdmittedHeader.answerTy 1 .listRoots := by
  intro he; injection he with hr; injection hr with ht; exact absurd ht (by decide)

/-! ## §A6 — falsifiers the proof SURVIVES

`EC1-F86` has two halves. The tag-erasure half is §A5. The other half —
"silently inhabit one of `El`'s empty arms" — the file does not commit: it
states `El (.susp .null) = Empty` and stops. Re-checked independently. -/

theorem susp_arm_stays_empty : El (Ast.susp Ast.null) = Empty := rfl

theorem no_bridge_can_inhabit_an_empty_arm (d : Bridge Empty) (x : El d.code) :
    False :=
  (d.ofEl x).elim

/-- `EC1-F02` analogue — swap an answer type and see whether the machinery
notices. A THIRD independent arm, on the signature the file never used:
`LlmSig`'s `infer` answers `String`; claim it answers `null`. The bridge
still fails, so §2's refutation is not tuned to `CasSig`/`RootSig`. -/
def swappedLlm : ToyAlphabet where
  sig := LlmSig
  answerTy := fun _ => .null

theorem swapped_llm_has_no_bridge
    (b : AnswerBridge swappedLlm (LlmE.infer "p")) : False := by
  obtain ⟨d, hcode⟩ := b
  have hs : ∀ x y : El d.code, x = y := by
    rw [hcode]; exact el_null_subsingleton
  have h : ("" : String) = "a" :=
    bridge_at_subsingleton_code d hs "" "a"
  exact absurd h (by decide)

/-- `EC1-F87` — "replace `Sig.Op`". The non-vacuity control
`admittedAlphabet` (`T004S.lean:588-590`) does replace it: its signature is
the minted `⟨AdmittedHeader, AdmittedHeader.ans⟩`, not a shipped one. §A2's
`llmSpecAlphabet` supplies the control over a shipped signature instead. -/
theorem admittedAlphabet_signature_is_minted (t : UInt8) :
    (admittedAlphabet t).sig.Op = AdmittedHeader :=
  rfl

theorem llm_control_is_over_a_shipped_signature :
    llmSpecAlphabet.sig.Op = LlmE ∧ llmSpecAlphabet.sig = LlmSig :=
  ⟨rfl, rfl⟩

end AttackT004S

/-! ## Axiom receipts

`Classical.choice`/`Quot.sound` appear exactly where a statement mentions a
`Bridge` (= `Cas.Schema.Described`), whose `wf` field is an `Ast.WF` proof —
the same library ceiling `T004S.lean` records. The two findings that do not
mention a `Bridge` are choice-free:
`casSig_op_has_no_finite_enumeration` and `admitted_bridge_leaves_listRoots_free`.

Checks OMITTED here: no `lake build`; nothing under `library/` was read for
byte identity; the TypeScript host was not consulted; `EC1-T004X`,
`EC1-T004RW` and `EC1-T003E` were not probed; and no claim is made about the
real `EC1-D010 Alphabet`'s representation, which freeze conditions 3 and 14
still own. -/

#print axioms AttackT004S.answer_bridge_is_not_a_theorem
#print axioms AttackT004S.generosity_runs_one_way
#print axioms AttackT004S.admitted_class_is_inhabited
#print axioms AttackT004S.witness_B_survives_the_header_narrowing
#print axioms AttackT004S.row_holds_on_the_narrower_class
#print axioms AttackT004S.generosity_inference_is_invalid
#print axioms AttackT004S.spec_row_holds
#print axioms AttackT004S.llmSpecAlphabet_is_over_a_shipped_signature
#print axioms AttackT004S.spec_row_is_not_vacuous
#print axioms AttackT004S.the_supported_dichotomy
#print axioms AttackT004S.field_repair_is_a_projection
#print axioms AttackT004S.field_repair_needs_no_alphabet
#print axioms AttackT004S.code_pinned_to_itself_is_a_tautology
#print axioms AttackT004S.field_repair_does_not_detect_the_refuted_table
#print axioms AttackT004S.honest_field_repair_is_a_projection
#print axioms AttackT004S.casSize_opOfNat
#print axioms AttackT004S.le_maxOf
#print axioms AttackT004S.casSig_op_has_no_finite_enumeration
#print axioms AttackT004S.shipped_ref_carrier_is_tagged
#print axioms AttackT004S.addr32_bridge_erases_the_tag
#print axioms AttackT004S.admitted_bridge_leaves_put_free
#print axioms AttackT004S.admitted_bridge_leaves_listRoots_free
#print axioms AttackT004S.susp_arm_stays_empty
#print axioms AttackT004S.no_bridge_can_inhabit_an_empty_arm
#print axioms AttackT004S.swapped_llm_has_no_bridge
#print axioms AttackT004S.admittedAlphabet_signature_is_minted
#print axioms AttackT004S.llm_control_is_over_a_shipped_signature
