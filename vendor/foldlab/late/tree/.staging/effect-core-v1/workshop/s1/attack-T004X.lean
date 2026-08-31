import Cas.Backend.SumAlgebra

/-!
# BREAKER attack on `EC1-T004X` (`workshop/s1/T004X.lean`), slice `EC1-S1`

Skill stage: `.claude/skills/lean/workflows/lean-assurance-review` — the target
is a landed proof reporting `PROVED-STRONGER`, so this is an adversarial
assurance review, not a proof lane.

Run from `library/cas`:

```
lake env lean ../../.staging/effect-core-v1/workshop/s1/attack-T004X.lean
```

§0 re-declares `T004X.lean`'s §1 carrier VERBATIM. Nothing is imported from
`T004X.lean` — it is not a Lake module — so every landed result this file leans
on is re-derived here rather than assumed.

## What survives the attack

* The file checks: exit 0, 33 `#print axioms` receipts for 33 theorems, ceiling
  `propext`/`Quot.sound`, no `sorryAx`, no `Classical.choice`, no
  `native_decide`, no `#eval` carrying a claim.
* NOT VACUOUS. §1 exhibits an alphabet pair with NONEMPTY operation sets
  satisfying all seven premises at once and derives a non-degenerate conclusion
  — the receipt the target never writes.
* The three necessity theorems are sound, and §3 closes the four the target
  claims but does not prove.
* §8's refutation at the derived carrier is sound and its admitted omission is
  a genuine obstruction, not missing effort: §8 here puts the disjoint-arm case
  in explicit bijection, so no cardinality argument can ever refute it.

## What does not

* §2 CONJUNCT INFLATION. Conjuncts (1), (4) and (5) of
  `alphabet_extend_preserves_arms` are functions of the `sig` FIELD ALONE:
  `conjuncts_1_4_5_depend_only_on_the_sig_field` proves all three by `rfl` for
  an ARBITRARY `ops` and `desc`. So (4) and (5) are re-readings of (1), not
  added content. Conjuncts (2) and (3) genuinely are added: `extendConst`
  satisfies (1), (4), (5) and breaks (2), (3). The independent count is six,
  not eight.
* §3 PREMISE ACCOUNTING. Four of the seven premises — `heb`, `hnb`, `hia`,
  `hib` — carry no necessity witness in the target, while its §6 prose asserts
  each premise is load-bearing. All four are proved necessary here.
* §4 A THIRD BLINDNESS the target does not have: the equation cannot see ARM
  ORDER either. `equation_is_blind_to_arm_order` and
  `enumeration_is_order_sensitive` show `extend` is not commutative while
  `toSig` cannot tell the two orders apart — which bears on `EFFECTS-BACKEND`
  R4 presentation identity and on the "sorted table" the target flags as
  unmodelled.
* §5 `EC1-F87` (flatten an extension arm) is named by the target and NOT
  exercised. Exercised here: flattening collapses every handler on the result,
  so the right arm's meaning is unrecoverable in the estate's own `Handler`
  vocabulary.
* §6 SELF-EXTENSION IS EXCLUDED. `IdsDisjoint a a` is false for every alphabet
  with an inhabited operation type, so the headline theorem has NO instance of
  the form `a.extend a`. The packet's "adding an operation changes the alphabet
  version" story is outside its reach.
* §8 `EC1-F82` (permute a duplicate-key row): the derived carrier's `extend` is
  order-sensitive on a shared key, proved here, which the target does not state.

No `sorry`, no `axiom`, no `native_decide`, no `#eval` carrying a claim. Every
theorem reports `#print axioms` at the foot.
-/

namespace EffectCoreV1.AttackT004X

open Cas.Lang

/-! ## §0 — the carrier, re-declared verbatim from `T004X.lean` §1 -/

inductive HandlerRoute where
  | builtin (handlerId : String)
  | service (serviceKey : String)
  deriving DecidableEq, Repr

inductive Resumption where
  | zero | one | many
  deriving DecidableEq, Repr

inductive Observation where
  | pub | receiptOnly | hidden
  deriving DecidableEq, Repr

structure OpDesc where
  opId : String
  handlerRoute : HandlerRoute
  resumption : Resumption
  observation : Observation
  deriving DecidableEq, Repr

structure Alphabet where
  sig : Sig
  ops : List sig.Op
  desc : sig.Op → OpDesc

def Alphabet.toSig (a : Alphabet) : Sig := a.sig

def Alphabet.opId (a : Alphabet) (op : a.toSig.Op) : String := (a.desc op).opId

def Alphabet.EnumComplete (a : Alphabet) : Prop := ∀ op : a.toSig.Op, op ∈ a.ops

def Alphabet.EnumNodup (a : Alphabet) : Prop := a.ops.Nodup

def Alphabet.IdsInjective (a : Alphabet) : Prop := Function.Injective a.opId

def Alphabet.IdsDisjoint (a b : Alphabet) : Prop :=
  ∀ (i : a.toSig.Op) (j : b.toSig.Op), a.opId i ≠ b.opId j

def Alphabet.extend (a b : Alphabet) : Alphabet where
  sig := a.sig ⊕ₛ b.sig
  ops := a.ops.map Sum.inl ++ b.ops.map Sum.inr
  desc := Sum.elim a.desc b.desc

/-! ### §0.1 — the landed clauses, RE-DERIVED

If the target's proofs were unsound these would not close. They are repeated
verbatim so that every attack below stands on this file's own kernel run. -/

theorem extend_toSig (a b : Alphabet) :
    (a.extend b).toSig = a.toSig ⊕ₛ b.toSig := rfl

theorem extend_enumComplete (a b : Alphabet)
    (ha : a.EnumComplete) (hb : b.EnumComplete) : (a.extend b).EnumComplete := by
  rintro (x | y)
  · exact List.mem_append_left _ (List.mem_map_of_mem (ha x))
  · exact List.mem_append_right _ (List.mem_map_of_mem (hb y))

theorem extend_enumNodup (a b : Alphabet)
    (ha : a.EnumNodup) (hb : b.EnumNodup) : (a.extend b).EnumNodup := by
  show (a.ops.map Sum.inl ++ b.ops.map Sum.inr).Nodup
  refine List.nodup_append.mpr ⟨?_, ?_, ?_⟩
  · exact List.Pairwise.map Sum.inl (fun _ _ h he => h (Sum.inl.inj he)) ha
  · exact List.Pairwise.map Sum.inr (fun _ _ h he => h (Sum.inr.inj he)) hb
  · intro p hp q hq
    rw [List.mem_map] at hp hq
    obtain ⟨x, _, hx⟩ := hp
    obtain ⟨y, _, hy⟩ := hq
    subst hx; subst hy
    simp

theorem extend_opId_injective (a b : Alphabet)
    (ha : a.IdsInjective) (hb : b.IdsInjective) (hd : a.IdsDisjoint b) :
    (a.extend b).IdsInjective := by
  rintro (x | x) (y | y) h
  · exact congrArg Sum.inl (ha h)
  · exact absurd h (hd x y)
  · exact absurd h.symm (hd y x)
  · exact congrArg Sum.inr (hb h)

/-! ### §0.2 — witnesses -/

def unitSig : Sig := ⟨Unit, fun _ => Unit⟩
def boolSig : Sig := ⟨Bool, fun _ => Unit⟩
def natSig : Sig := ⟨Unit, fun _ => Nat⟩

/-- Left arm publishing `"get"`, as in `T004X.lean` §2.3. -/
def uGet : Alphabet where
  sig := unitSig
  ops := [()]
  desc := fun _ => ⟨"get", .builtin "L", .one, .pub⟩

/-- Right arm publishing `"get"` as well — the collision witness. -/
def vGet : Alphabet where
  sig := unitSig
  ops := [()]
  desc := fun _ => ⟨"get", .service "R", .one, .pub⟩

/-- A right arm publishing a DIFFERENT identifier. The target has no such
alphabet, which is why it has no joint-inhabitation witness. -/
def bPut : Alphabet where
  sig := unitSig
  ops := [()]
  desc := fun _ => ⟨"put", .service "P", .one, .pub⟩

/-- `T004X.lean` §4.3's incomplete enumeration. -/
def missingOp : Alphabet where
  sig := unitSig
  ops := []
  desc := fun _ => ⟨"missing", .builtin "M", .one, .pub⟩

/-- `T004X.lean` §4.3's duplicated enumeration. -/
def dupOp : Alphabet where
  sig := unitSig
  ops := [(), ()]
  desc := fun _ => ⟨"dup", .builtin "D", .one, .pub⟩

/-- An alphabet with TWO operations sharing one identifier: the within-arm
collision the target's premises exclude but never witness. -/
def dupIds : Alphabet where
  sig := boolSig
  ops := [true, false]
  desc := fun _ => ⟨"same", .builtin "S", .one, .pub⟩

/-! ## §1 — VACUITY PROBE: the seven premises are jointly inhabited

The target's own anti-vacuity control is `aBuiltin_enum_ok`, which discharges
TWO of the seven premises for ONE alphabet. Nowhere does it exhibit a PAIR
satisfying all seven at once, so nowhere does it establish that
`alphabet_extend_preserves_arms` has a non-degenerate instance. It does. -/

theorem uGet_complete : uGet.EnumComplete := by
  intro op; cases op; exact List.mem_singleton_self _

theorem bPut_complete : bPut.EnumComplete := by
  intro op; cases op; exact List.mem_singleton_self _

theorem uGet_nodup : uGet.EnumNodup := by
  show List.Nodup ([()] : List Unit); simp

theorem bPut_nodup : bPut.EnumNodup := by
  show List.Nodup ([()] : List Unit); simp

theorem uGet_injective : uGet.IdsInjective := by
  intro x y _; cases x; cases y; rfl

theorem bPut_injective : bPut.IdsInjective := by
  intro x y _; cases x; cases y; rfl

theorem uGet_bPut_disjoint : uGet.IdsDisjoint bPut := by
  intro i j; cases i; cases j; decide

/-- **All seven premises hold of one pair with NONEMPTY operation types.** -/
theorem premises_are_jointly_inhabited :
    uGet.EnumComplete ∧ bPut.EnumComplete
      ∧ uGet.EnumNodup ∧ bPut.EnumNodup
      ∧ uGet.IdsInjective ∧ bPut.IdsInjective
      ∧ uGet.IdsDisjoint bPut :=
  ⟨uGet_complete, bPut_complete, uGet_nodup, bPut_nodup,
   uGet_injective, bPut_injective, uGet_bPut_disjoint⟩

/-- **And the conclusion at that instance is non-degenerate**: the extended
alphabet really has two distinct operations, and the three non-`rfl` conjuncts
all hold of it. `alphabet_extend_preserves_arms` is TRUE and NOT VACUOUS. -/
theorem headline_has_a_nondegenerate_instance :
    (uGet.extend bPut).EnumComplete
      ∧ (uGet.extend bPut).EnumNodup
      ∧ (uGet.extend bPut).IdsInjective
      ∧ (Sum.inl () : (uGet.extend bPut).toSig.Op) ≠ Sum.inr () := by
  refine ⟨extend_enumComplete _ _ uGet_complete bPut_complete,
          extend_enumNodup _ _ uGet_nodup bPut_nodup,
          extend_opId_injective _ _ uGet_injective bPut_injective uGet_bPut_disjoint,
          ?_⟩
  show (Sum.inl () : Unit ⊕ Unit) ≠ Sum.inr ()
  simp

/-! ## §2 — FINDING: conjunct inflation

The target reports the strengthening as "the DAG's one equation becomes eight
conjuncts". Two of the eight are not additions. -/

/-- **Conjuncts (1), (4) and (5) are determined by the `sig` FIELD ALONE.** For
an ARBITRARY enumeration and an ARBITRARY descriptor table, all three hold by
`rfl`. They say nothing whatever about the extension operator beyond what its
signature field already is — so (4) and (5) are re-readings of (1), not content
added to it. -/
theorem conjuncts_1_4_5_depend_only_on_the_sig_field (a b : Alphabet)
    (ops : List (a.sig ⊕ₛ b.sig).Op) (desc : (a.sig ⊕ₛ b.sig).Op → OpDesc) :
    ((Alphabet.mk (a.sig ⊕ₛ b.sig) ops desc).toSig = a.toSig ⊕ₛ b.toSig)
      ∧ (∀ op : a.toSig.Op,
          (Alphabet.mk (a.sig ⊕ₛ b.sig) ops desc).toSig.Ans (Sum.inl op)
            = a.toSig.Ans op)
      ∧ (∀ op : b.toSig.Op,
          (Alphabet.mk (a.sig ⊕ₛ b.sig) ops desc).toSig.Ans (Sum.inr op)
            = b.toSig.Ans op) :=
  ⟨rfl, fun _ => rfl, fun _ => rfl⟩

def junkDesc : OpDesc := ⟨"junk", .builtin "J", .zero, .hidden⟩

/-- An extension operator that keeps the DAG's signature equation and throws the
metadata away. This is the adversary the target's §3 says exists ("a different
`extend` would break them silently") and does not build. -/
def extendConst (a b : Alphabet) : Alphabet where
  sig := a.sig ⊕ₛ b.sig
  ops := a.ops.map Sum.inl ++ b.ops.map Sum.inr
  desc := fun _ => junkDesc

/-- `extendConst` satisfies conjuncts (1), (4), (5) — every one of them by
`rfl`. -/
theorem extendConst_satisfies_1_4_5 (a b : Alphabet) :
    ((extendConst a b).toSig = a.toSig ⊕ₛ b.toSig)
      ∧ (∀ op : a.toSig.Op,
          (extendConst a b).toSig.Ans (Sum.inl op) = a.toSig.Ans op)
      ∧ (∀ op : b.toSig.Op,
          (extendConst a b).toSig.Ans (Sum.inr op) = b.toSig.Ans op) :=
  ⟨rfl, fun _ => rfl, fun _ => rfl⟩

/-- **…and breaks conjuncts (2) and (3).** So (2) and (3) ARE independent
content, and the target's central diagnosis — that the equation carries nothing
— is sharper than it states: the equation cannot even pin the extension
OPERATOR, not merely the alphabets. -/
theorem extendConst_breaks_2_and_3 :
    (extendConst uGet bPut).desc (Sum.inl ()) ≠ uGet.desc ()
      ∧ (extendConst uGet bPut).desc (Sum.inr ()) ≠ bPut.desc () := by
  constructor <;> decide

/-- The independent conjunct count, stated: `extendConst` shows (1) does not
imply (2); `conjuncts_1_4_5_depend_only_on_the_sig_field` shows (1) DOES give
(4) and (5). -/
theorem eight_conjuncts_are_six (a b : Alphabet)
    (ops : List (a.sig ⊕ₛ b.sig).Op) (desc : (a.sig ⊕ₛ b.sig).Op → OpDesc) :
    ((Alphabet.mk (a.sig ⊕ₛ b.sig) ops desc).toSig = a.toSig ⊕ₛ b.toSig)
      ∧ (∀ op : a.toSig.Op,
          (Alphabet.mk (a.sig ⊕ₛ b.sig) ops desc).toSig.Ans (Sum.inl op)
            = a.toSig.Ans op)
      ∧ (extendConst uGet bPut).desc (Sum.inl ()) ≠ uGet.desc () :=
  ⟨rfl, fun _ => rfl, extendConst_breaks_2_and_3.1⟩

/-! ## §3 — FINDING: four premises carry no necessity witness

The target proves three necessity theorems — dropping `hea`, dropping `hna`,
dropping `hd` — and its §6 prose then asserts of all seven premises that "no
premise is decorative". The mirror four are proved here. -/

theorem dupIds_disjoint_bPut : dupIds.IdsDisjoint bPut := by
  intro i j; cases i <;> cases j <;> decide

theorem bPut_disjoint_dupIds : bPut.IdsDisjoint dupIds := by
  intro i j; cases i <;> cases j <;> decide

/-- **`heb` is necessary** — the RIGHT arm's completeness. The target proves
only the left. -/
theorem right_enumComplete_premise_is_necessary :
    ¬ ∀ (a b : Alphabet), a.EnumComplete → (a.extend b).EnumComplete := by
  intro h
  have hbad := h uGet missingOp uGet_complete (Sum.inr ())
  revert hbad
  show ¬ ((Sum.inr () : Unit ⊕ Unit) ∈ ([Sum.inl ()] : List (Unit ⊕ Unit)))
  simp

/-- **`hnb` is necessary** — the RIGHT arm's duplicate-freedom. -/
theorem right_enumNodup_premise_is_necessary :
    ¬ ∀ (a b : Alphabet), a.EnumNodup → (a.extend b).EnumNodup := by
  intro h
  have hbad := h uGet dupOp uGet_nodup
  revert hbad
  show ¬ (List.Nodup ([Sum.inl (), Sum.inr (), Sum.inr ()] : List (Unit ⊕ Unit)))
  simp

/-- **`hia` is necessary** — the LEFT arm's identifier injectivity. Disjointness
holds here (`"same" ≠ "put"`) and the right arm is injective, so the failure is
caused by the dropped premise alone. This is `EC1-F03` (duplicate an operation
identifier) fired INSIDE one arm, where the target only fires it ACROSS arms. -/
theorem left_idsInjective_premise_is_necessary :
    ¬ ∀ (a b : Alphabet),
        b.IdsInjective → a.IdsDisjoint b → (a.extend b).IdsInjective := by
  intro h
  have hinj := h dupIds bPut bPut_injective dupIds_disjoint_bPut
  have hcol : (dupIds.extend bPut).opId (Sum.inl true)
      = (dupIds.extend bPut).opId (Sum.inl false) := rfl
  have hbad := hinj hcol
  revert hbad
  show ¬ ((Sum.inl true : Bool ⊕ Unit) = Sum.inl false)
  simp

/-- **`hib` is necessary** — the RIGHT arm's identifier injectivity. -/
theorem right_idsInjective_premise_is_necessary :
    ¬ ∀ (a b : Alphabet),
        a.IdsInjective → a.IdsDisjoint b → (a.extend b).IdsInjective := by
  intro h
  have hinj := h bPut dupIds bPut_injective bPut_disjoint_dupIds
  have hcol : (bPut.extend dupIds).opId (Sum.inr true)
      = (bPut.extend dupIds).opId (Sum.inr false) := rfl
  have hbad := hinj hcol
  revert hbad
  show ¬ ((Sum.inr true : Unit ⊕ Bool) = Sum.inr false)
  simp

/-! ## §4 — FINDING: a third blindness — the equation cannot see ARM ORDER

The target exhibits two blindnesses (metadata, identifier collision). Here is a
third, and it is the one that bears on `EFFECTS-BACKEND` R4: identity hashes
PRESENTATIONS, and `extend` produces two different presentations that `toSig`
cannot distinguish. The target flags the "sorted table" of `ALGEBRA.md` §2.2 as
unmodelled; this is what that omission costs. -/

/-- **Finding 3 — the equation is blind to arm order.** Swapping the arms leaves
`toSig` definitionally equal and changes the descriptor table. -/
theorem equation_is_blind_to_arm_order :
    (uGet.extend vGet).toSig = (vGet.extend uGet).toSig
      ∧ (uGet.extend vGet).desc (Sum.inl ())
          ≠ (vGet.extend uGet).desc (Sum.inl ()) := by
  refine ⟨rfl, ?_⟩
  decide

/-- **`extend` is not commutative**, and the "canonical enumeration" is not
canonical up to the order of composition either. -/
theorem enumeration_is_order_sensitive :
    (uGet.extend dupOp).ops ≠ (dupOp.extend uGet).ops := by
  show ([Sum.inl (), Sum.inr (), Sum.inr ()] : List (Unit ⊕ Unit))
      ≠ ([Sum.inl (), Sum.inl (), Sum.inr ()] : List (Unit ⊕ Unit))
  decide

/-! ## §5 — `EC1-F87`, the flattening arm, EXERCISED

The target names `EC1-F87` and says nothing here is flattened. True — but it
never fires the falsifier, so it never measures what `Sig.sum` buys. Fired
here, in the estate's own `Handler` vocabulary. -/

/-- A left arm over a signature with a distinguishable answer type. -/
def nL : Alphabet where
  sig := natSig
  ops := [()]
  desc := fun _ => ⟨"n", .builtin "L", .one, .pub⟩

/-- A right arm over the SAME signature — the only case in which flattening is
even typeable, which is why it is the sharpest form of the falsifier. -/
def nR : Alphabet where
  sig := natSig
  ops := [()]
  desc := fun _ => ⟨"n", .service "R", .one, .pub⟩

/-- **The prohibited shortcut**: identify the arms instead of tagging them. -/
def flatten (a b : Alphabet) (_h : b.sig = a.sig) : Alphabet := a

def flatLR : Alphabet := flatten nL nR rfl

def hL : Handler nL.toSig Id := ⟨fun _ => (0 : Nat)⟩
def hR : Handler nR.toSig Id := ⟨fun _ => (1 : Nat)⟩

/-- With `Sig.sum` the two arms stay separately answerable. -/
theorem sum_keeps_both_arms_answerable :
    (hL.sum hR).handle (Sum.inl ()) = (0 : Nat)
      ∧ (hL.sum hR).handle (Sum.inr ()) = (1 : Nat) :=
  ⟨rfl, rfl⟩

/-- **`EC1-F87` fires.** On the flattened alphabet EVERY handler answers all
operations alike, so there is no handler at all that separates the arms: the
right arm's meaning is not merely discarded, it is unrepresentable. -/
theorem flattening_collapses_every_handler {M : Type → Type}
    (k : Handler flatLR.toSig M) (op op' : flatLR.toSig.Op) :
    k.handle op = k.handle op' := by
  cases op; cases op'; rfl

/-- …and the metadata goes with it. -/
theorem flattening_loses_the_right_arm :
    (∀ op : flatLR.toSig.Op, flatLR.desc op = nL.desc ())
      ∧ nR.desc () ≠ nL.desc () := by
  refine ⟨?_, by decide⟩
  intro op; cases op; rfl

/-! ## §6 — FINDING: the headline theorem excludes self-extension

`IdsDisjoint a a` is false for every alphabet with an inhabited operation type,
so `alphabet_extend_preserves_arms` has NO instance of the form `a.extend a`.
`ALGEBRA.md` §2.2's "adding an operation changes the alphabet version and
reopens all totality and code-generation tables" is therefore outside its
reach — as the target's own omission note concedes for the `version` column,
without noticing that the premise bundle excludes the case structurally. -/

theorem self_extension_is_never_admissible (a : Alphabet) (op : a.toSig.Op) :
    ¬ a.IdsDisjoint a := fun h => h op op rfl

theorem uGet_cannot_extend_itself : ¬ uGet.IdsDisjoint uGet :=
  self_extension_is_never_admissible uGet ()

/-! ## §7 — the projection rows of §7 are not vacuous

The target transplants `Handler.sum_unique`, `Prog.inl_unique` and
`Prog.inr_unique` and never shows their hypotheses inhabitable. They are. -/

theorem sum_unique_hypothesis_is_inhabited {M : Type → Type v} (a b : Alphabet)
    (h : Handler a.toSig M) (g : Handler b.toSig M) :
    (∀ op : a.toSig.Op, (h.sum g).handle (Sum.inl op) = h.handle op)
      ∧ (∀ op : b.toSig.Op, (h.sum g).handle (Sum.inr op) = g.handle op) :=
  ⟨fun op => Handler.sum_handle_inl h g op, fun op => Handler.sum_handle_inr h g op⟩

theorem inl_unique_hypothesis_is_inhabited (a b : Alphabet) :
    ∀ (M : Type → Type) [Monad M] [LawfulMonad M]
      (h : Handler a.toSig M) (g : Handler b.toSig M)
      {A : Type} (p : Prog a.toSig A),
      interpret (h.sum g) (Prog.inl (T := b.toSig) p) = interpret h p := by
  intro M _ _ h g A p
  exact interpret_inl h g p

theorem inr_unique_hypothesis_is_inhabited (a b : Alphabet) :
    ∀ (M : Type → Type) [Monad M] [LawfulMonad M]
      (h : Handler a.toSig M) (g : Handler b.toSig M)
      {A : Type} (q : Prog b.toSig A),
      interpret (h.sum g) (Prog.inr (S := a.toSig) q) = interpret g q := by
  intro M _ _ h g A q
  exact interpret_inr h g q

/-! ## §8 — the derived carrier: what §8 of the target proves, and what it can't

Re-declared verbatim from `T004X.lean` §8. Two additions:

* `EC1-F82` fires on it — concatenation is ORDER-SENSITIVE on a shared key, a
  fact the target's `derived_right_arm_metadata_is_lost` gestures at and does
  not state;
* the DISJOINT-arm case the target lists as an unproved omission is shown here
  to be a genuine OBSTRUCTION: the two sides are in explicit bijection, so no
  cardinality argument can ever refute it. -/

namespace Derived

inductive OpId where
  | get | put
  deriving DecidableEq, Repr

inductive AnsCode where
  | nat | str
  deriving DecidableEq, Repr

def AnsCode.interp : AnsCode → Type
  | .nat => Nat
  | .str => String

structure Row where
  op : OpId
  answerTy : AnsCode
  route : HandlerRoute
  deriving DecidableEq, Repr

structure PartialAlphabet where
  table : List Row

def PartialAlphabet.lookup (a : PartialAlphabet) (op : OpId) : Option Row :=
  a.table.find? (fun d => decide (d.op = op))

def PartialAlphabet.toSig (a : PartialAlphabet) : Sig where
  Op := { op : OpId // (a.lookup op).isSome = true }
  Ans := fun op => AnsCode.interp ((a.lookup op.1).get op.2).answerTy

def PartialAlphabet.extend (a b : PartialAlphabet) : PartialAlphabet :=
  ⟨a.table ++ b.table⟩

def aGet : PartialAlphabet := ⟨[⟨.get, .nat, .builtin "L"⟩]⟩
def bGet : PartialAlphabet := ⟨[⟨.get, .nat, .service "R"⟩]⟩

/-- **`EC1-F82` at the derived carrier.** The two composition orders of the same
two arms disagree on the shared key, so the flat-table `extend` does not even
normalize a duplicate key consistently. This is `EC1-CE030`'s ruled repair
("add a duplicate-free premise or make row validity supply it") owed one carrier
up, and the target states no such premise. -/
theorem derived_extend_is_order_sensitive :
    (aGet.extend bGet).lookup .get ≠ (bGet.extend aGet).lookup .get := by
  decide

/-! ### §8.2 — the disjoint-arm case is an obstruction, not an omission -/

def cGet : PartialAlphabet := ⟨[⟨.get, .nat, .builtin "L"⟩]⟩
def dPut : PartialAlphabet := ⟨[⟨.put, .str, .service "R"⟩]⟩

def split : (cGet.extend dPut).toSig.Op → (cGet.toSig.Op ⊕ dPut.toSig.Op)
  | ⟨.get, _⟩ => Sum.inl ⟨.get, by decide⟩
  | ⟨.put, _⟩ => Sum.inr ⟨.put, by decide⟩

def merge : (cGet.toSig.Op ⊕ dPut.toSig.Op) → (cGet.extend dPut).toSig.Op
  | Sum.inl ⟨.get, _⟩ => ⟨.get, by decide⟩
  | Sum.inl ⟨.put, h⟩ => absurd h (by decide)
  | Sum.inr ⟨.put, _⟩ => ⟨.put, by decide⟩
  | Sum.inr ⟨.get, h⟩ => absurd h (by decide)

/-- **The obstruction, made explicit.** For DISJOINT arms the derived carrier's
operation universe and the summed one are in bijection. The target's §8 refutes
the equation only for OVERLAPPING arms, by a subsingleton-versus-two-elements
cardinality argument; this proves no such argument can exist in the disjoint
case. Lean has no univalence, so the two sides remain independent — the target's
listed omission is a real limit of the method, not unfinished work. -/
theorem disjoint_arms_are_in_bijection :
    (∀ x, split (merge x) = x) ∧ (∀ x, merge (split x) = x) := by
  constructor
  · rintro (⟨(_ | _), h⟩ | ⟨(_ | _), h⟩)
    · rfl
    · exact absurd h (by decide)
    · exact absurd h (by decide)
    · rfl
  · rintro ⟨(_ | _), h⟩
    · rfl
    · rfl

end Derived

end EffectCoreV1.AttackT004X

/-! ## Kernel receipts -/

#print axioms EffectCoreV1.AttackT004X.extend_toSig
#print axioms EffectCoreV1.AttackT004X.extend_enumComplete
#print axioms EffectCoreV1.AttackT004X.extend_enumNodup
#print axioms EffectCoreV1.AttackT004X.extend_opId_injective
#print axioms EffectCoreV1.AttackT004X.uGet_complete
#print axioms EffectCoreV1.AttackT004X.bPut_complete
#print axioms EffectCoreV1.AttackT004X.uGet_nodup
#print axioms EffectCoreV1.AttackT004X.bPut_nodup
#print axioms EffectCoreV1.AttackT004X.uGet_injective
#print axioms EffectCoreV1.AttackT004X.bPut_injective
#print axioms EffectCoreV1.AttackT004X.uGet_bPut_disjoint
#print axioms EffectCoreV1.AttackT004X.premises_are_jointly_inhabited
#print axioms EffectCoreV1.AttackT004X.headline_has_a_nondegenerate_instance
#print axioms EffectCoreV1.AttackT004X.conjuncts_1_4_5_depend_only_on_the_sig_field
#print axioms EffectCoreV1.AttackT004X.extendConst_satisfies_1_4_5
#print axioms EffectCoreV1.AttackT004X.extendConst_breaks_2_and_3
#print axioms EffectCoreV1.AttackT004X.eight_conjuncts_are_six
#print axioms EffectCoreV1.AttackT004X.dupIds_disjoint_bPut
#print axioms EffectCoreV1.AttackT004X.bPut_disjoint_dupIds
#print axioms EffectCoreV1.AttackT004X.right_enumComplete_premise_is_necessary
#print axioms EffectCoreV1.AttackT004X.right_enumNodup_premise_is_necessary
#print axioms EffectCoreV1.AttackT004X.left_idsInjective_premise_is_necessary
#print axioms EffectCoreV1.AttackT004X.right_idsInjective_premise_is_necessary
#print axioms EffectCoreV1.AttackT004X.equation_is_blind_to_arm_order
#print axioms EffectCoreV1.AttackT004X.enumeration_is_order_sensitive
#print axioms EffectCoreV1.AttackT004X.sum_keeps_both_arms_answerable
#print axioms EffectCoreV1.AttackT004X.flattening_collapses_every_handler
#print axioms EffectCoreV1.AttackT004X.flattening_loses_the_right_arm
#print axioms EffectCoreV1.AttackT004X.self_extension_is_never_admissible
#print axioms EffectCoreV1.AttackT004X.uGet_cannot_extend_itself
#print axioms EffectCoreV1.AttackT004X.sum_unique_hypothesis_is_inhabited
#print axioms EffectCoreV1.AttackT004X.inl_unique_hypothesis_is_inhabited
#print axioms EffectCoreV1.AttackT004X.inr_unique_hypothesis_is_inhabited
#print axioms EffectCoreV1.AttackT004X.Derived.derived_extend_is_order_sensitive
#print axioms EffectCoreV1.AttackT004X.Derived.disjoint_arms_are_in_bijection
