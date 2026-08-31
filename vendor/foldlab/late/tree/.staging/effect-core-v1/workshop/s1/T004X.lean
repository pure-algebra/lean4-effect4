import Cas.Backend.SumAlgebra

/-!
# `EC1-T004X` — `alphabet_sum_preserves_arms`

Run from `library/cas`:

```
lake env lean ../../.staging/effect-core-v1/workshop/s1/T004X.lean
```

Skill stage: **`lean-algebraic-systems`** (the row is about operations, their
composition, and the interpreters that project out of a composed signature —
not about a data invariant). Its gate wants constructor/step equations and
composition laws, interpreter preservation/homomorphism laws, and deliberately
invalid programs beside the positive ones. §2–§7 supply the first two; §4.3,
§5.2 and §8 supply the third.

## The DAG row

`PROOF-DAG.md:195`

```text
EC1-T004X | alphabet_sum_preserves_arms :
  extend a b |>.toSig = a.toSig ⊕ₛ b.toSig
  "with left/right metadata and handler projections"
  depends on: existing Sig.sum, Handler.sum, Prog.inl/inr laws
```

`PROOF-DAG.md` §16 routes the family as *"pending condition 14: neutral
protocol identity plus explicit admission bridge for Lean-modeled operations to
existing `Sig.Op`; preserve `Sig.sum` with left/right laws"*, and prohibits
*"pretending every protocol identity already has a `Sig.Op`, or
modifying/replacing `Sig` to carry classification grades or flattening
Root/Word extensions"*. Nothing below modifies `Sig`, adds a field to it, or
flattens an extension arm; `Sig`, `Sig.sum`, `Handler`, `Handler.sum`, `Prog`,
`Prog.inl`/`Prog.inr` and `interpret` are used exactly as shipped, and the
stable protocol identifier is kept in `OpDesc` as a SEPARATE column with its own
obligation (§5) precisely so it is not confused with a `Sig.Op`.

## Carrier status — read this before reading a theorem

`EC1-D010 Alphabet` and `EC1-D011 OpDesc` **do not exist**. Verified this pass:
`grep -rn 'Alphabet' library/cas/Cas library/cas/tools` returns zero hits, and
`formal/effect-core-v1/EffectCore/Foundation/Alphabet.lean` is an 11-line
docstring stub with an empty namespace. §17 freeze condition 14 is **OPEN**.

So §1 builds a local model, first-order and minimal, transcribed from
`ALGEBRA.md` §2.2's own description of the candidate:

> content with a version, an existing semantic `Cas.Lang.Sig`, a finite
> canonical enumeration of that signature's `Sig.Op`, and a sorted dependent
> table of `EC1-A07 OpDesc` records

and from `ALGEBRA.md:166-168`:

> `Alphabet.toSig` returns this existing semantic signature; it does not create
> a replacement handler language. Extension is `Sig.sum`/`⊕ₛ`, with metadata
> reindexed over the left and right injections.

**Every theorem here is a theorem about that local model and about nothing
else.** It is not assurance about `EC1-D010`, and a green check does not close
the DAG row. What it does establish is what the row's statement is worth once a
carrier of this shape exists, and — in §8 — that the row is FALSE at the other
carrier freeze condition 14 leaves open.

## What is proved

| § | Result | Cost |
| --- | --- | --- |
| 2 | the DAG's equation, **premise-free** | `rfl` |
| 2 | ...and it is blind to metadata and to identifier collisions | witnesses |
| 3 | left/right metadata, answer-type and identifier arm laws | `rfl` |
| 4 | the canonical enumeration stays complete and duplicate-free | real induction-free proof; premises proved necessary |
| 5 | the extended stable-identifier map stays injective | real; premise proved necessary |
| 6 | **`alphabet_extend_preserves_arms`** — the bundle | — |
| 7 | handler and program projections AT THE EXTENDED ALPHABET | estate theorems, verbatim proof terms |
| 8 | **the equation is FALSE at the derived (partial-table) carrier** | kernel witness |

The headline equation is `rfl` and carries nothing: §2.2 and §2.3 exhibit two
alphabets it cannot tell apart, one pair differing in handler routing and one
pair colliding on a stable operation identifier. The row's content is entirely
in §4, §5 and §7, and §8 is why the carrier choice is load-bearing rather than
incidental.

Receipts at the foot: `#print axioms` on every theorem. Ceiling `propext` /
`Quot.sound`; no `sorryAx`, no `Classical.choice`, no `native_decide`, no
`#eval` carrying a claim.
-/

namespace EffectCoreT004X

open Cas.Lang

/-! ## §1 — the carrier

First-order metadata, an existing `Cas.Lang.Sig`, a finite enumeration of its
operations, and a total dependent descriptor table. Nothing here is proposed
for `library/` or for `formal/`; `EFFECTS-BACKEND` R14a keeps it outside `Prog`
as plain definitions on first-order data, which is what it is. -/

/-- `ALGEBRA.md` §2.2's `handlerRoute` column. -/
inductive HandlerRoute where
  | builtin (handlerId : String)
  | service (serviceKey : String)
  deriving DecidableEq, Repr

/-- `ALGEBRA.md` §2.2's `resumption` column. `EC1-R17` admits only `zero` and
`one` in v1; `many` stays representable so the checker can refuse it. That
ruling is not exercised here — this column is carried only to give the arm laws
of §3 more than one thing to say. -/
inductive Resumption where
  | zero | one | many
  deriving DecidableEq, Repr

/-- `ALGEBRA.md` §2.2's `observation` column. `pub` spells the packet's
`public`, which is not available as a Lean identifier. -/
inductive Observation where
  | pub | receiptOnly | hidden
  deriving DecidableEq, Repr

/-- `EC1-A07 OpDesc`, first-order and cut down.

OMITTED DELIBERATELY, and this is a real omission rather than an abbreviation:
`requestTy`, `answerTy`, `errorRow`, `requirementRow`. Those need `EC1-D001
ValueTy`, `EC1-D003 ErrorRow` and `EC1-D004 RequirementRow`, none of which
exist, and the `answerTy`-denotes-`Sig.Ans` bridge is `EC1-T004S`'s row, not
this one. Carrying a fake `answerTy` here would prejudge that row. -/
structure OpDesc where
  /-- The stable protocol operation identifier. NOT a `Sig.Op`: keeping it a
  separate column is exactly §16's "explicit admission bridge" discipline, and
  §5 is the obligation that separation creates. -/
  opId : String
  handlerRoute : HandlerRoute
  resumption : Resumption
  observation : Observation
  deriving DecidableEq, Repr

/-- `EC1-A06 Alphabet`, as `ALGEBRA.md` §2.2 describes it: an EXISTING semantic
signature, a finite canonical enumeration of its operations, and a total
dependent descriptor table over them.

The table is TOTAL (`sig.Op → OpDesc`) rather than an association list. That is
the estate's own registry shape — `Cas/Schema/Declarations.lean:159`
`DeclarationId.arity` and `:166 payloadWf` are total metadata maps by pattern
match over a closed inductive, with the enumeration's duplicate-freedom checked
separately at `:207`. §8 shows what happens to this row under the other shape.

The `version` field is omitted: it plays no part in the row, and inventing a
composition law for it would be minting. -/
structure Alphabet where
  sig : Sig
  ops : List sig.Op
  desc : sig.Op → OpDesc

/-- `Alphabet.toSig` RETURNS the existing signature. It does not build one.
This is `ALGEBRA.md:166` verbatim, and it is what keeps `EC1-T004RW`'s
`StoreSig`/`WordedSig` identities available downstream. -/
def Alphabet.toSig (a : Alphabet) : Sig := a.sig

/-- The stable identifier map induced by the descriptor table. -/
def Alphabet.opId (a : Alphabet) (op : a.toSig.Op) : String := (a.desc op).opId

/-- The enumeration names every operation of the signature. -/
def Alphabet.EnumComplete (a : Alphabet) : Prop := ∀ op : a.toSig.Op, op ∈ a.ops

/-- The enumeration names each operation once. -/
def Alphabet.EnumNodup (a : Alphabet) : Prop := a.ops.Nodup

/-- Distinct operations publish distinct stable identifiers. -/
def Alphabet.IdsInjective (a : Alphabet) : Prop := Function.Injective a.opId

/-- Two alphabets publish no identifier in common. -/
def Alphabet.IdsDisjoint (a b : Alphabet) : Prop :=
  ∀ (i : a.toSig.Op) (j : b.toSig.Op), a.opId i ≠ b.opId j

/-- **Extension**, exactly as `ALGEBRA.md:167` specifies it: the signature is
`Sig.sum`, and the metadata is reindexed over the left and right injections.

`Sig` is not modified, no second signature type is minted, and neither arm is
flattened — the sum is the shipped `Sig.sum` and the arms stay tagged. -/
def Alphabet.extend (a b : Alphabet) : Alphabet where
  sig := a.sig ⊕ₛ b.sig
  ops := a.ops.map Sum.inl ++ b.ops.map Sum.inr
  desc := Sum.elim a.desc b.desc

/-! ## §2 — the DAG's equation, and what it is worth

### §2.1 the equation itself -/

/-- **`EC1-T004X`, signature clause.** The row as the DAG writes it.

It takes NO premise, and its proof is `rfl`. Under the packet's own carrier the
headline equation is a definitional identity, not a theorem: `extend` was
DEFINED by `Sig.sum`, so the equation records that definition rather than
constraining it. That is the whole of what the schematic row says. -/
theorem extend_toSig (a b : Alphabet) :
    (a.extend b).toSig = a.toSig ⊕ₛ b.toSig := rfl

/-- The operation universe of the extended alphabet is the tagged sum, again
definitionally. This is the fact every projection in §7 stands on. -/
theorem extend_toSig_Op (a b : Alphabet) :
    (a.extend b).toSig.Op = (a.toSig.Op ⊕ b.toSig.Op) := rfl

/-! ### §2.2 the equation cannot see metadata

`Sig` has exactly two fields, `Op` and `Ans` (`Cas/Lang/Sig.lean:13`). Every
column of `OpDesc` is outside it, so the row's prose clause "with left/right
metadata" is not something the stated equation can express. Two witnesses. -/

/-- The one-operation signature used by the witnesses below. -/
def unitSig : Sig := ⟨Unit, fun _ => Unit⟩

/-- A one-operation alphabet publishing `"get"` through a builtin handler. -/
def aBuiltin : Alphabet where
  sig := unitSig
  ops := [()]
  desc := fun _ => ⟨"get", .builtin "getHandler", .one, .pub⟩

/-- The same operation, routed to a SERVICE instead. -/
def aService : Alphabet where
  sig := unitSig
  ops := [()]
  desc := fun _ => ⟨"get", .service "GetService", .one, .pub⟩

/-- **Finding 1 — the equation is metadata-blind.** Two alphabets that route
the same operation to opposite sides of `handlerRoute` have the same `toSig`.
Whatever the schematic row proves, it proves nothing about the descriptor
table, so the row's "left/right metadata" clause must be stated separately —
which is §3. -/
theorem equation_is_metadata_blind :
    aBuiltin.toSig = aService.toSig
      ∧ (aBuiltin.desc ()).handlerRoute ≠ (aService.desc ()).handlerRoute := by
  refine ⟨rfl, ?_⟩
  intro h
  exact absurd h (by decide)

/-! ### §2.3 the equation cannot see an identifier collision

`Sig.sum` tags by POSITION. Two arms that publish the same stable operation
identifier are summed without complaint, and the resulting alphabet has two
operations with one public identity — which breaks `EFFECTS-BACKEND` R4
(identity hashes presentations) and any generated handler or wire table keyed
by that identifier. `EC1-F87` guards this seam. -/

/-- Left arm publishing `"get"`. -/
def uGet : Alphabet where
  sig := unitSig
  ops := [()]
  desc := fun _ => ⟨"get", .builtin "L", .one, .pub⟩

/-- Right arm publishing `"get"` as well, routed elsewhere. -/
def vGet : Alphabet where
  sig := unitSig
  ops := [()]
  desc := fun _ => ⟨"get", .service "R", .one, .pub⟩

/-- **Finding 2 — the equation is blind to an identifier collision.** The row's
equation HOLDS of a pair of arms that publish one identifier twice. The
obligation that excludes them is §5, and no equation between `Sig`s can state
it. -/
theorem equation_is_blind_to_id_collision :
    ((uGet.extend vGet).toSig = uGet.toSig ⊕ₛ vGet.toSig)
      ∧ ¬ uGet.IdsDisjoint vGet := by
  refine ⟨rfl, fun h => ?_⟩
  exact h () () rfl

/-! ## §3 — the arm laws: metadata, answers, identifiers

The row's second clause. Each is `rfl`, because `extend` reindexes by
`Sum.elim`; they are stated anyway because the equation of §2 does not imply
them and a different `extend` would break them silently. -/

/-- **Left metadata arm law.** -/
theorem extend_desc_inl (a b : Alphabet) (op : a.toSig.Op) :
    (a.extend b).desc (Sum.inl op) = a.desc op := rfl

/-- **Right metadata arm law.** -/
theorem extend_desc_inr (a b : Alphabet) (op : b.toSig.Op) :
    (a.extend b).desc (Sum.inr op) = b.desc op := rfl

/-- **Left answer-type arm law.** An equality of TYPES, and the fact that makes
`Handler` and `Prog` transport in §7 typecheck at all. -/
theorem extend_ans_inl (a b : Alphabet) (op : a.toSig.Op) :
    (a.extend b).toSig.Ans (Sum.inl op) = a.toSig.Ans op := rfl

/-- **Right answer-type arm law.** -/
theorem extend_ans_inr (a b : Alphabet) (op : b.toSig.Op) :
    (a.extend b).toSig.Ans (Sum.inr op) = b.toSig.Ans op := rfl

/-- Left identifier arm law. -/
theorem extend_opId_inl (a b : Alphabet) (op : a.toSig.Op) :
    (a.extend b).opId (Sum.inl op) = a.opId op := rfl

/-- Right identifier arm law. -/
theorem extend_opId_inr (a b : Alphabet) (op : b.toSig.Op) :
    (a.extend b).opId (Sum.inr op) = b.opId op := rfl

/-! ## §4 — the canonical enumeration is preserved

`ALGEBRA.md` §2.2 makes "a finite canonical enumeration of that signature's
`Sig.Op`" part of the alphabet. This is the first clause of the row that is NOT
`rfl`, and it is the clause the phrase "preserves arms" is actually about: after
extension the enumeration must still name every operation, and still name each
one once.

The estate's model is `Cas/Schema/Declarations.lean:202 DeclarationId.all_complete`
(completeness, by `cases d <;> decide` over a closed inductive) together with
the `#guard` at `:207` (duplicate-freedom, at elaboration time). Under
composition neither is free. -/

/-- **Completeness is preserved.** -/
theorem extend_enumComplete (a b : Alphabet)
    (ha : a.EnumComplete) (hb : b.EnumComplete) : (a.extend b).EnumComplete := by
  rintro (x | y)
  · exact List.mem_append_left _ (List.mem_map_of_mem (ha x))
  · exact List.mem_append_right _ (List.mem_map_of_mem (hb y))

/-- **Duplicate-freedom is preserved.** The cross-arm clause is where `Sig.sum`
earns its keep: the tag makes the two arms' enumerations disjoint no matter what
the arms contain. -/
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

/-! ### §4.3 both premises are load-bearing

Deliberately invalid alphabets, per the `lean-algebraic-systems` gate. -/

/-- An alphabet whose enumeration omits its only operation. -/
def missingOp : Alphabet where
  sig := unitSig
  ops := []
  desc := fun _ => ⟨"missing", .builtin "M", .one, .pub⟩

/-- An alphabet whose enumeration lists its only operation twice. -/
def dupOp : Alphabet where
  sig := unitSig
  ops := [(), ()]
  desc := fun _ => ⟨"dup", .builtin "D", .one, .pub⟩

/-- `aBuiltin`'s enumeration is complete and duplicate-free — the positive
control, so §4.3's negatives are not vacuous. -/
theorem aBuiltin_enum_ok : aBuiltin.EnumComplete ∧ aBuiltin.EnumNodup := by
  refine ⟨?_, ?_⟩
  · intro op
    cases op
    exact List.mem_singleton_self _
  · show List.Nodup ([()] : List Unit)
    simp

/-- **The completeness premise is necessary.** Dropping it admits an extended
alphabet whose enumeration does not name one of its operations, so any
totality or code-generation table driven by the enumeration silently omits a
row. -/
theorem enumComplete_premise_is_necessary :
    ¬ ∀ (a b : Alphabet), b.EnumComplete → (a.extend b).EnumComplete := by
  intro h
  have hbad := h missingOp aBuiltin aBuiltin_enum_ok.1 (Sum.inl ())
  revert hbad
  show ¬ ((Sum.inl () : Unit ⊕ Unit) ∈ ([Sum.inr ()] : List (Unit ⊕ Unit)))
  simp

/-- **The duplicate-freedom premise is necessary.** -/
theorem enumNodup_premise_is_necessary :
    ¬ ∀ (a b : Alphabet), b.EnumNodup → (a.extend b).EnumNodup := by
  intro h
  have hbad := h dupOp aBuiltin aBuiltin_enum_ok.2
  revert hbad
  show ¬ (List.Nodup ([Sum.inl (), Sum.inl (), Sum.inr ()] : List (Unit ⊕ Unit)))
  simp

/-! ## §5 — the obligation the equation is blind to

`Sig.sum` tags by position; the stable protocol identifier is a separate column
(§16's "explicit admission bridge", kept explicit precisely so that a protocol
identity is not mistaken for a `Sig.Op`). Composition can therefore produce an
alphabet with two operations and one public identity. This is the alphabet-level
transplant of `EC1-CE030`'s ruled repair — *"add a duplicate-free premise or make
row validity supply it"* — one carrier up. -/

/-- **The identifier obligation.** The extended alphabet publishes distinct
identifiers for distinct operations exactly when each arm does and the arms are
id-disjoint. -/
theorem extend_opId_injective (a b : Alphabet)
    (ha : a.IdsInjective) (hb : b.IdsInjective) (hd : a.IdsDisjoint b) :
    (a.extend b).IdsInjective := by
  rintro (x | x) (y | y) h
  · exact congrArg Sum.inl (ha h)
  · exact absurd h (hd x y)
  · exact absurd h.symm (hd y x)
  · exact congrArg Sum.inr (hb h)

/-- Each arm here is trivially id-injective — its operation universe is a
singleton — so the collision in `id_disjointness_is_necessary` is caused by the
disjointness failure alone and by nothing else. -/
theorem uGet_vGet_arms_are_injective : uGet.IdsInjective ∧ vGet.IdsInjective := by
  constructor
  · intro x y _; cases x; cases y; rfl
  · intro x y _; cases x; cases y; rfl

/-- **The disjointness premise is necessary, and the failure survives the sum.**
Two arms publish `"get"`; `Sig.sum` admits them (§2.3); the extended identifier
map is not injective. This is the content `EC1-T004X` should carry and its
stated equation cannot. -/
theorem id_disjointness_is_necessary :
    ¬ ∀ (a b : Alphabet),
        a.IdsInjective → b.IdsInjective → (a.extend b).IdsInjective := by
  intro h
  have hinj := h uGet vGet uGet_vGet_arms_are_injective.1 uGet_vGet_arms_are_injective.2
  have hcol : (uGet.extend vGet).opId (Sum.inl ()) = (uGet.extend vGet).opId (Sum.inr ()) :=
    rfl
  exact absurd (hinj hcol) (by simp)

/-! ## §6 — the row, restated and proved

`EC1-T004X` as it should be spelled. Conjunct (1) is the DAG's signature
equation, unchanged; conjuncts (2)-(5) are the "left/right metadata" clause made
into propositions; conjuncts (6)-(8) are what "preserves arms" has to mean once
the alphabet carries an enumeration and a stable identifier column.

PREMISE ACCOUNTING, so nothing is credited to the wrong conjunct. Conjuncts
(1)-(5) use NO premise: they are `rfl` and hold of every pair of alphabets.
`hea`/`heb` are used only by (6), `hna`/`hnb` only by (7), and
`hia`/`hib`/`hd` only by (8). §4.3 and §5.2 prove each of those five load-bearing
by exhibiting an alphabet pair that fails the corresponding conjunct. -/
theorem alphabet_extend_preserves_arms (a b : Alphabet)
    (hea : a.EnumComplete) (heb : b.EnumComplete)
    (hna : a.EnumNodup) (hnb : b.EnumNodup)
    (hia : a.IdsInjective) (hib : b.IdsInjective)
    (hd : a.IdsDisjoint b) :
    -- (1) the DAG's signature equation
    ((a.extend b).toSig = a.toSig ⊕ₛ b.toSig)
    -- (2,3) left/right metadata arm laws
      ∧ (∀ op : a.toSig.Op, (a.extend b).desc (Sum.inl op) = a.desc op)
      ∧ (∀ op : b.toSig.Op, (a.extend b).desc (Sum.inr op) = b.desc op)
    -- (4,5) left/right answer-type arm laws
      ∧ (∀ op : a.toSig.Op, (a.extend b).toSig.Ans (Sum.inl op) = a.toSig.Ans op)
      ∧ (∀ op : b.toSig.Op, (a.extend b).toSig.Ans (Sum.inr op) = b.toSig.Ans op)
    -- (6,7) the canonical enumeration survives extension
      ∧ (a.extend b).EnumComplete
      ∧ (a.extend b).EnumNodup
    -- (8) and so does the stable-identifier discipline
      ∧ (a.extend b).IdsInjective :=
  ⟨extend_toSig a b,
   extend_desc_inl a b, extend_desc_inr a b,
   extend_ans_inl a b, extend_ans_inr a b,
   extend_enumComplete a b hea heb,
   extend_enumNodup a b hna hnb,
   extend_opId_injective a b hia hib hd⟩

/-! ## §7 — handler and program projections at the EXTENDED alphabet

The row's third clause, and the reason the equation is worth having at all:
because `(a.extend b).toSig` is DEFINITIONALLY `a.toSig ⊕ₛ b.toSig`, the whole
of `Cas/Backend/SumAlgebra.lean` applies to an extended alphabet with no
transport, no coercion, and no new proof. Every proof term below is a shipped
estate theorem, unmodified.

Note the direction of the dependency: this is bought by DEFINING `extend`
through `Sig.sum`, not by proving anything. §8 shows an `extend` for which it is
unavailable. -/

section Projections

variable {M : Type → Type v}

/-- The summed handler, TYPED at the extended alphabet. This definition
typechecks only because of `extend_toSig`. -/
def extendHandler (a b : Alphabet) (h : Handler a.toSig M) (g : Handler b.toSig M) :
    Handler (a.extend b).toSig M := h.sum g

/-- A left-arm program IS a program of the extended alphabet. -/
def extendInl {A : Type u} (a b : Alphabet) (p : Prog a.toSig A) :
    Prog (a.extend b).toSig A := Prog.inl p

/-- A right-arm program, likewise. -/
def extendInr {A : Type u} (a b : Alphabet) (q : Prog b.toSig A) :
    Prog (a.extend b).toSig A := Prog.inr q

/-- **L21 at the extended alphabet** (`Cas/Backend/SumAlgebra.lean:196`). -/
theorem extend_handler_projects_left (a b : Alphabet)
    (h : Handler a.toSig M) (g : Handler b.toSig M) (op : a.toSig.Op) :
    (extendHandler a b h g).handle (Sum.inl op) = h.handle op :=
  Handler.sum_handle_inl h g op

/-- **L22 at the extended alphabet** (`:202`). The row that kills an `extend`
which quietly discards the right arm's handler. -/
theorem extend_handler_projects_right (a b : Alphabet)
    (h : Handler a.toSig M) (g : Handler b.toSig M) (op : b.toSig.Op) :
    (extendHandler a b h g).handle (Sum.inr op) = g.handle op :=
  Handler.sum_handle_inr h g op

/-- **ADQ-SUM at the extended alphabet** (`:212`). L21/L22 do not merely hold of
`extendHandler`, they DETERMINE it: no wrong-but-passing composition exists. -/
theorem extend_handler_unique (a b : Alphabet)
    (h : Handler a.toSig M) (g : Handler b.toSig M)
    (k : Handler (a.extend b).toSig M)
    (hl : ∀ op : a.toSig.Op, k.handle (Sum.inl op) = h.handle op)
    (hr : ∀ op : b.toSig.Op, k.handle (Sum.inr op) = g.handle op) :
    k = extendHandler a b h g :=
  Handler.sum_unique h g k hl hr

/-- **L23 at the extended alphabet** (`:231`) — the interpreter homomorphism
law the `lean-algebraic-systems` gate asks for, on the left arm. -/
theorem extend_interpret_left [Monad M] {A : Type} (a b : Alphabet)
    (h : Handler a.toSig M) (g : Handler b.toSig M) (p : Prog a.toSig A) :
    interpret (extendHandler a b h g) (extendInl a b p) = interpret h p :=
  interpret_inl h g p

/-- **L24 at the extended alphabet** (`:239`). -/
theorem extend_interpret_right [Monad M] {A : Type} (a b : Alphabet)
    (h : Handler a.toSig M) (g : Handler b.toSig M) (q : Prog b.toSig A) :
    interpret (extendHandler a b h g) (extendInr a b q) = interpret g q :=
  interpret_inr h g q

end Projections

/-- **ADQ-INL at the extended alphabet** (`Cas/Backend/SumAlgebra.lean:427`).
Any injection of left-arm programs into the extended alphabet that interprets
correctly IS `extendInl`. Stated at `Type` because `Prog.inl_unique` is. -/
theorem extend_inl_unique (a b : Alphabet)
    (ι : {A : Type} → Prog a.toSig A → Prog (a.extend b).toSig A)
    (hι : ∀ (M : Type → Type) [Monad M] [LawfulMonad M]
            (h : Handler a.toSig M) (g : Handler b.toSig M)
            {A : Type} (p : Prog a.toSig A),
            interpret (h.sum g) (ι p) = interpret h p)
    {A : Type} (p : Prog a.toSig A) : ι p = extendInl a b p :=
  Prog.inl_unique ι hι p

/-- **ADQ-INR at the extended alphabet** (`:460`). -/
theorem extend_inr_unique (a b : Alphabet)
    (ι : {A : Type} → Prog b.toSig A → Prog (a.extend b).toSig A)
    (hι : ∀ (M : Type → Type) [Monad M] [LawfulMonad M]
            (h : Handler a.toSig M) (g : Handler b.toSig M)
            {A : Type} (q : Prog b.toSig A),
            interpret (h.sum g) (ι q) = interpret g q)
    {A : Type} (q : Prog b.toSig A) : ι q = extendInr a b q :=
  Prog.inr_unique ι hι q

/-- The estate's arm-swapping adversary, re-checked here so §7's projections are
not vacuous: without L21 an implementation that exchanges the arms satisfies
everything else known about a summed handler. Owned by
`Cas/Backend/SumAlgebra.lean:685`; `COUNTEREXAMPLES.md` §9 names that file as
the canonical owner of this family, so it is cited rather than copied. Its
siblings — `doubleInl_not_interpret_inl` (`:790`),
`badAgentSum_not_interpret_inr` (`:753`), `narrowing_to_Id_fails` (`:966`) —
guard the other three. -/
theorem estate_arm_swap_adversary_is_live :
    ¬ (∀ (S : Sig) (M : Type → Type) [Monad M] (h g : Handler S M) (op : S.Op),
         (Adversary.swapSum h g).handle (Sum.inl op) = h.handle op) :=
  Adversary.swapSum_not_sum_handle_inl

/-! ## §8 — the equation is FALSE at the other carrier

Freeze condition 14 is OPEN, so the shape of `Alphabet.toSig` is not decided.
§1 took `ALGEBRA.md` §2.2's reading: the alphabet CARRIES an existing `Sig` and
the descriptor table is total over it. The competing reading — the one an
`Option`-valued `lookup` forces, and the one `EC1-T004`'s own signature
(`lookup a op = some d`) implies — DERIVES the signature from an association
table, taking the operation universe to be the subtype of identifiers the table
declares. It has to: `Sig.Ans : Op → Type` is total by typing while `lookup` is
partial, so the found-ness proof must travel inside the operation.

Under that reading the only composition a flat table admits is concatenation,
and concatenation COLLAPSES an operation the two arms share while `Sig.sum`
keeps both, tagged. The row is then false. -/

namespace Derived

/-- Scratch operation identities. -/
inductive OpId where
  | get | put
  deriving DecidableEq, Repr

/-- Scratch first-order answer codes, standing in for `EC1-D001 ValueTy`. -/
inductive AnsCode where
  | nat | str
  deriving DecidableEq, Repr

/-- Their meaning. Answers factor through a first-order code universe, which is
`EFFECTS-BACKEND` R14a paying for itself: it is what would make an arm-wise
answer-type law provable here at all. -/
def AnsCode.interp : AnsCode → Type
  | .nat => Nat
  | .str => String

/-- A row of the association table. -/
structure Row where
  op : OpId
  answerTy : AnsCode
  route : HandlerRoute
  deriving DecidableEq, Repr

/-- The competing carrier: a flat keyed table, no stored signature. -/
structure PartialAlphabet where
  table : List Row

/-- Partial, `Option`-valued lookup — `EC1-T004`'s `lookup a op = some d`. -/
def PartialAlphabet.lookup (a : PartialAlphabet) (op : OpId) : Option Row :=
  a.table.find? (fun d => decide (d.op = op))

/-- The derived signature: operations are the DECLARED identifiers, carrying
their own found-ness, because `Sig.Ans` is total. `Sig` itself is untouched. -/
def PartialAlphabet.toSig (a : PartialAlphabet) : Sig where
  Op := { op : OpId // (a.lookup op).isSome = true }
  Ans := fun op => AnsCode.interp ((a.lookup op.1).get op.2).answerTy

/-- The only composition a flat table admits. -/
def PartialAlphabet.extend (a b : PartialAlphabet) : PartialAlphabet :=
  ⟨a.table ++ b.table⟩

/-- Left arm: `get`, routed to a builtin. -/
def aGet : PartialAlphabet := ⟨[⟨.get, .nat, .builtin "L"⟩]⟩

/-- Right arm: the same operation, routed to a service. Nothing in the packet
forbids this — the arms are authored independently and `Sig.sum` tags by
position, not by identifier. -/
def bGet : PartialAlphabet := ⟨[⟨.get, .nat, .service "R"⟩]⟩

/-- Lean has no univalence, so equivalent types are not equal; unequal
cardinality still gives a kernel-checkable inequality, which is all §8 needs. -/
theorem type_ne_of_subsingleton_of_two {α β : Type}
    (hα : ∀ x y : α, x = y) {u v : β} (huv : u ≠ v) : α ≠ β := by
  intro h
  subst h
  exact huv (hα u v)

/-- Every operation of the concatenated table is `get`: `put` is undeclared. -/
theorem extend_op_is_get (x : (aGet.extend bGet).toSig.Op) : x.1 = OpId.get := by
  obtain ⟨u, hu⟩ := x
  cases u
  · rfl
  · exact absurd hu (by decide)

/-- So the extended alphabet's operation universe is a subsingleton — the shared
operation was collapsed. -/
theorem extend_op_subsingleton (x y : (aGet.extend bGet).toSig.Op) : x = y :=
  Subtype.ext ((extend_op_is_get x).trans (extend_op_is_get y).symm)

/-- The left arm's `get`. -/
def lGet : aGet.toSig.Op := ⟨.get, by decide⟩

/-- The right arm's `get`. -/
def rGet : bGet.toSig.Op := ⟨.get, by decide⟩

/-- The summed signature keeps both arms' `get`, tagged. -/
theorem sum_op_has_two :
    (Sum.inl lGet : aGet.toSig.Op ⊕ bGet.toSig.Op) ≠ Sum.inr rGet := by
  simp

/-- **THE REFUTATION.** At the derived carrier the DAG's equation is FALSE, at
the smallest possible witness: one operation per arm, shared. The left side is a
subsingleton, the right side has two elements, and unequal cardinality gives
unequal types.

Consequence for the packet: `EC1-T004X` is not a row that becomes provable once
a carrier lands. Its truth is DECIDED by freeze condition 14. Under §1's reading
it is `rfl` and carries nothing; under this one it is refuted. Either way the
schematic equation is the wrong thing to have written down, and the obligations
that survive are §4, §5 and §7.

Not registered as a counterexample here: this is a candidate row against the
statement as written, not against the intended statement, and it needs an id
above the register's current maximum. -/
theorem T004X_false_at_the_derived_carrier :
    (aGet.extend bGet).toSig ≠ aGet.toSig ⊕ₛ bGet.toSig := by
  intro h
  exact type_ne_of_subsingleton_of_two
    extend_op_subsingleton sum_op_has_two (congrArg Sig.Op h)

/-- And the metadata half fails with it: concatenation resolves the shared
operation to the LEFT arm's row, so the right arm's routing is silently
discarded. A generated handler table built from the right arm's metadata would
route the operation to the wrong side. This is `EC1-CE030`'s duplicate-key
lesson at the alphabet carrier, with an independent witness. -/
theorem derived_right_arm_metadata_is_lost :
    (aGet.extend bGet).lookup .get = some ⟨.get, .nat, .builtin "L"⟩
      ∧ bGet.lookup .get = some ⟨.get, .nat, .service "R"⟩ := by
  constructor <;> rfl

end Derived

end EffectCoreT004X

/-! ## Kernel receipts -/

#print axioms EffectCoreT004X.extend_toSig
#print axioms EffectCoreT004X.extend_toSig_Op
#print axioms EffectCoreT004X.equation_is_metadata_blind
#print axioms EffectCoreT004X.equation_is_blind_to_id_collision
#print axioms EffectCoreT004X.extend_desc_inl
#print axioms EffectCoreT004X.extend_desc_inr
#print axioms EffectCoreT004X.extend_ans_inl
#print axioms EffectCoreT004X.extend_ans_inr
#print axioms EffectCoreT004X.extend_opId_inl
#print axioms EffectCoreT004X.extend_opId_inr
#print axioms EffectCoreT004X.extend_enumComplete
#print axioms EffectCoreT004X.extend_enumNodup
#print axioms EffectCoreT004X.aBuiltin_enum_ok
#print axioms EffectCoreT004X.enumComplete_premise_is_necessary
#print axioms EffectCoreT004X.enumNodup_premise_is_necessary
#print axioms EffectCoreT004X.extend_opId_injective
#print axioms EffectCoreT004X.uGet_vGet_arms_are_injective
#print axioms EffectCoreT004X.id_disjointness_is_necessary
#print axioms EffectCoreT004X.alphabet_extend_preserves_arms
#print axioms EffectCoreT004X.extend_handler_projects_left
#print axioms EffectCoreT004X.extend_handler_projects_right
#print axioms EffectCoreT004X.extend_handler_unique
#print axioms EffectCoreT004X.extend_interpret_left
#print axioms EffectCoreT004X.extend_interpret_right
#print axioms EffectCoreT004X.extend_inl_unique
#print axioms EffectCoreT004X.extend_inr_unique
#print axioms EffectCoreT004X.estate_arm_swap_adversary_is_live
#print axioms EffectCoreT004X.Derived.type_ne_of_subsingleton_of_two
#print axioms EffectCoreT004X.Derived.extend_op_is_get
#print axioms EffectCoreT004X.Derived.extend_op_subsingleton
#print axioms EffectCoreT004X.Derived.sum_op_has_two
#print axioms EffectCoreT004X.Derived.T004X_false_at_the_derived_carrier
#print axioms EffectCoreT004X.Derived.derived_right_arm_metadata_is_lost
