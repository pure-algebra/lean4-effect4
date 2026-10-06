import Effect4.Program.UnionRule
import Effect4.Laws.Program.Template
import Effect4.Laws.Auto.Semantics

/-!
# Laws.Program.UnionRule — the laws of a rule that reads a union member by member

The combinator is `UnionRule.lift` (`src/Effect4/Program/UnionRule.lean`): a member rule read at
every union member of the target's normal form, with the answers joined. This file proves its
laws once, for every member rule and every carrier of answers. An instance then owes the facts
of its member rule and nothing about unions. A member fact is stated at a normal union member:
each premise below may assume `Ty.Normal m` and `m.isMember = true`.

The laws, in order:

- **Total at `never`** (`lift_never`): the lifted rule answers the least answer.
- **One member** (`lift_member`): at a normal type that is one union member, the lifted rule is
  the member rule, up to the join with the least answer.
- **Normal form** (`lift_congr`): two types with one normal form have one answer.
- **Monotone** (`lift_mono`): where one member rule answers below another at each pair of normal
  union members in the order (`Below`), a smaller target has an answer where a larger one has,
  and the answer is smaller.
- **Transfer** (`lift_transfer`): a property of a value and an answer that the join keeps on
  each side passes from each union member to the lifted rule. `ReadsUnion.lift_sound` is its form
  for an operation on values: a member rule that is sound against a membership relation at each
  union member lifts to a rule that is sound against it.
- **Every member** (`lift_all`): a property of answers that the least answer has, and that the
  join of two answers with it has, holds of the lifted answer where each union member's answer
  has it. Closed types are the instance (`lift_closed`, `lift_closed_pair`).
- **Upper form** (`lift_upper`, `lift_least`): for a member rule with a map `C` from answers
  back into types, the lifted rule's answer `a` puts the target below `C a`, and `a` is the
  least such answer.
- **The claim as one statement** (`lift_laws`).

Three parts carry the proofs: a list read element by element (`mapM_answer`, `mapM_source`,
`mapM_total`), the join of a list (`joinAll_keeps`, `joinAll_all`), and the order of a carrier
(`AnswerOrder`, `le_joinAll`, `joinAll_le`).

Placement. Concept `subtyping-algebra`. Requirement R14, under the proposed claim
`union-rule-lift` (decisions rows 282 and 285). Reach: every member rule into a carrier with a
least answer and a join; the order `Ty.subN`, `Ty.normalize` and `Ty.members`; every relation
between values and types that reads the normal form and the union members. Consumers: the two
record rules (`src/Effect4/Laws/Program/Typed.lean`,
`src/Effect4/Laws/Program/Typed/RecordOperations.lean`,
`src/Effect4/Laws/Program/Typing/TermIntro.lean`), each conversion of candidate N, the closed
types of a checked program, and the lifted eliminators of the type gap. The laws do not
establish that any other rule reads a union this way, `checker-monotone`, or that tsgo agrees.
They say nothing at an invariant position. The design is
`docs/research/2026-10-06-seat-UNION-design.md`. The controls are in
`Test/Program/UnionRule.lean`.
-/

set_option autoImplicit false

namespace Effect4.Program.UnionRule

variable {α : Type} [Answer α]

/-! ## The order of a carrier -/

/-- **The order of a carrier of answers**: a preorder in which `Answer.bot` is least and
`Answer.join` is a least upper bound. It is the bounded join-semilattice of the dictionary, up
to the preorder's kernel. No definition of the core reads the order, so it is stated here. -/
class AnswerOrder (α : Type) [Answer α] where
  /-- `le a b`: the answer `a` is below the answer `b`. -/
  le : α → α → Prop
  /-- The order is reflexive. -/
  refl : ∀ a, le a a
  /-- The order is transitive. -/
  trans : ∀ {a b c}, le a b → le b c → le a c
  /-- The least answer is below every answer. -/
  bot_le : ∀ a, le Answer.bot a
  /-- The join is above its left side. -/
  le_join_left : ∀ a b, le a (Answer.join a b)
  /-- The join is above its right side. -/
  le_join_right : ∀ a b, le b (Answer.join a b)
  /-- The join is below each answer that is above both sides. -/
  join_le : ∀ {a b c}, le a c → le b c → le (Answer.join a b) c

open AnswerOrder (le)

/-- Types in the checker's order `Ty.subN`: both sides normalized, then `Ty.sub`. `never` is
least, and `Ty.join` is a least upper bound. -/
instance : AnswerOrder Ty where
  le a b := Ty.subN a b = true
  refl := Ty.subN_refl
  trans := Ty.subN_trans
  bot_le a := Ty.OrderProof.sub_never a.normalize
  le_join_left := Ty.subN_join_left
  le_join_right := Ty.subN_join_right
  join_le {a b c} hac hbc := by
    show Ty.sub (Ty.join a b).normalize c.normalize = true
    rw [Ty.normalize_join]
    exact Ty.OrderProof.sub_normalize_union_le Ty.sub_trans a b c.normalize hac hbc

/-- Pairs in the order of each component. -/
instance {α β : Type} [Answer α] [Answer β] [AnswerOrder α] [AnswerOrder β] :
    AnswerOrder (α × β) where
  le a b := le a.1 b.1 ∧ le a.2 b.2
  refl a := ⟨AnswerOrder.refl a.1, AnswerOrder.refl a.2⟩
  trans hab hbc := ⟨AnswerOrder.trans hab.1 hbc.1, AnswerOrder.trans hab.2 hbc.2⟩
  bot_le a := ⟨AnswerOrder.bot_le a.1, AnswerOrder.bot_le a.2⟩
  le_join_left a b := ⟨AnswerOrder.le_join_left a.1 b.1, AnswerOrder.le_join_left a.2 b.2⟩
  le_join_right a b := ⟨AnswerOrder.le_join_right a.1 b.1, AnswerOrder.le_join_right a.2 b.2⟩
  join_le hac hbc := ⟨AnswerOrder.join_le hac.1 hbc.1, AnswerOrder.join_le hac.2 hbc.2⟩

/-! ## The laws -/

/-- **Total at `never`.** `never` has no union member, so the lifted rule answers the least
answer, whatever the member rule is. A part of the claim `union-rule-lift`. It does not say that
a by-shape rule answers at `never`: `fiberTy` refuses it until its conversion. -/
@[semantics "subtyping-algebra" (requirement := R14)]
proof_goal lift_never (rule : Ty → Option α) : lift rule .never = some Answer.bot

/-- **One member.** At a normal type that is one union member, the lifted rule is the member
rule, up to the join with the least answer. At the carrier `Ty` that join is the answer's normal
form (`Ty.join_never`). A part of the claim `union-rule-lift`. Its consumers are
`Record.fieldType_normal` and `Record.setType_normal`
(`src/Effect4/Laws/Program/Typing/TermIntro.lean`). It says nothing at a union of two members. -/
@[semantics "subtyping-algebra" (requirement := R14)]
proof_goal lift_member (rule : Ty → Option α) {t : Ty} (normal : Ty.Normal t)
    (member : t.isMember = true) : lift rule t = (rule t).map (Answer.join Answer.bot)

/-- **Normal form.** Two types with one normal form have one answer: the lifted rule reads the
normal form and nothing else of its target. A part of the claim `union-rule-lift`. Its consumer
is each rule that compares a stated type with a type the checker produced. -/
@[semantics "subtyping-algebra" (requirement := R14)]
proof_goal lift_congr (rule : Ty → Option α) {s t : Ty} (same : s.normalize = t.normalize) :
    lift rule s = lift rule t

/-- **The premise of the monotone law.** The rule `lower` answers below the rule `upper` at each
pair of normal union members in the order: where `upper` answers at the larger member, `lower`
answers at the smaller one, and its answer is below. With one rule on both sides, the member
rule is monotone in the order `Ty.sub`. An instance receives `Ty.Normal` and `isMember` for both
members, which rule out `never` and a union. -/
def Below [AnswerOrder α] (lower upper : Ty → Option α) : Prop :=
  ∀ ⦃x y : Ty⦄, Ty.Normal x → Ty.Normal y → x.isMember = true → y.isMember = true →
    Ty.sub x y = true → ∀ ⦃b : α⦄, upper y = some b → ∃ a, lower x = some a ∧ le a b

/-- **Monotone.** Take two member rules with `Below lower upper`, and a target `s` below a target
`t` in the checker's order. Where the lifted `upper` answers `b` at `t`, the lifted `lower`
answers at `s`, and its answer is below `b`. Each union member of the smaller normal form is
below a union member of the larger one (`Ty.OrderProof.sub_iff_members`). A part of the claim
`union-rule-lift`. Its consumer is `checker-monotone`: a field read at a smaller target, and an
overwrite at a smaller target and a smaller value. It is conditional: it proves `Below` for no
rule. -/
@[semantics "subtyping-algebra" (requirement := R14)]
proof_goal lift_mono [AnswerOrder α] {lower upper : Ty → Option α} (below : Below lower upper)
    {s t : Ty} (smaller : Ty.subN s t = true) {b : α} (typed : lift upper t = some b) :
    ∃ a, lift lower s = some a ∧ le a b

/-- **Transfer.** Take a relation `In` between values and types that reads the normal form and
the union members. Take a property `P` of a value and an answer that the join keeps on each
side. Where the member rule gives `P` at each normal union member that the value fits, the
lifted rule gives `P` at the target. A part of the claim `union-rule-lift`. Its consumer is
`ReadsUnion.lift_sound`, and each rule whose answer is no type. It carries the property that it
is given and no other: it says nothing of evaluation or of a target. -/
@[semantics "subtyping-algebra" (requirement := R14)]
proof_goal lift_transfer {V : Type} {In : V → Ty → Prop} {P : V → α → Prop}
    (normal : ∀ {v : V} {t : Ty}, In v t → In v t.normalize)
    (members : ∀ {v : V} {t : Ty}, In v t → ∃ m ∈ t.members, In v m)
    (left : ∀ {v : V} (a b : α), P v a → P v (Answer.join a b))
    (right : ∀ {v : V} (a b : α), P v b → P v (Answer.join a b))
    {rule : Ty → Option α}
    (member : ∀ {m : Ty} {a : α} {v : V}, Ty.Normal m → m.isMember = true → rule m = some a →
      In v m → P v a)
    {t : Ty} {a : α} {v : V} (typed : lift rule t = some a) (fit : In v t) : P v a

/-- **A membership relation that reads a union**: it reads the normal form, the union members
and the join. A value that fits a type fits its normal form, and fits one of its union members.
A value that fits a type fits each join with it. The tree has two such relations: the shape
check `Val.hasTy` (`RecordChecks.has_reads`, `src/Effect4/Laws/Program/Typed.lean`) and `Fits w`
(`fits_reads`, `src/Effect4/Laws/Program/Typed/RecordOperations.lean`). -/
structure ReadsUnion {V : Type} (M : V → Ty → Prop) : Prop where
  /-- A value that fits a type fits its normal form. -/
  normalize : ∀ {v : V} {t : Ty}, M v t → M v t.normalize
  /-- A value that fits a type fits one of its union members. -/
  members : ∀ {v : V} {t : Ty}, M v t → ∃ m ∈ t.members, M v m
  /-- A value that fits a type fits its join with a type on the right. -/
  joinLeft : ∀ {v : V} (a b : Ty), M v a → M v (Ty.join a b)
  /-- A value that fits a type fits its join with a type on the left. -/
  joinRight : ∀ {v : V} (a b : Ty), M v b → M v (Ty.join a b)

/-- **Soundness transfer.** Take a membership relation that reads a union, a member rule that
answers a type, and an operation on values. Let the member rule be sound against the relation at
each normal union member: the operation answers a value that fits the member rule's answer.
Then the lifted rule is sound against the relation at the target. A part of the claim
`union-rule-lift`, as `lift_transfer` at one property. Its consumers are the four record
theorems: `RecordChecks.fieldType` and `RecordChecks.setType`
(`src/Effect4/Laws/Program/Typed.lean`), `record_fieldType_fits` and `record_setType_fits`
(`src/Effect4/Laws/Program/Typed/RecordOperations.lean`). It is conditional on the member rule's
own law, and it says nothing of a host. -/
@[semantics "subtyping-algebra" (requirement := R14)]
proof_goal ReadsUnion.lift_sound {V : Type} {M : V → Ty → Prop} (reads : ReadsUnion M)
    {rule : Ty → Option Ty} {op : V → Option V}
    (sound : ∀ {m a : Ty} {v : V}, Ty.Normal m → m.isMember = true → rule m = some a → M v m →
      ∃ out, op v = some out ∧ M out a)
    {t a : Ty} {v : V} (typed : lift rule t = some a) (fit : M v t) :
    ∃ out, op v = some out ∧ M out a

/-- **Every member.** Take a property of answers that the least answer has, and that the join of
two answers with it has. Where the member rule's answer has it at each union member of the
target's normal form, the lifted answer has it. It differs from `lift_transfer`, whose property
the join keeps on one side: here the join needs both sides. A part of the claim
`union-rule-lift`. Its consumers are `lift_closed` and `lift_closed_pair`. It reads no property
of the target: an instance derives each member's property from the target's. -/
@[semantics "subtyping-algebra" (requirement := R14)]
proof_goal lift_all {Q : α → Prop} (bot : Q Answer.bot)
    (join : ∀ {a b : α}, Q a → Q b → Q (Answer.join a b)) {rule : Ty → Option α} {t : Ty}
    (member : ∀ m ∈ t.normalize.members, ∀ {a : α}, rule m = some a → Q a)
    {a : α} (typed : lift rule t = some a) : Q a

/-- **A lifted rule keeps closed types closed.** Take a member rule that answers a type. At each
normal union member that is closed, let its answer be closed. Then the lifted rule answers a
closed type at each closed target. `never` is closed, the join keeps closed types closed, and a
closed type has a closed normal form with closed union members (`Ty.closed_normalize`,
`Ty.closed_members`). A part of the claim `union-rule-lift`, as `lift_all` at one property. Its
consumer is the record case of the proposed claim `checked-types-closed`, and then the same case
of each conversion. It proves the member rule's fact for no rule. -/
@[semantics "subtyping-algebra" (requirement := R14)]
proof_goal lift_closed {rule : Ty → Option Ty}
    (member : ∀ {m a : Ty}, Ty.Normal m → m.isMember = true → m.closed = true →
      rule m = some a → a.closed = true)
    {t a : Ty} (typed : lift rule t = some a) (closed : t.closed = true) : a.closed = true

/-- **A lifted rule keeps closed types closed, at a pair.** The form of `lift_closed` for a rule
that answers two types: both are closed. A part of the claim `union-rule-lift`. Its consumer is
the same case of a rule that reads a fiber type or an exit type, at its conversion. -/
@[semantics "subtyping-algebra" (requirement := R14)]
proof_goal lift_closed_pair {rule : Ty → Option (Ty × Ty)}
    (member : ∀ {m : Ty} {a : Ty × Ty}, Ty.Normal m → m.isMember = true → m.closed = true →
      rule m = some a → a.1.closed = true ∧ a.2.closed = true)
    {t : Ty} {a : Ty × Ty} (typed : lift rule t = some a) (closed : t.closed = true) :
    a.1.closed = true ∧ a.2.closed = true

/-- **Upper form.** Take a member rule and a map `C` from answers back into types that keeps the
order. Let each normal union member that the rule answers be below `C` of its answer. Then a
target that the lifted rule answers is below `C` of the answer, in the checker's order. With
`fits_subN`, a value of the target is a value of `C a`. A part of the claim `union-rule-lift`.
Its consumer is each conversion of a rule that reads one constructor: `fiberTy` first, in place
of the equation `fiberTy_eq_some` (`src/Effect4/Laws/Program/Typed/Membership.lean`). The
inequality is false in raw `Ty.sub` at a target that is not its own normal form
(`Test/Program/UnionRule.lean`). It says nothing at an invariant constructor, and the record
field rule has no such `C`: the order has no width rule. -/
@[semantics "subtyping-algebra" (requirement := R14)]
proof_goal lift_upper [AnswerOrder α] {rule : Ty → Option α} {C : α → Ty}
    (mono : ∀ {a b : α}, le a b → Ty.subN (C a) (C b) = true)
    (member : ∀ {m : Ty} {a : α}, Ty.Normal m → m.isMember = true → rule m = some a →
      Ty.subN m (C a) = true)
    {t : Ty} {a : α} (typed : lift rule t = some a) : Ty.subN t (C a) = true

/-- **The upper form's answer is the least.** Take a member rule and a map `C` from answers into
types. At each normal union member that the rule answers, let an answer `b` with the member
below `C b` be above the rule's answer. Then the lifted rule's answer is below each `b` with the
target below `C b`. A part of the claim `union-rule-lift`, with `lift_upper`: the lifted rule
answers the least `a` with the target below `C a`. Its consumer is the same conversion: a type
written at a call must be above the lifted answer. -/
@[semantics "subtyping-algebra" (requirement := R14)]
proof_goal lift_least [AnswerOrder α] {rule : Ty → Option α} {C : α → Ty}
    (member : ∀ {m : Ty} {a b : α}, Ty.Normal m → m.isMember = true → rule m = some a →
      Ty.subN m (C b) = true → le a b)
    {t : Ty} {a b : α} (typed : lift rule t = some a) (upper : Ty.subN t (C b) = true) :
    le a b

end Effect4.Program.UnionRule
