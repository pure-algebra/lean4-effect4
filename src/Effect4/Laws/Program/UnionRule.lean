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
- **The eliminator of one covariant constructor** (`Eliminator`): three facts of a member rule
  that reads one constructor give the monotone law and the upper form with its least half
  (`Eliminator.lift_mono`, `Eliminator.lift_upper`, `Eliminator.lift_least`). In one statement,
  the lifted rule is the constructor's lower adjoint (`Eliminator.adjoint`).
- **Join and uniqueness** (`lift_union`, `lift_union_eq`, `lift_unique`): the lifted rule keeps
  joins where the member rule is monotone in the order, and it is the one map that does.
- **The guard** (`liftOne_eq_some_iff` and its uses): the guarded rule `UnionRule.liftOne`
  answers exactly where the target's normal form has at most one union member and the lifted
  rule answers. It implies the lifted rule's answer (`liftOne_some`), it is the lifted rule at
  one union member or none (`liftOne_eq`), and it reads the normal form (`liftOne_congr`).
- **The extended rule** (`extend_eq_some_iff` and its uses): `UnionRule.extend` is the member
  rule's own answer where the member rule answers at the raw target, and the guarded rule
  elsewhere. It agrees with the member rule (`extend_agrees`), and it is the guarded rule where
  the member rule refuses (`extend_refused`).
- **The contract of a converted eliminator** (`Eliminator.extend_laws`): what the extended rule
  of an eliminator gives, stated once for every `Eliminator`. A converted rule of the checker
  proves none of it again (`src/Effect4/Laws/Program/Eliminators.lean`).

`UnionRule.lift` is the fold of a union: the unique map that answers the least answer at
`never`, the member rule at one union member and the join at a union (`lift_unique`, at the
carrier `Ty`). `UnionRule.Answer` is its algebra: a least answer and a join.

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

The guard, the extended rule and the contract have their own question: the proposed claim
`union-rule-extend`, at the same concept and requirement (decisions rows 292, 293 and 294). Its
pointer is `Eliminator.extend_laws`. Reach: the extended rule of a member rule with the three
facts of `Eliminator`, in the order `Ty.subN`. Consumers: each converted rule of candidate N,
`fiberTy` first, and a hole that is declared at `never` under an eliminator. They do not
establish `checker-monotone`: a converted rule is not monotone in the order at a proper union.
They do not say that a type and its normal form have one answer: the extended rule keeps the
raw answer of its member rule. They say nothing of what tsgo accepts. The design is
`docs/research/2026-10-06-seat-PILOT-design.md`.
-/

set_option autoImplicit false

namespace Effect4.Program.UnionRule

/-! ## A list read element by element

`List.mapM` at `Option` answers a list exactly when it answers each element, in order. -/

/-- A read of a list that is not empty answers its head and its tail. A step of the three laws
of this section, its consumers. -/
@[semantics "subtyping-algebra" (requirement := R14)]
theorem mapM_cons_eq_some {β γ : Type} {f : β → Option γ} {x : β} {xs : List β} {ys : List γ} :
    (x :: xs).mapM f = some ys ↔
      ∃ y rest, f x = some y ∧ xs.mapM f = some rest ∧ ys = y :: rest := by
  simp only [List.mapM_cons, bind, Option.bind_eq_some_iff, pure, Option.some.injEq]
  constructor
  · rintro ⟨y, hy, rest, hrest, rfl⟩
    exact ⟨y, rest, hy, hrest, rfl⟩
  · rintro ⟨y, rest, hy, hrest, rfl⟩
    exact ⟨y, hy, rest, hrest, rfl⟩

/-- Each element of an answered list has its answer among the answers. A step of `lift_mono`,
`lift_transfer` and `lift_upper`. -/
@[semantics "subtyping-algebra" (requirement := R14)]
theorem mapM_answer {β γ : Type} {f : β → Option γ} :
    ∀ {xs : List β} {ys : List γ}, xs.mapM f = some ys → ∀ x ∈ xs, ∃ y ∈ ys, f x = some y
  | [], _, _, _, hx => absurd hx List.not_mem_nil
  | _ :: _, _, h, x, hx => by
    obtain ⟨y, rest, hy, hrest, rfl⟩ := mapM_cons_eq_some.mp h
    rcases List.mem_cons.mp hx with rfl | hx
    · exact ⟨y, List.mem_cons_self, hy⟩
    · obtain ⟨z, hz, hxz⟩ := mapM_answer hrest x hx
      exact ⟨z, List.mem_cons_of_mem _ hz, hxz⟩

/-- Each answer is the answer of an element. A step of `lift_all` and `lift_least`. -/
@[semantics "subtyping-algebra" (requirement := R14)]
theorem mapM_source {β γ : Type} {f : β → Option γ} :
    ∀ {xs : List β} {ys : List γ}, xs.mapM f = some ys → ∀ y ∈ ys, ∃ x ∈ xs, f x = some y
  | [], _, h, y, hy => by
    cases h
    exact absurd hy List.not_mem_nil
  | _ :: _, _, h, y, hy => by
    obtain ⟨z, rest, hz, hrest, rfl⟩ := mapM_cons_eq_some.mp h
    rcases List.mem_cons.mp hy with rfl | hy
    · exact ⟨_, List.mem_cons_self, hz⟩
    · obtain ⟨x, hx, hxy⟩ := mapM_source hrest y hy
      exact ⟨x, List.mem_cons_of_mem _ hx, hxy⟩

/-- A list whose every element is answered is answered, and a property of each element's answer
holds of every answer. A step of `lift_mono`, its one consumer. -/
@[semantics "subtyping-algebra" (requirement := R14)]
theorem mapM_total {β γ : Type} {f : β → Option γ} {P : γ → Prop} :
    ∀ {xs : List β}, (∀ x ∈ xs, ∃ y, f x = some y ∧ P y) →
      ∃ ys, xs.mapM f = some ys ∧ ∀ y ∈ ys, P y
  | [], _ => ⟨[], rfl, fun _ hy => absurd hy List.not_mem_nil⟩
  | x :: xs, h => by
    obtain ⟨y, hy, py⟩ := h x List.mem_cons_self
    obtain ⟨ys, hys, pys⟩ := mapM_total (xs := xs) fun z hz => h z (List.mem_cons_of_mem _ hz)
    refine ⟨y :: ys, mapM_cons_eq_some.mpr ⟨y, ys, hy, hys, rfl⟩, fun z hz => ?_⟩
    rcases List.mem_cons.mp hz with rfl | hz
    · exact py
    · exact pys z hz

/-! ## The join of a list of answers

Two ways for a property to reach the join of a list. A property that the join keeps on each side
needs one listed answer that has it. A property that the join keeps on two answers that have it
needs every listed answer, and the least answer, to have it. -/

variable {α : Type} [Answer α]

/-- A property that the join keeps on each side passes from the start or from one listed answer
to the fold. The general form of `joinAll_keeps`, its one consumer. -/
@[semantics "subtyping-algebra" (requirement := R14)]
theorem foldl_keeps {Q : α → Prop} (left : ∀ a b, Q a → Q (Answer.join a b))
    (right : ∀ a b, Q b → Q (Answer.join a b)) :
    ∀ (answers : List α) (acc : α), (Q acc ∨ ∃ a ∈ answers, Q a) →
      Q (answers.foldl Answer.join acc)
  | [], _, h => h.elim id fun ⟨_, inside, _⟩ => absurd inside List.not_mem_nil
  | x :: rest, acc, h => by
    refine foldl_keeps left right rest (Answer.join acc x) ?_
    rcases h with h | ⟨a, inside, h⟩
    · exact Or.inl (left acc x h)
    · rcases List.mem_cons.mp inside with rfl | inside
      · exact Or.inl (right acc a h)
      · exact Or.inr ⟨a, inside, h⟩

/-- **A property that the join keeps on each side passes from one listed answer to the join of
the list.** With membership of a value as the property, a value that fits one branch's answer
fits the joined answer. A step of `lift_transfer` and of `le_joinAll`. -/
@[semantics "subtyping-algebra" (requirement := R14)]
theorem joinAll_keeps {Q : α → Prop} (left : ∀ a b, Q a → Q (Answer.join a b))
    (right : ∀ a b, Q b → Q (Answer.join a b)) {answers : List α} {a : α}
    (inside : a ∈ answers) (holds : Q a) : Q (joinAll answers) :=
  foldl_keeps left right answers Answer.bot (Or.inr ⟨a, inside, holds⟩)

/-- A property that the join of two answers with it has holds of the fold, where the start and
every listed answer have it. The general form of `joinAll_all`, its one consumer. -/
@[semantics "subtyping-algebra" (requirement := R14)]
theorem foldl_all {Q : α → Prop} (join : ∀ {a b : α}, Q a → Q b → Q (Answer.join a b)) :
    ∀ (answers : List α) (acc : α), Q acc → (∀ a ∈ answers, Q a) →
      Q (answers.foldl Answer.join acc)
  | [], _, hacc, _ => hacc
  | x :: rest, acc, hacc, h =>
    foldl_all join rest (Answer.join acc x) (join hacc (h x List.mem_cons_self))
      fun a inside => h a (List.mem_cons_of_mem _ inside)

/-- **A property that the least answer has, and that the join of two answers with it has, holds
of the join of a list whose every answer has it.** A step of `lift_all` and of `joinAll_le`. -/
@[semantics "subtyping-algebra" (requirement := R14)]
theorem joinAll_all {Q : α → Prop} (bot : Q Answer.bot)
    (join : ∀ {a b : α}, Q a → Q b → Q (Answer.join a b)) {answers : List α}
    (all : ∀ a ∈ answers, Q a) : Q (joinAll answers) :=
  foldl_all join answers Answer.bot bot all

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

/-- Each listed answer is below the join of the list. A step of `lift_mono` and `lift_upper`. -/
@[semantics "subtyping-algebra" (requirement := R14)]
theorem le_joinAll [AnswerOrder α] {answers : List α} {a : α} (inside : a ∈ answers) :
    le a (joinAll answers) :=
  joinAll_keeps (Q := le a) (fun x y h => AnswerOrder.trans h (AnswerOrder.le_join_left x y))
    (fun x y h => AnswerOrder.trans h (AnswerOrder.le_join_right x y)) inside (AnswerOrder.refl a)

/-- The join of a list is below each answer that is above every listed answer: it is a least
upper bound. A step of `lift_mono` and `lift_least`. -/
@[semantics "subtyping-algebra" (requirement := R14)]
theorem joinAll_le [AnswerOrder α] {answers : List α} {b : α} (below : ∀ a ∈ answers, le a b) :
    le (joinAll answers) b :=
  joinAll_all (Q := fun a => le a b) (AnswerOrder.bot_le b) AnswerOrder.join_le below

/-! ## The laws -/

/-- **Total at `never`.** `never` has no union member, so the lifted rule answers the least
answer, whatever the member rule is. A part of the claim `union-rule-lift`. It does not say that
a by-shape rule answers at `never`: `fiberTy` refuses it until its conversion. -/
@[semantics "subtyping-algebra" (requirement := R14)]
theorem lift_never (rule : Ty → Option α) : lift rule .never = some Answer.bot := rfl

/-- **One member.** At a normal type that is one union member, the lifted rule is the member
rule, up to the join with the least answer. At the carrier `Ty` that join is the answer's normal
form (`Ty.join_never`). A part of the claim `union-rule-lift`. Its consumers are
`Record.fieldType_normal` and `Record.setType_normal`
(`src/Effect4/Laws/Program/Typing/TermIntro.lean`). It says nothing at a union of two members. -/
@[semantics "subtyping-algebra" (requirement := R14)]
theorem lift_member (rule : Ty → Option α) {t : Ty} (normal : Ty.Normal t)
    (member : t.isMember = true) : lift rule t = (rule t).map (Answer.join Answer.bot) := by
  unfold lift
  rw [normal.fixed, Ty.members_atom member]
  show Option.map joinAll (rule t >>= fun a => List.mapM.loop rule [] [a]) = _
  cases rule t <;> rfl

/-- **Normal form.** Two types with one normal form have one answer: the lifted rule reads the
normal form and nothing else of its target. A part of the claim `union-rule-lift`. Its consumer
is each rule that compares a stated type with a type the checker produced. -/
@[semantics "subtyping-algebra" (requirement := R14)]
theorem lift_congr (rule : Ty → Option α) {s t : Ty} (same : s.normalize = t.normalize) :
    lift rule s = lift rule t := by
  unfold lift
  rw [same]

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
theorem lift_mono [AnswerOrder α] {lower upper : Ty → Option α} (below : Below lower upper)
    {s t : Ty} (smaller : Ty.subN s t = true) {b : α} (typed : lift upper t = some b) :
    ∃ a, lift lower s = some a ∧ le a b := by
  obtain ⟨answers, hanswers, rfl⟩ := Option.map_eq_some_iff.mp typed
  have hmembers := (Ty.OrderProof.sub_iff_members Ty.sub_trans _ _).mp smaller
  obtain ⟨lowers, hlowers, hbelow⟩ := mapM_total (f := lower)
    (P := fun a => le a (joinAll answers)) (xs := s.normalize.members) fun x hx => by
      obtain ⟨y, hy, hxy⟩ := hmembers x hx
      obtain ⟨c, hc, hrule⟩ := mapM_answer hanswers y hy
      obtain ⟨a, ha, hac⟩ := below ((Ty.normal_normalize s).members hx)
        ((Ty.normal_normalize t).members hy) (Ty.members_isMember hx) (Ty.members_isMember hy)
        hxy hrule
      exact ⟨a, ha, AnswerOrder.trans hac (le_joinAll hc)⟩
  exact ⟨joinAll lowers, Option.map_eq_some_iff.mpr ⟨lowers, hlowers, rfl⟩, joinAll_le hbelow⟩

/-- **Transfer.** Take a relation `In` between values and types that reads the normal form and
the union members. Take a property `P` of a value and an answer that the join keeps on each
side. Where the member rule gives `P` at each normal union member that the value fits, the
lifted rule gives `P` at the target. A part of the claim `union-rule-lift`. Its consumer is
`ReadsUnion.lift_sound`, and each rule whose answer is no type. It carries the property that it
is given and no other: it says nothing of evaluation or of a target. -/
@[semantics "subtyping-algebra" (requirement := R14)]
theorem lift_transfer {V : Type} {In : V → Ty → Prop} {P : V → α → Prop}
    (normal : ∀ {v : V} {t : Ty}, In v t → In v t.normalize)
    (members : ∀ {v : V} {t : Ty}, In v t → ∃ m ∈ t.members, In v m)
    (left : ∀ {v : V} (a b : α), P v a → P v (Answer.join a b))
    (right : ∀ {v : V} (a b : α), P v b → P v (Answer.join a b))
    {rule : Ty → Option α}
    (member : ∀ {m : Ty} {a : α} {v : V}, Ty.Normal m → m.isMember = true → rule m = some a →
      In v m → P v a)
    {t : Ty} {a : α} {v : V} (typed : lift rule t = some a) (fit : In v t) : P v a := by
  obtain ⟨answers, hanswers, rfl⟩ := Option.map_eq_some_iff.mp typed
  obtain ⟨m, hm, hfit⟩ := members (normal fit)
  obtain ⟨c, hc, hrule⟩ := mapM_answer hanswers m hm
  exact joinAll_keeps (fun a b => left a b) (fun a b => right a b) hc
    (member ((Ty.normal_normalize t).members hm) (Ty.members_isMember hm) hrule hfit)

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
theorem ReadsUnion.lift_sound {V : Type} {M : V → Ty → Prop} (reads : ReadsUnion M)
    {rule : Ty → Option Ty} {op : V → Option V}
    (sound : ∀ {m a : Ty} {v : V}, Ty.Normal m → m.isMember = true → rule m = some a → M v m →
      ∃ out, op v = some out ∧ M out a)
    {t a : Ty} {v : V} (typed : lift rule t = some a) (fit : M v t) :
    ∃ out, op v = some out ∧ M out a :=
  lift_transfer (In := M) (P := fun v a => ∃ out, op v = some out ∧ M out a) reads.normalize
    reads.members
    (fun a b ⟨out, hop, hout⟩ => ⟨out, hop, reads.joinLeft a b hout⟩)
    (fun a b ⟨out, hop, hout⟩ => ⟨out, hop, reads.joinRight a b hout⟩) sound typed fit

/-- **Every member.** Take a property of answers that the least answer has, and that the join of
two answers with it has. Where the member rule's answer has it at each union member of the
target's normal form, the lifted answer has it. It differs from `lift_transfer`, whose property
the join keeps on one side: here the join needs both sides. A part of the claim
`union-rule-lift`. Its consumers are `lift_closed` and `lift_closed_pair`. It reads no property
of the target: an instance derives each member's property from the target's. -/
@[semantics "subtyping-algebra" (requirement := R14)]
theorem lift_all {Q : α → Prop} (bot : Q Answer.bot)
    (join : ∀ {a b : α}, Q a → Q b → Q (Answer.join a b)) {rule : Ty → Option α} {t : Ty}
    (member : ∀ m ∈ t.normalize.members, ∀ {a : α}, rule m = some a → Q a)
    {a : α} (typed : lift rule t = some a) : Q a := by
  obtain ⟨answers, hanswers, rfl⟩ := Option.map_eq_some_iff.mp typed
  refine joinAll_all bot join fun c hc => ?_
  obtain ⟨m, hm, hrule⟩ := mapM_source hanswers c hc
  exact member m hm hrule

/-- The join of two closed types is closed: the join is the normal form of their union, and a
normal form keeps closedness (`Ty.closed_normalize`). A step of `lift_closed` and
`lift_closed_pair`. -/
@[semantics "subtyping-algebra" (requirement := R14)]
theorem closed_join {a b : Ty} (ha : a.closed = true) (hb : b.closed = true) :
    (Ty.join a b).closed = true :=
  Ty.closed_normalize (.union a b) (by
    show (a.closed && b.closed) = true
    rw [ha, hb]
    rfl)

/-- **A lifted rule keeps closed types closed.** Take a member rule that answers a type. At each
normal union member that is closed, let its answer be closed. Then the lifted rule answers a
closed type at each closed target. `never` is closed, the join keeps closed types closed, and a
closed type has a closed normal form with closed union members (`Ty.closed_normalize`,
`Ty.closed_members`). A part of the claim `union-rule-lift`, as `lift_all` at one property. Its
consumer is the record case of the proposed claim `checked-types-closed`, and then the same case
of each conversion. It proves the member rule's fact for no rule. -/
@[semantics "subtyping-algebra" (requirement := R14)]
theorem lift_closed {rule : Ty → Option Ty}
    (member : ∀ {m a : Ty}, Ty.Normal m → m.isMember = true → m.closed = true →
      rule m = some a → a.closed = true)
    {t a : Ty} (typed : lift rule t = some a) (closed : t.closed = true) : a.closed = true :=
  lift_all (Q := fun a => a.closed = true) rfl closed_join
    (fun m hm _ h => member ((Ty.normal_normalize t).members hm) (Ty.members_isMember hm)
      (Ty.closed_members _ (Ty.closed_normalize t closed) m hm) h) typed

/-- **A lifted rule keeps closed types closed, at a pair.** The form of `lift_closed` for a rule
that answers two types: both are closed. A part of the claim `union-rule-lift`. Its consumer is
the same case of a rule that reads a fiber type or an exit type, at its conversion. -/
@[semantics "subtyping-algebra" (requirement := R14)]
theorem lift_closed_pair {rule : Ty → Option (Ty × Ty)}
    (member : ∀ {m : Ty} {a : Ty × Ty}, Ty.Normal m → m.isMember = true → m.closed = true →
      rule m = some a → a.1.closed = true ∧ a.2.closed = true)
    {t : Ty} {a : Ty × Ty} (typed : lift rule t = some a) (closed : t.closed = true) :
    a.1.closed = true ∧ a.2.closed = true :=
  lift_all (Q := fun a : Ty × Ty => a.1.closed = true ∧ a.2.closed = true) ⟨rfl, rfl⟩
    (fun ha hb => ⟨closed_join ha.1 hb.1, closed_join ha.2 hb.2⟩)
    (fun m hm _ h => member ((Ty.normal_normalize t).members hm) (Ty.members_isMember hm)
      (Ty.closed_members _ (Ty.closed_normalize t closed) m hm) h) typed

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
theorem lift_upper [AnswerOrder α] {rule : Ty → Option α} {C : α → Ty}
    (mono : ∀ {a b : α}, le a b → Ty.subN (C a) (C b) = true)
    (member : ∀ {m : Ty} {a : α}, Ty.Normal m → m.isMember = true → rule m = some a →
      Ty.subN m (C a) = true)
    {t : Ty} {a : α} (typed : lift rule t = some a) : Ty.subN t (C a) = true := by
  obtain ⟨answers, hanswers, rfl⟩ := Option.map_eq_some_iff.mp typed
  refine (Ty.OrderProof.sub_iff_members Ty.sub_trans _ _).mpr fun x hx => ?_
  have hnormal := (Ty.normal_normalize t).members hx
  obtain ⟨c, hc, hrule⟩ := mapM_answer hanswers x hx
  have hbelow : Ty.subN x (C (joinAll answers)) = true :=
    Ty.subN_trans (member hnormal (Ty.members_isMember hx) hrule) (mono (le_joinAll hc))
  have hraw : Ty.sub x (C (joinAll answers)).normalize = true := by
    have h := hbelow
    unfold Ty.subN at h
    rw [hnormal.fixed] at h
    exact h
  exact (Ty.OrderProof.sub_member_right_iff x _ (Ty.members_isMember hx)).mp hraw

/-- **The upper form's answer is the least.** Take a member rule and a map `C` from answers into
types. At each normal union member that the rule answers, let an answer `b` with the member
below `C b` be above the rule's answer. Then the lifted rule's answer is below each `b` with the
target below `C b`. A part of the claim `union-rule-lift`, with `lift_upper`: the lifted rule
answers the least `a` with the target below `C a`. Its consumer is the same conversion: a type
written at a call must be above the lifted answer. -/
@[semantics "subtyping-algebra" (requirement := R14)]
theorem lift_least [AnswerOrder α] {rule : Ty → Option α} {C : α → Ty}
    (member : ∀ {m : Ty} {a b : α}, Ty.Normal m → m.isMember = true → rule m = some a →
      Ty.subN m (C b) = true → le a b)
    {t : Ty} {a b : α} (typed : lift rule t = some a) (upper : Ty.subN t (C b) = true) :
    le a b := by
  obtain ⟨answers, hanswers, rfl⟩ := Option.map_eq_some_iff.mp typed
  refine joinAll_le fun c hc => ?_
  obtain ⟨x, hx, hrule⟩ := mapM_source hanswers c hc
  have hnormal := (Ty.normal_normalize t).members hx
  have hmember : Ty.subN x t = true := by
    unfold Ty.subN
    rw [hnormal.fixed]
    exact Ty.OrderProof.member_sub_self hx
  exact member hnormal (Ty.members_isMember hx) hrule (Ty.subN_trans hmember upper)

/-- **The claim `union-rule-lift`, as one statement**: its five parts of the brief, for one
member rule. The lifted rule answers the least answer at `never`. At a normal type that is one
union member it is the member rule, up to the join with the least answer. Two types with one
normal form have one answer. A member rule that is monotone in the order lifts to a monotone
rule. A property of a value and an answer that the join keeps on each side passes from the
union members to the lifted rule. It is the pointer that the claim's row needs, and it adds
nothing to its parts. `lift_all`, `lift_upper` and `lift_least` stand beside it. -/
@[semantics "subtyping-algebra" (requirement := R14)]
theorem lift_laws [AnswerOrder α] (rule : Ty → Option α) :
    lift rule .never = some Answer.bot ∧
    (∀ {t : Ty}, Ty.Normal t → t.isMember = true →
      lift rule t = (rule t).map (Answer.join Answer.bot)) ∧
    (∀ {s t : Ty}, s.normalize = t.normalize → lift rule s = lift rule t) ∧
    (Below rule rule → ∀ {s t : Ty} {b : α}, Ty.subN s t = true → lift rule t = some b →
      ∃ a, lift rule s = some a ∧ le a b) ∧
    (∀ {V : Type} {In : V → Ty → Prop} {P : V → α → Prop},
      (∀ {v : V} {t : Ty}, In v t → In v t.normalize) →
      (∀ {v : V} {t : Ty}, In v t → ∃ m ∈ t.members, In v m) →
      (∀ {v : V} (a b : α), P v a → P v (Answer.join a b)) →
      (∀ {v : V} (a b : α), P v b → P v (Answer.join a b)) →
      (∀ {m : Ty} {a : α} {v : V}, Ty.Normal m → m.isMember = true → rule m = some a →
        In v m → P v a) →
      ∀ {t : Ty} {a : α} {v : V}, lift rule t = some a → In v t → P v a) := by
  refine ⟨lift_never rule, fun normal member => lift_member rule normal member,
    fun same => lift_congr rule same,
    fun below _ _ _ smaller typed => lift_mono below smaller typed, ?_⟩
  intro V In P normal members left right member t a v typed fit
  exact lift_transfer (In := In) (P := P) normal members left right member typed fit

/-! ## A member rule that reads one covariant constructor

A by-shape rule of the checker reads one constructor: `fiberTy` reads a fiber type, and
`Checker.listOf?` a list type. Such a rule owes three facts, and the order laws follow from them
with no word about unions. A rule that reads two heads owes the member facts of `lift_upper`,
`lift_least` and `below_of_upper` instead. -/

/-- **`Below` from an upper map.** Take a member rule and a map `C` from answers into types.
Let each normal union member that the rule answers be below `C` of its answer, and let that
answer be the least such. Let the rule read each normal union member that is below some `C b`.
Then the member rule is monotone in the order: `Below rule rule`. A part of the claim
`union-rule-lift`. Its consumers are `Eliminator.monotone`, and a rule that reads two heads, such
as the cause rule `causeInputError?` (`src/Effect4/Program/NativeAtom.lean`). -/
@[semantics "subtyping-algebra" (requirement := R14)]
theorem below_of_upper [AnswerOrder α] {rule : Ty → Option α} {C : α → Ty}
    (upper : ∀ {m : Ty} {a : α}, Ty.Normal m → m.isMember = true → rule m = some a →
      Ty.subN m (C a) = true)
    (least : ∀ {m : Ty} {a b : α}, Ty.Normal m → m.isMember = true → rule m = some a →
      Ty.subN m (C b) = true → le a b)
    (reads : ∀ {m : Ty} {b : α}, Ty.Normal m → m.isMember = true → Ty.subN m (C b) = true →
      ∃ a, rule m = some a) :
    Below rule rule := by
  intro x y nx ny hx hy hxy b hb
  have hxb : Ty.subN x (C b) = true := Ty.subN_trans (Ty.sub_le_subN hxy) (upper ny hy hb)
  obtain ⟨a, ha⟩ := reads nx hx hxb
  exact ⟨a, ha, least nx hx ha hxb⟩

/-- **The eliminator of one covariant constructor**: the three facts that a member rule `rule`
owes for a constructor `C`. The rule answers only at the constructor. The constructor keeps and
reflects the order. The rule reads each normal union member below the constructor. An invariant
constructor has no instance: `embeds` fails there. -/
structure Eliminator [AnswerOrder α] (rule : Ty → Option α) (C : α → Ty) : Prop where
  /-- The rule answers only at the constructor, with the constructor's arguments. -/
  shape : ∀ {m : Ty} {a : α}, rule m = some a → m = C a
  /-- The constructor keeps and reflects the order. -/
  embeds : ∀ {a b : α}, Ty.subN (C a) (C b) = true ↔ le a b
  /-- The rule reads each normal union member below the constructor. -/
  reads : ∀ {m : Ty} {b : α}, Ty.Normal m → m.isMember = true → Ty.subN m (C b) = true →
    ∃ a, rule m = some a

section Eliminator

variable [AnswerOrder α] {rule : Ty → Option α} {C : α → Ty}

/-- The eliminator of one constructor is monotone in the order: the premise of `lift_mono`. A
part of the claim `union-rule-lift`. Its consumer is `Eliminator.lift_mono`. -/
@[semantics "subtyping-algebra" (requirement := R14)]
theorem Eliminator.monotone (e : Eliminator rule C) : Below rule rule :=
  below_of_upper (fun _ _ answered => by rw [e.shape answered]; exact Ty.subN_refl _)
    (fun _ _ answered upper => by rw [e.shape answered] at upper; exact e.embeds.mp upper)
    e.reads

/-- **The lifted eliminator is monotone.** A smaller target has an answer where a larger one
has, and the answer is smaller. A part of the claim `union-rule-lift`. Its consumer is
`checker-monotone` at each converted rule. -/
@[semantics "subtyping-algebra" (requirement := R14)]
theorem Eliminator.lift_mono (e : Eliminator rule C) {s t : Ty}
    (smaller : Ty.subN s t = true) {b : α} (typed : lift rule t = some b) :
    ∃ a, lift rule s = some a ∧ le a b :=
  UnionRule.lift_mono e.monotone smaller typed

/-- **The upper form of an eliminator.** A target that the lifted rule answers at `a` is below
`C a`, in the checker's order. It takes the place of the equation that a by-shape rule has
today, such as `fiberTy_eq_some` (`src/Effect4/Laws/Program/Typed/Membership.lean`): a use site
moves a value of the target up by `fits_subN`. A part of the claim `union-rule-lift`. Its
consumer is each conversion of candidate N. -/
@[semantics "subtyping-algebra" (requirement := R14)]
theorem Eliminator.lift_upper (e : Eliminator rule C) {t : Ty} {a : α}
    (typed : lift rule t = some a) : Ty.subN t (C a) = true :=
  UnionRule.lift_upper (fun below => e.embeds.mpr below)
    (fun _ _ answered => by rw [e.shape answered]; exact Ty.subN_refl _) typed

/-- **The lifted eliminator answers the least.** Each `b` with the target below `C b` is above
the lifted answer. A part of the claim `union-rule-lift`. Its consumer is a type that a printer
writes at a call: it must be above the lifted answer. -/
@[semantics "subtyping-algebra" (requirement := R14)]
theorem Eliminator.lift_least (e : Eliminator rule C) {t : Ty} {a b : α}
    (typed : lift rule t = some a) (upper : Ty.subN t (C b) = true) : le a b :=
  UnionRule.lift_least
    (fun _ _ answered upper => by rw [e.shape answered] at upper; exact e.embeds.mp upper)
    typed upper

/-- **The adjoint form.** The lifted rule of a covariant constructor is that constructor's lower
adjoint, and it answers exactly below the constructor's image. First, the lifted rule answers at
a target exactly when the target is below some `C b`. Second, where it answers `a`, an answer
`b` is above `a` exactly when the target is below `C b`. It is one statement for the upper form,
its least half and the fact `reads`. A part of the claim `union-rule-lift`. Its consumers are a
converted rule's monotone law with no further premise, the type arguments that a printer writes
at a proper union, and the expected type of a hole under an eliminator. It says nothing at an
invariant constructor or about a target. -/
@[semantics "subtyping-algebra" (requirement := R14)]
theorem Eliminator.adjoint (e : Eliminator rule C) (t : Ty) :
    ((lift rule t).isSome = true ↔ ∃ b, Ty.subN t (C b) = true) ∧
    ∀ {a : α}, lift rule t = some a → ∀ b : α, le a b ↔ Ty.subN t (C b) = true := by
  refine ⟨⟨fun answered => ?_, fun ⟨b, upper⟩ => ?_⟩,
    fun typed b => ⟨fun below => ?_, fun upper => e.lift_least typed upper⟩⟩
  · obtain ⟨a, typed⟩ := Option.isSome_iff_exists.mp answered
    exact ⟨a, e.lift_upper typed⟩
  · obtain ⟨answers, hanswers, -⟩ := mapM_total (f := rule) (P := fun _ => True)
      (xs := t.normalize.members) fun x hx => by
        have hnormal := (Ty.normal_normalize t).members hx
        have hmember : Ty.subN x t = true := by
          unfold Ty.subN
          rw [hnormal.fixed]
          exact Ty.OrderProof.member_sub_self hx
        obtain ⟨a, ha⟩ := e.reads hnormal (Ty.members_isMember hx) (Ty.subN_trans hmember upper)
        exact ⟨a, ha, trivial⟩
    exact Option.isSome_iff_exists.mpr
      ⟨joinAll answers, Option.map_eq_some_iff.mpr ⟨answers, hanswers, rfl⟩⟩
  · exact Ty.subN_trans (e.lift_upper typed) (e.embeds.mpr below)

end Eliminator

/-! ## The lifted rule is the fold of a union

A type's normal form is a join of its union members, and `never` is the empty join. The lifted
rule is the map out of that structure that the member rule determines: it answers the least
answer at `never`, the member rule at one union member, and the join at a union. `Answer` is its
algebra. Two statements say so. The lifted rule keeps joins, where the member rule is monotone
in the order (`lift_union`, and `lift_union_eq` at the carrier `Ty`). And a map with those four
properties is the lifted rule (`lift_unique`, at the carrier `Ty`). So two rules that read a
union agree when they agree at `never`, at one union member and at a normal union: no proof
compares two recursions. -/

/-- The union members of a union's normal form are union members of the two sides' normal
forms, and each union member of a side is below one of them. A normal form keeps maximal
members only. A step of `lift_union`, its one consumer. -/
@[semantics "subtyping-algebra" (requirement := R14)]
theorem members_union (s t : Ty) :
    (∀ k ∈ (Ty.union s t).normalize.members,
      k ∈ s.normalize.members ∨ k ∈ t.normalize.members) ∧
    (∀ m, m ∈ s.normalize.members ∨ m ∈ t.normalize.members →
      ∃ k ∈ (Ty.union s t).normalize.members, Ty.sub m k = true) := by
  rw [Ty.OrderProof.members_normalize_union]
  constructor
  · intro k hk
    exact List.mem_append.mp ((Ty.mem_normalizeRow k _).mp hk).1
  · intro m hm
    exact Ty.normalizeRow_coverage _ m (List.mem_append.mpr hm)

/-- **Join.** Take a member rule that is monotone in the order: `Below rule rule`. The lifted
rule answers at a union exactly when it answers at both sides: a refusal on either side refuses
the union. Where it answers, its answer at the union is the join of the two answers, up to the
order: each is below the other. The premise is used at a member that the union's normal form
drops: it is below a kept member, so the rule answers it, below the kept member's answer. A part
of the claim `union-rule-lift`. Its consumers are `lift_union_eq`, and each rule that reads the
join of two branch types. Without the premise the first half still holds one way, and the
second fails (`Test/Program/UnionRule.lean`). -/
@[semantics "subtyping-algebra" (requirement := R14)]
theorem lift_union [AnswerOrder α] {rule : Ty → Option α} (mono : Below rule rule) (s t : Ty) :
    (∀ {a b : α}, lift rule s = some a → lift rule t = some b →
      ∃ c, lift rule (.union s t) = some c ∧ le c (Answer.join a b) ∧ le (Answer.join a b) c) ∧
    (∀ {c : α}, lift rule (.union s t) = some c →
      ∃ a b, lift rule s = some a ∧ lift rule t = some b) := by
  obtain ⟨hkept, hcover⟩ := members_union s t
  have hnormalS := fun m (hm : m ∈ s.normalize.members) => (Ty.normal_normalize s).members hm
  have hnormalT := fun m (hm : m ∈ t.normalize.members) => (Ty.normal_normalize t).members hm
  have hnormalK := fun k (hk : k ∈ (Ty.union s t).normalize.members) =>
    (Ty.normal_normalize (.union s t)).members hk
  constructor
  · intro a b typedS typedT
    obtain ⟨as, has, rfl⟩ := Option.map_eq_some_iff.mp typedS
    obtain ⟨bs, hbs, rfl⟩ := Option.map_eq_some_iff.mp typedT
    -- each kept member is answered, below the join of the two sides
    obtain ⟨cs, hcs, hbelow⟩ := mapM_total (f := rule)
      (P := fun c => le c (Answer.join (joinAll as) (joinAll bs)))
      (xs := (Ty.union s t).normalize.members) fun k hk => by
        rcases hkept k hk with hk | hk
        · obtain ⟨x, hx, hrule⟩ := mapM_answer has k hk
          exact ⟨x, hrule, AnswerOrder.trans (le_joinAll hx) (AnswerOrder.le_join_left _ _)⟩
        · obtain ⟨x, hx, hrule⟩ := mapM_answer hbs k hk
          exact ⟨x, hrule, AnswerOrder.trans (le_joinAll hx) (AnswerOrder.le_join_right _ _)⟩
    refine ⟨joinAll cs, Option.map_eq_some_iff.mpr ⟨cs, hcs, rfl⟩, joinAll_le hbelow, ?_⟩
    -- each side's answer is below the union's: a dropped member is below a kept one
    have side : ∀ (xs : List α) (ms : List Ty), ms.mapM rule = some xs →
        (∀ m ∈ ms, Ty.Normal m ∧ (m ∈ s.normalize.members ∨ m ∈ t.normalize.members)) →
        le (joinAll xs) (joinAll cs) := by
      intro xs ms hxs hms
      refine joinAll_le fun x hx => ?_
      obtain ⟨m, hm, hrule⟩ := mapM_source hxs x hx
      obtain ⟨k, hk, hmk⟩ := hcover m (hms m hm).2
      obtain ⟨y, hy, hruleK⟩ := mapM_answer hcs k hk
      obtain ⟨x', hx', hle⟩ := mono (hms m hm).1 (hnormalK k hk)
        ((hms m hm).2.elim Ty.members_isMember Ty.members_isMember) (Ty.members_isMember hk)
        hmk hruleK
      rw [hrule] at hx'
      cases hx'
      exact AnswerOrder.trans hle (le_joinAll hy)
    exact AnswerOrder.join_le
      (side as _ has fun m hm => ⟨hnormalS m hm, Or.inl hm⟩)
      (side bs _ hbs fun m hm => ⟨hnormalT m hm, Or.inr hm⟩)
  · intro c typed
    obtain ⟨cs, hcs, rfl⟩ := Option.map_eq_some_iff.mp typed
    have side : ∀ (ms : List Ty),
        (∀ m ∈ ms, Ty.Normal m ∧ (m ∈ s.normalize.members ∨ m ∈ t.normalize.members)) →
        ∃ xs, ms.mapM rule = some xs := by
      intro ms hms
      obtain ⟨xs, hxs, -⟩ := mapM_total (f := rule) (P := fun _ => True) (xs := ms)
        fun m hm => by
          obtain ⟨k, hk, hmk⟩ := hcover m (hms m hm).2
          obtain ⟨y, -, hruleK⟩ := mapM_answer hcs k hk
          obtain ⟨x, hx, -⟩ := mono (hms m hm).1 (hnormalK k hk)
            ((hms m hm).2.elim Ty.members_isMember Ty.members_isMember) (Ty.members_isMember hk)
            hmk hruleK
          exact ⟨x, hx, trivial⟩
      exact ⟨xs, hxs⟩
    obtain ⟨as, has⟩ := side s.normalize.members fun m hm => ⟨hnormalS m hm, Or.inl hm⟩
    obtain ⟨bs, hbs⟩ := side t.normalize.members fun m hm => ⟨hnormalT m hm, Or.inr hm⟩
    exact ⟨joinAll as, joinAll bs, Option.map_eq_some_iff.mpr ⟨as, has, rfl⟩,
      Option.map_eq_some_iff.mpr ⟨bs, hbs, rfl⟩⟩

/-- A fold of joins from a normal start is its own normal form: each step is a join. The general
form of `joinAll_normalize`, its one consumer. -/
@[semantics "subtyping-algebra" (requirement := R14)]
theorem foldl_join_normalize : ∀ (types : List Ty) (acc : Ty), acc.normalize = acc →
    (types.foldl Ty.join acc).normalize = types.foldl Ty.join acc
  | [], _, hacc => hacc
  | x :: rest, acc, _ => foldl_join_normalize rest (Ty.join acc x) (Ty.normalize_join acc x)

/-- The join of a list of types is its own normal form. So a lifted rule that answers a type
answers a normal type. A step of `lift_union_eq`, its one consumer. -/
@[semantics "subtyping-algebra" (requirement := R14)]
theorem joinAll_normalize (types : List Ty) : (joinAll types).normalize = joinAll types :=
  foldl_join_normalize types .never rfl

/-- **Join, at the carrier `Ty`.** For a member rule that answers a type and is monotone in the
order, the lifted rule at a union is the join of the lifted rule at the two sides, as an
equation: `Option` joins strictly. Two normal types that are each below the other are one type
(`Ty.subN_equiv_iff`). A part of the claim `union-rule-lift`, as `lift_union` at a carrier whose
joins are canonical. At a pair the equation is not stated: `lift_union` gives it up to the
order. -/
@[semantics "subtyping-algebra" (requirement := R14)]
theorem lift_union_eq {rule : Ty → Option Ty} (mono : Below rule rule) (s t : Ty) :
    lift rule (.union s t) = (lift rule s).bind fun a => (lift rule t).map (Ty.join a) := by
  obtain ⟨some_some, inverse⟩ := lift_union mono s t
  cases hs : lift rule s with
  | none =>
    cases hu : lift rule (.union s t) with
    | none => rfl
    | some c =>
      obtain ⟨a, b, ha, -⟩ := inverse hu
      rw [hs] at ha
      exact nomatch ha
  | some a =>
    cases ht : lift rule t with
    | none =>
      cases hu : lift rule (.union s t) with
      | none => rfl
      | some c =>
        obtain ⟨a', b, -, hb⟩ := inverse hu
        rw [ht] at hb
        exact nomatch hb
    | some b =>
      obtain ⟨c, hc, hle, hge⟩ := some_some hs ht
      rw [hc]
      show some c = some (Ty.join a b)
      obtain ⟨cs, -, rfl⟩ := Option.map_eq_some_iff.mp hc
      have same : (joinAll cs).normalize = (Ty.join a b).normalize :=
        (Ty.subN_equiv_iff _ _).mp ⟨hle, hge⟩
      rw [joinAll_normalize, Ty.normalize_join] at same
      rw [same]

/-- The join reads its right side's normal form. A step of `foldl_join_start`, its one
consumer. -/
@[semantics "subtyping-algebra" (requirement := R14)]
theorem join_normalize_right (a b : Ty) : Ty.join a b.normalize = Ty.join a b := by
  rw [Ty.join_eq_ofMembers, Ty.join_eq_ofMembers, Ty.normalize_idem]

/-- A fold of joins from a normal start is the join of the start with the fold from `never`: the
join is associative, and `never` is its unit up to the normal form. It relates the fold of
`joinAll`, which starts at the left, to a rule that joins a union's head with its rest. A step
of `lift_unique`, its one consumer. -/
@[semantics "subtyping-algebra" (requirement := R14)]
theorem foldl_join_start : ∀ (types : List Ty) (acc : Ty), acc.normalize = acc →
    types.foldl Ty.join acc = Ty.join acc (types.foldl Ty.join .never)
  | [], acc, hacc => by
    show acc = Ty.join acc .never
    rw [Ty.join_never_right, hacc]
  | y :: rest, acc, _ => by
    show rest.foldl Ty.join (Ty.join acc y) = Ty.join acc (rest.foldl Ty.join (Ty.join .never y))
    rw [foldl_join_start rest (Ty.join acc y) (Ty.normalize_join acc y),
      foldl_join_start rest (Ty.join .never y) (Ty.normalize_join .never y), Ty.join_never,
      ← Ty.join_assoc, join_normalize_right]

/-- A list of normal union members in the row order, none below another, is the member list of
a normal type. A step of `lift_unique`, its one consumer: each tail of a normal union is
normal. -/
@[semantics "subtyping-algebra" (requirement := R14)]
theorem normal_ofMembers {ms : List Ty} (normal : ∀ m ∈ ms, Ty.Normal m)
    (atoms : ∀ m ∈ ms, m.isMember = true) (ascending : Effect4.Ascending ms)
    (maximal : ∀ x ∈ ms, ∀ y ∈ ms, Ty.sub x y = true → Ty.sub y x = true) :
    Ty.Normal (Ty.ofMembers ms) := by
  have h := Ty.normal_row ms normal atoms
  rw [Ty.normalizeRow_fixed ms ascending maximal] at h
  exact h

/-- **Uniqueness, at the carrier `Ty`.** Take a member rule that answers a type, and a map `f`
from types to answers with four properties. It reads the normal form. It answers `never` at
`never`. At a normal union member it is the member rule, up to the answer's normal form. At a
normal union of a union member `m` and a rest `r`, it is the join of its answers at `m` and at
`r`, and a refusal on either side refuses. Then `f` is the lifted rule. The lifted rule has the
four properties (`lift_congr`, `lift_never`, `lift_member`, and `lift_union_eq` for a monotone
member rule), so it is the one map that has them. A part of the claim `union-rule-lift`. Its
consumer is each rule that reads a union by its own recursion: `Tuple.typeAt`
(`src/Effect4/Program/Tuple.lean`) is one (`Test/Program/UnionRule.lean`), and each later
conversion states one equation with no induction of its own. It asks the join at normal unions
only, so it needs no monotone member rule. At another carrier it is not stated: it would need
the carrier's joins to be associative as an equation. -/
@[semantics "subtyping-algebra" (requirement := R14)]
theorem lift_unique {rule f : Ty → Option Ty}
    (normal : ∀ t, f t = f t.normalize)
    (never : f .never = some .never)
    (member : ∀ {m : Ty}, Ty.Normal m → m.isMember = true → f m = (rule m).map Ty.normalize)
    (union : ∀ {m r : Ty}, Ty.Normal m → m.isMember = true → Ty.Normal r →
      Ty.Normal (.union m r) → f (.union m r) = (f m).bind fun a => (f r).map (Ty.join a))
    (t : Ty) : f t = lift rule t := by
  have row : ∀ (ms : List Ty), (∀ m ∈ ms, Ty.Normal m) → (∀ m ∈ ms, m.isMember = true) →
      Effect4.Ascending ms →
      (∀ x ∈ ms, ∀ y ∈ ms, Ty.sub x y = true → Ty.sub y x = true) →
      f (Ty.ofMembers ms) = (ms.mapM rule).map joinAll := by
    intro ms
    induction ms with
    | nil => intro _ _ _ _; exact never
    | cons m rest ih =>
      intro hn ha hs hm
      have hnm := hn m List.mem_cons_self
      have ham := ha m List.mem_cons_self
      cases rest with
      | nil =>
        show f m = Option.map joinAll (rule m >>= fun a => List.mapM.loop rule [] [a])
        rw [member hnm ham]
        cases rule m with
        | none => rfl
        | some x =>
          show some x.normalize = some (Ty.join .never x)
          rw [Ty.join_never]
      | cons m' rest' =>
        have hnTail := fun x hx => hn x (List.mem_cons_of_mem m hx)
        have haTail := fun x hx => ha x (List.mem_cons_of_mem m hx)
        have hmTail := fun x hx y hy =>
          hm x (List.mem_cons_of_mem m hx) y (List.mem_cons_of_mem m hy)
        have tail := ih hnTail haTail (List.Pairwise.tail hs) hmTail
        show f (.union m (Ty.ofMembers (m' :: rest'))) = _
        rw [union hnm ham (normal_ofMembers hnTail haTail (List.Pairwise.tail hs) hmTail)
          (normal_ofMembers hn ha hs hm), member hnm ham, tail]
        cases hrule : rule m with
        | none =>
          have refused : (m :: m' :: rest').mapM rule = none := by
            cases hall : (m :: m' :: rest').mapM rule with
            | none => rfl
            | some ys =>
              obtain ⟨y, _, hy, -, -⟩ := mapM_cons_eq_some.mp hall
              rw [hrule] at hy
              exact nomatch hy
          rw [refused]
          rfl
        | some x =>
          cases hrest : (m' :: rest').mapM rule with
          | none =>
            have refused : (m :: m' :: rest').mapM rule = none := by
              cases hall : (m :: m' :: rest').mapM rule with
              | none => rfl
              | some ys =>
                obtain ⟨_, zs, -, hzs, -⟩ := mapM_cons_eq_some.mp hall
                rw [hrest] at hzs
                exact nomatch hzs
            rw [refused]
            rfl
          | some xs =>
            rw [mapM_cons_eq_some.mpr ⟨x, xs, hrule, hrest, rfl⟩]
            show some (Ty.join x.normalize (xs.foldl Ty.join .never)) =
              some (xs.foldl Ty.join (Ty.join .never x))
            rw [foldl_join_start xs (Ty.join .never x) (Ty.normalize_join .never x), Ty.join_never]
  have hN := Ty.normal_normalize t
  rw [normal t, lift_congr rule (Ty.normalize_idem t).symm]
  have hrow := row t.normalize.members (fun m hm => hN.members hm)
    (fun m hm => Ty.members_isMember hm) hN.members_ascending hN.members_maximal
  rw [hN.ofMembers_members] at hrow
  rw [hrow]
  unfold lift
  rw [Ty.normalize_idem]

/-! ## The guard: the lifted rule at one union member or none

`UnionRule.liftOne` is the lifted rule where the target's normal form has at most one union
member, and a refusal elsewhere (`src/Effect4/Program/UnionRule.lean`, decisions row 292). A
converted rule of the checker keeps it until the TypeScript printer writes the type arguments of
a call at a proper union. The laws above are written for the lifted rule, and the guard adds one
fact to them: `liftOne_eq_some_iff`. So the guard goes by one line: a rule that says `liftOne`
says `lift`, and each proof that used `liftOne_some` keeps its premise.

What the guard costs is stated here too. The monotone law holds only where the smaller target
has at most one union member (`Eliminator.liftOne_mono`). A guarded rule refuses a proper union
that is below a target it answers. -/

/-- **The guard, as one fact.** The guarded rule answers `a` at a target exactly when the
target's normal form has at most one union member and the lifted rule answers `a` there. It is
the whole meaning of the guard. A step of the proposed claim `union-rule-extend`. Its consumers
are the laws of this section. It says nothing of a member rule. -/
@[semantics "subtyping-algebra" (requirement := R14)]
proof_goal liftOne_eq_some_iff (rule : Ty → Option α) {t : Ty} {a : α} :
    liftOne rule t = some a ↔ t.normalize.members.length ≤ 1 ∧ lift rule t = some a

/-- **The guarded rule implies the lifted rule's answer.** Each law whose premise is an answer
of the lifted rule holds of the guarded rule through it: the transfer law, the closed types, the
upper form and its least half. A step of the proposed claim `union-rule-extend`. Its consumers
are `Eliminator.extend_adjoint`, and the closed types of a converted rule (`lift_closed_pair`).
The converse fails at a proper union. -/
@[semantics "subtyping-algebra" (requirement := R14)]
proof_goal liftOne_some {rule : Ty → Option α} {t : Ty} {a : α}
    (typed : liftOne rule t = some a) : lift rule t = some a

/-- **The guarded rule is the lifted rule at one union member or none.** A step of the proposed
claim `union-rule-extend`. Its consumer is `liftOne_member`. It says nothing at a proper union:
`liftOne_two` does. -/
@[semantics "subtyping-algebra" (requirement := R14)]
proof_goal liftOne_eq (rule : Ty → Option α) {t : Ty}
    (one : t.normalize.members.length ≤ 1) : liftOne rule t = lift rule t

/-- **The guarded rule refuses a proper union.** A target whose normal form has two union
members or more has no answer, whatever the member rule is. A step of the proposed claim
`union-rule-extend`: the refusal that decisions row 292 keeps. Its consumer is `extend_two`. It
is the guard's own refusal: the lifted rule can answer at such a target. -/
@[semantics "subtyping-algebra" (requirement := R14)]
proof_goal liftOne_two (rule : Ty → Option α) {t : Ty}
    (two : 1 < t.normalize.members.length) : liftOne rule t = none

/-- **The guarded rule reads the normal form.** Two types with one normal form have one answer.
A step of the proposed claim `union-rule-extend`, as `lift_congr` under the guard. Its consumers
are the control that shows what the guarded rule alone answers at a raw fiber type
(`Test/Program/Eliminators.lean`), and a converted rule once its raw answer goes. The extended
rule does not have this law: it keeps the raw answer of its member rule. -/
@[semantics "subtyping-algebra" (requirement := R14)]
proof_goal liftOne_congr (rule : Ty → Option α) {s t : Ty} (same : s.normalize = t.normalize) :
    liftOne rule s = liftOne rule t

/-- **The guarded rule is total at `never`.** It answers the least answer, whatever the member
rule is. A step of the proposed claim `union-rule-extend`. Its consumer is `extend_never`. -/
@[semantics "subtyping-algebra" (requirement := R14)]
proof_goal liftOne_never (rule : Ty → Option α) : liftOne rule .never = some Answer.bot

/-- **The guarded rule at one normal union member is the member rule**, up to the join with the
least answer. A step of the proposed claim `union-rule-extend`, as `lift_member` under the
guard. Its consumers are the same control as `liftOne_congr`, and a converted rule at a raw type
of its constructor once its raw answer goes. -/
@[semantics "subtyping-algebra" (requirement := R14)]
proof_goal liftOne_member (rule : Ty → Option α) {t : Ty} (normal : Ty.Normal t)
    (member : t.isMember = true) : liftOne rule t = (rule t).map (Answer.join Answer.bot)

section GuardedEliminator

variable [AnswerOrder α] {rule : Ty → Option α} {C : α → Ty}

/-- **Where the member rule answers at a raw type.** Let the member rule of an eliminator answer
`a` at a type that need not be normal. The guarded rule answers there, with an answer that is
above `a` and below `a`, exactly when the type's normal form has at most one union member. That
condition is the exact member premise: the three facts of `Eliminator` do not give it. A
constructor whose normal form distributes over a union fails it, and a product is one
(`Test/Program/Eliminators.lean`). A step of the proposed claim `union-rule-extend`. Its
consumer is `Eliminator.extend_liftOne`. It gives no equation: the answer's spelling can
change, which is why the extended rule keeps the raw answer. -/
@[semantics "subtyping-algebra" (requirement := R14)]
proof_goal Eliminator.liftOne_answers (e : Eliminator rule C) {t : Ty} {a : α}
    (answered : rule t = some a) :
    (∃ a', liftOne rule t = some a' ∧ le a a' ∧ le a' a) ↔ t.normalize.members.length ≤ 1

/-- **Where a guarded eliminator answers.** It answers exactly at a target whose normal form has
at most one union member and that is below some `C b`. It is the first half of
`Eliminator.adjoint` under the guard: the guard removes the proper unions and nothing else. A
step of the proposed claim `union-rule-extend`. Its consumers are
`Eliminator.extend_isSome_iff` and `Eliminator.extend_liftOne`. -/
@[semantics "subtyping-algebra" (requirement := R14)]
proof_goal Eliminator.liftOne_isSome_iff (e : Eliminator rule C) (t : Ty) :
    (liftOne rule t).isSome = true ↔
      t.normalize.members.length ≤ 1 ∧ ∃ b, Ty.subN t (C b) = true

/-- **What the guard keeps of the monotone law.** Take a target `s` below a target `t` in the
checker's order, and let the normal form of `s` have at most one union member. Where the guarded
rule answers `b` at `t`, it answers at `s`, and its answer is below `b`. Without the premise on
`s` the law is false: a proper union below a fiber type is refused
(`Test/Program/Eliminators.lean`). A step of the proposed claim `union-rule-extend`. Its
consumer is the proposed claim `checker-monotone` at a converted rule once its raw answer goes.
It does not establish `checker-monotone`. -/
@[semantics "subtyping-algebra" (requirement := R14)]
proof_goal Eliminator.liftOne_mono (e : Eliminator rule C) {s t : Ty}
    (smaller : Ty.subN s t = true) (one : s.normalize.members.length ≤ 1) {b : α}
    (typed : liftOne rule t = some b) : ∃ a, liftOne rule s = some a ∧ le a b

end GuardedEliminator

/-! ## The extended rule: a converted rule of the checker

`UnionRule.extend` is the member rule's own answer where the member rule answers at the raw
target, and the guarded rule elsewhere (`src/Effect4/Program/UnionRule.lean`, decisions row
294). A by-shape function of the checker is converted to `extend` of itself. The conversion
then refuses no program that the function admitted, and it changes no type of such a program:
`extend_agrees` is the exact statement. It gains the targets that the guarded rule answers and
the function refuses: `never`, and a raw union whose normal form is one union member.

The raw answer is interim, as the guard is. It goes when the match of a template reads a
request up to its normal form. `Eliminator.extend_liftOne` says what that removal changes at a
rule whose member rule answers only where the normal form has at most one union member: no
verdict, and each answer up to the order only. -/

/-- **The extended rule, as one fact.** It answers `a` at a target exactly when the member rule
answers `a` there, or the member rule refuses the target and the guarded rule answers `a`. It
is the whole meaning of the definition. A step of the proposed claim `union-rule-extend`. Its
consumers are the laws of this section, and each law of a converted rule that is proved by its
two alternatives. -/
@[semantics "subtyping-algebra" (requirement := R14)]
proof_goal extend_eq_some_iff (rule : Ty → Option α) {t : Ty} {a : α} :
    extend rule t = some a ↔ rule t = some a ∨ (rule t = none ∧ liftOne rule t = some a)

/-- **Agreement.** Where the member rule answers at a raw target, the extended rule answers
there, with the same answer. So a conversion to the extended rule refuses no target that the
by-shape function answered, and it changes no answer: no admitted program moves at this rule. A
part of the proposed claim `union-rule-extend`. Its consumers are `Eliminator.extend_laws`, and
each converted rule at a raw type of its constructor: `fiberTy_fiberOf`
(`src/Effect4/Laws/Program/Eliminators.lean`). It says nothing of a rule of the checker that
reads the same type through another function. -/
@[semantics "subtyping-algebra" (requirement := R14)]
proof_goal extend_agrees {rule : Ty → Option α} {t : Ty} {a : α} (answered : rule t = some a) :
    extend rule t = some a

/-- **Where the member rule refuses, the extended rule is the guarded rule.** A part of the
proposed claim `union-rule-extend`. Its consumers are `extend_never` and `extend_two`. -/
@[semantics "subtyping-algebra" (requirement := R14)]
proof_goal extend_refused {rule : Ty → Option α} {t : Ty} (refused : rule t = none) :
    extend rule t = liftOne rule t

/-- **The extended rule at `never`.** A member rule that refuses `never` extends to a rule that
answers the least answer there. `never` is no union member, so a by-shape function refuses it.
A part of the proposed claim `union-rule-extend`. Its consumers are `Eliminator.extend_bot`, and
a hole that is declared at `never` under a converted rule (`Test/Program/Eliminators.lean`). -/
@[semantics "subtyping-algebra" (requirement := R14)]
proof_goal extend_never {rule : Ty → Option α} (refused : rule .never = none) :
    extend rule .never = some Answer.bot

/-- **The extended rule keeps the refusal at a proper union.** Where the member rule refuses a
target whose normal form has two union members or more, the extended rule refuses it. A part of
the proposed claim `union-rule-extend`: the refusal that decisions row 292 keeps. Its consumer
is `Eliminator.extend_laws`. The premise on the member rule is needed: a member rule can answer
at a raw type whose normal form is a proper union, and a product is such a type. -/
@[semantics "subtyping-algebra" (requirement := R14)]
proof_goal extend_two {rule : Ty → Option α} {t : Ty} (refused : rule t = none)
    (two : 1 < t.normalize.members.length) : extend rule t = none

section ConvertedEliminator

variable [AnswerOrder α] {rule : Ty → Option α} {C : α → Ty}

/-- **The upper form and its least half, through both alternatives.** Where the extended rule of
an eliminator answers `a` at a target, an answer `b` is above `a` exactly when the target is
below `C b`, in the checker's order. At the member rule's own answer the target is `C a`, and
the constructor keeps and reflects the order. At the guarded rule's answer it is the second half
of `Eliminator.adjoint`. A part of the proposed claim `union-rule-extend`. Its consumers are
`Eliminator.extend_upper` and `Eliminator.extend_least`. -/
@[semantics "subtyping-algebra" (requirement := R14)]
proof_goal Eliminator.extend_adjoint (e : Eliminator rule C) {t : Ty} {a : α}
    (typed : extend rule t = some a) (b : α) : le a b ↔ Ty.subN t (C b) = true

/-- **The upper form of a converted eliminator.** A target that the extended rule answers at `a`
is below `C a`, in the checker's order. It takes the place of the equation of a by-shape rule:
a use site moves a value of the target up by `fits_subN`. A part of the proposed claim
`union-rule-extend`. Its consumer is the upper form at each converted rule: `fiberTy_upper`
(`src/Effect4/Laws/Program/Eliminators.lean`). The inequality is false in raw `Ty.sub`. -/
@[semantics "subtyping-algebra" (requirement := R14)]
proof_goal Eliminator.extend_upper (e : Eliminator rule C) {t : Ty} {a : α}
    (typed : extend rule t = some a) : Ty.subN t (C a) = true

/-- **A converted eliminator answers the least.** Each `b` with the target below `C b` is above
the extended rule's answer. A part of the proposed claim `union-rule-extend`. Its consumers are
`Eliminator.extend_mono`, and a type that a printer writes at a call, which must be above the
answer. -/
@[semantics "subtyping-algebra" (requirement := R14)]
proof_goal Eliminator.extend_least (e : Eliminator rule C) {t : Ty} {a b : α}
    (typed : extend rule t = some a) (upper : Ty.subN t (C b) = true) : le a b

/-- **A converted eliminator answers a least answer at `never`.** Its answer there is below
every answer. Where the member rule refuses `never`, the answer is the least answer itself
(`extend_never`). A part of the proposed claim `union-rule-extend`. Its consumer is
`Eliminator.extend_laws`. -/
@[semantics "subtyping-algebra" (requirement := R14)]
proof_goal Eliminator.extend_bot (e : Eliminator rule C) :
    ∃ a, extend rule .never = some a ∧ ∀ b, le a b

/-- **Where a converted eliminator answers.** It answers exactly where its member rule answers,
or where the target's normal form has at most one union member and the target is below some
`C b`. A part of the proposed claim `union-rule-extend`. Its consumers are
`Eliminator.extend_mono` and `Eliminator.extend_liftOne`, and the reading of a conversion's
differential: a refusal that stays is a proper union or a target below no `C b`. -/
@[semantics "subtyping-algebra" (requirement := R14)]
proof_goal Eliminator.extend_isSome_iff (e : Eliminator rule C) (t : Ty) :
    (extend rule t).isSome = true ↔
      (rule t).isSome = true ∨ (t.normalize.members.length ≤ 1 ∧ ∃ b, Ty.subN t (C b) = true)

/-- **What a converted eliminator keeps of the monotone law.** Take a target `s` below a target
`t` in the checker's order, and let the normal form of `s` have at most one union member. Where
the extended rule answers `b` at `t`, it answers at `s`, and its answer is below `b`. Without
the premise on `s` the law is false: a proper union below a fiber type is refused
(`Test/Program/Eliminators.lean`). A part of the proposed claim `union-rule-extend`. Its
consumer is the proposed claim `checker-monotone` at a converted rule, where a smaller type is
`never` or one union member. It does not establish `checker-monotone`. -/
@[semantics "subtyping-algebra" (requirement := R14)]
proof_goal Eliminator.extend_mono (e : Eliminator rule C) {s t : Ty}
    (smaller : Ty.subN s t = true) (one : s.normalize.members.length ≤ 1) {b : α}
    (typed : extend rule t = some b) : ∃ a, extend rule s = some a ∧ le a b

/-- **The raw answer is a matter of spelling, where the member rule answers at one union
member.** Fix a target, and let its normal form have at most one union member wherever the
member rule answers at it. Then the extended rule and the guarded rule answer at the target
together, and their answers are each below the other. So the removal of the raw answer changes
no verdict at such a rule, and it changes an answer up to the order only. A part of the proposed
claim `union-rule-extend`. Its consumer is that removal (decisions row 294), at each converted
rule whose member rule has the premise: `Member.fiber_one`
(`src/Effect4/Laws/Program/Eliminators.lean`). It does not say that a later rule of the checker
reads the two answers alike: an atom's scheme does not. -/
@[semantics "subtyping-algebra" (requirement := R14)]
proof_goal Eliminator.extend_liftOne (e : Eliminator rule C) {t : Ty}
    (one : ∀ {a : α}, rule t = some a → t.normalize.members.length ≤ 1) :
    (∀ {a : α}, extend rule t = some a → ∃ a', liftOne rule t = some a' ∧ le a a' ∧ le a' a) ∧
    (∀ {a' : α}, liftOne rule t = some a' → ∃ a, extend rule t = some a ∧ le a a' ∧ le a' a)

/-- **The contract of a converted eliminator, as one statement**: what the extended rule of an
eliminator gives, for every `Eliminator rule C`. It agrees with the member rule wherever the
member rule answers. Where the member rule refuses, it is the guarded rule. It answers a least
answer at `never`. Its answer `a` puts the target below `C a`, in the checker's order, and an
answer `b` is above `a` exactly when the target is below `C b`. Where the member rule refuses a
target whose normal form has two union members or more, it refuses. It is the pointer of the
proposed claim `union-rule-extend`, and it adds nothing to its parts.
`Eliminator.extend_isSome_iff`, `Eliminator.extend_mono` and `Eliminator.extend_liftOne` stand
beside it. Its consumer is each conversion of candidate N: an instance proves the three facts of
`Eliminator` and reads its contract here. It does not establish `checker-monotone`, or anything
that tsgo accepts. It says that no admitted program moves at the converted rule, and it says
nothing of another rule. -/
@[semantics "subtyping-algebra" (requirement := R14)]
proof_goal Eliminator.extend_laws (e : Eliminator rule C) :
    (∀ {t : Ty} {a : α}, rule t = some a → extend rule t = some a) ∧
    (∀ {t : Ty}, rule t = none → extend rule t = liftOne rule t) ∧
    (∃ a, extend rule .never = some a ∧ ∀ b, le a b) ∧
    (∀ {t : Ty} {a : α}, extend rule t = some a →
      Ty.subN t (C a) = true ∧ ∀ b : α, le a b ↔ Ty.subN t (C b) = true) ∧
    (∀ {t : Ty}, rule t = none → 1 < t.normalize.members.length → extend rule t = none)

end ConvertedEliminator

end Effect4.Program.UnionRule
