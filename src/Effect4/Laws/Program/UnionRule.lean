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

end Effect4.Program.UnionRule
