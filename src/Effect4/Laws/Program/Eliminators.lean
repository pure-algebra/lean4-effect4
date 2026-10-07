import Effect4.Program.Typing.Rules
import Effect4.Program.Decision
import Effect4.Program.NativeAtom
import Effect4.Laws.Program.UnionRule
import Effect4.Laws.Program.TypeAlgebra

/-!
# Laws.Program.Eliminators — the converted eliminators of the checker

A rule of the checker that reads a type by one constructor is an eliminator. Its conversion
makes it the extended rule of its member rule (`UnionRule.extend`,
`src/Effect4/Program/UnionRule.lean`; candidate N, decisions rows 285 and 292 to 294). This file
holds one section for each converted rule, and each later conversion adds its section here.

**What a section holds, in order.** The member rule is `Member.<rule>`
(`src/Effect4/Program/Typing/Rules.lean`), and the rule keeps its name.

1. **The constructor's order**: the checker's order on two types of the constructor is the order
   on their arguments. It is the fact `embeds` of the instance.
2. **The instance**: the member rule is the eliminator of the constructor
   (`UnionRule.Eliminator`), from three facts of the member rule.
3. **The member rule at one union member**, where it holds: the member rule answers only at a
   type whose normal form has at most one union member. A constructor whose normal form
   distributes over a union does not have it.
4. **The member rule at a closed type**: a closed type of the constructor has closed arguments.
   The rule's closed case is then one application
   (`extend_closed_pair`; `closed_fiberTy`, `src/Effect4/Laws/Program/Typing/Closed.lean`).
5. **The rule's own facts**, each by one application of the contract: the rule at a raw type of
   its constructor, and the upper form that a use site names.

**What a section does not hold.** It proves nothing about unions, normal forms or the guard. The
contract of a converted eliminator is proved once, for every `Eliminator`
(`Eliminator.extend_laws`, `src/Effect4/Laws/Program/UnionRule.lean`): the rule agrees with its
member rule, it answers a least answer at `never`, its answer is the least with the target below
the constructor's image, and it keeps the refusal at a proper union.

**At a use site.** Where a proof rewrote by the equation of a by-shape rule, it moves the value
up: `fits_subN w (fiberTy_upper hfib) v hfit` (`src/Effect4/Laws/Program/Typed/Denotation.lean`).
The inequality is in `Ty.subN`, and never in raw `Ty.sub`.

Placement. Concept `subtyping-algebra`, requirement R14, under the claim
`union-rule-extend`. Reach: the fiber rule, in the order `Ty.subN`. The laws do not establish
`checker-monotone`, and they say nothing of what tsgo accepts. The controls are in
`Test/Program/Eliminators.lean`. The design is `docs/research/2026-10-06-seat-PILOT-design.md`.
-/

set_option autoImplicit false

namespace Effect4.Program

open UnionRule

/-! ## The fiber rule

`fiberTy` is the extended rule of `Member.fiber`. Its constructor is the fiber type of a pair
of columns, `Function.uncurry Ty.fiberOf`, and it is covariant in both columns. -/

/-- The checker's order on fiber types is the order on their columns: the fiber constructor
keeps and reflects the order. The fact `embeds` of `Member.fiber_eliminator`, its consumer. -/
@[semantics "subtyping-algebra" (requirement := R14)]
theorem Ty.subN_fiberOf_iff (a e a' e' : Ty) :
    Ty.subN (.fiberOf a e) (.fiberOf a' e') = true ↔
      Ty.subN a a' = true ∧ Ty.subN e e' = true := by
  show Ty.sub (.fiberOf a.normalize e.normalize) (.fiberOf a'.normalize e'.normalize) = true ↔ _
  rw [Ty.sub_args_fiberOf]
  simp only [Ty.argsBelow, Ty.args, Ty.Variance.holds, List.zip, List.zipWith, List.all_cons,
    List.all_nil, Bool.and_true, Bool.and_eq_true, Ty.subN]

/-- **`Member.fiber` is the eliminator of the fiber constructor.** It answers only at a fiber
type, with that type's columns. The constructor keeps and reflects the order. It reads each
normal union member that is below a fiber type. A step of the claim
`union-rule-extend`, at its first instance. Its consumers are `fiberTy_upper`, and the order
laws of the fiber rule by projection (`Test/Program/Eliminators.lean`). -/
@[semantics "subtyping-algebra" (requirement := R14)]
theorem Member.fiber_eliminator : Eliminator Member.fiber (Function.uncurry Ty.fiberOf) where
  shape {m a} answered := by
    cases m with
    | fiberOf value error =>
      cases answered
      rfl
    | _ => exact nomatch answered
  embeds := Ty.subN_fiberOf_iff _ _ _ _
  reads {m b} normal member below := by
    have raw : Ty.sub m (.fiberOf b.1.normalize b.2.normalize) = true := by
      have h := below
      unfold Ty.subN at h
      rw [normal.fixed] at h
      exact h
    rw [Ty.sub_eq_args m _ member rfl (Ty.leafRule_of_right_none m _ rfl)
      (Ty.topRule_eq_false (fun h => Ty.noConfusion h)), Bool.and_eq_true] at raw
    cases m with
    | fiberOf value error => exact ⟨(value, error), rfl⟩
    | _ => exact nomatch raw.1

/-- **`Member.fiber` answers at one union member.** Where it answers at a raw type, that type's
normal form has at most one union member: the normal form of a fiber type is a fiber type. It
is the premise of `Eliminator.extend_liftOne` at the fiber rule, its consumer: the raw answer of
`fiberTy` is a matter of spelling. A rule that reads a product does not have this fact. -/
@[semantics "subtyping-algebra" (requirement := R14)]
theorem Member.fiber_one {t : Ty} {a : Ty × Ty} (answered : Member.fiber t = some a) :
    t.normalize.members.length ≤ 1 := by
  cases t with
  | fiberOf value error => exact Nat.le_refl 1
  | _ => exact nomatch answered

/-- **A closed fiber type has closed columns**: the member fact of `extend_closed_pair` at the
fiber rule. Its consumer is `closed_fiberTy`
(`src/Effect4/Laws/Program/Typing/Closed.lean`), the fiber case of the claim
`checked-types-closed`. -/
@[semantics "subtyping-algebra" (requirement := R14)]
theorem Member.fiber_closed {m : Ty} {a : Ty × Ty} (closed : m.closed = true)
    (answered : Member.fiber m = some a) : a.1.closed = true ∧ a.2.closed = true := by
  cases m with
  | fiberOf value error =>
    cases answered
    exact Bool.and_eq_true_iff.mp closed
  | _ => exact nomatch answered

/-- **The fiber rule at a raw fiber type**: the two columns as they are spelled, as before the
conversion. It is `extend_agrees` at the fiber rule: no program that the by-shape rule admitted
moves at this rule, and its type keeps its spelling. A step of the claim
`union-rule-extend`. Its consumers are the differential of the conversion, and a typing
derivation of a join of a forked fiber. -/
@[semantics "subtyping-algebra" (requirement := R14)]
theorem fiberTy_fiberOf (value error : Ty) :
    fiberTy (.fiberOf value error) = some (value, error) :=
  extend_agrees rfl

/-- **The upper form of the fiber rule.** A handle type that the fiber rule answers at a pair of
columns is below the fiber type of that pair, in the checker's order. It takes the place of the
equation `fiberTy_eq_some`, which is false of the converted rule: at `never` the rule answers
and the type is no fiber type. A use site moves a value of the handle type up by `fits_subN`.
A step of the claim `denote-typed` (R3). Its consumer is the fiber arms of
`src/Effect4/Laws/Program/Typed/Denotation.lean`. The inequality is false in raw `Ty.sub`. -/
@[semantics "subtyping-algebra" (requirement := R14)]
theorem fiberTy_upper {t : Ty} {pair : Ty × Ty} (typed : fiberTy t = some pair) :
    Ty.subN t (.fiberOf pair.1 pair.2) = true :=
  Member.fiber_eliminator.extend_upper typed

/-! ## The list rule

`Checker.listOf?` is the extended rule of `Member.list`. Its constructor is the list constructor,
`Ty.list`, and it is covariant. -/

/-- The checker's order on list types is the order on their element types: the list constructor
keeps and reflects the order. The fact `embeds` of `Member.list_eliminator`, its consumer. -/
@[semantics "subtyping-algebra" (requirement := R14)]
theorem Ty.subN_list_iff (t t' : Ty) :
    Ty.subN (.list t) (.list t') = true ↔ Ty.subN t t' = true := by
  show Ty.sub (.list t.normalize) (.list t'.normalize) = true ↔ _
  rw [Ty.sub_args_list]
  simp only [Ty.argsBelow, Ty.args, Ty.Variance.holds, List.zip, List.zipWith, List.all_cons,
    List.all_nil, Bool.and_true, Ty.subN]

/-- **`Member.list` is the eliminator of the list constructor.** It answers only at a list type,
with that type's element type. The constructor keeps and reflects the order. It reads each normal
union member that is below a list type. A step of the claim `union-rule-extend`. -/
@[semantics "subtyping-algebra" (requirement := R14)]
theorem Member.list_eliminator : Eliminator Member.list Ty.list where
  shape {m a} answered := by
    cases m with
    | list t =>
      cases answered
      rfl
    | _ => exact nomatch answered
  embeds := Ty.subN_list_iff _ _
  reads {m b} normal member below := by
    have raw : Ty.sub m (.list b.normalize) = true := by
      have h := below
      unfold Ty.subN at h
      rw [normal.fixed] at h
      exact h
    rw [Ty.sub_eq_args m _ member rfl (Ty.leafRule_of_right_none m _ rfl)
      (Ty.topRule_eq_false (fun h => Ty.noConfusion h)), Bool.and_eq_true] at raw
    cases m with
    | list t => exact ⟨t, rfl⟩
    | _ => exact nomatch raw.1

/-- **`Member.list` answers at one union member.** -/
@[semantics "subtyping-algebra" (requirement := R14)]
theorem Member.list_one {t : Ty} {a : Ty} (answered : Member.list t = some a) :
    t.normalize.members.length ≤ 1 := by
  cases t with
  | list _ => exact Nat.le_refl 1
  | _ => exact nomatch answered

/-- **A closed list type has a closed element type.** -/
@[semantics "subtyping-algebra" (requirement := R14)]
theorem Member.list_closed {m : Ty} {a : Ty} (closed : m.closed = true)
    (answered : Member.list m = some a) : a.closed = true := by
  cases m with
  | list _ =>
    cases answered
    exact closed
  | _ => exact nomatch answered

/-- **The list rule at a raw list type**: today's answer. -/
@[semantics "subtyping-algebra" (requirement := R14)]
theorem listOf_list (t : Ty) : Checker.listOf? (.list t) = some t :=
  extend_agrees rfl

/-- **The upper form of the list rule.** -/
@[semantics "subtyping-algebra" (requirement := R14)]
theorem listOf_upper {t : Ty} {item : Ty} (typed : Checker.listOf? t = some item) :
    Ty.subN t (.list item) = true :=
  Member.list_eliminator.extend_upper typed

/-! ## The exit rule

`Checker.exitOf?` is the extended rule of `Member.exit`. Its constructor is the exit type of a pair
of types, `Function.uncurry Ty.exitOf`, and it is covariant in both columns. -/

/-- The checker's order on exit types is the order on their columns: the exit constructor
keeps and reflects the order. The fact `embeds` of `Member.exit_eliminator`, its consumer. -/
@[semantics "subtyping-algebra" (requirement := R14)]
theorem Ty.subN_exitOf_iff (a e a' e' : Ty) :
    Ty.subN (.exitOf a e) (.exitOf a' e') = true ↔
      Ty.subN a a' = true ∧ Ty.subN e e' = true := by
  show Ty.sub (.exitOf a.normalize e.normalize) (.exitOf a'.normalize e'.normalize) = true ↔ _
  rw [Ty.sub_args_exitOf]
  simp only [Ty.argsBelow, Ty.args, Ty.Variance.holds, List.zip, List.zipWith, List.all_cons,
    List.all_nil, Bool.and_true, Bool.and_eq_true, Ty.subN]

/-- **`Member.exit` is the eliminator of the exit constructor.** It answers only at an exit type,
with that type's columns. The constructor keeps and reflects the order. It reads each normal
union member that is below an exit type. A step of the claim `union-rule-extend`. -/
@[semantics "subtyping-algebra" (requirement := R14)]
theorem Member.exit_eliminator : Eliminator Member.exit (Function.uncurry Ty.exitOf) where
  shape {m a} answered := by
    cases m with
    | exitOf value error =>
      cases answered
      rfl
    | _ => exact nomatch answered
  embeds := Ty.subN_exitOf_iff _ _ _ _
  reads {m b} normal member below := by
    have raw : Ty.sub m (.exitOf b.1.normalize b.2.normalize) = true := by
      have h := below
      unfold Ty.subN at h
      rw [normal.fixed] at h
      exact h
    rw [Ty.sub_eq_args m _ member rfl (Ty.leafRule_of_right_none m _ rfl)
      (Ty.topRule_eq_false (fun h => Ty.noConfusion h)), Bool.and_eq_true] at raw
    cases m with
    | exitOf value error => exact ⟨(value, error), rfl⟩
    | _ => exact nomatch raw.1

/-- **`Member.exit` answers at one union member.** -/
@[semantics "subtyping-algebra" (requirement := R14)]
theorem Member.exit_one {t : Ty} {a : Ty × Ty} (answered : Member.exit t = some a) :
    t.normalize.members.length ≤ 1 := by
  cases t with
  | exitOf _ _ => exact Nat.le_refl 1
  | _ => exact nomatch answered

/-- **A closed exit type has closed value and error types.** -/
@[semantics "subtyping-algebra" (requirement := R14)]
theorem Member.exit_closed {m : Ty} {a : Ty × Ty} (closed : m.closed = true)
    (answered : Member.exit m = some a) : a.1.closed = true ∧ a.2.closed = true := by
  cases m with
  | exitOf _ _ =>
    cases answered
    exact Bool.and_eq_true_iff.mp closed
  | _ => exact nomatch answered

/-- **The exit rule at a raw exit type**: today's answer. -/
@[semantics "subtyping-algebra" (requirement := R14)]
theorem exitOf_exitOf (v e : Ty) : Checker.exitOf? (.exitOf v e) = some (v, e) :=
  extend_agrees rfl

/-- **The upper form of the exit rule.** -/
@[semantics "subtyping-algebra" (requirement := R14)]
theorem exitOf_upper {t : Ty} {pair : Ty × Ty} (typed : Checker.exitOf? t = some pair) :
    Ty.subN t (.exitOf pair.1 pair.2) = true :=
  Member.exit_eliminator.extend_upper typed

/-! ## The option rule

`optionTy` is the guarded rule of `Member.option` (`UnionRule.liftOne`). Its constructor is
`Ty.option`, and it is covariant. The rule that `Decision.arms` held before its conversion read
the normal form of its target, and never the raw head. So its conversion is the guarded rule, and
not the extended rule: the extended rule answers the raw element at a raw option type, which moves
a type (`optionTy_eq_normal`; the controls are in `Test/Program/Eliminators.lean`). -/

/-- The checker's order on option types is the order on their element types: the option constructor
keeps and reflects the order. The fact `embeds` of `Member.option_eliminator`, its consumer. -/
@[semantics "subtyping-algebra" (requirement := R14)]
theorem Ty.subN_option_iff (t t' : Ty) :
    Ty.subN (.option t) (.option t') = true ↔ Ty.subN t t' = true := by
  show Ty.sub (.option t.normalize) (.option t'.normalize) = true ↔ _
  rw [Ty.sub_args_option]
  simp only [Ty.argsBelow, Ty.args, Ty.Variance.holds, List.zip, List.zipWith, List.all_cons,
    List.all_nil, Bool.and_true, Ty.subN]

/-- **`Member.option` is the eliminator of the option constructor.** It answers only at an option type,
with that type's element type. The constructor keeps and reflects the order. It reads each normal
union member that is below an option type. A step of the claim `union-rule-extend`. -/
@[semantics "subtyping-algebra" (requirement := R14)]
theorem Member.option_eliminator : Eliminator Member.option Ty.option where
  shape {m a} answered := by
    cases m with
    | option a =>
      cases answered
      rfl
    | _ => exact nomatch answered
  embeds := Ty.subN_option_iff _ _
  reads {m b} normal member below := by
    have raw : Ty.sub m (.option b.normalize) = true := by
      have h := below
      unfold Ty.subN at h
      rw [normal.fixed] at h
      exact h
    rw [Ty.sub_eq_args m _ member rfl (Ty.leafRule_of_right_none m _ rfl)
      (Ty.topRule_eq_false (fun h => Ty.noConfusion h)), Bool.and_eq_true] at raw
    cases m with
    | option a => exact ⟨a, rfl⟩
    | _ => exact nomatch raw.1

/-- **A closed option type has a closed element type.** -/
@[semantics "subtyping-algebra" (requirement := R14)]
theorem Member.option_closed {m : Ty} {a : Ty} (closed : m.closed = true)
    (answered : Member.option m = some a) : a.closed = true := by
  cases m with
  | option _ =>
    cases answered
    exact closed
  | _ => exact nomatch answered

/-- **The option rule at an option type whose element is its own normal form**: the element.
The guarded rule at one normal union member is the member rule (`liftOne_member`). A step of the
claim `union-rule-extend`, at a rule that reads the normal form. Its consumer is
`answers_selectOptionWith_kept` (`src/Effect4/Laws/Modules/Waiting.lean`). At an element that is
not its own normal form the answer is the normal form, as it was before the conversion. -/
@[semantics "subtyping-algebra" (requirement := R14)]
theorem optionTy_option {a : Ty} (canonical : a.normalize = a) : optionTy (.option a) = some a := by
  have fixed : (Ty.option a).normalize = .option a := by
    show Ty.option a.normalize = Ty.option a
    rw [canonical]
  have normal : Ty.Normal (.option a) := fixed ▸ Ty.normal_normalize (.option a)
  show liftOne Member.option (.option a) = some a
  rw [liftOne_member Member.option normal rfl]
  show some (Ty.join .never a) = some a
  rw [Ty.join_never, canonical]

/-- **The upper form of the option rule.** A target that the rule answers is below the option
type of the answer, in the checker's order: the guarded rule answers the lifted rule's answer.
Its consumers are `Decision.decide_typed` (`src/Effect4/Laws/Program/Decision.lean`) and the
membership laws of a selection. -/
@[semantics "subtyping-algebra" (requirement := R14)]
theorem optionTy_upper {t : Ty} {a : Ty} (typed : optionTy t = some a) :
    Ty.subN t (.option a) = true :=
  Member.option_eliminator.lift_upper (liftOne_some typed)

/-- **The option rule is the rule it was, away from `never`.** Before its conversion
`Decision.arms` read the target's normal form by its head: the element type at an option type,
and a refusal elsewhere. At every target whose normal form is not `never`, the converted rule is
that function. So the conversion refuses no program that the rule admitted, and it moves no type.
It is the connector of the conversion (`AGENTS.md`, Working), and a step of the claim
`union-rule-extend`. At `never` the old rule refused, and the converted rule answers `never`
(`UnionRule.liftOne_never`): that is the conversion's one new answer. -/
@[semantics "subtyping-algebra" (requirement := R14)]
theorem optionTy_eq_normal {t : Ty} (some_member : t.normalize ≠ .never) :
    optionTy t = (match t.normalize with
      | .option a => some a
      | _ => none) := by
  have normal := Ty.normal_normalize t
  have built := normal.ofMembers_members
  show liftOne Member.option t = _
  unfold liftOne lift
  generalize t.normalize = n at normal built some_member ⊢
  match hm : n.members with
  | [] =>
    rw [hm] at built
    exact absurd built.symm some_member
  | [m] =>
    rw [hm] at built
    have same : m = n := built
    subst same
    cases m with
    | option a =>
      have fixed := normal.fixed
      have inner : a.normalize = a := by
        change Ty.option a.normalize = Ty.option a at fixed
        exact Ty.option.inj fixed
      show some (Ty.join .never a) = some a
      rw [Ty.join_never, inner]
    | _ => rfl
  | m₁ :: m₂ :: rest =>
    rw [hm] at built
    subst built
    rfl

/-! ## The cause rule

`causeInputError?` is the extended rule of `Member.cause`. It reads two heads: `.causeOf` and
`.exitOf`. Its upper map is `causeUpper e := .union (.causeOf e) (.exitOf .unknown e)`. -/

/-- The upper map of the cause rule: every cause or exit input with error type `e` is below
`causeUpper e`. The cause rule reads two heads, so it is no eliminator of one constructor, and
this union of the two heads takes the constructor's place in its four member facts
(`Member.cause_upper`, `Member.cause_least`, `Member.cause_reads`, `cause_mono`). -/
def causeUpper (e : Ty) : Ty := .union (.causeOf e) (.exitOf .unknown e)

/-- The checker's order on cause types is the order on their error types: the cause constructor
keeps and reflects the order. A step of `cause_mono` and of `Member.cause_cases_of_below`, its
consumers. -/
@[semantics "subtyping-algebra" (requirement := R14)]
theorem Ty.subN_causeOf_iff (e e' : Ty) :
    Ty.subN (.causeOf e) (.causeOf e') = true ↔ Ty.subN e e' = true := by
  show Ty.sub (.causeOf e.normalize) (.causeOf e'.normalize) = true ↔ _
  rw [Ty.sub_args_causeOf]
  simp only [Ty.argsBelow, Ty.args, Ty.Variance.holds, List.zip, List.zipWith, List.all_cons,
    List.all_nil, Bool.and_true, Ty.subN]

/-- A cause type is below the upper type of its error type. A step of `Member.cause_upper`, its
consumer. -/
@[semantics "subtyping-algebra" (requirement := R14)]
theorem subN_causeOf_causeUpper (e : Ty) : Ty.subN (.causeOf e) (causeUpper e) = true :=
  Ty.OrderProof.sub_normalize_union_left Ty.sub_trans (.causeOf e) (.exitOf .unknown e)

/-- An exit type is below the upper type of its error type, whatever its value type is. A step
of `Member.cause_upper`, its consumer. -/
@[semantics "subtyping-algebra" (requirement := R14)]
theorem subN_exitOf_causeUpper (v e : Ty) : Ty.subN (.exitOf v e) (causeUpper e) = true := by
  have hright : Ty.subN (.exitOf .unknown e) (causeUpper e) = true :=
    Ty.OrderProof.sub_normalize_union_right Ty.sub_trans (.causeOf e) (.exitOf .unknown e)
  have hsub : Ty.subN (.exitOf v e) (.exitOf .unknown e) = true := by
    rw [Ty.subN_exitOf_iff]
    exact ⟨Ty.sub_unknown _, Ty.subN_refl e⟩
  exact Ty.subN_trans hsub hright

/-- `causeUpper` is monotonic in the error type. -/
@[semantics "subtyping-algebra" (requirement := R14)]
theorem cause_mono {a b : Ty} (h : Ty.subN a b = true) :
    Ty.subN (causeUpper a) (causeUpper b) = true := by
  have hleft : Ty.subN (.causeOf a) (causeUpper b) = true := by
    have h1 : Ty.subN (.causeOf a) (.causeOf b) = true := by
      rw [Ty.subN_causeOf_iff]
      exact h
    exact Ty.subN_trans h1 (subN_causeOf_causeUpper b)
  have hright : Ty.subN (.exitOf .unknown a) (causeUpper b) = true := by
    have h2 : Ty.subN (.exitOf .unknown a) (.exitOf .unknown b) = true := by
      rw [Ty.subN_exitOf_iff]
      exact ⟨Ty.sub_unknown _, h⟩
    exact Ty.subN_trans h2 (Ty.OrderProof.sub_normalize_union_right Ty.sub_trans (.causeOf b) (.exitOf .unknown b))
  exact Ty.OrderProof.sub_normalize_union_le Ty.sub_trans (.causeOf a) (.exitOf .unknown a)
    (causeUpper b).normalize hleft hright

/-- **The upper member fact of the cause rule.** Every normal member that `Member.cause`
answers is below `causeUpper` of its answer. -/
@[semantics "subtyping-algebra" (requirement := R14)]
theorem Member.cause_upper {m : Ty} {a : Ty} (normal : Ty.Normal m) (member : m.isMember = true)
    (answered : Member.cause m = some a) : Ty.subN m (causeUpper a) = true := by
  cases m with
  | causeOf e =>
    cases answered
    exact subN_causeOf_causeUpper a
  | exitOf v e =>
    cases answered
    exact subN_exitOf_causeUpper v a
  | _ => exact nomatch answered

/-- A normal member below `causeUpper b` is a cause or exit type whose error is below `b`. The
one inversion that `Member.cause_least` and `Member.cause_reads` read, its two consumers. -/
@[semantics "subtyping-algebra" (requirement := R14)]
theorem Member.cause_cases_of_below {m : Ty} {b : Ty}
    (normal : Ty.Normal m) (member : m.isMember = true)
    (below : Ty.subN m (causeUpper b) = true) :
    ∃ e, Member.cause m = some e ∧ Ty.subN e b = true := by
  have hraw : Ty.sub m (causeUpper b).normalize = true := by
    have h := below
    unfold Ty.subN at h
    rw [normal.fixed] at h
    exact h
  have hm_mem : m ∈ m.members := by rw [Ty.members_atom member]; exact List.mem_singleton_self _
  obtain ⟨y, hy, hsub⟩ := (Ty.OrderProof.sub_iff_members Ty.sub_trans m (causeUpper b).normalize).mp hraw m hm_mem
  have hnm : (causeUpper b).normalize.members =
      (Ty.normalizeRow ((Ty.causeOf b).normalize.members ++ (Ty.exitOf .unknown b).normalize.members)).elems :=
    Ty.OrderProof.members_normalize_union (.causeOf b) (.exitOf .unknown b)
  rw [hnm] at hy
  have hym := ((Ty.mem_normalizeRow y _).mp hy).1
  rw [List.mem_append] at hym
  rcases hym with hy1 | hy2
  · rw [Ty.members_atom rfl] at hy1
    have hy : y = .causeOf b.normalize := List.mem_singleton.mp hy1
    subst hy
    rw [Ty.sub_eq_args m (.causeOf b.normalize) member rfl (Ty.leafRule_of_right_none m _ rfl)
      (Ty.topRule_eq_false (fun h => Ty.noConfusion h)), Bool.and_eq_true] at hsub
    cases m with
    | causeOf e =>
      have he : e.normalize = e := by
        have h := normal.fixed
        change Ty.causeOf e.normalize = Ty.causeOf e at h
        rw [Ty.causeOf.injEq] at h
        exact h
      simp only [Ty.argsBelow, Ty.args, Ty.Variance.holds, List.zip, List.zipWith, List.all_cons,
        List.all_nil, Bool.and_true] at hsub
      have hsubN : Ty.subN e b = true := by
        unfold Ty.subN
        rw [he]
        exact hsub.2
      exact ⟨e, rfl, hsubN⟩
    | _ => exact nomatch hsub.1
  · rw [Ty.members_atom rfl] at hy2
    have hy : y = .exitOf .unknown b.normalize := List.mem_singleton.mp hy2
    subst hy
    rw [Ty.sub_eq_args m (.exitOf .unknown b.normalize) member rfl (Ty.leafRule_of_right_none m _ rfl)
      (Ty.topRule_eq_false (fun h => Ty.noConfusion h)), Bool.and_eq_true] at hsub
    cases m with
    | exitOf v e =>
      have he : e.normalize = e := by
        have h := normal.fixed
        change Ty.exitOf v.normalize e.normalize = Ty.exitOf v e at h
        rw [Ty.exitOf.injEq] at h
        exact h.2
      simp only [Ty.argsBelow, Ty.args, Ty.Variance.holds, List.zip, List.zipWith, List.all_cons,
        List.all_nil, Bool.and_true, Bool.and_eq_true] at hsub
      have hsubN : Ty.subN e b = true := by
        unfold Ty.subN
        rw [he]
        exact hsub.2.2
      exact ⟨e, rfl, hsubN⟩
    | _ => exact nomatch hsub.1

/-- **The least member fact of the cause rule.** -/
@[semantics "subtyping-algebra" (requirement := R14)]
theorem Member.cause_least {m : Ty} {a b : Ty} (normal : Ty.Normal m) (member : m.isMember = true)
    (answered : Member.cause m = some a) (below : Ty.subN m (causeUpper b) = true) :
    Ty.subN a b = true := by
  obtain ⟨e, he, hsub⟩ := Member.cause_cases_of_below normal member below
  cases answered ▸ he
  exact hsub

/-- **The reads member fact of the cause rule.** -/
@[semantics "subtyping-algebra" (requirement := R14)]
theorem Member.cause_reads {m : Ty} {b : Ty} (normal : Ty.Normal m) (member : m.isMember = true)
    (below : Ty.subN m (causeUpper b) = true) : ∃ a, Member.cause m = some a := by
  obtain ⟨e, he, -⟩ := Member.cause_cases_of_below normal member below
  exact ⟨e, he⟩

/-- **The cause rule is monotone on normal union members.** -/
@[semantics "subtyping-algebra" (requirement := R14)]
theorem Member.cause_monotone : Below Member.cause Member.cause :=
  below_of_upper Member.cause_upper Member.cause_least Member.cause_reads

/-- **The upper form of `causeInputError?`.** -/
@[semantics "subtyping-algebra" (requirement := R14)]
theorem causeInputError_upper {t : Ty} {error : Ty}
    (typed : causeInputError? t = some error) :
    Ty.subN t (causeUpper error) = true := by
  unfold causeInputError? at typed
  obtain (hraw | ⟨-, hlift⟩) := (extend_eq_some_iff Member.cause).mp typed
  · cases t with
    | causeOf e =>
      cases hraw
      exact subN_causeOf_causeUpper error
    | exitOf v e =>
      cases hraw
      exact subN_exitOf_causeUpper v error
    | _ => exact nomatch hraw
  · unfold liftOne at hlift
    split at hlift
    · exact lift_upper (fun {a b} h => cause_mono h)
        (fun {m a} nm hm ha => Member.cause_upper nm hm ha) hlift
    · exact nomatch hlift

/-- **`causeInputError?` at a cause type**: today's answer. -/
@[semantics "subtyping-algebra" (requirement := R14)]
theorem causeInputError_causeOf (e : Ty) : causeInputError? (.causeOf e) = some e :=
  extend_agrees rfl

/-- **`causeInputError?` at an exit type**: today's answer. -/
@[semantics "subtyping-algebra" (requirement := R14)]
theorem causeInputError_exitOf (a e : Ty) : causeInputError? (.exitOf a e) = some e :=
  extend_agrees rfl

end Effect4.Program

