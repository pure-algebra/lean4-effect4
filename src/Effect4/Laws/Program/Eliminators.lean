import Effect4.Program.Typing.Rules
import Effect4.Laws.Program.UnionRule

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

Placement. Concept `subtyping-algebra`, requirement R14, under the proposed claim
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
normal union member that is below a fiber type. A step of the proposed claim
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
moves at this rule, and its type keeps its spelling. A step of the proposed claim
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

end Effect4.Program
