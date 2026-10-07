import Effect4.Laws.Program.UnionRule
import Effect4.Laws.Program.Eliminators
import Effect4.Laws.Program.Typing.TermIntro
import Effect4.Program.Checker
import Effect4.Program.Native
import Effect4.Program.Tuple

/-!
# Controls of the rule that reads a union member by member

The combinator is `UnionRule.lift` (`src/Effect4/Program/UnionRule.lean`), and its laws are in
`src/Effect4/Laws/Program/UnionRule.lean`. Each control below is finite: a guard on closed
types, or a law at one instance. A guard is a finite check and no theorem.

Green controls:

- the two record rules are their definitions before the combinator, by `rfl`;
- the lifted rule at `never`, at a union of two records, and at a union with one member that
  refuses;
- the lifted rule at one member, and at two spellings of one normal form;
- a lifted rule keeps closed types closed, at a type and at a pair.

Red controls, each red for its stated reason:

- a member rule that is not monotone in the order, whose lifted rule is not;
- `Member.fiber`, the member rule of the fiber rule, at a union of two fiber types and at
  `never`: it refuses both, because it reads one union member. Its lifted rule answers both;
- the upper form in raw `Ty.sub`, at a target that is not its own normal form;
- the field read against a record of one field: the order has no width rule, so the field read
  has no upper form;
- a member rule that answers an open type, whose lifted rule does not keep closed types closed;
- the cause rule against `Eliminator`: it reads two heads (`causeInput_no_eliminator`).

The last sections give the order laws of the lifted `Member.fiber` by projection of its instance
(`Member.fiber_eliminator`, `src/Effect4/Laws/Program/Eliminators.lean`), `Checker.listOf?` as
an instance of `Eliminator`, and a finite probe of the cause rule's upper form. Then the adjoint
form at `Member.fiber`, the join law at `Checker.listOf?` with its red control, and uniqueness at
its consumer: `Tuple.typeAt` is the lifted projection (`typeAt_eq_lift`).

The battery converts no rule of the checker. The fiber rule is converted
(`fiberTy`, `src/Effect4/Program/Typing/Rules.lean`), and its controls, with those of the guard
and of the extended rule, are in `Test/Program/Eliminators.lean`.
-/

set_option autoImplicit false

namespace Effect4.Test.UnionRule

open Effect4 Effect4.Program Effect4.Program.UnionRule

/-! ## The two record rules are their definitions before the combinator -/

-- The right sides are the bodies at the base of this slice, word for word.
example (optional : Bool) (target : Ty) (name : String) :
    Record.fieldType optional target name =
      ((Ty.members target.normalize).mapM (Record.fieldOf optional name)).map
        Record.joinResults := rfl

example (target : Ty) (name : String) (valueType : Ty) :
    Record.setType target name valueType =
      ((Ty.members target.normalize).mapM (Record.setOf name valueType)).map
        Record.joinResults := rfl

example (types : List Ty) : Record.joinResults types = types.foldl Ty.join .never := rfl

/-! ## Green: `never`, a union of two records, a member that refuses -/

/-- A record with the field `a` at `nat`. -/
def natRecord : Ty := .record [("a", false, .nat), ("b", false, .bool)]

/-- A record with the field `a` at `string`. -/
def stringRecord : Ty := .record [("a", false, .string)]

-- `never` has no union member: each lifted rule answers its least answer, in each read mode.
#guard Record.fieldType false .never "a" = some .never
#guard Record.fieldType true .never "a" = some .never
#guard Record.setType .never "a" .nat = some .never
example (rule : Ty → Option Ty) : lift rule .never = some .never := lift_never rule
example (rule : Ty → Option (Ty × Ty)) : lift rule .never = some (.never, .never) :=
  lift_never rule

-- A union of two records: the answers of the two members, joined.
#guard Ty.join .nat .string = .union .nat .string
#guard Record.fieldType false (.union natRecord stringRecord) "a" = some (.union .nat .string)
#guard Record.fieldType true (.union natRecord stringRecord) "a" =
  some (Ty.join (.option .nat) (.option .string))
#guard Record.setType (.union natRecord stringRecord) "a" .unit =
  some (Ty.join (.record [("a", false, .unit), ("b", false, .bool)])
    (.record [("a", false, .unit)]))

-- One member that refuses refuses the target: a record without the field, and no record.
#guard Record.fieldType false (.union natRecord (.record [("b", false, .bool)])) "a" = none
#guard Record.fieldType false (.union natRecord .nat) "a" = none
#guard Record.setType (.union natRecord .nat) "a" .unit = none

/-! ## Green: one member, and one normal form -/

-- At one union member the lifted rule is the member rule, up to the join with `never`.
example : lift (Record.fieldOf false "a") natRecord =
    (Record.fieldOf false "a" natRecord).map (Ty.join .never) :=
  lift_member _ (Ty.normal_of_canonical (t := natRecord) rfl) rfl
#guard Record.fieldType false natRecord "a" = some .nat

-- Two spellings of one normal form have one answer.
example (optional : Bool) (name : String) :
    Record.fieldType optional (.union stringRecord natRecord) name =
      Record.fieldType optional (.union natRecord stringRecord) name :=
  lift_congr _ rfl

-- A normal form keeps maximal members only: the lifted rule does not read a member that is
-- below another member. The literal's record is below the string's record.
#guard Ty.normalize (.union (.record [("a", false, .lit "x")]) stringRecord) = stringRecord
#guard Record.fieldType false (.union (.record [("a", false, .lit "x")]) stringRecord) "a" =
  some .string

/-! ## Red: a member rule that is not monotone in the order -/

/-- A member rule that answers at `string` and refuses a literal. -/
def stringOnly (member : Ty) : Option Ty := if member = .string then some .nat else none

/-- The premise of the monotone law fails at `stringOnly`: a literal is below `string`, and the
rule refuses the literal. -/
theorem stringOnly_not_below : ¬ Below stringOnly stringOnly := by
  intro below
  obtain ⟨a, answered, -⟩ := below (x := .lit "a") (y := .string) (.lit "a") .string rfl rfl
    (Ty.sub_lit_string "a") (b := .nat) rfl
  exact nomatch answered

-- Its lifted rule is not monotone: it answers at `string` and refuses the smaller literal.
#guard Ty.subN (.lit "a") .string
#guard lift stringOnly .string = some .nat
#guard lift stringOnly (.lit "a") = none

/-! ## Red: a member rule refuses a union and `never`, and its lifted rule answers

`Member.fiber` is the member rule of the checker's fiber rule
(`src/Effect4/Program/Typing/Rules.lean`). It reads one fiber type, and it answers a pair. -/

/-- A union of two fiber types, as a term's type. -/
def twoFibers : Ty := .union (.fiberOf .nat .never) (.fiberOf .string .bool)

-- The member rule, as a function: it refuses the union, its normal form and `never`.
#guard Member.fiber twoFibers = none
#guard Member.fiber twoFibers.normalize = none
#guard Member.fiber .never = none

-- The same member rule, lifted: the pair of the joined columns, and the least pair at `never`.
-- One member that is no fiber type refuses the target.
#guard lift Member.fiber twoFibers = some (.union .nat .string, .bool)
#guard lift Member.fiber .never = some (.never, .never)
#guard lift Member.fiber (.union (.fiberOf .nat .never) .nat) = none

/-! ## Red: the upper form in raw `Ty.sub`, and the field read -/

/-- A fiber type whose value column is not its own normal form: normalization distributes the
product over the union. -/
def rawFiber : Ty := .fiberOf (.prod (.union .nat .string) .unit) .never

-- The lifted rule answers there. The target is below the answer's fiber type in the checker's
-- order, and not in raw `Ty.sub`: raw `sub` never distributes a product over a union.
#guard lift Member.fiber rawFiber = some (.union (.prod .nat .unit) (.prod .string .unit), .never)
#guard Ty.subN rawFiber (.fiberOf (.union (.prod .nat .unit) (.prod .string .unit)) .never)
#guard !Ty.sub rawFiber (.fiberOf (.union (.prod .nat .unit) (.prod .string .unit)) .never)

-- The order has no width rule (decisions row 178): a record of two fields is not below the
-- record of one of them, in either order. So the field read has no upper form.
#guard Record.fieldType false natRecord "a" = some .nat
#guard !Ty.subN natRecord (.record [("a", false, .nat)])
#guard !Ty.sub natRecord (.record [("a", false, .nat)])

/-! ## Green and red: closed types -/

/-- The lifted `Member.fiber` answers closed columns at a closed target. The member fact is
`Member.fiber_closed` (`src/Effect4/Laws/Program/Eliminators.lean`): a fiber type that is closed
has closed columns. -/
theorem lift_fiber_closed {t : Ty} {a : Ty × Ty} (typed : lift Member.fiber t = some a)
    (closed : t.closed = true) : a.1.closed = true ∧ a.2.closed = true :=
  lift_closed_pair (fun _ _ closed answered => Member.fiber_closed closed answered) typed closed

/-- A list type that is closed has a closed element type: the member fact of `lift_closed`. -/
theorem listOf_closed {m a : Ty} (closed : m.closed = true)
    (answered : Checker.listOf? m = some a) : a.closed = true := by
  cases m with
  | list inner =>
    cases answered
    exact closed
  | _ => exact nomatch answered

/-- The lifted `Checker.listOf?` answers a closed type at a closed target. -/
theorem lift_listOf_closed {t a : Ty} (typed : lift Checker.listOf? t = some a)
    (closed : t.closed = true) : a.closed = true :=
  lift_closed (fun _ _ closed answered => listOf_closed closed answered) typed closed

/-- A member rule that answers an open type at a closed member. -/
def openAnswer (member : Ty) : Option Ty := if member = .string then some (.var 0) else none

-- Its lifted rule answers an open type at a closed target: the member's fact is needed.
#guard Ty.closed .string
#guard lift openAnswer .string = some (.var 0)
#guard !(Ty.var 0).closed

/-! ## The eliminator of one constructor: the order laws by projection

`Member.fiber` is an instance of `UnionRule.Eliminator`
(`Member.fiber_eliminator`, `src/Effect4/Laws/Program/Eliminators.lean`), and the order laws of
its lifted rule follow by projection. `Checker.listOf?` is an instance too, from the same three
facts. It is not converted: its instance here shows what its conversion owes. -/

/-- The upper form at the lifted `Member.fiber`: a target that it answers is below the fiber
type of the answer. -/
theorem lift_fiber_upper {t : Ty} {pair : Ty × Ty} (typed : lift Member.fiber t = some pair) :
    Ty.subN t (.fiberOf pair.1 pair.2) = true :=
  Member.fiber_eliminator.lift_upper typed

/-- The lifted `Member.fiber` answers the least pair of columns. -/
theorem lift_fiber_least {t : Ty} {pair b : Ty × Ty} (typed : lift Member.fiber t = some pair)
    (upper : Ty.subN t (.fiberOf b.1 b.2) = true) :
    Ty.subN pair.1 b.1 = true ∧ Ty.subN pair.2 b.2 = true :=
  Member.fiber_eliminator.lift_least typed upper

/-- The lifted `Member.fiber` is monotone in the checker's order. -/
theorem lift_fiber_mono {s t : Ty} (smaller : Ty.subN s t = true) {b : Ty × Ty}
    (typed : lift Member.fiber t = some b) :
    ∃ a, lift Member.fiber s = some a ∧ Ty.subN a.1 b.1 = true ∧ Ty.subN a.2 b.2 = true :=
  Member.fiber_eliminator.lift_mono smaller typed

/-- **`Checker.listOf?` is the eliminator of the list constructor**, as a member rule. -/
theorem listOf_eliminator : Eliminator Checker.listOf? Ty.list where
  shape {m a} answered := by
    cases m with
    | list inner =>
      cases answered
      rfl
    | _ => exact nomatch answered
  embeds {a b} := by
    show Ty.sub (.list a.normalize) (.list b.normalize) = true ↔ Ty.subN a b = true
    rw [Ty.sub_list]
    exact Iff.rfl
  reads {m b} normal member below := by
    have raw : Ty.sub m (.list b.normalize) = true := by
      have h := below
      unfold Ty.subN at h
      rw [normal.fixed] at h
      exact h
    rw [Ty.sub_eq_args m _ member rfl (Ty.leafRule_of_right_none m _ rfl)
      (Ty.topRule_eq_false (fun h => Ty.noConfusion h)), Bool.and_eq_true] at raw
    cases m with
    | list inner => exact ⟨inner, rfl⟩
    | _ => exact nomatch raw.1

-- The upper form on closed targets, as guards: a union of two list types and `never`.
#guard lift Checker.listOf? (.union (.list .nat) (.list .string)) = some (.union .nat .string)
#guard Ty.subN (.union (.list .nat) (.list .string)) (.list (.union .nat .string))
#guard Checker.listOf? (.union (.list .nat) (.list .string)) = none
#guard lift Checker.listOf? .never = some .never

/-! ## Red: the cause rule reads two heads, so it is no eliminator of one constructor -/

/-- The cause rule `causeInputError?` answers one error type at a cause type and at an exit
type. So no map `C` has the `shape` fact: `Eliminator` asks one head. -/
theorem causeInput_no_eliminator (C : Ty → Ty) : ¬ Eliminator causeInputError? C := by
  intro e
  have atCause : Ty.causeOf .nat = C .nat := e.shape (m := .causeOf .nat) rfl
  have atExit : Ty.exitOf .bool .nat = C .nat := e.shape (m := .exitOf .bool .nat) rfl
  exact nomatch atCause.trans atExit.symm

/-- The upper map of the cause rule: a cause of the error, or an exit of any value and the
error. -/
def causeUpper (error : Ty) : Ty := .union (.causeOf error) (.exitOf .unknown error)

-- A finite probe of the general upper form at that map: the lifted cause rule on five targets.
#guard lift causeInputError? (.union (.causeOf .nat) (.exitOf .bool .string)) =
  some (.union .nat .string)
#guard [Ty.never, .causeOf .nat, .exitOf .bool .string,
    .union (.causeOf .nat) (.exitOf .bool .string),
    .union (.causeOf (.lit "a")) (.causeOf .string)].all fun target =>
  match lift causeInputError? target with
  | some error => Ty.subN target (causeUpper error)
  | none => false
#guard lift causeInputError? (.union (.causeOf .nat) .nat) = none

/-! ## The adjoint form, the join law and uniqueness -/

/-- The lifted `Member.fiber` answers exactly at the targets below a fiber type, and its answer
is the least pair of columns: the adjoint form at the fiber constructor. -/
theorem lift_fiber_adjoint (t : Ty) :
    ((lift Member.fiber t).isSome = true ↔
      ∃ b : Ty × Ty, Ty.subN t (.fiberOf b.1 b.2) = true) ∧
    ∀ {a : Ty × Ty}, lift Member.fiber t = some a → ∀ b : Ty × Ty,
      (Ty.subN a.1 b.1 = true ∧ Ty.subN a.2 b.2 = true) ↔
        Ty.subN t (.fiberOf b.1 b.2) = true :=
  Member.fiber_eliminator.adjoint t

/-- The lifted `Checker.listOf?` at a union is the join of its answers at the two sides. -/
theorem lift_listOf_union (s t : Ty) :
    lift Checker.listOf? (.union s t) =
      (lift Checker.listOf? s).bind fun a => (lift Checker.listOf? t).map (Ty.join a) :=
  lift_union_eq listOf_eliminator.monotone s t

-- Red: the join law fails at a member rule that is not monotone. The union's normal form drops
-- the literal, so the lifted rule answers at the union and refuses one side.
#guard lift stringOnly (.union (.lit "a") .string) = some .nat
#guard lift stringOnly (.lit "a") = none

/-- A normal union member's positional read answers a normal type. -/
theorem project_normal {m a : Ty} {index : Nat} (normal : Ty.Normal m)
    (member : m.isMember = true) (answered : Tuple.project index m = some a) :
    a.normalize = a := by
  have children := Ty.OrderProof.normal_args normal member
  cases m with
  | tuple items =>
    exact (children a (List.mem_map.mpr ⟨(.co, a), List.mem_map.mpr
      ⟨a, List.mem_of_getElem? answered, rfl⟩, rfl⟩)).fixed
  | prod first second =>
    have inside : a ∈ [first, second] := List.mem_of_getElem? answered
    rcases List.mem_cons.mp inside with rfl | inside
    · exact (children a (List.mem_cons_self)).fixed
    · rcases List.mem_cons.mp inside with rfl | inside
      · exact (children a (List.mem_cons_of_mem _ List.mem_cons_self)).fixed
      · exact absurd inside List.not_mem_nil
  | never => exact Bool.noConfusion member
  | union _ _ => exact Bool.noConfusion member
  | _ => exact nomatch answered

/-- **The positional read is the lifted projection.** `Tuple.typeAt` reads a union by its own
recursion over the normal form (`src/Effect4/Program/Tuple.lean`). It has the four properties of
`lift_unique`, so it is `UnionRule.lift` at the projection of one member. The proof compares no
two recursions. The rule is not converted here: the theorem is the equation that its conversion
states. -/
theorem typeAt_eq_lift (target : Ty) (index : Nat) :
    Tuple.typeAt target index = lift (Tuple.project index) target := by
  refine lift_unique (f := fun t => Tuple.typeAt t index) (fun t => ?_) rfl
    (fun {m} normal member => ?_) (fun {m r} normalM _ normalR normalU => ?_) target
  · show Tuple.project index t.normalize = Tuple.project index t.normalize.normalize
    rw [Ty.normalize_idem]
  · show Tuple.project index m.normalize = (Tuple.project index m).map Ty.normalize
    rw [normal.fixed]
    cases answered : Tuple.project index m with
    | none => rfl
    | some a =>
      show some a = some a.normalize
      rw [project_normal normal member answered]
  · show Tuple.project index (Ty.normalize (.union m r)) =
      (Tuple.project index m.normalize).bind fun a =>
        (Tuple.project index r.normalize).map (Ty.join a)
    rw [normalU.fixed, normalM.fixed, normalR.fixed]
    show (Tuple.project index m >>= fun a =>
      Tuple.project index r >>= fun b => some (Ty.join a b)) = _
    cases Tuple.project index m <;> cases Tuple.project index r <;> rfl

end Effect4.Test.UnionRule
