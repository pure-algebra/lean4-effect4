import Effect4.Laws.Program.UnionRule
import Effect4.Laws.Program.Typing.TermIntro
import Effect4.Program.Checker
import Effect4.Program.Native

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
- `fiberTy` at a union of two fiber types, and at `never`: it refuses both today, as a function
  and in the checker. The control records the present behaviour for the conversion that changes
  it;
- the upper form in raw `Ty.sub`, at a target that is not its own normal form;
- the field read against a record of one field: the order has no width rule, so the field read
  has no upper form;
- a member rule that answers an open type, whose lifted rule does not keep closed types closed.

The battery converts no rule of the checker.
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

/-! ## Red: `fiberTy` refuses a union of two fiber types today -/

/-- A union of two fiber types, as a term's type. -/
def twoFibers : Ty := .union (.fiberOf .nat .never) (.fiberOf .string .bool)

-- The by-shape rule, as a function: it refuses the union, its normal form and `never`.
#guard fiberTy twoFibers = none
#guard fiberTy twoFibers.normalize = none
#guard fiberTy .never = none

-- The checker today: a join of a handle of that type is refused, as no fiber. So is `never`.
#guard explain nativeSignature [twoFibers] (.awaitFiber (.var 0) .joinEffect) =
  some ⟨[], .notFiber twoFibers⟩
#guard explain nativeSignature [.never] (.awaitFiber (.var 0) .joinEffect) =
  some ⟨[], .notFiber .never⟩

-- The same member rule, lifted: the pair of the joined columns, and the least pair at `never`.
-- No rule of the checker reads it.
#guard lift fiberTy twoFibers = some (.union .nat .string, .bool)
#guard lift fiberTy .never = some (.never, .never)
#guard lift fiberTy (.union (.fiberOf .nat .never) .nat) = none

/-! ## Red: the upper form in raw `Ty.sub`, and the field read -/

/-- A fiber type whose value column is not its own normal form: normalization distributes the
product over the union. -/
def rawFiber : Ty := .fiberOf (.prod (.union .nat .string) .unit) .never

-- The lifted rule answers there. The target is below the answer's fiber type in the checker's
-- order, and not in raw `Ty.sub`: raw `sub` never distributes a product over a union.
#guard lift fiberTy rawFiber = some (.union (.prod .nat .unit) (.prod .string .unit), .never)
#guard Ty.subN rawFiber (.fiberOf (.union (.prod .nat .unit) (.prod .string .unit)) .never)
#guard !Ty.sub rawFiber (.fiberOf (.union (.prod .nat .unit) (.prod .string .unit)) .never)

-- The order has no width rule (decisions row 178): a record of two fields is not below the
-- record of one of them, in either order. So the field read has no upper form.
#guard Record.fieldType false natRecord "a" = some .nat
#guard !Ty.subN natRecord (.record [("a", false, .nat)])
#guard !Ty.sub natRecord (.record [("a", false, .nat)])

/-! ## Green and red: closed types -/

/-- A fiber type that is closed has closed columns: the member fact of `lift_closed_pair`. -/
theorem fiberTy_closed {m : Ty} {a : Ty × Ty} (closed : m.closed = true)
    (answered : fiberTy m = some a) : a.1.closed = true ∧ a.2.closed = true := by
  cases m with
  | fiberOf value error =>
    cases answered
    exact Bool.and_eq_true_iff.mp closed
  | _ => exact nomatch answered

/-- The lifted `fiberTy` answers closed columns at a closed target. -/
theorem lift_fiberTy_closed {t : Ty} {a : Ty × Ty} (typed : lift fiberTy t = some a)
    (closed : t.closed = true) : a.1.closed = true ∧ a.2.closed = true :=
  lift_closed_pair (fun _ _ closed answered => fiberTy_closed closed answered) typed closed

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

end Effect4.Test.UnionRule
