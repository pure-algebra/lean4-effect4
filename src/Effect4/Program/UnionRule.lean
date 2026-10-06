module

public import Effect4.Program.Ty

/-!
# Program.UnionRule — a rule that reads a union member by member

**What it is.** One combinator for the rules of the checker that read a type by its union
members (decisions row 285). A **union member** is an element of `Ty.members`
(`src/Effect4/Program/Ty.lean`): a type that is not `never` and whose head is not a union. A
**member rule** answers at one union member, or refuses it. The record field rule is one
(`Record.fieldOf`, `src/Effect4/Program/Record.lean`): it reads one record type.

`UnionRule.lift` makes a member rule a rule on every type. It reads its target in three steps.

1. It takes the target's normal form (`Ty.normalize`). Two spellings of one type have one answer.
2. It asks the member rule at every union member of the normal form. One refusal refuses the
   target.
3. It joins the answers, from the least answer.

`never` has no union member. So the lifted rule answers the least answer there, and it never
refuses `never`. A normal form keeps maximal members only, so the lifted rule does not read a
member that is below another member.

**What an answer is.** `UnionRule.Answer α` gives the carrier `α` its least answer and its join.
A type is an answer, with `never` and `Ty.join`. A pair of answers is an answer, component by
component: a fiber rule answers a value type and an error type.

**Depends on.** `Ty` alone: its normal form, its union members and its join. The module holds no
`match` on a type.

**Properties.** The laws are in `src/Effect4/Laws/Program/UnionRule.lean`:
* the answer at `never` (`lift_never`) and at one union member (`lift_member`);
* one answer for one normal form (`lift_congr`);
* the order: a smaller target has a smaller answer, where the member rule keeps the order
  (`lift_mono`);
* a property that holds at each union member holds at the lifted rule (`lift_transfer`). The
  soundness of the two record rules against `Fits` and against `Val.hasTy` is an instance.

An instance is one line here, and the facts of its member rule there.
-/

@[expose] public section

namespace Effect4.Program.UnionRule

/-- The carrier of a member rule's answers. `bot` is the answer at `never`, where no union
member constrains it. `join` is the answer of two union members together. The laws need an
order too, and the law module states it (`AnswerOrder`,
`src/Effect4/Laws/Program/UnionRule.lean`): no definition reads it. -/
class Answer (α : Type) where
  /-- The least answer: the lifted rule's answer at `never`. -/
  bot : α
  /-- The join of two answers. -/
  join : α → α → α

/-- A type is an answer: `never` is least, and `Ty.join` is the join in the checker's order. -/
instance : Answer Ty where
  bot := .never
  join := Ty.join

/-- A pair of answers is an answer, component by component. A rule that reads a fiber type or
an exit type answers a value type and an error type. -/
instance {α β : Type} [Answer α] [Answer β] : Answer (α × β) where
  bot := (Answer.bot, Answer.bot)
  join a b := (Answer.join a.1 b.1, Answer.join a.2 b.2)

variable {α : Type} [Answer α]

/-- The join of the answers of a union's members, from the least answer. An empty list has the
least answer. -/
def joinAll (answers : List α) : α :=
  answers.foldl Answer.join Answer.bot

/-- **The lifted rule**: the member rule at every union member of the target's normal form, and
the join of the answers. One refusal refuses the target. At `never` it answers the least
answer. -/
def lift (rule : Ty → Option α) (target : Ty) : Option α :=
  (target.normalize.members.mapM rule).map joinAll

end Effect4.Program.UnionRule
