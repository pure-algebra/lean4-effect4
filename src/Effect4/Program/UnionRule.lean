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

**The fold of a union.** `UnionRule.lift` is the fold of a union: the one map that answers the
least answer at `never`, the member rule at one union member and the join at a union
(`lift_unique`, at the carrier `Ty`). `UnionRule.Answer` is its algebra: a least answer and a
join.

**A converted rule of the checker.** The four raw-head classifiers use `extendAll`.
It keeps a raw answer first and uses the full normalized lift elsewhere.
The option classifier uses the full normalized lift directly.
`extend` and `liftOne` retain the historical guarded definitions and their controls.
Raw-first answers can retain a different spelling from their normalized lift.

**Depends on.** `Ty` alone: its normal form, its union members and its join. The module holds no
`match` on a type.

**Properties.** The laws are in `src/Effect4/Laws/Program/UnionRule.lean`, and its head lists
them:
* the answer at `never` (`lift_never`) and at one union member (`lift_member`);
* one answer for one normal form (`lift_congr`);
* the order: a smaller target has a smaller answer, where the member rule keeps the order
  (`lift_mono`);
* a property that holds at each union member holds at the lifted rule (`lift_transfer`,
  `lift_all`). The soundness of the two record rules against `Fits` and against `Val.hasTy` is
  an instance;
* for a rule that reads one constructor, the lifted rule is the constructor's lower adjoint
  (`Eliminator`);
* the guarded rule answers exactly where the lifted rule answers at a target with at most one
  union member (`liftOne_eq_some_iff`);
* the extended rule agrees with its member rule (`extend_agrees`), and the contract of a
  converted eliminator (`Eliminator.extend_laws`).

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

/-- **The guarded rule**: the lifted rule where the target's normal form has at most one union
member, and a refusal elsewhere. At `never` and at one union member it is the lifted rule. At a
proper union, a normal form with two union members or more, it refuses.

**Why it exists** (decisions row 292, point 1). The lifted rule of a by-shape function answers
at a proper union. The TypeScript printer writes no type argument at the printed call there,
and the owner ruled that the checker keeps today's refusal until it does
(`docs/research/2026-10-06-uniform-eliminators-landing-probe.md`, finding 3 and proposal 4).

**What removes it.** The printer writes the type arguments of the call at the join, which are
the lifted rule's own answer. A rule that says `liftOne` then says `lift`, in one line, and each
proof that used `liftOne_some` (`src/Effect4/Laws/Program/UnionRule.lean`) still has its
premise. Until then a guarded rule is not monotone in the order at a proper union. -/
def liftOne (rule : Ty → Option α) (target : Ty) : Option α :=
  if target.normalize.members.length ≤ 1 then lift rule target else none

/-- The legacy guarded raw-first rule. It keeps the member rule's raw answer and
uses `liftOne` elsewhere. P2b's approved classifiers use `extendAll` instead.
This definition retains its guarded laws and synthetic controls unchanged. -/
def extend (rule : Ty → Option α) (target : Ty) : Option α :=
  (rule target).orElse fun _ => liftOne rule target

/-- The member rule's raw answer first, and the full normalized lift elsewhere.
It keeps every answer of `extend`, including its spelling, and admits proper unions
whose retained normal members all answer. The four approved raw-head classifiers use it.
The option classifier uses `lift`, preserving its normalized answers. -/
def extendAll (rule : Ty → Option α) (target : Ty) : Option α :=
  (rule target).orElse fun _ => lift rule target

end Effect4.Program.UnionRule
