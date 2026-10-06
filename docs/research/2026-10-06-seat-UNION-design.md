# 2026-10-06 seat UNION design: one combinator for a rule that reads a union member by member

Status: research note (history, not authority). Base: `08afe77c`. Brief:
`docs/research/2026-10-05-claude-lead/briefs/seat-union-brief.md`. Decisions rows 282 and 285.

## Question

Two rules of the checker read a union member by member: `Record.fieldType` and
`Record.setType` (`src/Effect4/Program/Record.lean`). How does one combinator name that
pattern, so that each later rule is an instance that owes its member rule's facts and no more?

The words of this note:

- A **union member** is an element of `Ty.members` (`src/Effect4/Program/Ty.lean`): a type that
  is not `never` and whose head is not a union.
- A **member rule** is a function `Ty → Option α` that the checker asks at one union member.
- The **lifted rule** is the member rule read at every union member of the target's normal form.
- An **answer** is a value of `α`. The **carrier** is `α` with its least answer and its join.

## What was read or run (each with its evidence word)

| What | Evidence |
| --- | --- |
| The brief's reading list: `Record.lean`, `Ty.members`, `Ty.join`, `Ty.normalize`, `Ty.sub`, the four soundness proofs, the laws of members, `fiberTy`, `Decision.arms`, `Record.tagArms`, seat GAP's study (5.3, 9.7, 10.2) | reading |
| The combinator, its seven laws and their consumers, compiled against the base build with the combinator declared in the scratch file | proved in scratch: the kernel accepted each theorem at `[propext, Quot.sound]`; no gate has read one |
| The two record rules equal the combinator at `Record.fieldOf` and `Record.setOf`, by `rfl` | proved in scratch |
| The proof of `cell_msgsTy` (`src/Effect4/Laws/Modules/Queue/Typing.lean`) replayed against a rule that is written through the combinator | tested: the `rw` fails |
| The lifted `fiberTy` at `never`, at a union of two fiber types and at a union with a member that is no fiber | tested: four guards |
| `Tuple.typeAt` against the lifted `Tuple.project`, on 11 targets and 4 positions | tested: a finite probe |
| The import closures of the three law files of the reading list | tested: a script over the import lines |

The probes are filed beside this note:
`docs/research/2026-10-06-seat-UNION-probe-laws.lean.txt` and
`docs/research/2026-10-06-seat-UNION-probe-unfold.lean.txt`.

## Findings (each with its evidence)

### 1. The combinator, as Lean elaborates it

```lean
namespace Effect4.Program.UnionRule

class Answer (α : Type) where
  bot : α
  join : α → α → α

instance : Answer Ty := ⟨.never, Ty.join⟩
instance {α β : Type} [Answer α] [Answer β] : Answer (α × β) :=
  ⟨(Answer.bot, Answer.bot), fun a b => (Answer.join a.1 b.1, Answer.join a.2 b.2)⟩

def joinAll {α : Type} [Answer α] (answers : List α) : α :=
  answers.foldl Answer.join Answer.bot

def lift {α : Type} [Answer α] (rule : Ty → Option α) (target : Ty) : Option α :=
  (target.normalize.members.mapM rule).map joinAll
```

The two record rules become one line each.

```lean
def joinResults (types : List Ty) : Ty := UnionRule.joinAll types
def fieldType (optional : Bool) (target : Ty) (name : String) : Option Ty :=
  UnionRule.lift (fieldOf optional name) target
def setType (target : Ty) (name : String) (valueType : Ty) : Option Ty :=
  UnionRule.lift (setOf name valueType) target
```

Each equals its present definition by `rfl` (proved in scratch). `Record.joinResults` keeps its
name, and it is the join of a list at the carrier `Ty`.

The lifted rule reads the normal form inside. A rule that states `target.normalize` at each
use would leave the pattern without a name, and a later rule could forget the step.

### 2. The answer's carrier

The carrier gives two things: a least answer `bot`, for `never`, and a join. It is a class of
the core module, with data only. Lean's instance search then finds the carrier of each rule.

| Rule | Its answer | Carrier |
| --- | --- | --- |
| the field read, the overwrite, a positional read, `Checker.listOf?`, `Decision.arms .option` | one type | `Ty`, with `never` and `Ty.join` |
| `fiberTy`, `exitOf?`, `Decision.arms .tag` | a value type and an error type, or two bound types | `Ty × Ty`, by the product instance |
| a test by equality, such as `t = .bool` | nothing | a unit carrier: one more instance, when a test converts |

Three reasons decide the form.

- **No class of Lean's core serves.** Core has `Max` for a join and no class for a least
  element. The `LE` of `Ty` is the key order that sorts union members, not subtyping. A `Max Ty`
  beside it would be the join of another order.
- **The carrier is raw `Ty`, not `CTy`.** Each rule answers `Option Ty` today, and no type moves.
- **`Ty` is lawful up to the checker's order only.** `Ty.join .never a` is `a.normalize`, and not
  `a`. So the law at one member says "up to the join with the least answer".

The order is no field of the core class, because no definition reads it. The law module adds
it: `AnswerOrder α` gives `le`, a preorder in which `bot` is least and `join` is a least upper
bound. At `Ty` it is `Ty.subN`, the checker's order
(`src/Effect4/Laws/Program/TypeAlgebra.lean`). At a pair it holds on each component.
`CTy.ofRaw a ≤ CTy.ofRaw b` unfolds to `Ty.subN a b`. So a view of seat LATTICE's module can
read a lifted answer in its own classes.

### 3. The homes

- **The core module** is `src/Effect4/Program/UnionRule.lean`. It imports
  `Effect4.Program.Ty` only, and `Record.lean` imports it. It holds the class, its two
  instances, `joinAll` and `lift`. It holds no `match` on `Ty`, so the case-site policy gains no
  site.
- **The law module** is `src/Effect4/Laws/Program/UnionRule.lean`. It imports the core module,
  `Effect4.Laws.Program.TypeAlgebra` and `Effect4.Laws.Auto.Semantics`, and no more. So
  `Typed.lean`, `Typed/RecordOperations.lean` and `Typing/TermIntro.lean` can each import it:
  none of the three is in its import closure (tested).
- **The two membership relations** stay where they are. `Has` is private to `Typed.lean`, and
  `Fits w` needs `Typed/Membership.lean`. Each proves one small fact beside itself
  (finding 5).

### 4. The premise of the monotone law

The premise relates two member rules. With one rule on both sides it says that the member rule
is monotone in the order `Ty.sub`.

```lean
def Below [AnswerOrder α] (lower upper : Ty → Option α) : Prop :=
  ∀ ⦃x y : Ty⦄, Ty.Normal x → Ty.Normal y → x.isMember = true → y.isMember = true →
    Ty.sub x y = true → ∀ ⦃b : α⦄, upper y = some b → ∃ a, lower x = some a ∧ le a b
```

- It asks only what the lifted rule reads: two union members of two normal forms. An instance
  receives `Ty.Normal` and `isMember` for both, which rule out `never` and a union.
- Two rules, because an overwrite is monotone in its target and in its value at once:
  `setOf name V'` below `setOf name V`. The record case of `checker-monotone` needs that form.
- The law then reads as follows. Take `Ty.subN s t`, and let the upper rule's lift answer `b`
  at `t`. Then the lower rule's lift answers some `a` at `s`, and `a` is below `b`.

The proof reads `sub_iff_members`: each member of the smaller normal form is below a member
of the larger one.

### 5. The transfer law and the two membership relations

The transfer law has no value operation in its general form. It carries any property of a value
and an answer that the join keeps on each side.

```lean
theorem lift_transfer {V : Type} {In : V → Ty → Prop} {P : V → α → Prop}
    (normal : ∀ {v : V} {t : Ty}, In v t → In v t.normalize)
    (members : ∀ {v : V} {t : Ty}, In v t → ∃ m ∈ t.members, In v m)
    (left : ∀ {v : V} (a b : α), P v a → P v (Answer.join a b))
    (right : ∀ {v : V} (a b : α), P v b → P v (Answer.join a b))
    {rule : Ty → Option α}
    (member : ∀ {m : Ty} {a : α} {v : V}, rule m = some a → In v m → P v a)
    {t : Ty} {a : α} {v : V} (typed : lift rule t = some a) (fit : In v t) : P v a
```

One structure states what the brief asks of a membership relation. It serves a rule that
answers a type, with an operation whose result is a member again.

```lean
structure ReadsUnion {V : Type} (M : V → Ty → Prop) : Prop where
  normalize : ∀ {v : V} {t : Ty}, M v t → M v t.normalize
  members : ∀ {v : V} {t : Ty}, M v t → ∃ m ∈ t.members, M v m
  joinLeft : ∀ {v : V} (a b : Ty), M v a → M v (Ty.join a b)
  joinRight : ∀ {v : V} (a b : Ty), M v b → M v (Ty.join a b)

theorem ReadsUnion.lift_sound {V : Type} {M : V → Ty → Prop} (reads : ReadsUnion M)
    {rule : Ty → Option Ty} {op : V → Option V}
    (sound : ∀ {m a : Ty} {v : V}, rule m = some a → M v m → ∃ out, op v = some out ∧ M out a)
    {t a : Ty} {v : V} (typed : lift rule t = some a) (fit : M v t) :
    ∃ out, op v = some out ∧ M out a
```

`Has` and `Fits w` each prove `ReadsUnion` once, from four lemmas that exist. Each of the four
theorems of soundness against `Has` or `Fits w` is then one application. Its statement is
unchanged (proved in scratch):

```lean
  (fits_reads w).lift_sound (fun typed fit => record_fieldOf_fits typed fit) htype hfit
```

### 6. The upper form (the coordinator's addition)

A member rule that reads one constructor has a map `C : α → Ty` back into types. The lifted
rule then answers the least `a` with the target below `C a`.

```lean
theorem lift_upper [AnswerOrder α] {rule : Ty → Option α} {C : α → Ty}
    (mono : ∀ {a b : α}, le a b → Ty.subN (C a) (C b) = true)
    (member : ∀ {m : Ty} {a : α}, Ty.Normal m → m.isMember = true → rule m = some a →
      Ty.subN m (C a) = true)
    {t : Ty} {a : α} (typed : lift rule t = some a) : Ty.subN t (C a) = true

theorem lift_least [AnswerOrder α] {rule : Ty → Option α} {C : α → Ty}
    (member : ∀ {m : Ty} {a b : α}, Ty.Normal m → m.isMember = true → rule m = some a →
      Ty.subN m (C b) = true → le a b)
    {t : Ty} {a b : α} (typed : lift rule t = some a) (upper : Ty.subN t (C b) = true) : le a b
```

Two facts correct the form that the coordinator sketched.

- **The inequality holds in `Ty.subN`, and not in raw `Ty.sub`.** At the target
  `fiberOf (prod (nat | string) unit) never` the lifted `fiberTy` answers, and raw `sub` refuses
  the target below the answer's fiber type (tested). Raw `sub` never distributes a product over
  a union. So a use site moves a value up by `fits_subN`, and not by `fits_sub`.
- **The field read has no upper form.** The order has no width rule (decisions row 178): a
  record of two fields is not below the record of one of them (tested). So no `C` exists for
  `Record.fieldOf`, and the honest instance in this slice is `fiberTy` itself, in the battery.

Both halves fall out of the same two lemmas on the join of a list, so the second half does not
hold the slice.

### 7. Lean's own tools

| Tool | Verdict |
| --- | --- |
| a class for the carrier, with a product instance | used: instance search finds the carrier, and a pair carrier costs no declaration |
| a structure for a membership relation, with its law as a projection | used: each theorem of soundness against a membership relation is one application |
| `rfl` for the equality with the present definitions | used: the two rules and `joinResults` |
| `proof_goal` with `@[semantics]` | used: each law is placed before it is proved |
| a command or an attribute that declares an instance and its theorem of soundness against `Has` or `Fits w` | not built: with the laws, an instance's theorem is one application already. A command would hide one line and need the theorem's statement as its input. Two instances do not pay for it |
| an aesop bank | not built: a member rule's facts are no search problem |

One packaging does pay for the conversions, and it is a structure and not a command. A rule
that reads one covariant constructor owes three facts.

- It answers only at the constructor.
- The constructor reflects and keeps the order.
- The rule reads each normal member below the constructor.

From the three, `Below`, the upper form and its least half each follow in one line (proved in
scratch). `fiberTy` is an instance in 12 lines. Proposal 2 below is to land it.

### 8. The consumers

- **The conversions of candidate N**: `fiberTy`, `Checker.listOf?`, `exitOf?` and
  `Decision.arms .option` each read one constructor. `fiberTy_eq_some`
  (`src/Effect4/Laws/Program/Typed/Membership.lean`) becomes the upper form at its 13 uses in
  `src/Effect4/Laws/Program/Typed/Denotation.lean`.
- **A third rule reads a union member by member today**: `Tuple.typeAt`
  (`src/Effect4/Program/Tuple.lean`), by its own recursion over the normal form. It agrees with
  the lifted `Tuple.project` on every probed target (tested: a finite probe). The brief does not
  assign it.
- **The printer**: the coordinator ran tsgo 7 on the printed TypeScript forms. This seat ran no
  TypeScript, so the result is assumed here: it is relayed. tsgo accepts `never` at every
  eliminator as printed. It refuses
  a proper union at a generic call when the type arguments are inferred. It accepts the same
  call when the type arguments are written at the join. So the upper form is also what the
  printer writes at a proper union.
- **The gap**: each lifted eliminator of seat GAP's study (5.3) is the member rule and one line
  for a gap member.

### 9. One proof outside the brief's list

`cell_msgsTy` unfolds `Record.fieldType` and rewrites the target's normal form inside. Once the
rule is written through the combinator, the unfolded goal holds no `normalize`, and the `rw`
fails (tested). The coordinator added the proof to the seat's list on 2026-10-06: its body
becomes `Record.fieldType_normal (cellTy_normal canonical) rfl`, as its siblings have, and its
statement stays. No other proof outside the three law files unfolds `fieldType`, `setType` or
`joinResults` (reading: a search of `src`, `Test` and `tools`).

## The statements (compiled in scratch)

Findings 4, 5 and 6 give five of them. The other four:

```lean
theorem lift_never (rule : Ty → Option α) : lift rule .never = some Answer.bot

theorem lift_member (rule : Ty → Option α) {t : Ty} (normal : Ty.Normal t)
    (member : t.isMember = true) : lift rule t = (rule t).map (Answer.join Answer.bot)

theorem lift_congr (rule : Ty → Option α) {s t : Ty} (same : s.normalize = t.normalize) :
    lift rule s = lift rule t

theorem lift_mono [AnswerOrder α] {lower upper : Ty → Option α} (below : Below lower upper)
    {s t : Ty} (smaller : Ty.subN s t = true) {b : α} (typed : lift upper t = some b) :
    ∃ a, lift lower s = some a ∧ le a b
```

`fieldType_normal` and `setType_normal` follow from `lift_member`, with `Ty.join_never`. One
last statement gives the claim's parts as one, for the claim's pointer.

## Proposals (not rulings)

1. **The order of the commits.** The laws land before `Record.lean` moves. So each consumer
   proof lands once, in its final form, and `Record.lean` is edited once.
2. **The eliminator of one constructor.** It is the last section of the law module, in one
   commit that can be dropped. It holds the structure of finding 7 and its three one-line laws.
   `fiberTy` and `Checker.listOf?` are its controls in the battery. It converts no rule.
3. **The claim** `union-rule-lift`, concept `subtyping-algebra`, at R14. The receipt gives the
   row's text.

## What this does not establish

- No rule of the checker changes, and no by-shape rule is converted. `fiberTy` still refuses a
  union and `never`.
- The monotone law is conditional. No statement here proves `Below` for `Record.fieldOf` or
  `Record.setOf`. `checker-monotone` stays open.
- The upper form says nothing at an invariant constructor (`refOf`, `deferredOf`, a handle).
- The transfer law keeps membership. It says nothing of behaviour, of a target or of tsgo.
- A theorem proved in scratch was accepted by the kernel in a scratch file. No gate has read it.
- The host boundary stays where `docs/core/host-boundary.md` puts it.
