# 2026-10-06 seat UNION receipt: one combinator for a rule that reads a union member by member

**The one thing to know before merging:** the merge makes `generated/semantics.md` stale. The
law module places 38 theorems at `subtyping-algebra`, each as a node of R14, and the semantics
registry has no claim row for them. Add the row of section 11, then run `make gen-semantics`.
`make gen-fixtures` leaves `git status` empty, and `check-gen` is not run. One proof outside
the brief's list changed, by the coordinator's ruling: `cell_msgsTy` (section 2). The last Lean
commit, `132325b6`, can be dropped alone.

Brief: `docs/research/2026-10-05-claude-lead/briefs/seat-union-brief.md`. Design:
`docs/research/2026-10-06-seat-UNION-design.md`. In this receipt a **union member** is an
element of `Ty.members`: a type that is not `never` and whose head is not a union. A **member
rule** answers at one union member, or refuses it. The **lifted rule** is `UnionRule.lift` of a
member rule.

## 1. Base and head

Branch `seat/union`, in the worktree `/Users/pooks/Dev/lean4-effect4-qtypes`. Base `08afe77c`.
The head of the Lean work is `132325b6`. The commit after it holds documents only: this receipt,
the design note's last section and the two statement lists.

| Commit | Step |
| --- | --- |
| `f2484054` | 1: the design note, with its probes |
| `65e0db13` | 2: the core module `Effect4.Program.UnionRule`; the law module with `AnswerOrder`, `Below`, `ReadsUnion` and eleven planned goals at R14; the import in `src/Effect4/Laws.lean` |
| `c95b8037` | 3: the eleven laws proved in place, with their helper lemmas; `lift_laws`, the claim as one statement |
| `98308cb2` | 4: `Record.fieldType`, `Record.setType` and `Record.joinResults` through the combinator; `fieldType_normal` and `setType_normal` from `lift_member`; `cell_msgsTy` in its siblings' form |
| `31b9ed42` | 5: the four soundness theorems from `ReadsUnion.lift_sound`; `has_reads` and `fits_reads` |
| `95dd8a1e` | 6: the battery; the import in `Test/All.lean` |
| `103e9bab` | 7: `Eliminator`, `below_of_upper` and four projections; two instances and a red control in the battery |
| `132325b6` | 8: `lift_union`, `lift_union_eq`, `lift_unique` and `Eliminator.adjoint`; `typeAt_eq_lift` in the battery. It can be dropped alone |

The order differs from the brief's in one place. The laws land before `Record.lean` moves. So
each consumer proof lands once, in its final form, and `Record.lean` is edited once.

Steps 7 and 8 were committed twice. The first time, the structure's monotone law was named
`Eliminator.below`. The estate's population filter reads the name `below` under an inductive
type as a generated companion (`isGeneratedCompanion`, `tools/ProofGraph/Population.lean`). So
the semantics census would not count that theorem. It is `Eliminator.monotone` now, and the two
commits were made again with that one name changed. The default build of section 3 is the
build after the rename.

## 2. Changed files

| File | What changed |
| --- | --- |
| `src/Effect4/Program/UnionRule.lean` | new, a core module: `Answer`, its instances at `Ty` and at a pair, `joinAll`, `lift` |
| `src/Effect4/Laws/Program/UnionRule.lean` | new: the laws |
| `Test/Program/UnionRule.lean` | new: the battery |
| `src/Effect4/Program/Record.lean` | one import; `joinResults`, `fieldType` and `setType` through the combinator; the head comment |
| `src/Effect4/Laws/Program/Typing/TermIntro.lean` | one import; the proofs of `fieldType_normal` and `setType_normal`; the private `mapM_singleton` goes, with no use left |
| `src/Effect4/Laws/Program/Typed.lean` | one import; `has_reads`; the proofs of `RecordChecks.fieldType` and `RecordChecks.setType` |
| `src/Effect4/Laws/Program/Typed/RecordOperations.lean` | one import; `fits_reads`; the proofs of `record_fieldType_fits` and `record_setType_fits` |
| `src/Effect4/Laws/Modules/Queue/Typing.lean` | the proof of `cell_msgsTy`: `Record.fieldType_normal (cellTy_normal canonical) rfl` |
| `src/Effect4/Laws.lean` | one import, directly before `Effect4.Laws.Program.TypeAlgebra` |
| `Test/All.lean` | one import, directly after `Test.Program.RecordOperations` |
| `docs/research/2026-10-06-seat-UNION-*` | the design note, three probe files, this receipt, the two statement lists and their producer |

**The proof outside the brief's list.** `cell_msgsTy` unfolded `Record.fieldType` and rewrote
the target's normal form inside. With the rule written through the combinator the unfolded goal
holds no `normalize`, and the `rw` fails (tested, before the change:
`docs/research/2026-10-06-seat-UNION-probe-unfold.lean.txt`). The coordinator added the proof to
the seat's list on 2026-10-06. Its statement stays. No other proof outside the list looks inside
`fieldType`, `setType` or `joinResults`: the default build is the evidence (tested).

**Five theorems lose their last use in `src`.** `mapM_some_mem`
(`src/Effect4/Laws/Program/Typed/RecordValues.lean`), `RecordChecks.foldl_join` and
`RecordChecks.joinResults` (`src/Effect4/Laws/Program/Typed.lean`), `fits_foldl_join` and
`fits_joinResults` (`src/Effect4/Laws/Program/Typed/RecordOperations.lean`). Each keeps its
statement and its proof. `Test/Program/RecordOperations.lean` prints the axioms of three of them.
Section 14 proposes the cut.

## 3. Commands and results

Each Lean, Lake and `make` command ran through `/Users/pooks/Dev/lean4-effect4/scratch/lean-slot.sh`,
from the worktree. The table gives the command after the slot script.

| Command | Result |
| --- | --- |
| `lake build Effect4.Laws.Program.UnionRule` and `lake build Effect4.Laws`, at steps 2 and 3 | `Build completed successfully` (275 and 693 jobs) |
| `lake build Effect4.Laws.Program.Typing.TermIntro Effect4.Laws.Program.Typed.RecordOperations Effect4.Laws.Modules.Queue.Typing`, at step 4 | `Build completed successfully (460 jobs).` The four soundness proofs of the base compile unchanged against the rules as rewritten |
| the same two last targets, at step 5 | `Build completed successfully (460 jobs).` |
| `lake env lean -DwarningAsError=true Test/Program/UnionRule.lean`, at steps 6, 7 and 8 | no message |
| `lake build`, the default targets, at the head | `Build completed successfully (1035 jobs).` It ran once more before the rename of section 1, with the same line |
| `make -o build -o ts/eff/node_modules -o harness/truth/node_modules gen-fixtures` | `PASS generate: requested producers ran in dependency order`. `git status --short` then lists this seat's own pending edit of the design note and no other path |
| `make -o build -o ts/eff/node_modules -o harness/truth/node_modules check-cases` | `conform cases: PASS, exit 0; .lake/conform/cases.json` |
| `make -o build -o ts/eff/node_modules -o harness/truth/node_modules check-docs` | `PASS check-docs: every path, link, citation and make target in 76 documents resolves` |
| `python3 scripts/check-language.py --show` on the design note and on this receipt | no finding |

**The gate lines, at the base and at the head.** The base's lines are from
`lake env lean -DwarningAsError=true Test/All.lean` at the base. The head's are from the log of
the default build, which elaborates `Test/All.lean` again.

| Gate | Base `08afe77c` | Head |
| --- | --- | --- |
| library-root gate | 178 API and utility modules, 319 Laws-only modules | 179 API and utility modules, 320 Laws-only modules |
| module and axiom gate | 782 modules and 91031 declarations at `[propext, Quot.sound]` | 785 modules and 91339 declarations at `[propext, Quot.sound]` |
| goal gate | 28 planned goals, 12 declarations rest on goals | 28 planned goals, 12 declarations rest on goals |
| proof-style ratchet | 1911 recorded uses and 52 recorded unread commands in 1161 entries | the same line |

**No existing statement changes.** The producer
`docs/research/2026-10-06-seat-UNION-statements.lean.txt` prints the signature that `#check`
prints, for each authored theorem whose statement names `Record.fieldType`, `Record.setType` or
`Record.joinResults`. It loads `Effect4.Laws` and `Test.All`.

| Run | Result |
| --- | --- |
| at the base, after step 4: the four sources that had changed by then as `git show 08afe77c:<path>` gives them, the new files held aside, `lake build` restored from Lake's cache | 59 theorems, 251 lines (`docs/research/2026-10-06-seat-UNION-statements-base.txt`) |
| at the head | 59 theorems, 251 lines (`docs/research/2026-10-06-seat-UNION-statements-head.txt`) |
| `diff` of the two files | no difference: no existing statement changes |

**Not run**, as the brief lists: `check-gen`, `check-slow`, `check-corpus`, `check-target`,
`check-truth`, the conservativity script and `gen-semantics`. Also not run: `dune`, any
TypeScript, `make check`, `make check-full`, `check-semantics`, `check-proof-style` as its own
target (the default build runs the ratchet inside `Test.Audit.ProofStyle`), `gen-lcnf` and
`check-compiler`.

## 4. Axiom output

The axiom gate's line is in section 3. The law module holds 51 theorem constants: its 38
authored theorems and the 13 law fields of `AnswerOrder`, `ReadsUnion` and `Eliminator`. The
table gives `collectAxioms` of each, through the slot.

| Axioms | Count | Theorems |
| --- | --- | --- |
| `[propext, Quot.sound]` | 39 | `Eliminator.adjoint`, `Eliminator.embeds`, `Eliminator.lift_least`, `Eliminator.lift_mono`, `Eliminator.lift_upper`, `Eliminator.monotone`, `Eliminator.reads`, `Eliminator.shape`, `ReadsUnion.joinLeft`, `ReadsUnion.joinRight`, `ReadsUnion.lift_sound`, `ReadsUnion.members`, `ReadsUnion.normalize`, `below_of_upper`, `closed_join`, `foldl_join_normalize`, `foldl_join_start`, `joinAll_normalize`, `join_normalize_right`, `lift_all`, `lift_closed`, `lift_closed_pair`, `lift_congr`, `lift_laws`, `lift_least`, `lift_member`, `lift_mono`, `lift_never`, `lift_transfer`, `lift_union`, `lift_union_eq`, `lift_unique`, `lift_upper`, `mapM_answer`, `mapM_cons_eq_some`, `mapM_source`, `mapM_total`, `members_union`, `normal_ofMembers` |
| `[propext]` | 3 | `foldl_keeps`, `joinAll_keeps`, `le_joinAll` |
| no axiom | 9 | `AnswerOrder.bot_le`, `AnswerOrder.join_le`, `AnswerOrder.le_join_left`, `AnswerOrder.le_join_right`, `AnswerOrder.refl`, `AnswerOrder.trans`, `foldl_all`, `joinAll_all`, `joinAll_le` |

The plan (`#plan_status`, `tools/ProofGraph/Plan.lean`) reads `lift_laws` and the 20 other
named statements of section 6 as proved, with `next goals: 0`, in one run at the head. The
module holds no planned goal.

## 5. Evidence

| Claim | Evidence |
| --- | --- |
| each statement of section 6 | proved: the kernel accepted it, and the axiom gate read it in the default build |
| the two record rules and `joinResults` equal their definitions at the base | proved: three `rfl` examples in the battery, whose right sides are the bodies at the base |
| no existing statement changes | tested: the two statement lists are equal |
| no admitted program changes | proved for the two rules, by the `rfl` above. Tested for the engine's fixtures: `gen-fixtures` leaves `git status` empty |
| the four proofs of soundness against `Has` and `Fits w`, as written at the base, survive the redefinition | tested: the narrow build at step 4 |
| each red control is red for its stated reason | tested: the battery's guards, and proved for `stringOnly_not_below` and `causeInput_no_eliminator` |
| `fiberTy` and `Checker.listOf?` are instances of `Eliminator`, as member rules | proved: `fiberTy_eliminator`, `listOf_eliminator` (`Test/Program/UnionRule.lean`) |
| `Tuple.typeAt` is the lifted `Tuple.project` | proved: `typeAt_eq_lift` (the same file). A finite probe on 11 targets and 4 positions came first (`docs/research/2026-10-06-seat-UNION-probe-laws.lean.txt`) |
| the cause rule's upper form at `causeOf e \| exitOf unknown e` | tested: a finite probe on five targets; no theorem |
| `exitOf?` and `Decision.arms .option` fit `Eliminator` | reading: the same three facts as `fiberTy` and `Checker.listOf?`; not compiled |
| `Record.fieldOf` and `Record.setOf` satisfy `Below` | reading; not compiled |
| tsgo's verdicts on a printed union | assumed: relayed by the coordinator. This seat ran no TypeScript |

No evidence is host-only. Each guard is a finite check on closed types and no theorem.

## 6. The landed statements and their placement

One placement serves every theorem of the law module.

- Concept: `subtyping-algebra`; property: proposed in section 11, "a rule that reads a union
  member by member".
- Question: the proposed registry claim `union-rule-lift` (role compatibility); its pointer is
  `lift_laws`. Consumers: the two record rules today; each conversion of candidate N; seat
  FORM's `check_closed`; the lifted eliminators of the type gap.
- Reach: every member rule into a carrier with a least answer and a join. The order is
  `Ty.subN`, with `Ty.normalize` and `Ty.members`. A relation between values and types must read
  the normal form and the union members. Decisions rows 282 and 285.
- Does not establish: that any other rule reads a union this way; `checker-monotone`; that tsgo
  agrees; anything at an invariant position; any run. A conditional law leaves its member
  premise open.
- Unlocks: R14, as groundwork of the proposed claims `checker-monotone` and `gradual-checker`.

| Statement | What it says | Its own limit |
| --- | --- | --- |
| `lift_never` | the lifted rule answers the least answer at `never` | no by-shape rule answers `never` until its conversion |
| `lift_member` | at a normal type that is one union member, the lifted rule is the member rule, up to the join with the least answer | nothing at a union of two members |
| `lift_congr` | two types with one normal form have one answer | — |
| `lift_mono`, with `Below` | where `Below lower upper` holds, a smaller target has an answer where a larger one has, and the answer is smaller | conditional: it proves `Below` for no rule |
| `lift_transfer` | a property of a value and an answer that the join keeps on each side passes from the union members to the lifted rule | it carries the property it is given and no other |
| `ReadsUnion.lift_sound`, with `ReadsUnion` | a member rule that is sound against a membership relation at each normal union member lifts to a rule that is sound against it | conditional on the member rule's law |
| `lift_all` | a property that the least answer has, and that the join of two answers with it has, holds of the lifted answer where each union member's answer has it | it reads no property of the target |
| `lift_closed`, `lift_closed_pair` | a lifted rule answers closed types at a closed target, where the member rule does at each closed normal union member | they prove the member fact for no rule |
| `lift_upper` | for a map `C` that keeps the order, with each answered normal union member below `C` of its answer: the target is below `C a`, in `Ty.subN` | false in raw `Ty.sub`; nothing at an invariant constructor |
| `lift_least` | the lifted answer is below each `b` with the target below `C b`, under the matching member fact | the same |
| `lift_laws` | the five parts of the brief as one statement | it adds nothing to its parts |
| `below_of_upper` | `Below rule rule` from three member facts of an upper map | — |
| `Eliminator` and `.monotone`, `.lift_mono`, `.lift_upper`, `.lift_least` | three facts of a member rule that reads one covariant constructor give the order laws | an invariant constructor has no instance |
| `Eliminator.adjoint` | the lifted rule answers exactly below the constructor's image, and `le a b ↔ Ty.subN t (C b)` | the same |
| `lift_union` | for a monotone member rule, the lifted rule answers at a union exactly when it answers at both sides, and its answer is their join up to the order | up to the order: no equation at a pair |
| `lift_union_eq` | the same as an equation, at the carrier `Ty` | `Ty` only |
| `lift_unique` | at the carrier `Ty`, a map with the four properties of the lifted rule is the lifted rule | `Ty` only: another carrier needs associative joins as an equation |

Two theorems stand outside the module, each with the placement of its file. `has_reads` is in
`RecordChecks`, for the Boolean value check. `fits_reads` is a step of the claim `denote-typed`,
at R3. Each proves `ReadsUnion` once for its relation.

**Three statements differ from the design message.** The member premises of `lift_transfer` and
`ReadsUnion.lift_sound` give `Ty.Normal m` and `m.isMember = true` too, so every member fact is
stated at a normal union member. The law module imports `Effect4.Laws.Program.Template`, for the
closed instances, so `Typing/TermIntro.lean` gains that module in its import closure. The
structure's third field is `reads`, and it reads `Ty.subN`.

## 7. What an instance owes

A conversion's brief can copy this list. An instance is a by-shape rule written as a lifted
rule. It owes nothing about unions, normal forms, `mapM` or the join of a list.

**In the core module of the rule, one line.**

| It supplies | Form |
| --- | --- |
| its member rule | a function `Ty → Option α` that answers at one union member. The present by-shape function serves as it is: `fiberTy`, `Checker.listOf?`, `exitOf?` |
| its carrier `α` | `Ty` for one type, a pair for two. Instance search finds both. A test by equality needs a unit carrier: one instance of `Answer` and one of `AnswerOrder`, to add with the first test that converts |
| the rule | `UnionRule.lift memberRule target` |

**In its law file, the member rule's facts.** Each fact is stated at one normal union member:
it may assume `Ty.Normal m` and `m.isMember = true`.

| For | It owes | It gets |
| --- | --- | --- |
| the answer at `never`, one normal form, one member | nothing | `lift_never`, `lift_congr`, `lift_member` |
| soundness against `Fits w` or against `Val.hasTy`, with an operation on values | the member rule's own law at one union member | `(fits_reads w).lift_sound` or `RecordChecks.has_reads.lift_sound`: one application |
| another property of a value and an answer | the member fact, and that the join keeps the property on each side | `lift_transfer` |
| closed types | a closed union member has a closed answer | `lift_closed`, `lift_closed_pair` |
| another property of answers alone | it holds of the least answer, the join of two answers with it has it, and each member's answer has it | `lift_all` |
| **the order, for a rule that reads one covariant constructor `C`** | **three facts**, as `Eliminator rule C`: | `Eliminator.lift_mono`, `.lift_upper`, `.lift_least`, `.adjoint`, `.monotone` |
| | `shape`: `rule m = some a → m = C a` | |
| | `embeds`: `Ty.subN (C a) (C b) = true ↔ le a b` | |
| | `reads`: a normal union member below `C b`, in `Ty.subN`, is answered | |
| the order, for a rule that reads two heads | four member facts of an upper map `C`: `C` keeps the order; an answered member is below `C` of its answer; that answer is the least; a member below `C b` is answered | `lift_upper`, `lift_least`, `below_of_upper`, then `lift_mono` |
| the order, for a rule with no upper map (the record rules) | `Below rule rule` itself | `lift_mono` |
| agreement with a rule that reads a union by its own recursion, at the carrier `Ty` | four facts of that rule: it reads the normal form; it answers `never` at `never`; it is the member rule at a normal union member; it joins at a normal union | `lift_unique`: one equation, with no induction |

**The measured cost, in lines of the battery.** `fiberTy_eliminator` takes 19 lines and
`listOf_eliminator` 22. Each proves `shape` and `reads` by cases on the member, and `embeds`
from the generated view (`Ty.sub_args_fiberOf`, `Ty.sub_list`). `subN_fiberOf_iff` takes 7 more.
`typeAt_eq_lift` takes 20 lines, and its member fact `project_normal` 18.

**At a use site.** Where a proof rewrote by the equation of a by-shape rule
(`rw [fiberTy_eq_some hfib] at hty`), it now moves the value up:
`fits_subN w (e.lift_upper hfib) v hfit`. The inequality is in `Ty.subN`. It is false in raw
`Ty.sub` at a target that is not its own normal form (the battery's `rawFiber`).

## 8. Which rule fits `Eliminator`

| Rule | Member rule and carrier | `C` | Fits as it stands? |
| --- | --- | --- | --- |
| `fiberTy` | itself; `Ty × Ty` | `fun pair => .fiberOf pair.1 pair.2` | yes: proved, `fiberTy_eliminator` in the battery |
| `Checker.listOf?` | itself; `Ty` | `Ty.list` | yes: proved, `listOf_eliminator` in the battery |
| `exitOf?` | itself; `Ty × Ty` | `fun pair => .exitOf pair.1 pair.2` | yes, by reading: the exit constructor is covariant in both columns, and the facts are `fiberTy`'s with `Ty.sub_args_exitOf` |
| `Decision.arms` at `.option` | the match on `.option a`, which has no name today; `Ty` | `Ty.option` | yes, by reading. The decision then maps the lifted answer `a` to `([], [a])`. At `never` it binds `never`, and `arms_length` holds |
| `Decision.arms` at `.bool` | the test `t = .bool`; a unit carrier | `fun _ => .bool` | yes, by reading, once the unit carrier exists. Today the test is on the raw type, so `bool \| bool` is refused |
| the cause atoms, through `causeInputError?` | itself; `Ty` | none | **no: it needs the variant.** The rule answers one error type at a cause type and at an exit type, so no `C` has `shape` (proved: `causeInput_no_eliminator`). It owes the four member facts of the upper map `fun e => causeOf e \| exitOf unknown e` and uses `lift_upper`, `lift_least` and `below_of_upper`. A finite probe of that upper form passes on five targets |
| `NativeAtom.projectProduct`, for `fst` and `snd` | the product arm; `Ty` | none | no, the same variant, by reading: one column of a product is read and the other is lost. The upper map of `fst` is `fun a => .prod a .unknown`. The rule already reads a union, by its own recursion over the raw type, so its answer is not normalized. A conversion changes a raw answer. Whether it keeps each answer's normal form is not checked |
| `Tuple.typeAt` | `Tuple.project index`; `Ty` | none | no upper map of one constructor, and it needs none: it reads a union today. `typeAt_eq_lift` is the equation that its conversion states (proved in the battery) |
| `Record.fieldType`, `Record.setType` | `Record.fieldOf`, `Record.setOf`; `Ty` | none | no: the order has no width rule (tested: the battery's guard). They owe `Below` itself |

## 9. A restriction at a proper union

The coordinator asks whether the module would hold one definition beside `lift`. It is the
lifted rule, restricted to a target whose normal form has at most one union member. Nothing is
built.

- **The module holds it cleanly.** It is one definition in the core module and two lemmas in
  the law module.

```lean
-- not compiled
def liftOne (rule : Ty → Option α) (target : Ty) : Option α :=
  if target.normalize.members.length ≤ 1 then lift rule target else none

theorem liftOne_some : liftOne rule t = some a → lift rule t = some a
theorem liftOne_eq : t.normalize.members.length ≤ 1 → liftOne rule t = lift rule t
```

- **What carries over by `liftOne_some`.** Each law whose premise is an answer of the lifted
  rule: `lift_transfer`, `ReadsUnion.lift_sound`, `lift_all`, the closed instances, `lift_upper`,
  `lift_least` and the second half of `Eliminator.adjoint`. `lift_never` and `lift_member` carry
  over by `liftOne_eq`. The restriction reads the normal form, so `lift_congr` has a one-line
  copy.
- **What does not carry over.** `lift_mono`, `lift_union` and the first half of
  `Eliminator.adjoint` are false of the restriction. A proper union below a one-member target is
  refused: `fiberOf nat never | fiberOf string never` is below `fiberOf (nat | string) never`.
  So a rule under the restriction is not monotone in the order, at exactly the proper unions.
  `checker-monotone` then stays open at such a rule, by the owner's choice.
- **The restriction goes by one line.** A rule that says `liftOne` says `lift` later, and each
  proof that used `liftOne_some` still has its premise.

## 10. Lean's own tools

| Tool | Verdict |
| --- | --- |
| a class for the carrier, with a product instance | used: instance search finds the carrier, and a pair carrier costs no declaration |
| a class for the order, beside it | used, in the law module only: no definition reads the order |
| a structure for a membership relation, and one for a constructor's eliminator, each with its laws as projections | used: an instance's law is one application |
| `rfl` | used: the two rules and `joinResults` against their bodies at the base |
| `proof_goal` with `@[semantics]` | used: eleven goals at step 2, each proved in place at step 3 |
| a command or an attribute that declares an instance with its theorem | not built: an instance's theorem is one application already, and a command would need the theorem's statement as its input |
| an aesop bank | not built: a member rule's fact is no search problem. Each new proof names its lemmas |

No new proof uses `simp_all`, `first` or `try`. One `simp only` is new, in `mapM_cons_eq_some`.

## 11. The proposed text of the semantics registry and of the documents

Proposals only. Each file below is the coordinator's.

**`tools/Tools/SemanticsRegistry.lean`, a claim under `-- 6. subtyping-algebra`:**

```lean
    { id := "union-rule-lift", concept := "subtyping-algebra", role := .compatibility
      title := "A member rule lifted to every type by reading the union members of the normal form and joining the answers: it answers the least answer at never; at one normal union member it is the member rule, up to the join with the least answer; two types with one normal form have one answer; a member rule that is monotone in the order lifts to a monotone rule; a property of a value and an answer that the join keeps on each side passes from the union members to the lifted rule; the two record rules are its instances, and no by-shape rule is converted (decisions rows 282, 285)"
      pointer := .witness `Effect4.Program.UnionRule.lift_laws },
```

The role `.compatibility` follows the transfer law, which the four record theorems use. The
role `.monotonicity` fits `lift_mono` alone.

**The same file, the requirement R14.** The open part `checker-monotone` gains the sentence
below. R14's `top` does not move: the claim is groundwork, and it states no part of R14's row.

```text
its union groundwork is proved (union-rule-lift): each converted rule owes the three facts of
UnionRule.Eliminator, and the record rules owe UnionRule.Below
```

**`docs/core/semantics.md`, section 2.6, a required property:**

```text
- **A rule that reads a union member by member (`union-rule-lift`)**: The statement fixes a
  member rule, a function from a type to an optional answer, and a carrier of answers with a
  least answer and a join.
  The lifted rule reads the member rule at every union member of the target's normal form, and
  it joins the answers.
  It answers the least answer at `never`.
  At one normal union member it is the member rule, up to the join with the least answer.
  Two types with one normal form have one answer.
  Where the member rule is monotone in the order on normal union members, a smaller target has
  an answer where a larger one has, and the answer is smaller.
  A property of a value and an answer that the join keeps on each side passes from the union
  members to the lifted rule.
  It is proved (`UnionRule.lift_laws`, `src/Effect4/Laws/Program/UnionRule.lean`; seat UNION).
  It establishes no conversion of a by-shape rule, no `checker-monotone` and nothing at an
  invariant position.
```

**`docs/core/system-map.md`, section 8, the status of R14.** No part of the row is proved by
this work. The groundwork of two proposed claims is: `checker-monotone` and `gradual-checker`
read a union through one combinator with proved laws.

**`docs/core/controlled-english.md`, the dictionary.** The word "member" is a form of
"membership" there, and "monotone" is a predicate on worlds. Proposed entries:

| Term | Meaning here | Tree anchor |
| --- | --- | --- |
| **union member** | An element of `Ty.members`: a type that is not `never` and whose head is not a union | `members` (`src/Effect4/Program/Ty.lean`) |
| **member rule** | A function from a type to an optional answer that the checker asks at one union member | `lift` (`src/Effect4/Program/UnionRule.lean`) |
| **lifted rule** | A member rule read at every union member of the target's normal form, with the answers joined | `lift` (the same file) |
| **answer** (of a rule) | A value of the rule's carrier: a type, or a pair of types | `Answer` (the same file) |
| **monotone in the order** | Of a rule: a smaller target has an answer where a larger one has, and the answer is smaller | `lift_mono` (`src/Effect4/Laws/Program/UnionRule.lean`) |
| **eliminator** (of a constructor) | A member rule that answers only at one constructor, with that constructor's arguments | `Eliminator` (the same file) |

`docs/core/traversal-census.md` is not asserted. `Record.fieldType` and `Record.setType` now
delegate to `UnionRule.lift`, which delegates to `Ty.normalize` and `Ty.members`.

## 12. R1 to R14

The work serves R14, as groundwork, and it touches R3 and R4 by proof only. R1: no signature is
named. R2: no constructor is appended, and no alphabet moves. R3: the two record rules of the
data language keep their definitions up to `rfl`, and the four theorems of record membership
keep their statements. R4: `Fits w` gains one fact, `fits_reads`, and no rule of the typed state
changes. R5 to R13: untouched. No statement names a service (R5), the host (R6), a retained
behaviour (R7) or a face (R8). None names an exit (R9), a module (R10), a resource (R11), a
frontier (R12) or a run's input (R13). The Queue's typing changes in one proof and in no
statement. R14: no part of the row is proved. Two of its proposed claims gain their groundwork.
A rule that reads a union has one definition and proved laws. So each conversion of candidate N
owes member facts only. R14 stays open.

## 13. Open obligations

The law module holds no planned goal. These obligations pass to later slices.

| Obligation | Who owes it | What it waits on |
| --- | --- | --- |
| each conversion of candidate N: `fiberTy`, `Checker.listOf?`, `exitOf?`, `Decision.arms` | the conversion slices | the owner's ruling on a proper union; the names in the compatibility policy |
| `Below` for `Record.fieldOf` and for `Record.setOf` | the slice that states `checker-monotone` | a lemma on two field lists with equal heads: a lookup in one finds a smaller type in the other |
| the four member facts of the cause rule and of `projectProduct` | their conversions | a decision on the variant of section 8 |
| `Tuple.typeAt` through `lift` | its conversion | nothing: `typeAt_eq_lift` moves from the battery to a law file |
| the equation of `lift_union` at a pair, and `lift_unique` at another carrier | the first consumer | associative joins as an equation at that carrier, and `joinAll` at a pair read by component |
| a unit carrier, for a test by equality | the first test that converts | nothing |
| seat FORM's copy of the closed case | the coordinator, after both merges | `lift_closed` replaces its body |

## 14. Proposed decisions rows (proposals only)

1. **One combinator reads a union.** A rule of the checker that reads a type by its union
   members is `UnionRule.lift` of a member rule. The carrier of its answers is an instance of
   `UnionRule.Answer`. No rule states `target.normalize` and a traversal of the members by
   hand.
2. **A member fact is stated at a normal union member.** Each law of the lifted rule takes its
   member premise at `Ty.Normal m` and `m.isMember = true`.
3. **The inequality of a converted rule is in `Ty.subN`.** A use site moves a value by
   `fits_subN`. Raw `Ty.sub` does not hold there.
4. **A proper union at a converted rule**: open, the owner's. Section 9 gives what the
   restriction keeps and what it loses: the monotone law fails at exactly the proper unions.
5. **Five theorems with no use left in `src`** (section 2): cut them with their three lines of
   `Test/Program/RecordOperations.lean`, or keep them. The seat recommends the cut, in a slice
   whose brief names the two files.

## 15. The statements, as Lean compiles them

Each block is the signature that `#check` prints, from one run through the slot at the head.

```text
Effect4.Program.UnionRule.Answer (α : Type) : Type

Effect4.Program.UnionRule.joinAll {α : Type} [Effect4.Program.UnionRule.Answer α]
  (answers : List α) : α

Effect4.Program.UnionRule.lift {α : Type} [Effect4.Program.UnionRule.Answer α]
  (rule : Effect4.Program.Ty → Option α) (target : Effect4.Program.Ty) : Option α

Effect4.Program.UnionRule.AnswerOrder (α : Type) [Effect4.Program.UnionRule.Answer α] : Type

Effect4.Program.UnionRule.Below {α : Type} [Effect4.Program.UnionRule.Answer α]
  [Effect4.Program.UnionRule.AnswerOrder α] (lower upper : Effect4.Program.Ty → Option α) : Prop

Effect4.Program.UnionRule.ReadsUnion {V : Type} (M : V → Effect4.Program.Ty → Prop) : Prop

Effect4.Program.UnionRule.Eliminator {α : Type} [Effect4.Program.UnionRule.Answer α]
  [Effect4.Program.UnionRule.AnswerOrder α] (rule : Effect4.Program.Ty → Option α)
  (C : α → Effect4.Program.Ty) : Prop

Effect4.Program.UnionRule.lift_never {α : Type} [Effect4.Program.UnionRule.Answer α]
  (rule : Effect4.Program.Ty → Option α) :
  Effect4.Program.UnionRule.lift rule Effect4.Program.Ty.never =
    some Effect4.Program.UnionRule.Answer.bot

Effect4.Program.UnionRule.lift_member {α : Type} [Effect4.Program.UnionRule.Answer α]
  (rule : Effect4.Program.Ty → Option α) {t : Effect4.Program.Ty} (normal : t.Normal)
  (member : t.isMember = true) :
  Effect4.Program.UnionRule.lift rule t =
    Option.map (Effect4.Program.UnionRule.Answer.join Effect4.Program.UnionRule.Answer.bot) (rule t)

Effect4.Program.UnionRule.lift_congr {α : Type} [Effect4.Program.UnionRule.Answer α]
  (rule : Effect4.Program.Ty → Option α) {s t : Effect4.Program.Ty}
  (same : s.normalize = t.normalize) :
  Effect4.Program.UnionRule.lift rule s = Effect4.Program.UnionRule.lift rule t

Effect4.Program.UnionRule.lift_mono {α : Type} [Effect4.Program.UnionRule.Answer α]
  [Effect4.Program.UnionRule.AnswerOrder α] {lower upper : Effect4.Program.Ty → Option α}
  (below : Effect4.Program.UnionRule.Below lower upper) {s t : Effect4.Program.Ty}
  (smaller : s.subN t = true) {b : α} (typed : Effect4.Program.UnionRule.lift upper t = some b) :
  ∃ a,
    Effect4.Program.UnionRule.lift lower s = some a ∧ Effect4.Program.UnionRule.AnswerOrder.le a b

Effect4.Program.UnionRule.lift_transfer {α : Type} [Effect4.Program.UnionRule.Answer α] {V : Type}
  {In : V → Effect4.Program.Ty → Prop} {P : V → α → Prop}
  (normal : ∀ {v : V} {t : Effect4.Program.Ty}, In v t → In v t.normalize)
  (members : ∀ {v : V} {t : Effect4.Program.Ty}, In v t → ∃ m, m ∈ t.members ∧ In v m)
  (left : ∀ {v : V} (a b : α), P v a → P v (Effect4.Program.UnionRule.Answer.join a b))
  (right : ∀ {v : V} (a b : α), P v b → P v (Effect4.Program.UnionRule.Answer.join a b))
  {rule : Effect4.Program.Ty → Option α}
  (member :
    ∀ {m : Effect4.Program.Ty} {a : α} {v : V},
      m.Normal → m.isMember = true → rule m = some a → In v m → P v a)
  {t : Effect4.Program.Ty} {a : α} {v : V} (typed : Effect4.Program.UnionRule.lift rule t = some a)
  (fit : In v t) : P v a

Effect4.Program.UnionRule.ReadsUnion.lift_sound {V : Type} {M : V → Effect4.Program.Ty → Prop}
  (reads : Effect4.Program.UnionRule.ReadsUnion M)
  {rule : Effect4.Program.Ty → Option Effect4.Program.Ty} {op : V → Option V}
  (sound :
    ∀ {m a : Effect4.Program.Ty} {v : V},
      m.Normal → m.isMember = true → rule m = some a → M v m → ∃ out, op v = some out ∧ M out a)
  {t a : Effect4.Program.Ty} {v : V} (typed : Effect4.Program.UnionRule.lift rule t = some a)
  (fit : M v t) : ∃ out, op v = some out ∧ M out a

Effect4.Program.UnionRule.lift_all {α : Type} [Effect4.Program.UnionRule.Answer α] {Q : α → Prop}
  (bot : Q Effect4.Program.UnionRule.Answer.bot)
  (join : ∀ {a b : α}, Q a → Q b → Q (Effect4.Program.UnionRule.Answer.join a b))
  {rule : Effect4.Program.Ty → Option α} {t : Effect4.Program.Ty}
  (member : ∀ (m : Effect4.Program.Ty), m ∈ t.normalize.members → ∀ {a : α}, rule m = some a → Q a)
  {a : α} (typed : Effect4.Program.UnionRule.lift rule t = some a) : Q a

Effect4.Program.UnionRule.lift_closed {rule : Effect4.Program.Ty → Option Effect4.Program.Ty}
  (member :
    ∀ {m a : Effect4.Program.Ty},
      m.Normal → m.isMember = true → m.closed = true → rule m = some a → a.closed = true)
  {t a : Effect4.Program.Ty} (typed : Effect4.Program.UnionRule.lift rule t = some a)
  (closed : t.closed = true) : a.closed = true

Effect4.Program.UnionRule.lift_closed_pair
  {rule : Effect4.Program.Ty → Option (Effect4.Program.Ty × Effect4.Program.Ty)}
  (member :
    ∀ {m : Effect4.Program.Ty} {a : Effect4.Program.Ty × Effect4.Program.Ty},
      m.Normal →
        m.isMember = true →
          m.closed = true → rule m = some a → a.fst.closed = true ∧ a.snd.closed = true)
  {t : Effect4.Program.Ty} {a : Effect4.Program.Ty × Effect4.Program.Ty}
  (typed : Effect4.Program.UnionRule.lift rule t = some a) (closed : t.closed = true) :
  a.fst.closed = true ∧ a.snd.closed = true

Effect4.Program.UnionRule.lift_upper {α : Type} [Effect4.Program.UnionRule.Answer α]
  [Effect4.Program.UnionRule.AnswerOrder α] {rule : Effect4.Program.Ty → Option α}
  {C : α → Effect4.Program.Ty}
  (mono : ∀ {a b : α}, Effect4.Program.UnionRule.AnswerOrder.le a b → (C a).subN (C b) = true)
  (member :
    ∀ {m : Effect4.Program.Ty} {a : α},
      m.Normal → m.isMember = true → rule m = some a → m.subN (C a) = true)
  {t : Effect4.Program.Ty} {a : α} (typed : Effect4.Program.UnionRule.lift rule t = some a) :
  t.subN (C a) = true

Effect4.Program.UnionRule.lift_least {α : Type} [Effect4.Program.UnionRule.Answer α]
  [Effect4.Program.UnionRule.AnswerOrder α] {rule : Effect4.Program.Ty → Option α}
  {C : α → Effect4.Program.Ty}
  (member :
    ∀ {m : Effect4.Program.Ty} {a b : α},
      m.Normal →
        m.isMember = true →
          rule m = some a → m.subN (C b) = true → Effect4.Program.UnionRule.AnswerOrder.le a b)
  {t : Effect4.Program.Ty} {a b : α} (typed : Effect4.Program.UnionRule.lift rule t = some a)
  (upper : t.subN (C b) = true) : Effect4.Program.UnionRule.AnswerOrder.le a b

Effect4.Program.UnionRule.lift_laws {α : Type} [Effect4.Program.UnionRule.Answer α]
  [Effect4.Program.UnionRule.AnswerOrder α] (rule : Effect4.Program.Ty → Option α) :
  Effect4.Program.UnionRule.lift rule Effect4.Program.Ty.never =
      some Effect4.Program.UnionRule.Answer.bot ∧
    (∀ {t : Effect4.Program.Ty},
        t.Normal →
          t.isMember = true →
            Effect4.Program.UnionRule.lift rule t =
              Option.map
                (Effect4.Program.UnionRule.Answer.join Effect4.Program.UnionRule.Answer.bot)
                (rule t)) ∧
      (∀ {s t : Effect4.Program.Ty},
          s.normalize = t.normalize →
            Effect4.Program.UnionRule.lift rule s = Effect4.Program.UnionRule.lift rule t) ∧
        (Effect4.Program.UnionRule.Below rule rule →
            ∀ {s t : Effect4.Program.Ty} {b : α},
              s.subN t = true →
                Effect4.Program.UnionRule.lift rule t = some b →
                  ∃ a,
                    Effect4.Program.UnionRule.lift rule s = some a ∧
                      Effect4.Program.UnionRule.AnswerOrder.le a b) ∧
          ∀ {V : Type} {In : V → Effect4.Program.Ty → Prop} {P : V → α → Prop},
            (∀ {v : V} {t : Effect4.Program.Ty}, In v t → In v t.normalize) →
              (∀ {v : V} {t : Effect4.Program.Ty}, In v t → ∃ m, m ∈ t.members ∧ In v m) →
                (∀ {v : V} (a b : α), P v a → P v (Effect4.Program.UnionRule.Answer.join a b)) →
                  (∀ {v : V} (a b : α), P v b → P v (Effect4.Program.UnionRule.Answer.join a b)) →
                    (∀ {m : Effect4.Program.Ty} {a : α} {v : V},
                        m.Normal → m.isMember = true → rule m = some a → In v m → P v a) →
                      ∀ {t : Effect4.Program.Ty} {a : α} {v : V},
                        Effect4.Program.UnionRule.lift rule t = some a → In v t → P v a

Effect4.Program.UnionRule.below_of_upper {α : Type} [Effect4.Program.UnionRule.Answer α]
  [Effect4.Program.UnionRule.AnswerOrder α] {rule : Effect4.Program.Ty → Option α}
  {C : α → Effect4.Program.Ty}
  (upper :
    ∀ {m : Effect4.Program.Ty} {a : α},
      m.Normal → m.isMember = true → rule m = some a → m.subN (C a) = true)
  (least :
    ∀ {m : Effect4.Program.Ty} {a b : α},
      m.Normal →
        m.isMember = true →
          rule m = some a → m.subN (C b) = true → Effect4.Program.UnionRule.AnswerOrder.le a b)
  (reads :
    ∀ {m : Effect4.Program.Ty} {b : α},
      m.Normal → m.isMember = true → m.subN (C b) = true → ∃ a, rule m = some a) :
  Effect4.Program.UnionRule.Below rule rule

Effect4.Program.UnionRule.Eliminator.monotone {α : Type} [Effect4.Program.UnionRule.Answer α]
  [Effect4.Program.UnionRule.AnswerOrder α] {rule : Effect4.Program.Ty → Option α}
  {C : α → Effect4.Program.Ty} (e : Effect4.Program.UnionRule.Eliminator rule C) :
  Effect4.Program.UnionRule.Below rule rule

Effect4.Program.UnionRule.Eliminator.lift_mono {α : Type} [Effect4.Program.UnionRule.Answer α]
  [Effect4.Program.UnionRule.AnswerOrder α] {rule : Effect4.Program.Ty → Option α}
  {C : α → Effect4.Program.Ty} (e : Effect4.Program.UnionRule.Eliminator rule C)
  {s t : Effect4.Program.Ty} (smaller : s.subN t = true) {b : α}
  (typed : Effect4.Program.UnionRule.lift rule t = some b) :
  ∃ a, Effect4.Program.UnionRule.lift rule s = some a ∧ Effect4.Program.UnionRule.AnswerOrder.le a b

Effect4.Program.UnionRule.Eliminator.lift_upper {α : Type} [Effect4.Program.UnionRule.Answer α]
  [Effect4.Program.UnionRule.AnswerOrder α] {rule : Effect4.Program.Ty → Option α}
  {C : α → Effect4.Program.Ty} (e : Effect4.Program.UnionRule.Eliminator rule C)
  {t : Effect4.Program.Ty} {a : α} (typed : Effect4.Program.UnionRule.lift rule t = some a) :
  t.subN (C a) = true

Effect4.Program.UnionRule.Eliminator.lift_least {α : Type} [Effect4.Program.UnionRule.Answer α]
  [Effect4.Program.UnionRule.AnswerOrder α] {rule : Effect4.Program.Ty → Option α}
  {C : α → Effect4.Program.Ty} (e : Effect4.Program.UnionRule.Eliminator rule C)
  {t : Effect4.Program.Ty} {a b : α} (typed : Effect4.Program.UnionRule.lift rule t = some a)
  (upper : t.subN (C b) = true) : Effect4.Program.UnionRule.AnswerOrder.le a b

Effect4.Program.UnionRule.Eliminator.adjoint {α : Type} [Effect4.Program.UnionRule.Answer α]
  [Effect4.Program.UnionRule.AnswerOrder α] {rule : Effect4.Program.Ty → Option α}
  {C : α → Effect4.Program.Ty} (e : Effect4.Program.UnionRule.Eliminator rule C)
  (t : Effect4.Program.Ty) :
  ((Effect4.Program.UnionRule.lift rule t).isSome = true ↔ ∃ b, t.subN (C b) = true) ∧
    ∀ {a : α},
      Effect4.Program.UnionRule.lift rule t = some a →
        ∀ (b : α), Effect4.Program.UnionRule.AnswerOrder.le a b ↔ t.subN (C b) = true

Effect4.Program.UnionRule.lift_union {α : Type} [Effect4.Program.UnionRule.Answer α]
  [Effect4.Program.UnionRule.AnswerOrder α] {rule : Effect4.Program.Ty → Option α}
  (mono : Effect4.Program.UnionRule.Below rule rule) (s t : Effect4.Program.Ty) :
  (∀ {a b : α},
      Effect4.Program.UnionRule.lift rule s = some a →
        Effect4.Program.UnionRule.lift rule t = some b →
          ∃ c,
            Effect4.Program.UnionRule.lift rule (s.union t) = some c ∧
              Effect4.Program.UnionRule.AnswerOrder.le c
                  (Effect4.Program.UnionRule.Answer.join a b) ∧
                Effect4.Program.UnionRule.AnswerOrder.le (Effect4.Program.UnionRule.Answer.join a b)
                  c) ∧
    ∀ {c : α},
      Effect4.Program.UnionRule.lift rule (s.union t) = some c →
        ∃ a b,
          Effect4.Program.UnionRule.lift rule s = some a ∧
            Effect4.Program.UnionRule.lift rule t = some b

Effect4.Program.UnionRule.lift_union_eq {rule : Effect4.Program.Ty → Option Effect4.Program.Ty}
  (mono : Effect4.Program.UnionRule.Below rule rule) (s t : Effect4.Program.Ty) :
  Effect4.Program.UnionRule.lift rule (s.union t) =
    (Effect4.Program.UnionRule.lift rule s).bind fun a =>
      Option.map a.join (Effect4.Program.UnionRule.lift rule t)

Effect4.Program.UnionRule.lift_unique {rule f : Effect4.Program.Ty → Option Effect4.Program.Ty}
  (normal : ∀ (t : Effect4.Program.Ty), f t = f t.normalize)
  (never : f Effect4.Program.Ty.never = some Effect4.Program.Ty.never)
  (member :
    ∀ {m : Effect4.Program.Ty},
      m.Normal → m.isMember = true → f m = Option.map Effect4.Program.Ty.normalize (rule m))
  (union :
    ∀ {m r : Effect4.Program.Ty},
      m.Normal →
        m.isMember = true →
          r.Normal →
            (m.union r).Normal → f (m.union r) = (f m).bind fun a => Option.map a.join (f r))
  (t : Effect4.Program.Ty) : f t = Effect4.Program.UnionRule.lift rule t

Effect4.Program.RecordChecks.has_reads :
  Effect4.Program.UnionRule.ReadsUnion Effect4.Program.RecordChecks.Has✝

Effect4.Program.Typed.fits_reads (w : Effect4.Program.Typed.World) :
  Effect4.Program.UnionRule.ReadsUnion (Effect4.Program.Typed.Fits w)
```
