# 2026-10-06 seat PILOT: the landing note, in place of a receipt

Status: a receipt in the form of a research note (history, not authority). The coordinator
wrote it at the merge. The owner said to wrap the seats up. The seat handed back eight
commits and a note in the session, and the coordinator finished the slice. Brief:
`docs/research/2026-10-05-claude-lead/briefs/seat-pilot-brief.md`. Decisions row 298.

**The one thing to know before merging:** the fiber rule is converted, and no admitted program
moves. `fiberTy` is `UnionRule.extend Member.fiber`. At the merged head the 473 programs of the
two corpora have the verdict and the type of the base, by spelling.

## Base and head

- Branch `seat/pilot`, base `9d50ac20`, head `56c3f2e9`: eight commits.
  1. `40533c59`: the design note and its probes.
  2. `098d58d8`, `e933b927`: `UnionRule.liftOne` and `UnionRule.extend`, with 23 laws, as planned
     goals and then proved in place.
  3. `d02f19c5`, `c76e2a6e`: the conversion, with its member facts.
  4. `7c2e9125`: the battery `Test/Program/Eliminators.lean`.
  5. `fd212944`, `56c3f2e9`: the closed types of a converted rule.
- The merge commit adds three things that the seat did not commit: the repair of
  `closed_fiberTy`, the pin of the case policy, and the records.
- The cut of five theorems is the commit after the merge.

## Changed files

| File | Change |
| --- | --- |
| `src/Effect4/Program/UnionRule.lean` | `liftOne`, the guarded rule; `extend`, the extended rule |
| `src/Effect4/Program/Typing/Rules.lean` | `Member.fiber`, the by-shape function; `fiberTy` in one line |
| `src/Effect4/Laws/Program/UnionRule.lean` | the laws of the guard and of the extended rule; the contract `Eliminator.extend_laws` |
| `src/Effect4/Laws/Program/Eliminators.lean` | new: the member facts of the fiber rule |
| `src/Effect4/Laws/Program/Typed/Membership.lean` | `fiberTy_eq_some` is cut |
| `src/Effect4/Laws/Program/Typed/Denotation.lean` | 11 uses move the value up; `subN_list` is new |
| `src/Effect4/Laws/Program/Typing/Closed.lean` | `closed_fiberTy` is one application (at the merge) |
| `Test/Program/Eliminators.lean`, `Test/Program/UnionRule.lean` | the controls of the converted rule; the instance moved out of the first battery |
| `src/Effect4/Laws.lean`, `Test/All.lean` | one import each, at the brief's anchors |
| `tools/Conform/Effect4/cases-policy.json` | pinned again (at the merge) |

## What the slice decided

1. **A conversion is one line.** The by-shape function stays, as the member rule
   `Member.fiber`. The rule keeps its name, so the judgment and the checker name it as before.
2. **The converted rule is the extended rule, not the guarded rule alone.** The first design
   was `UnionRule.liftOne Member.fiber`. It refused one closed program that the checker
   admits. A forked body answers a list of one pair over `nat | string`. The fiber is joined,
   and `mapFromEntries` reads the joined value. The coordinator ruled the raw answer (decisions row
   296, point 5), and the seat built `UnionRule.extend`.
3. **The contract is stated once**, for every `Eliminator`: `Eliminator.extend_laws`.
4. **The use sites read an inequality.** `fiberTy_upper` puts the handle type below the fiber
   type of the answered columns, in `Ty.subN`. Each use moves the value up by `fits_subN`.

## Commands and results

Each Lean command ran through the Lean slot, on the merged tree, before the merge commit.

- **The default build**: `lake build`, 1052 jobs, exit 0. The gate lines:
  - 182 API and utility modules, and 328 modules of the law graph only;
  - 802 modules and 92977 declarations at `[propext, Quot.sound]`;
  - 28 planned goals, and 12 declarations that rest on goals;
  - proof style: 1911 recorded uses and 52 recorded unread commands, in 1161 entries.
- **The case policy**: `make check-cases` refused twice before the pin. The row of
  `Effect4.Program.fiberTy` was stale, and `Effect4.Program.Member.fiber` was not named. The
  seeded policy moves the row, with the same cover. After the pin the check passes.
- **The differential** (`docs/research/2026-10-06-seat-PILOT-evidence/differential.lean.txt`,
  run by `run-head.sh.txt` beside it). One row for each program: the verdict, and the type or
  the refusal, as spelled and at the normal form.
  - 477 rows: 400 generated programs, 73 of the truth lane, and 4 controls.
  - The 473 corpus rows at the merged head equal the base's rows. 128 generated programs and
    all 73 of the truth lane are admitted.
  - Two controls move from `notFiber` to admitted, as they must. One joins a handle at
    `never`, and one awaits every fiber of the empty list.
  - The closed program of point 2 keeps its type, `map string (nat | string)`.
  - A join of two fiber types with no order stays refused, with `notFiber`.
- **The statement list** (`statements.lean.txt`): 26 statements name `fiberTy` at the base and
  at the head. The 18 of the nine rules and their nine inversions have one text. Eight left:
  `fiberTy_eq_some` and seven of the first battery. Eight entered: `closed_fiberTy`,
  `fiberTy_fiberOf`, `fiberTy_upper`, and five of the new battery.
- **The wide gates** ran on this tree before the merge commit. The commit's message gives them.

## Axiom output

The axiom gate read every declaration of the merged tree at `[propext, Quot.sound]`: the line
above. No declaration of the slice is exempted.

## Landed theorems and their placement

| Statements | Concept; claim | Reach | It does not establish | Consumer |
| --- | --- | --- | --- | --- |
| `liftOne_eq_some_iff` and six more laws of the guard; `Eliminator.liftOne_answers`, `liftOne_isSome_iff`, `liftOne_mono` | `subtyping-algebra`; parts of `union-rule-extend`; R14 | every member rule; the last three at every `Eliminator` | anything at a proper union, where the guard refuses | the laws of the extended rule |
| `extend_eq_some_iff`, `extend_agrees`, `extend_refused`, `extend_never`, `extend_two`, `extend_closed_pair` | the same | every member rule | the order laws | each law of a converted rule |
| `Eliminator.extend_adjoint`, `extend_upper`, `extend_least`, `extend_bot`, `extend_isSome_iff`, `extend_mono`, `extend_liftOne`, `extend_laws` | the same; `extend_laws` is the claim's pointer | every `Eliminator`; the order `Ty.subN` | `checker-monotone`; anything that tsgo accepts; another rule of the checker | each conversion |
| `Ty.subN_fiberOf_iff`, `Member.fiber_eliminator`, `Member.fiber_one`, `Member.fiber_closed`, `fiberTy_fiberOf`, `fiberTy_upper` | the same, at its first instance; `fiberTy_upper` is a step of `denote-typed` (R3) | the fiber rule | the list rule, the exit rule and the other heads | the fiber arms of `Typed/Denotation.lean`; `closed_fiberTy` |
| `subN_list` | `residual-program-typing`; a step of `denote-typed`; R3 | two list types | the converse | the three arms that read a list of handles |

## Open obligations

1. **The other conversions.** `HasTy` states the list rule and the exit rule by shape, so their
   conversions state those rules through the function first. That changes statements.
2. **The two interim parts.** The guard goes when the TypeScript printer writes the type
   arguments at a proper union. The raw answer goes when the match of a template reads a
   request up to its normal form. `Eliminator.extend_liftOne` says what the second removal
   changes.
3. **A word in the docstrings.** Each docstring of the slice says "the proposed claim
   `union-rule-extend`". The claim is in the registry now. The word goes at the next edit of
   those files: an edit now would rebuild the tree for a comment.
4. **The design note** describes the first design. Its last section says what landed.

## Evidence that is bounded

- The differential is a finite check: 473 programs and 4 controls. It is no proof that every
  admitted program keeps its type. `Eliminator.extend_laws` proves that at the fiber rule
  alone: the rule agrees with the by-shape function wherever that function answered.
- The seat ran no TypeScript. The diagnostics lane ran at the merge, with the wide gates.
- No program ran on a host.

## The requirements R1 to R14

R14 gains a groundwork and no part: the first eliminator is converted, and the contract of a
converted eliminator is a registry claim. R3 keeps `denote-typed`: its fiber arms read the
upper form. R1, R2 and R4 to R13 are not touched. No machine, store, session, codec, printer
or reader changed, and no constructor of `Ty`, `Term` or `Eff` is added.
