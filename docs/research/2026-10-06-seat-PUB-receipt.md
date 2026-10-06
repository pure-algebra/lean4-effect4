# 2026-10-06 receipt of seat PUB: the Queue's first public operations

Status: a receipt (history, not authority).
The brief is `docs/research/2026-10-05-claude-lead/briefs/seat-pub-brief.md`.
The design note is `docs/research/2026-10-06-seat-PUB-design.md`.

## 1. First: what the coordinator must know before merging

Only this receipt is not merged. The head and the main line agree on every other file.
The seat merged the coordinator's head `1d10d8aa` before the receipt's commit.
The receipt's commit holds one Markdown file under `docs/research`, and it moves no checked file.

Two things are still owed by the main line, and neither blocks the merge.

1. **Two law modules have no default concept in the semantics registry.**
   They are `Effect4.Laws.Modules.Waiting` and `Effect4.Laws.Modules.Queue.Ops`. Section 9 proposes one for each.
2. **The first open point** is a limit of the recorder, in section 8. It is stated, and it is not repaired.

## 2. Base, head and each step's commit

The base is `b199c15f`. The branch is `seat/pub`, in the worktree `/Users/pooks/Dev/lean4-effect4-mask`.
The head is the commit of this receipt, on top of the coordinator's head `1d10d8aa`.

| Step | Commit | What it holds | Merged as |
| --- | --- | --- | --- |
| 1 | `a22ddd28` | the design note | `f046975b` |
| 2, first part | `ac975fb1` | the shared pieces, the operations, scope, the moved batteries | `f046975b` |
| 3 | `6d83dd31` | the attempt laws | `c957bfab` |
| 4 | `10134eb3` | the acceptance traces and the hygiene controls | `c957bfab` |
| 4 | `08ee3109` | trace 7 names `embedded-budget-sufficient` | `5701a5dc` |
| 5 | `fa1507b5` | the fiber numbers of the truth lane's Lean face | `5701a5dc` |
| 5 | `9f7241dd` | six programs enter the truth lane | `5701a5dc` |
| 5 | `a1d358a0` | the reduction's docstring, and the runner's comment | `5701a5dc` |
| 5 | `0338b004` | the faces of the operations | `41be5ef3` |
| 5 | `f9f24092` | the engine's lane at five runs | `41be5ef3` |
| 2, second part | `be5170f6` | the typing at every scope | `c46e3ca1` |
| 6 | `985b7828` | the documents | `c46e3ca1` |
| 6 | this commit | the receipt | not merged |

The seat merged the coordinator's heads `f046975b`, `c957bfab`, `41be5ef3` and `1d10d8aa` when each came.

## 3. The changed files

New files:

- `src/Effect4/Modules/Waiting.lean` and `src/Effect4/Modules/Queue/Ops.lean`;
- `src/Effect4/Laws/Modules/Waiting.lean` and `src/Effect4/Laws/Modules/Queue/Ops.lean`;
- `Test/Program/QueueOps.lean` and `Test/Program/QueueTraces.lean`;
- `harness/truth/generated/pLateSeen.ts`, and the five modules `pQueueWake.ts`, `pQueueFull.ts`, `pQueueInterrupted.ts`, `pQueueMasked.ts` and `pQueueOrder.ts` beside it;
- `docs/research/2026-10-06-seat-PUB-design.md`, this receipt, and the folder `docs/research/2026-10-06-seat-pub-evidence/`.

Edited files:

- the roots, each at its anchor: `src/Effect4.lean`, `src/Effect4/Laws.lean` and `Test/All.lean`;
- `src/Effect4/Laws/Modules/Queue/Reading.lean`: `reads_sameOffer` is deleted. It had no consumer since seat MOVE's slice.
- the batteries `Test/Program/QueueScenarios.lean`, `QueueMask.lean`, `QueueFaces.lean`, `QueueEngine.lean` and `QueueSteps.lean`;
- the truth lane: `harness/truth/Truth.lean`, `harness/truth/run-truth.ts` (one comment), `harness/truth/corpus.json`, `harness/truth/result.json`, `harness/truth/result.md` and `Test/fixtures/target/selection.json`;
- the engine's lane: `ocaml/engine/test/queue/write.lean`, `test_queue.ml`, `dune` and `queue.txt`;
- the documents: `Test/contracts/queue.contract.md`, `README.md`, `docs/ARCHITECTURE.md` and `tools/Tools/ArchitectureRoles.lean`.

## 4. The commands and their results

The hosts: bun 1.4.2, effect 4.0.0-rc.112, and tsgo 7 as `@typescript/native-preview` 7.0.0-dev.20260629.1.
`harness/truth/result.md` states the first two for each run of the lane.
Every Lean, Lake and make command ran through `scratch/lean-slot.sh` of the coordinator's checkout.
Every make command had the flags `-o build -o ts/eff/node_modules -o harness/truth/node_modules`.

### Run at `985b7828`, the last commit before the receipt

| Command | Result | Evidence |
| --- | --- | --- |
| `lake build` | `Build completed successfully (990 jobs).` | tested |
| `make gen-fixtures` | `PASS generate: requested producers ran in dependency order`; no file moved | reproduced |
| `dune build`, in `ocaml/` | exit 0 | tested |
| `dune test --force engine`, in `ocaml/` | exit 0; 1754 lines `PASS`, no line `FAIL`; `test_queue: 47 checks, 0 failures` | tested |
| `make gen-truth` | `PASS: 52 programs agree on exits, schedules and sync exits; 1 signed divergence(s)`; no file moved | reproduced |
| `make check-truth` | 23 host tests pass; `PASS truth: pinned corpus, bounded differential and signed U-01 divergence checked; the regenerated modules type-check` | reproduced |
| `make check-cases` | `conform cases: PASS, exit 0`; it printed no refusal line | tested |
| `make check-docs` | `PASS check-docs: every path, link, citation and make target in 75 documents resolves` | tested |

The gate lines of that build, from `Test/All.lean` and from `Test/Audit/ProofStyle.lean`:

- the library-root gate: 173 API and utility modules, 302 Laws-only modules, and `Effect4` never reaches Laws;
- the module and axiom gate: 740 modules and 87890 declarations, at `[propext, Quot.sound]`;
- the goal gate: 24 planned goals, and 11 declarations rest on goals;
- the proof-style ratchet: 1914 recorded uses, and it refused no new use.

`dune test` read `E4_LEAN_CORPUS` at this worktree's `.lake/corpus`.
Its cross-face line reads `agree=9 differ=2`, which is known and does not gate.

### Narrow builds of the last two steps

| Command | Result |
| --- | --- |
| `lake build Effect4.Laws.Modules.Queue.Ops` | 504 jobs, success |
| `lake build Test.Program.QueueOps Tools.ArchitectureRoles` | 515 jobs, success |
| `lake build Test.Program.QueueFaces` | 350 jobs, success |
| `lake build Test.Program.QueueEngine` | 170 jobs, success |
| `bun test tools/target/profile.test.ts -t "selected IDs cannot vanish"` | 1 pass |
| `bun run check.ts` on `harness/truth/generated`, in `ts/eff` | 46 modules accepted, the six new ones among them |

### Not run by the seat

`make check-gen`, `make check-slow`, `make check-corpus`, `make check-target`, `make check-truth-release`, the conservativity script and `make gen-semantics`.

### What the coordinator measured at the merges

The coordinator reported these results. The seat did not run them.

At the merges of the commits up to `f9f24092`:

- `make gen-corpus-results`: two cells moved, the cell `leanSchedule` of `g102` and the cell `lean` of `g246`. No outcome column moved.
- `make check-corpus`: 400 programs match, with 25 registered disagreements.
- `make check-truth-release`: 53 programs, and 44 agree with both builds. Each of the six new programs agrees on rc.112 and on 4.0.1.
- `make check-ts-reader`: 726 tests pass. `make check-target`: PASS.

At the merge of the typing and the documents (`c46e3ca1`):

- the default build: 990 jobs, 740 modules, 87890 declarations at `[propext, Quot.sound]`, 24 planned goals;
- `make gen-semantics` wrote `generated/semantics.md` again, with the five typing statements;
- the readme group wrote no byte, and the semantics, cases and documents checks pass;
- the conservativity check passes. The compatibility policy names the moved corpus row `g102` (`6b2b5cda`).

## 5. The axioms and the plan status

Each statement below is at `[propext, Quot.sound]`, and `Test/Program/QueueOps.lean` pins each output.

- The attempt laws: `take_attempt`, `take_withdrawal`, `offer_attempt`, `offer_withdrawal`, `poll_attempt`, `size_read` and `bounded_makes`.
- Their forms at the operation's own binders: `take_attempt_minted`, `take_withdrawal_minted`, `offer_attempt_minted` and `offer_withdrawal_minted`.
- The typing statements: `bounded_types`, `size_types`, `poll_types`, `offer_types` and `take_types`.
- Three scope laws: `take_scoped`, `offer_scoped` and `waitRetry_scoped`.
- Six helpers: `captured_answer_in_row`, `later_mint_ne_answer`, `postAll_answers`, `waitAt_answers`, `answers_refModifyWith` and `kept_var`.

`#plan_status` answers `proved` for each of the sixteen placed statements, with `next goals: 0`.
The same battery pins both outputs. No statement of the slice rests on a planned goal.

## 6. The placement of each landed statement

All are in `src/Effect4/Laws/Modules/Waiting.lean` or `src/Effect4/Laws/Modules/Queue/Ops.lean`.

| Statements | Concept; requirement; claim | Reach | What it does not establish | Consumer |
| --- | --- | --- | --- | --- |
| The scope laws of each shared piece, each step and each operation | `initial-algebras-folds`; R4; a step of `operation-data-scoped` | every scope | typing, a run | `Api.Author.build` of each client |
| The seven attempt laws, and their four forms at the operation's own binders | `translation-simulation`; R10; a part of the proposed claim `queue-expansion-agrees` | one store step, from a cell that encodes a state of `FirstProfile`, with `Requested` and an injective table, at every scope and every `MessageTy` | delivery, an order across steps, a cancellation law, a budget, liveness, a host | the run-level law of the next slice |
| The minted names: `resolve_unshadowed`, `later_mint_ne_answer`, `captured_answer_in_row`, `capturedTy_answer_in_row` | `translation-simulation`; R10; helpers of the attempt laws | every scope | a run | the capture premises of the attempt laws |
| The five typing statements | `store-typing`; R4 | the checker's `effTy` at every typed scope and path, at the native signature of any row table, for every `MessageTy` and every kept term of a caller | a run, a string literal as a caller's term | a client's admission |
| The typing rules: `Kept`, `Answers`, one rule for each builder, the rows of a cell, `postAll_answers`, `onInterrupt_answers`, `waitAt_answers` | `store-typing`; R4; helpers of a module's typing statements | every typed scope; the rows at the native signature | a run | the Queue's typing statements, and Semaphore's next |

Two labels stay apart.
The scope's premises of an attempt law hold at the wrapper's own binders for every caller's scope: proved, in section 4 of `Test/Program/QueueOps.lean`.
The comparison of each statement's term with the operation's own tree is a finite battery.
It reads three lists of a caller's names, at the message type `nat`.

## 7. What the slice holds, part by part

### The operations

`Queue.bounded`, `Queue.offer`, `Queue.take`, `Queue.poll` and `Queue.size` are library programs.
The handle is the `Ref` of the queue's cell, and the slice adds no handle type.
The shared wrapper has two forms over one `Waiter`: `waitRetry` for a take, and `waitAnswer` for an offer.
A capacity of zero is refused where an author writes it: `Queue.bounded` takes a proof of `0 < capacity`.
`Test/Program/QueueOps.lean` pins that refusal's two messages.

### The trees and the bytes

The comparison is tested, against a dump of the base's thirteen fixture programs.
Each written form of the batteries reproduces its base program byte for byte.
The library's program equals the base's in one of thirteen: the mask battery's R7.
The twelve others differ by the mask alone, and each keeps its exit.

- The eight scenarios' fixture wrote a stand-in for the mask: `uninterruptible`, with `interruptible` for its restore.
- The masked caller's fixture restored in `take`, and it kept the stand-in in `offer`.
- The library's `take` and `offer` both use the mask that restores (decisions rows 244 to 246).

The batteries hold both written forms as controls (`Written.restoring`, `Written.standIn`).

### The controls on the Lean machine

Every pinned answer of the eight scenarios and of the masked caller is kept.
The masked caller answers `[1, 9, true, 0, 0]`, and its red control with the stand-in answers `[0, 0, true, 1, 0]`.
Hygiene: for each of the names `id`, `hint`, `r`, `e` and `s`, a caller's variable of that name keeps its reading.
The fixture's written form is the red control of each.

The seven acceptance traces are in `Test/Program/QueueTraces.lean`. Each is one run on one schedule.

| # | Trace | Positive control | The fault's answer |
| --- | --- | --- | --- |
| 1 | a notification before the await | marks `[101, 7]` | an inline delivery marks `[7, 101]` |
| 2 | a cancellation after the selection | `[0, 0, true, 0, true, false]`; masked `[0, 1, false, 1, true, true]` | a withdrawal that posts nothing: `[1, 1, true, 0, true, true]` |
| 3 | a late delivery to an old hint | `[1, false, 0, 7]` | one hint for every round: `[1, true, 0, 7]`, and no exit at fuel 1000 |
| 4 | an offerer cancelled before acceptance | `[1, 0, 1, none, true, some 3, true, 0, true]` | no withdrawal: the message stays |
| 5 | an offerer cancelled after acceptance | `[1, 1, 0, some 2, true, [], true]` | a withdrawal that takes the message back |
| 6 | the signalling fiber exits first | `[false, 7]` | a supervised helper: no exit |
| 7 | the receiver's continuation that grows | least fuel `49 + 3n` at eight lengths | at one unit less: no exit |

A cancellation control records row 222's four observations apart.
They are the commitment, the operation's exit, the entry of the caller's continuation, and the fiber's exit.

Trace 7 claims no bound. At one unit of fuel less the task is cut, and five more flushes do not finish the run.
Decisions row 226 excludes a cut inside an owned operation from the first profile.
So the lost rest is the excluded case, and no new fault of the wrapper.
The open part `embedded-budget-sufficient` of the semantics registry is the coordinator's addition at the merge.

### The faces, the host and the engine

- `Test/Program/QueueFaces.lean` pins the printed text of one use of each operation. Each text reads back.
- Five programs over the operations run on rc.112: `pQueueWake`, `pQueueFull`, `pQueueInterrupted`, `pQueueMasked` and `pQueueOrder`.
  Each printed module type-checks under tsgo 7. Each agrees with the Lean machine on its exit, its compared rows and its sync exit.
- `pLateSeen` is the control of the fiber numbers in an exit. Its exit names an interruptor and a handle that the numbering moves.
- The engine's lane runs five programs on both instances: R1, R4, R2, R5 and the masked caller.

## 8. Findings, limits and open points

1. **A limit of the recorder: a fiber that is awaited before its first sight.**
   The recorder adds its exit observer when it first sees a fiber.
   An awaiter that registered earlier has its observer in front.
   So rc.112's row `exited k` comes after the rows of the awaiter's resumption, and the machine writes it at the exit.
   No renaming of the fibers repairs that. One run reproduced it, with a probe that is no lane program.
   The evidence is `docs/research/2026-10-06-seat-pub-evidence/late-seen-joined.probe.json`.
   No lane program awaits such a fiber: the Queue's posted helpers are never awaited.
   The docstring of `reduce` in `harness/truth/Truth.lean` states the limit. The recorder is not repaired.
2. **The fiber numbers (found and repaired; decisions row 274).**
   `pQueueOrder` agreed with rc.112 on its exit, and its compared rows differed at row 7.
   The machine numbers a fiber when it allocates it, and the recorder when it first sees it.
   The Lean face now writes each compared fiber under the recorder's number (`numbering`).
   The lane no longer checks the machine's allocation order.
3. **The generated corpus under that repair.** Measured in scratch, one run of `--corpus <out> 400 4` before and one after.
   397 of 400 manifest entries are equal. `g102`, `g204` and `g246` move.
   The file `generated-corpus.moved.json` of the evidence folder holds the three.
4. **A string literal as a caller's term** stays outside the typing statements, as in seat QTYPES's receipt.
   A string literal has two types, by the literal flag, so it is no kept term.
   The checker types one such tree: tested, in section 6 of `Test/Program/QueueOps.lean`.
5. **A hint's type.** The three rows of a hint are typed at `unit` and at `bool`, by the kernel's decision of each closed row.
   A hint of another type needs its own three row facts (`HintTy`).
6. **The wrapper's two forms have no typing statement of their own.**
   `waitRetry` and `waitAnswer` take a module's attempt as a function of its two exits.
   Each operation's typing proof follows them, in the module's own file.
7. **A reading, not measured.** The recorder numbers a `Ref` and a `Deferred` by its first place in a wired value.
   The Lean face writes the allocation index. No lane program showed a difference.
8. **`ifElse` under a union error column** (decisions row 266, point 3) was not met: every arm of an operation fails with nothing.

## 9. Choices, and proposals

Choices of the seat:

- The wrapper takes a module's attempt in continuation style, so the wrapper adds no node to an operation's tree.
- The operations take the pin's names: `bounded`, `offer`, `take`, `poll` and `size`.
  The first profile is narrower: a positive capacity, the `suspend` strategy, and one message for each request.
- The typing is proved through the declarative judgment `HasTy` and `effTy_complete`.
  A builder that binds a name hands its continuation the name's reader with its typing.
- The rows are typed at the native signature of any row table, and not at an abstract signature.
- `pLateSeen` entered the lane as a sixth program, with the coordinator's assent.

Proposals for the semantics registry (`tools/Tools/SemanticsRegistry.lean`, which the seat did not edit).
A default is wanted for each module: neither has one, so each untagged statement counts as unplaced.
The counts below are a script's, over the `theorem` lines of each file.

1. **`Effect4.Laws.Modules.Waiting`: the default concept `store-typing`**, beside `Effect4.Laws.Modules.Checking`.
   It holds 74 theorems, and none carries a tag. 58 of them are the typing rules.
   Five are scope laws, which belong to `initial-algebras-folds`.
   Eleven are the minted names' helpers, which belong to `translation-simulation`.
2. **`Effect4.Laws.Modules.Queue.Ops`: the default concept `translation-simulation`**, beside `Effect4.Laws.Modules.Queue.Steps`.
   It holds 43 theorems. Sixteen carry their own tag: eleven `translation-simulation`, and five `store-typing`.
   Fourteen are scope laws, twelve are helpers of the typing statements, and one is a helper of `bounded_makes`.
3. A default labels a statement of another concept under the module's concept.
   A later slice can give each scope law the tag `initial-algebras-folds`, where the semantics registry wants each exact.

One stale sentence in a document that is the coordinator's: `docs/STATE.md` named two runs of the engine's lane, and it is five.

## 10. The requirements R1 to R13

The lists come from `generated/semantics.md` at the head and from `#plan_status`.
A step theorem of one module closes no requirement.

### What the slice advances

- **R4.** Each operation keeps scope, and each is typed at every scope: proved. No open part of R4 closes.
- **R10.** Seven attempt laws are parts of the proposed claim `queue-expansion-agrees`: proved, for one store step.
  The claim itself stays open: no run-level law is stated.
- **R8.** Finite checks only: each operation prints and reads back, and six programs agree with rc.112.
  The comparison's fiber numbers are one renaming by first sight. The open part on one identity bijection (DI-81) stays open.
- **R12.** Trace 7 is a finite control of `embedded-budget-sufficient`. It proves nothing of R12.

### What the slice's theorems still rest on

- No planned goal: `#plan_status` answers `proved` for each, with `next goals: 0`.
- The premises of each attempt law: a cell that encodes a state of `FirstProfile`, `Requested`, an injective table, and the captures.
  No theorem says that a run reaches a step with such a cell.
- The typing statements rest on `MessageTy` and on a kept term for each caller's term.

### The older open parts that the slice leaves untouched

- R1 (4 open parts), R2 (5), R3 (6), R5 (2), R6 (7), R7 (4), R9 (1), R11 (7) and R13 (4): untouched.
- R4: its 5 open parts stay, `semaphore-accounting-preserved` and `atomic-attempt-isolation` among them.
- R8: its 6 open parts stay.
- R10: its 12 open parts stay, with `queue-expansion-agrees`, `posted-wake-profile-agrees` and `semaphore-expansion-agrees`.
- R12: its 8 open parts stay, with `wait-registration-no-gap`, `posted-task-decision-preserves` and `embedded-budget-sufficient`.
