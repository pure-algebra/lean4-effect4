# 2026-10-06 receipt of seat SEMW: Semaphore's public operations, with the protected permit

Status: a receipt (history, not authority).
The brief is `docs/research/2026-10-05-claude-lead/briefs/seat-semw-brief.md`.
The design note is `docs/research/2026-10-06-seat-SEMW-design.md`.
The receipt is written for a reader with no part in this session.
Section 9 lists every obligation that stays open, and section 10 gives each lane's commands.

## 1. First: what the coordinator must know before merging

Only this receipt is not merged.
The head and the main line's `831a76f3` agree on every other file.
The seat merged `831a76f3` before the receipt's commit, as the merge `81fcfa94`.
The receipt's commit holds one Markdown file under `docs/research`, and it moves no checked file.
The main line's later head `d734aa6a` is not in this branch: the coordinator said that no merge is needed.

Four things stand first.

1. **A finding of the truth lane: the runner's exit column compares two different entries.**
   The line is `const host = entry.runSync.sync ? hostSync : hostFork`, in `main` of `harness/truth/run-truth.ts`.
   The Lean side of the column is `leanVerdict(entry.run)`, the exit of the fork run.
   So the column compares the Lean fork exit with the rc.112 sync exit whenever the sync run settles.
   That comparison is right only where a program's two entries give one exit.
   Section 8 gives the facts, the measure, the two candidate rules and the reading of the faces contract.
2. **Two programs are stopped for that reason, and no operation disagrees with the host.**
   `pSemaphoreProtected` and `pSemaphoreBodies` ran the cases P1 and P4 as the batteries write them.
   On each entry the Lean machine and rc.112 give one exit.
   Their records are in `docs/research/2026-10-06-seat-semw-evidence/`.
   Two joined forms run in their place, and the lane is green at 61 programs.
3. **The first open point is what Pool's `use` still needs beyond `protectedBy`.** Section 9 opens with it.
4. **Two proposals wait for the coordinator.**
   Section 11 gives the rows of the semantics registry as they can be entered.
   It gives a decisions row for the runner's rule too.

## 2. Base, head and each step's commit

The base is `59241284`. The branch is `seat/semw`, in the worktree `/Users/pooks/Dev/lean4-effect4-qtypes`.
The head is the commit of this receipt, on top of the merge `81fcfa94`.

| Step | Commit | What it holds | Merged as |
| --- | --- | --- | --- |
| the design note | `7cef7b9b` | the design note | `aa70b078` |
| 1 | `73f9d6e5` | the wrapper's two forms, with the Queue unmoved | `aa70b078` |
| 2 | `1a81b2e3` | the six operations, and the scenarios over them | `4b57609c` |
| 3 and 4 | `6900d1b0` | scope, the typing at every scope, and the attempt laws | `ea036307` |
| 5 | `bb9863da` | the acceptance traces, and the protected permit's red controls | `ea036307` |
| 6 | `e2a62887` | the faces, eight truth programs, and the evidence of the finding | `5fc17c3f` |
| 7 | `542e2736` | the case P9 on the engine, with its tape as data | `75ad13b7` |
| 8 | `ac6f1a29` | the documents | `831a76f3` |
| 9 | this commit | the receipt | not merged |

The seat took the coordinator's heads `aa70b078`, `4b57609c`, `0c4f9774`, `c986b839` and `831a76f3` when each came.

## 3. The changed files

New files:

- `src/Effect4/Modules/Semaphore/Ops.lean` and `src/Effect4/Laws/Modules/Semaphore/Ops.lean`;
- the batteries `SemaphoreWrapper.lean`, `SemaphoreOps.lean`, `SemaphoreTraces.lean` and `SemaphoreFaces.lean`, under `Test/Program/`;
- eight modules under `harness/truth/generated/`, one for each program of section 7;
- `docs/research/2026-10-06-seat-SEMW-design.md`, this receipt, and the folder `docs/research/2026-10-06-seat-semw-evidence/`.

Edited files:

- the roots, each at its anchor: `src/Effect4.lean`, `src/Effect4/Laws.lean` and `Test/All.lean`;
- the shared wrapper and its laws: `src/Effect4/Modules/Waiting.lean` and `src/Effect4/Laws/Modules/Waiting.lean`;
- the batteries `Test/Program/SemaphoreScenarios.lean` and `Test/Program/SemaphoreEngine.lean`;
- the truth lane: `harness/truth/Truth.lean`, `harness/truth/corpus.json`, `harness/truth/result.json`, `harness/truth/result.md` and `Test/fixtures/target/selection.json`;
- the engine's lane: `ocaml/engine/test/semaphore/write.lean`, `test_semaphore.ml`, `dune` and `semaphore.txt`;
- the documents: `Test/contracts/semaphore.contract.md`, `README.md`, `docs/ARCHITECTURE.md` and `tools/Tools/ArchitectureRoles.lean`.

Not edited:

- any file of the Queue's or of Pool's folders, batteries, lanes or contracts. The diff from the base to the head is empty on them.
- the shared rule files `Words.lean`, `Reading.lean`, `Checking.lean` and `Store.lean`;
- `harness/truth/run-truth.ts`, the Makefile, and the coordinator's registers.

## 4. The commands and their results

The hosts: bun 1.4.2, effect 4.0.0-rc.112, and tsgo 7 as `@typescript/native-preview` 7.0.0-dev.20260629.1.
`harness/truth/result.md` states the first two for each run of the lane.
Every Lean, Lake and make command ran through `scratch/lean-slot.sh` of the coordinator's checkout.
Every make command had the flags `-o build -o ts/eff/node_modules -o harness/truth/node_modules`.

### The acceptance run at the head `81fcfa94`

| Command | Result | Evidence |
| --- | --- | --- |
| `lake build` | `Build completed successfully (1016 jobs).` Every module was up to date | tested |
| `lake env lean -M6144 Test/All.lean` | the three gate lines below | tested |
| `make gen-fixtures` | up to date: make ran nothing, and no file moved | tested |
| `make corpus` | `lake build Drivers.Corpus`, 157 jobs; the corpus was up to date | tested |
| `dune build`, in `ocaml/` | exit 0 | tested |
| `dune test --force engine`, in `ocaml/` | exit 0; 1785 lines `PASS`, no line `FAIL`; `test_semaphore: 31 checks, 0 failures` | tested |
| `make gen-truth` | `PASS: 60 programs agree on exits, schedules and sync exits; 1 signed divergence(s)`; no file moved | reproduced |
| `make check-truth` | 23 host tests pass; `PASS truth: pinned corpus, bounded differential and signed U-01 divergence checked; the regenerated modules type-check` | reproduced |
| `make check-cases` | `conform cases: PASS, exit 0` | tested |
| `make check-docs` | `PASS check-docs: every path, link, citation and make target in 76 documents resolves` | tested |
| `git status --short`, after all of them | no line | tested |

The gate lines of `Test/All.lean` at the head:

- the library-root gate: 176 API and utility modules, 312 Laws-only modules, and `Effect4` never reaches Laws;
- the module and axiom gate: 766 modules and 89578 declarations, at `[propext, Quot.sound]`;
- the goal gate: 24 planned goals, and 11 declarations rest on goals.

The proof-style ratchet reads 1911 recorded uses, and it refused no new use.

Two targets were up to date, so the head's run of each is make's verdict on its inputs.

- `make gen-fixtures` ran last on the tree of `542e2736`. It ran the writers of five lanes, and `semaphore.txt` alone moved, by one run.
- `make corpus` ran last on the same tree: `kept 408 (readable 385) refused 0`.
- No Lean file under `src` or `Test` changed after that tree. `git diff --stat 542e2736 HEAD -- '*.lean'` names two files under `tools/` only.

`dune test` read the Lean corpus at this worktree's `.lake/corpus`: 408 files, 408 decoded.
Its cross-face line reads `agree=9 differ=2`, which is known and does not gate.

**The Queue did not move.** After `make gen-fixtures` and `make gen-truth`, `git status` names no file.
The 53 corpus entries and the 53 result rows of the base are equal at the head, value for value.
`waitRetry_unmoved` and `queue_take_unmoved` state the two trees' equality, each by `rfl`.

### Narrow builds and probes

| Command | Result |
| --- | --- |
| `lake build` of the two law modules, the six Semaphore batteries and `Tools.ArchitectureRoles`, in one call | 529 jobs, success |
| `bun test tools/target/profile.test.ts -t "selected IDs cannot vanish"` | 1 pass |
| the evidence folder's command, on `red-manifest.json` | `FAIL: 2 of 2 programs disagree with rc.112 (pSemaphoreProtected, pSemaphoreBodies)`, status 1 |
| the README's example as written, with one guard, by `lake env lean` in scratch | exit 0: the pair type, and the answer `[1, 7]` |
| `python3 scripts/check-language.py --strict`, on the contract, the evidence note and this receipt | no finding in each |

Section 10 writes each command out in full.

### Not run by the seat

`make check-gen`, `make check-slow`, `make check-corpus`, `make check-target`, the release ledger, the conservativity script and `make gen-semantics`.

### What the coordinator measured at the merges

The coordinator reported these results. The seat did not run them.

- At `aa70b078`: the default build has 1011 jobs. `make gen-fixtures` and `make gen-truth` wrote no byte. `make check-truth` passes at 52 programs.
- At `4b57609c`: the default build has 1012 jobs. `dune test --force engine` has 1773 passing lines, and `test_semaphore` has 19 checks.
- At `ea036307`: the default build has 1015 jobs. The fixtures, the corpus and the truth lane wrote no byte. The conservativity check passes, 4 of 4.
- At `5fc17c3f`: the truth lane has 61 programs, and 60 agree with 1 signed divergence. The corpus lane's 400 programs match, and no row moved. `make check-target` and `make check-ts-reader` pass.
- At `5fc17c3f`, the release ledger: 61 programs. 52 agree with both builds, 8 with rc.112 only and 1 with 4.0.1 only.
- At `75ad13b7`: the default build has 1016 jobs, 766 modules and 89578 declarations. `dune test --force engine` has 1785 passing lines.
- At `831a76f3`: the role register builds, and `make check-docs` passes.

## 5. The axioms and the plan status

Each statement below is at `[propext, Quot.sound]` or less.
`Test/Program/SemaphoreOps.lean` and `Test/Program/SemaphoreWrapper.lean` pin each output.

- The attempt statements: `take_attempt`, `take_withdrawal`, `release_attempt`, `takeIfAvailable_attempt` and `visit_attempt`. `make_makes` is at `[propext]`.
- Their forms at the operations' own binders: `take_attempt_minted`, `take_withdrawal_minted` and `visit_attempt_minted`.
- The typing statements: `make_types`, `takeIfAvailable_types`, `release_types`, `take_types`, `withPermits_types` and `withPermitsIfAvailable_types`.
- The wrapper's laws: `waitRetryAt_scoped`, `protectedBy_scoped`, `waitRetryAt_answers`, `waitRetry_answers` and `protectedBy_has`.
- Three scope laws of the operations: `take_scoped`, `release_scoped` and `withPermits_scoped`.
- Nine helpers: `walk_answers`, `taker_typed`, `captured_cursorOr`, `kept_cursor`, `kept_payload`, `answers_iterateWith_kept`, `join_absorb`, `captured_cursor_in_row` and `captured_current`.
- The two statements of the Queue's trees, `waitRetry_unmoved` and `queue_take_unmoved`, are at `[propext]`.

`#plan_status` answers `proved` for each of the fifteen placed statements, with `next goals: 0`.
The same battery pins that output. No statement of the slice rests on a planned goal.
The axiom gate holds every other declaration of the slice to `[propext, Quot.sound]`.

## 6. The placement of each landed statement

All are in `src/Effect4/Laws/Modules/Waiting.lean` or `src/Effect4/Laws/Modules/Semaphore/Ops.lean`.

| Statements | Concept; requirement; claim | Reach | What it does not establish | Consumer |
| --- | --- | --- | --- | --- |
| The scope laws: `waitRetryAt_scoped`, `protectedBy_scoped`, and one for each step term and each operation | `initial-algebras-folds`; R4; a step of `operation-data-scoped` | every scope; every scoped term of a caller and every scoped body | typing, a run | `Api.Author.build` of each client |
| The six typing statements of the operations | `store-typing`; R4; the cell's half of the proposed claim `semaphore-accounting-preserved` | the checker's `effTy` at every typed scope and path, at the native signature of any row table, for every kept term of a caller; a protected body of any effect type | a run; a string literal as a caller's term | a client's admission |
| The shared typing: `Has` with its rules, `Waiter.Typed`, `waitRetryAt_answers`, `waitRetry_answers`, `protectedBy_has`, and three rules that hand a kept cursor, a kept payload and a captured current value | `store-typing`; R4; helpers of a module's typing statements | every typed scope; a result type in normal form; an acquisition and a release with no failure and no requirement | a run; a law of the mask | Semaphore's typing statements now; Pool's `use` next |
| The nine attempt statements | `translation-simulation`; R10; parts of the proposed claim `semaphore-expansion-agrees` | one store step, from a cell that encodes any model state, with the cell's membership, at every scope; an injective table where the step tests an identity | delivery, an order across steps or visits, a cancellation law, a law of the protected permit, a budget, liveness, a host | the law of a run, in a later slice |
| The minted names in a row: `resolve_minted_in_row`, `captured_minted_in_row`, `capturedTy_minted_in_row`, `captured_cursor_in_row`, `capturedTy_cursor_in_row`, `captured_current`, `capturedTy_current`, `captured_cursorOr` and `capturedTy_cursorOr` | `translation-simulation`; R10; helpers of the attempt statements | every scope | a run | the capture premises of the attempt statements |

**Two departures from the brief's table, both accepted by the coordinator.**
The attempt statements hold on every model state, and not only on a state of the first profile.
`profile_closed` is the separate fact, and a law of a run uses both.
`make_makes` holds at every total: the positive total is a premise of the construction alone.

**No attempt statement says that a run reaches its step with such a cell.**
The cell's membership and the table's injectivity are premises.
The premise of decisions row 261 is no premise here: the release step is total, as the model's is.

Two labels stay apart.
The scope's premises of an attempt statement hold at the operations' own binders for every caller's scope: proved, in section 4 of `Test/Program/SemaphoreOps.lean`.
The comparison of each statement's term with the operation's own tree is a finite battery, at three caller scopes.

## 7. What the slice holds, part by part

### The two forms of the wrapper

`waitRetryAt restore result ended w` is the loop of `waitRetry` at a restore site that the caller supplies.
`waitRetry` is its use under its own mask, so its tree is the earlier tree.
`protectedBy acquire release body` is one mask over three things.
They are the acquisition at the mask's restore, the hook's installation, and the body at the restore site.
The hook is the release, and it runs at every exit of the body.

The shared typing follows decisions row 275, point 3.
`Waiter.Typed` states a module's part: the attempt answers the join of what its two exits answer.
`waitRetryAt_answers` and `waitRetry_answers` type the wrapper once, over any such part.
`Has` is `Answers` at any effect type, so a protected body may fail and may require a service.
`protectedBy_has` keeps the body's answer, its failure type in normal form and its requirement.

### The operations

`Semaphore.make`, `take`, `release`, `takeIfAvailable`, `withPermits` and `withPermitsIfAvailable` are library programs.
The handle is the `Ref` of the semaphore's cell, and it stands first.
`take` answers the count, and `release` answers the free count.
The pin's `take` and `release` answer the same two values: read in `vendor/effect-4.0.0-rc.112/src/Semaphore.ts`, and not probed.
A total of zero is refused where an author writes it: `make` takes a proof of `0 < permits`.
A release posts one helper when a waiter is enrolled, and the helper's body is `walk`.
Each step is one `Ref.modify` of its own, and no step term stands inside a step term.
The contract's section "The operations over the steps" gives each operation's program and answer.

### The trees and the bytes

The scenarios moved from the earlier slice's written forms to the library's operations.
Every pinned answer and every pinned order of exits is kept.
The library's trees differ from the written forms in five places.

- The mask that restores stands where the fixture wrote `uninterruptible` and `interruptible`.
- `take` is the shared wrapper: its cursor is an option of the result, and it answers the count.
- `release` runs under `uninterruptible`, and the walk's cursor states no type.
- The protected form is one `protectedBy`, whose hook is the release itself.
- A withdrawal is its row alone.

So the engine fixture's two programs took other bytes at step 2, and no exit moved.
P1 went from 38407 to 39643 bytes, and P3 from 44754 to 46495 bytes.
The battery keeps the written forms as controls (`Written`, in `Test/Program/SemaphoreScenarios.lean`).

### The controls on the Lean machine

`Test/Program/SemaphoreScenarios.lean` holds eleven scenarios, one schedule each.

| Scenario | Its answer on the machine |
| --- | --- |
| P1 | `[[2,2,[2,1],[0,1]], [2,1,[1],[1]], [22]]`: B takes inside the walk, and C is not visited |
| P2 | `[[2,2,[2,1],[0,1]], 1, [2,1,[2],[0]], [31]]`: the walk passes B and resumes C |
| P3 | `[[2,2,[1,1],[0,1]], [2,1,[1],[1]], [21,22]]`: B takes twice inside the walk |
| P4 | `[[2,2,[2,1],[0,1]], [0,0,[],[]], [22,31]]`: both protected bodies run inside one walk |
| P7 | each interrupted waiter's entry leaves, and `taken` stays 1 |
| P9, which is P1 under a second tape | `[[2,2,[2,1],[0,1]], [1,1,[2],[2]], [31]]`: C takes, and B waits again |
| T1 | `[true, false, [2,0,[],[]]]` |
| the forms that never wait | `[some 7, [0,0,[],[]], none, true, false, [2,0,[],[]], [2]]` |
| the README's example | `[1, 7]` |
| the masked caller | `[[1,1,[1],[0]], 11, true, [0,0,[],[]]]` |
| the joined P1 and the joined P4 | the answers of P1 and of P4 |

A count is `[taken, the number of waiters, their counts, their stamps]`.

Three changed policies stay red, each on its own case.
A walk that wakes the head alone fails P2. A walk that grants fails P3. A retry with no second check fails P9.
Each changed policy builds, so typing does not catch it.

`Test/Program/SemaphoreOps.lean` holds the controls of the operations that the scenarios do not run.

- **The forms that never wait.** Where the step does not take, the body does not run and nothing is released. Each of the two faults is a red control.
- **Hygiene.** The fixtures wrote `id`, `hint`, `took`, `r`, `e` and `s` around a caller's variable. A caller's variable of each name keeps its reading in the library's operation. The fixture's written form is the red control of each.
- **Typing.** The checker's own answer on each operation's tree agrees with each typing statement, at three scopes. A count of another type and a handle of another type are refused.

`Test/Program/SemaphoreTraces.lean` holds eight traces. Each is one run on one schedule.

| # | Trace | Positive control | The fault's answer |
| --- | --- | --- | --- |
| 1 | a notification before the await | at the five budgets from 21 to 25, on two tapes, the taker takes after the visit | the two tapes are two schedules |
| 2 | a cancellation between the release and the walk | interruptible: `[1, [0,1,[1],[1]], [1,0,[],[]], true, 0, true, false]`; masked: `[1, [1,1,[1],[1]], [1,1,[1],[1]], false, 1, true, true]` | no withdrawal: two entries stand where one request waits |
| 3 | a late delivery to an old hint | `[1, false, 1, 1]` | one hint for every round: `[1, true, 157, 1]`, and no exit at fuel 1000 |
| 4 | a holder interrupted inside the take's mask | one region: nothing stays taken | two regions: one permit stays taken by a fiber that has exited |
| 5 | a waiter interrupted under a mask of the form's making | the protected form: the entry leaves, and no mark is written | the nested mask: the waiter stays, takes after its interruption, and writes the mark 9 |
| 6 | the signalling fiber exits first | `[false, 1]` | a supervised helper: no exit |
| 7 | the receiver's continuation that grows | least fuel `49 + 3n` at eight lengths | at one unit less: no exit |
| 8 | the protected permit under a masked caller | `[[1,1,[1],[0]], 11, true, [0,0,[],[]]]` | the stand-in for the mask: `[[1,0,[],[]], 0, true, [0,0,[],[]]]` |

Traces 4 and 5 are the two red controls of `protectedBy`.
Trace 4 has a second form with no written yield.
The library's `take` and then the hook lose the permit at the fifteen operation budgets from 13 to 27.
The measure covers the budgets from 8 to 35, and the library's `withPermits` loses it at none.
Trace 2 records the four observations of decisions row 222 apart.
Trace 7 claims no bound.

### The faces, the host and the engine

- `Test/Program/SemaphoreFaces.lean`: each of the eleven scenarios prints as a module and reads back. One use of each operation prints and reads back, and its text is pinned. Each of the five step terms prints and reads back alone.
- Eight programs run on rc.112: `pSemaphoreProtectedJoined`, `pSemaphoreScan`, `pSemaphoreOvertake`, `pSemaphoreBodiesJoined`, `pSemaphoreInterrupted`, `pSemaphoreIfAvailable`, `pSemaphoreMasked` and `pSemaphoreHandoff`.
- Each printed module type-checks under tsgo 7. Each agrees with the Lean machine on its exit, its compared rows and its sync exit.
- Each program is a scenario of the battery, so rc.112 runs the program that the battery runs.
- P9 has no host run: its yield is a decision of a tape.
- The engine's lane runs P1, P3 and P9 on both instances. P9's tape is one line of the fixture: `tape evaluate:0 yieldVerdict:2:true flush`.
- The engine's new property S5 has two red controls. Under the drive loop, and under the verdict `false`, P9's program gives P1's exit.

### The rows that the slice moved

- **Corpus rows** (`harness/truth/corpus.json`): eight entries after `pQueueOrder`, in the order of the list above. The corpus goes from 53 to 61 programs, and no earlier entry moves.
- **Result rows** (`harness/truth/result.json`, `harness/truth/result.md`): the same eight rows. The last line goes from 52 to 60 agreeing programs.
- **Target rows** (`Test/fixtures/target/selection.json`): the same eight names, in the same order, at the end of `programs`.
- **Generated modules**: eight new files under `harness/truth/generated/`, so 61 modules stand for 61 programs.
- **The engine's fixture** (`ocaml/engine/test/semaphore/semaphore.txt`): step 2 moved the two `program` lines, and step 7 added the run `p9`. No other lane's fixture moved.
- **The release ledger** (`harness/truth/build-ledger.tsv`) holds one line for each corpus program. The coordinator added the eight lines at the merge `5fc17c3f`.

## 8. The finding of the truth lane

### The facts

`make gen-truth` ended red when the corpus held P1 and P4 as the batteries write them.
Its last line was `FAIL: 2 of 61 programs disagree with rc.112 (pSemaphoreProtected, pSemaphoreBodies)`.
On each of the two rows the schedules agree and the sync exits agree. Only the exit column says `NO`.

| Program | Entry | The Lean machine | rc.112 |
| --- | --- | --- | --- |
| `pSemaphoreProtected` | fork | `[[2,2,[2,1],[0,1]],[2,1,[1],[1]],[22]]` | the same |
| `pSemaphoreProtected` | sync | `[[2,2,[2,1],[0,1]],[0,2,[2,1],[0,1]],[]]` | the same |
| `pSemaphoreBodies` | fork | `[[2,2,[2,1],[0,1]],[0,0,[],[]],[22,31]]` | the same |
| `pSemaphoreBodies` | sync | `[[2,2,[2,1],[0,1]],[0,2,[2,1],[0,1]],[]]` | the same |

So no operation disagrees with the host. On each entry the two faces give one exit.

### The cause

In P1 and P4 a child's hook releases: A's protected body ends.
A release posts its helper on the dispatcher of the fiber that releases.
The sync entry flushes the root's dispatcher only: `fiber._dispatcher?.flush()` in `runSyncExitWith`.
The Lean machine transcribes that as `runSyncExit`, in `src/Effect4/Machine/Fibers.lean`.
So under the sync entry the root's four yields end before the walk.
The root then reads the cell between the release and the walk.

The runner's exit column takes the rc.112 sync exit whenever the Lean sync run settles.
It compares that exit with the Lean fork exit. The two differ for these programs, on both faces.

One reading is from the vendored source, and no probe ran for it.
The pin's own `Semaphore.ts` schedules its scan with `fiber.currentDispatcher.scheduleTask`.
So the pin's own semaphore has the same shape under the sync entry.

### The measure

The measure reads `harness/truth/result.json`, at the red run and at the head.

- At the red run of 61 programs: of the 53 earlier programs, 48 take the sync entry and 5 the fork entry.
- On each of the 48, the two entries of rc.112 give one exit, and so do the two entries of the Lean machine.
- No earlier row holds the runner's note `runSyncExit and runFork exits differ`.
- At the head: 54 rows take the sync entry and 7 the fork entry. On each of the 54 the two entries give one exit.

So P1 and P4 are the lane's first programs whose two entries settle on two exits.

### The two candidate rules

| Rule | What the exit column compares | What moves at the head |
| --- | --- | --- |
| the seat's first proposal | the Lean fork exit with the rc.112 fork exit, only where both entries settle on two exits; as today elsewhere | no present row |
| the alternative, which the seat now recommends | the Lean fork exit with the rc.112 fork exit, always | the cell `entry` of 54 rows, and no verdict |

The sync pair has its own column under both rules.
Under both rules P1 and P4 are green on the three columns: the red records show each pair equal.
The seat recommends the alternative, for three reasons.

1. Each column then compares one entry on both faces.
2. It closes a gap of the present rule. Where the sync run settles, a disagreement of the fork entry is a note only: `runFork entry disagrees too`. That is read in the code. No program shows it.
3. The measure above says that no present verdict moves. The seat computed it by JSON equality of the two fork exits, on the 61 rows.

The choice changes what a gate checks, so it is the coordinator's or the owner's.
The seat did not edit `harness/truth/run-truth.ts`.

### What the faces contract says

`Test/contracts/faces.contract.md` states no comparison across the two entries.
Its section 4, quantifier 5, says that exits are compared exactly. It names no entry there.
Its amendment of 2026-10-06 lists the compared fields that hold a fiber.
Two of them are exits: "The exits of the fork run and of the sync run".
Its evidence line counts three things: exits, schedules and sync exits.
So the present text supports the alternative: fork with fork, and the sync pair in its own column.
The runner's own comment says that the verdict's entry is "the one the Lean verdict names".
The Lean verdict is the fork run's.

### What is filed, and how the two programs come back

The folder `docs/research/2026-10-06-seat-semw-evidence/` holds, for both programs:

- the four exits, in `README.md`;
- the two result rows with both host observations, in `red-result.json` and `red-result.md`;
- the two generated modules that rc.112 ran;
- `red-manifest.json`, the two manifest entries as Lean wrote them;
- the one command that reproduces the red run, and the five steps that add the two programs again.

The seat ran that command once: the two rows equal the first run's, field for field.
The scenarios P1 and P4 stay in the batteries and in the engine's fixture.
A guard of `Test/Program/SemaphoreScenarios.lean` holds the two sync exits on the Lean machine.

### Smaller findings

1. **A missing withdrawal loses no wake under the live scan.** In trace 2's fault the interrupted request's entry stays. The walk spends one visit on it, and the next waiter still takes. So the fault shows as two entries for one request, and as no lost permit. Tested, on one schedule.
2. **P9's tape on the joined P1 gives a frontier.** B yields at its resume and waits again, so the root's join does not return. The run has no exit, and the root and B are parked. So P9 keeps the form that yields.
3. **An up-to-date build prints no gate line.** `lake build` replays no elaboration of `Test/All.lean` then. `lake env lean -M6144 Test/All.lean` prints the three lines.
4. **A hook of this session refuses a commit command that holds one word of the mask's vocabulary.** The seat wrote each commit message to a file and passed it with `-F`. It set no bypass.

## 9. Open points

### What Pool's `use` still needs beyond `protectedBy`

Pool's `use pool body` is `protectedBy` with the lease's loop and the return (decisions row 276, point 1).
The form, its scope law and its typing rule exist. Eight things are still owed.

1. **Pool's part of the wrapper: a `Waiter` over the lease step.** The lease step has three answers: an item, an enrolment, and `closed`. The wrapper's attempt has two exits. So the refusal is a value of the loop's result, and `use` branches on it. `withPermitsIfAvailable` shows that route: its hook and its body branch on the acquired Boolean.
2. **What `use` answers at a closed pool.** Seat POOL's receipt leaves it to the public slice. The pin interrupts there: read in `vendor/effect-4.0.0-rc.112/src/Pool.ts`, and not probed by this seat. This is a choice of meaning, so it is the owner's.
3. **`Waiter.Typed` for that part**, from the lease step's typing statement, as `taker_typed` is from the take step's. Then `waitRetryAt_answers` types the loop.
4. **The return in the hook**: the return step, and then the wake's helper where the reply says that a wake is owed. `Semaphore.release` shows the shape. Pool's helper is one selection step and then each selected hint in order. Its test forms are `wakeWith` and `resolveAll` of `Test/Program/PoolScenarios.lean`.
5. **An acquisition or a release that fails.** `protectedBy_has` takes both with no failure and no requirement. A lease loop that fails, or a return that requires a service, needs the rule at `Has`. That rule is not written.
6. **The public `make`**, with the acquisition inside the pool's scope, and the finalizers at the close. A failed acquisition fails `make`, so `make` is typed with `Has`, which exists now.
7. **The closer's request step** (decisions row 276, point 2): one new step term, its typing statement and its agreement, and its own `Waiter`.
8. **The law of a run.** The coordinator reports one fact of the main line since `d734aa6a`, which this branch does not hold. The mask's chain is proved at every live fiber of a run, and at every entry that returns a machine. The claim is `saved-mask-chain-runs` of the semantics registry. The bracket of a region stays open. So the protected form's law of a whole run still waits for it, for Pool and for Semaphore.

The shared helpers for a minted name inside a row exist now, in `src/Effect4/Laws/Modules/Waiting.lean`.
They serve the capture premises of Pool's attempt statements: `captured_minted_in_row`, `capturedTy_minted_in_row`, `captured_current` and `capturedTy_current`.

### Every other obligation that stays open

Semaphore's laws of a run. None is stated.

1. **`semaphore-expansion-agrees`** (R10). Three laws are owed.
   - The wrapper's run: its enrolment, its wait, its retry and its withdrawal.
   - The walk across visits, with the reach of one visit up to the resumed caller's cut.
   - The protected form's run.
2. **`semaphore-accounting-preserved`** (R4): along a run the cell stays a member of its type, and its state stays in the profile. Three parts are owed.
   - The cell's first membership, from the handles that the table names.
   - That a run reaches each step with a cell that encodes a model state.
   - The composition with `profile_closed`.
3. **The table along a run.** Each attempt statement takes an injective table. No statement says that a fresh hint is no handle inside the cell.
4. **`semaphore-protected-permit`** (R11): three clauses, in the card's section 8. The semantics registry does not hold it. Traces 4, 5 and 8 are its finite controls. Its third clause has no control: a cleanup reported as finished at a frontier.
5. **The embedded budget** (decisions row 226; `embedded-budget-sufficient`). Trace 7 measures, and it claims no bound.
6. **The waiting claims of the semantics registry**: `wait-registration-no-gap`, `waiting-request-obligation-preserved`, `posted-task-decision-preserves` and `posted-wake-profile-agrees`. Traces 1, 2, 3 and 6 are finite controls, one schedule each.

Premises that a caller keeps. No check refuses a breach.

7. **A request above the total** enrols, and no visit selects it. The profile's law takes "at most the total" as a premise.
8. **A release of more than is taken** releases what is taken (decisions row 261). The public law takes "at most `taken`" as a premise.

Limits of the typing statements.

9. A string literal is no kept term, so the statements say nothing of one. A count is a number.
10. `withPermitsIfAvailable_types` takes the body's answer type in normal form.
11. `waitAnswer` has no shared typing rule. The Queue's `offer_types` still follows the wrapper's tree.

The lanes.

12. **The runner's rule** (section 8), and then P1 and P4 as lane programs.
13. **P9 has no host run.** Its yield is a decision of a tape, and the runner has no such control.
14. **The engine's lane** is three runs. It states no law of the engine's replay.
15. **Each trace and each scenario is one schedule.** P9's tape is pinned on P1 alone. On the joined P1 that tape gives a frontier: B waits again, so the join does not return.

The semantics registry.

16. The rows and sentences of section 11 are not entered.
17. The fifteen scope laws of `Effect4.Laws.Modules.Semaphore.Ops` stand under the module's default concept. A later slice can tag each with `initial-algebras-folds`.

## 10. How to run each lane again

Run each command at the repository's root, on a clean tree, unless its row names a folder.
`AGENTS.md` bounds Lean's threads: write `LEAN_NUM_THREADS=3` before a `lake` command.
The seat's worktree links the coordinator's install of the TypeScript packages.
So each `make` of the seat had three more flags: `-o build -o ts/eff/node_modules -o harness/truth/node_modules`.
A checkout with its own install needs none of them.
The OCaml commands need the opam switch `effect4`, and `make corpus` first.

| Lane | Command | What a green run shows |
| --- | --- | --- |
| the laws | `LEAN_NUM_THREADS=3 lake build Effect4.Laws.Modules.Waiting Effect4.Laws.Modules.Semaphore.Ops` | each law elaborates |
| the batteries | `LEAN_NUM_THREADS=3 lake build Test.Program.SemaphoreWrapper Test.Program.SemaphoreScenarios Test.Program.SemaphoreOps Test.Program.SemaphoreTraces Test.Program.SemaphoreFaces Test.Program.SemaphoreEngine` | every guard, each pinned axiom list and each plan status |
| the gates | `make build`, and `lake env lean -M6144 Test/All.lean` for the gate lines alone | the three gates of `Test/All.lean`, and the proof-style ratchet |
| the engine's fixture | `make gen-fixtures`, then `git status --short` | Lean writes the committed fixture again, byte for byte |
| the engine | `make corpus`, then in `ocaml/`: `opam exec --switch=effect4 -- dune build` and `opam exec --switch=effect4 -- dune test --force engine` | `test_semaphore: 31 checks, 0 failures` |
| the truth lane | `make gen-truth`, then `git status --short`, then `make check-truth` | 60 programs agree, with 1 signed divergence; the modules type-check under tsgo 7 |
| the target's selection | `bun test tools/target/profile.test.ts -t "selected IDs cannot vanish"` | the selected names are the corpus's names, in order |
| the red run of section 8 | the command of `docs/research/2026-10-06-seat-semw-evidence/README.md` | status 1, and `FAIL: 2 of 2 programs disagree` |
| the case policy | `make check-cases` | `conform cases: PASS` |
| the documents | `make check-docs`, and `python3 scripts/check-language.py --strict <file>` | every cited path resolves; no language finding |

The writer of the engine's fixture runs alone too: `lake env lean --run ocaml/engine/test/semaphore/write.lean`.
A red control is inside its battery. To see one fail, change its expected value and build the battery.

## 11. Choices, and proposals

Choices of the seat:

- The handle stands first in each operation, as in the Queue's.
- `withPermitsIfAvailable` is `protectedBy` too. Its acquisition answers a Boolean, and its hook releases only where the step took.
- The shared typing is one structure for a module's part (`Waiter.Typed`), and one judgment for a body that may fail (`Has`).
- Three shared rules gained a more general form, and each earlier statement stays as it was: `answers_iterateWith_kept`, `answers_selectOptionWith_kept` and `answers_refModifyWith_captured`.
- The two stopped programs keep their names in the evidence folder. The joined forms have names of their own.
- The engine's fixture holds a tape as words, and the writer refuses a decision with no word.

### Proposals for the semantics registry

The seat did not edit `tools/Tools/SemanticsRegistry.lean`.
The semantics registry already places `Effect4.Laws.Modules.Semaphore.Ops` under `translation-simulation` by default.

Two claims, each with a theorem that states it:

| id | concept | role | title | pointer |
| --- | --- | --- | --- | --- |
| `waiting-wrapper-typed` | `store-typing` | `compatibility` | The waiting wrapper at a caller's restore answers its result type at every typed scope, when the module's part is typed: its attempt answers the join of what its two exits answer, and its withdrawal answers a type (the shared typing of a module that waits, decisions row 275, point 3; its users are Semaphore's take and its protected form; a result type in normal form; no run) | `.witness` at `Effect4.Modules.waitRetryAt_answers` |
| `protected-form-typed` | `store-typing` | `compatibility` | The protected form keeps its body's effect type: one mask over an acquisition that answers a type, a body of any effect type at the restore site, and a release that answers a type under the exit's binder; the form has the body's answer, its failure type in normal form and its requirement (decisions row 276, point 1; its users are Semaphore's two protected forms; typing only: no run, no law of the mask and no release at an exit) | `.witness` at `Effect4.Modules.protectedBy_has` |

Five open parts, each as the seat would have it read:

| Requirement | The change | The sentence |
| --- | --- | --- |
| R4 | replace the present sentence | semaphore-accounting-preserved (proposed claim; store-typing): along a run of the public operations the cell stays a member of its type and its state stays in the first profile; the model's half is profile_closed; the cell's half is the six typing statements of the steps with step_keeps_cell, and each attempt statement of the operations gives the membership of the reply and of the stored value from the membership of the cell before the step; no statement gives that first membership from the handles that the table names, and no goal states the run-level claim (decisions rows 260, 261, 265, 276) |
| R10 | replace the present sentence | semaphore-expansion-agrees (proposed claim; translation-simulation): Semaphore's expansion agrees with the first profile's public observation; it keeps the selected identities and the permit commits, with its premises on the wake's policy, the admitted callers, interruption and the work budget; its parts on one atomic step are semaphore-steps-agree and the nine attempt statements of the operations, each on every model state; the operations, the walk and the protected form are library programs (src/Effect4/Modules/Semaphore/Ops.lean); the wrapper's run, the walk across visits and the protected form's run are not stated (decisions rows 79, 226, 259 to 261, 276) |
| R11 | add one part | semaphore-protected-permit (proposed claim; scope-lifetime-finalization): across every prefix of a run a committed activation of Semaphore's protected form releases at most once; an activation whose exit has completed through its cleanup has released exactly once, with enough work for the cleanup or a retained frontier; while the cleanup has not completed, the release obligation stays in the observation, and a frontier is no completed exit; the form is one mask over the take's loop, the hook and the body at the restore site (protectedBy), scoped and typed (protectedBy_has, withPermits_types); no goal states a clause, and each waits for the bracket of a region; finite controls: a take in its own mask loses its permit under an interruption, a wait inside a mask of the form's making cannot be interrupted, and the stand-in for the mask fails under a masked caller (Test/Program/SemaphoreTraces.lean, traces 4, 5 and 8); Pool's lease is the second user (decisions rows 222, 259, 276) |
| R8 | replace the sentence on the TypeScript face | the TypeScript face against rc.112: finite checks only, by the truth harness and by the keyed lane's runs of the scenarios' scripts on their printed modules (DI-49; decisions row 254); the truth harness compares the fork run's exit with rc.112's sync exit whenever the sync run settles, so it holds no program whose two entries settle on two exits: two Semaphore programs are filed with their four exits, and the two faces give one exit on each entry (docs/research/2026-10-06-seat-semw-evidence/README.md) |
| R12 | in `embedded-budget-sufficient`, replace the citation of trace 7 | (Test/Program/QueueTraces.lean and Test/Program/SemaphoreTraces.lean, trace 7 of each) |

### A proposal for the decisions register

One row: the truth runner's exit column.
Its options are the two rules of section 8, and the seat recommends the alternative.
The row would name the line of `harness/truth/run-truth.ts`, the evidence folder, and the faces contract's amendment of 2026-10-06.
The slice that lands it adds P1 and P4 to the corpus again.
It amends section 4 of the faces contract with one sentence on the two entries.

### What the Queue's typing statements could take from the shared typing

The seat did not edit the Queue's files. The reading is of `src/Effect4/Laws/Modules/Queue/Ops.lean`.

- `take_types` follows the wrapper's tree by hand, in 66 lines. With a `Waiter.Typed` for the Queue's taker it is one application of `waitRetry_answers`, as Semaphore's `take_types` is.
- `offer_types` follows `waitAnswer`'s tree by hand, in 43 lines. It needs a rule `waitAnswer_answers` over the same `Waiter.Typed`, which this slice does not write.
- `bounded_types`, `size_types` and `poll_types` use no wrapper, and they take nothing.

### Smaller proposals

- The wrapper's own scopes are written out twice in batteries: in `Test/Program/QueueOps.lean` and in `Test/Program/SemaphoreOps.lean`. One shared definition can serve both, and Pool's battery next.
- `kept_cursor` and `kept_payload` are one rule for each stem. One rule for every stem can replace them.
- A release that posts one helper where its reply owes a wake is written in Semaphore's `release`. Pool's return has the same shape. A shared builder can hold it when Pool lands.
- `docs/STATE.md` is the coordinator's. It can name the engine's three runs of Semaphore, the eight truth programs and the two stopped ones.

## 12. The requirements R1 to R13

The lists come from `generated/semantics.md` at the head and from `#plan_status`.
A statement of one module closes no requirement.

### What the slice advances

- **R4.** Each operation keeps scope, and each is typed at every scope: proved. The wrapper and the protected form are typed once, for every module's part: proved. No open part of R4 closes.
- **R10.** Nine attempt statements are parts of the proposed claim `semaphore-expansion-agrees`: proved, for one store step each. The claim stays open: no law of a run is stated.
- **R8.** Finite checks only. Each operation prints and reads back, and eight programs agree with rc.112. One finding stands against the truth lane's rule (section 8).
- **R11.** Finite checks only. Three traces are controls of the proposed claim `semaphore-protected-permit`. The form that a law needs is stated, scoped and typed.
- **R12.** Finite checks only. Traces 1, 2, 3, 6 and 7 are controls of open parts, and three engine runs are controls of row 259's reading. They prove nothing of R12.

### What the slice's theorems still rest on

- No planned goal: `#plan_status` answers `proved` for each, with `next goals: 0`.
- The premises of each attempt statement: a cell that encodes a model state, the cell's membership, and the captures.
  Where the step tests an identity, an injective table is a premise too.
  No theorem says that a run reaches a step with such a cell.
- The typing statements rest on a kept term for each caller's term, and on a typed body at every scope that the form's binders reach.
- `protectedBy_has` rests on an acquisition and a release with no failure and no requirement.

### The older open parts that the slice leaves untouched

- R1 (4 open parts), R2 (5), R3 (6), R5 (2), R6 (7), R7 (4), R9 (1) and R13 (4): untouched.
- R4: its 6 open parts stay, `semaphore-accounting-preserved` and `pool-profile-preserved` among them.
- R8: its 6 open parts stay.
- R10: its 13 open parts stay, with `semaphore-expansion-agrees`, `queue-expansion-agrees` and `pool-expansion-agrees`.
- R11: its 8 open parts stay, with the lift of `saved-mask-pop-discipline` as this branch's tree states it.
- R12: its 9 open parts stay, with `wait-registration-no-gap`, `posted-task-decision-preserves` and `embedded-budget-sufficient`.
