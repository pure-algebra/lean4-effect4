# 2026-10-06 receipt of seat POOLOPS: Pool's public operations

Status: a receipt (history, not authority).
The brief is `docs/research/2026-10-05-claude-lead/briefs/seat-poolops-brief.md`.
The design note is `docs/research/2026-10-06-seat-POOLOPS-design.md`.
The receipt is written for a reader with no part in this session.
Section 9 opens with what the law of a whole run needs from this slice.
Section 10 gives each lane's commands, and section 11 gives the proposals.

## 1. First: what the coordinator must know before merging

Three commits of this branch are not merged: this receipt, and the corrections `ca307963` and `2a89eb8e`.
The head and the main line's `c67fa03c` agree on every other file.
The seat merged `c67fa03c` before the receipt's commit, as the merge `71e53d99`.
The receipt's commit holds one Markdown file under `docs/research`, and it moves no checked file.
Each correction changes one docstring, and no statement or proof.

Five things stand first.

1. **The slice is whole, and nothing is red.**
   The acceptance run at `2a89eb8e` is green on every lane of the brief (section 4).
   Each case gives the contract's answer on the Lean machine, on the generated engine and on rc.112.
2. **One finding of this seat is corrected: one core lemma reaches `Classical.choice`, and not three.**
   The seat's message of step 1 named three lemmas and did not separate them.
   Measured at Lean v4.33.1, `List.filter_eq_nil_iff` reaches it, and the two others do not.
   Section 8 gives the three lines.
3. **Five sentences of the main line say more than a statement or a guard.**
   The seat read them in the coordinator's checkout and wrote nothing there.
   Section 11 gives each with its replacement.
4. **The first open point is what the law of a whole run needs from this slice.**
   Section 9 opens with it, for Pool and for the protected form.
5. **The proposals for the semantics registry wait for the coordinator.**
   Section 11 gives them in the order that the coordinator asked for.
   They are the place of the scope laws, three claims of typing and eleven attempt statements.
   Four replacement sentences of open parts and two smaller edits follow them.

## 2. Base, head and each step's commit

The base is `33b10a77`. The branch is `seat/poolops`, in the worktree `/Users/pooks/Dev/lean4-effect4-qtypes`.
The head is the commit of this receipt, on top of `2a89eb8e`.

| Step | Commit | What it holds | Merged as |
| --- | --- | --- | --- |
| the design note | `cc991fc4` | the design note | `61029f33` |
| 1 | `2d1c4734` | the closer's step: the model's sixth transition, its step term, its typing and its agreement | `61029f33` |
| 2 | `05954112` | the operations, and ten cases over them on the Lean machine | `33e063a8` |
| 3 and 4 | `8d79b774` | scope, the typing at every scope, and the attempt laws | `0fd28e74` |
| 5 | `9a81bafa` | nine acceptance traces, with the red controls of the lease and of the close | `dc1ad4b7` |
| 6 | `86b47644` | the faces, ten truth programs, and the pin of three sync runs | `adf6b779` |
| 7 | `d0c6891d` | the ten public cases on the generated engine | `181451a4` |
| 8 | `773d8354` | the documents | `c67fa03c` |
| a correction | `ca307963` | one docstring, to the measured axioms | not merged |
| a correction | `2a89eb8e` | one count in a docstring: six steps | not merged |
| 9 | this commit | the receipt | not merged |

The seat took the coordinator's heads `61029f33`, `33e063a8`, `0fd28e74`, `dc1ad4b7`, `adf6b779` and `c67fa03c` when each came.
The first five were fast-forward merges. The last is the merge `71e53d99`, and `2a89eb8e` stands on it.

## 3. The changed files

New files:

- `src/Effect4/Modules/Pool/Ops.lean` and `src/Effect4/Laws/Modules/Pool/Ops.lean`;
- the batteries `PoolPublic.lean`, `PoolOps.lean`, `PoolTraces.lean` and `PoolFaces.lean`, under `Test/Program/`;
- ten modules under `harness/truth/generated/`, one for each program of section 7;
- `docs/research/2026-10-06-seat-POOLOPS-design.md` and this receipt.

Edited files:

- the roots, each at its anchor: `src/Effect4.lean`, `src/Effect4/Laws.lean` and `Test/All.lean`;
- Pool's two folders, for the closer's step: `Cell.lean` and `Steps.lean` under `src/Effect4/Modules/Pool/`, and `Model.lean`, `Profile.lean`, `Typing.lean`, `Reading.lean`, `Relation.lean` and `Steps.lean` under `src/Effect4/Laws/Modules/Pool/`;
- two shared rule files, each in one section at the file's end: `src/Effect4/Laws/Modules/Waiting.lean` and `src/Effect4/Laws/Modules/Reading.lean`;
- the earlier batteries `PoolContract.lean`, `PoolSteps.lean`, `PoolAgreement.lean`, `PoolRelation.lean`, `PoolScenarios.lean` and `PoolEngine.lean`, under `Test/Program/`;
- the truth lane: `harness/truth/Truth.lean`, `harness/truth/corpus.json`, `harness/truth/result.json`, `harness/truth/result.md` and `Test/fixtures/target/selection.json`;
- the engine's lane: `ocaml/engine/test/pool/write.lean`, `test_pool.ml`, `dune` and `pool.txt`;
- the documents: `Test/contracts/pool.contract.md`, `README.md`, `docs/ARCHITECTURE.md` and `tools/Tools/ArchitectureRoles.lean`.

Not edited:

- any file of the Queue's or of Semaphore's folders, batteries, lanes or contracts;
- any file under `src/Effect4/Machine/`, and `harness/truth/run-truth.ts`;
- the shared rule files `Words.lean`, `Checking.lean` and `Store.lean`;
- `Test/contracts/faces.contract.md`, the Makefile, `lakefile.toml` and the coordinator's registers.

The shared rules that the slice added, by file:

- `src/Effect4/Laws/Modules/Waiting.lean`, in the section `Further`: `has_andThen`, `has_acquireRelease`, `answers_getId`, `answers_interrupt`, `Kept.field`, `kept_nat`, `single_scoped`, `front_scoped` and `listOf_scoped`;
- `src/Effect4/Laws/Modules/Reading.lean`: `captured_field` and `reads_listOf`.

No landed statement of either file changed.

## 4. The commands and their results

The hosts: bun 1.4.2, effect 4.0.0-rc.112, and tsgo 7 as `@typescript/native-preview` 7.0.0-dev.20260629.1.
`harness/truth/result.md` states the first two for each run of the lane.
Every Lean, Lake and make command ran through `scratch/lean-slot.sh` of the coordinator's checkout.
Every make command had the flags `-o build -o ts/eff/node_modules -o harness/truth/node_modules`.

### The acceptance run at the head `2a89eb8e`

| Command | Result | Evidence |
| --- | --- | --- |
| `lake build` | `Build completed successfully (1032 jobs).` | tested |
| the gate lines of `Test/All.lean`, in that build's log | the three lines below | tested |
| `make gen-fixtures` | the writers of every lane ran, and no file moved | tested |
| `make corpus` | `lake build Drivers.Corpus`, 157 jobs; the corpus was up to date | tested |
| `dune build`, in `ocaml/` | exit 0 | tested |
| `dune test --force engine`, in `ocaml/` | exit 0; 1907 lines `PASS`, no line `FAIL`; `test_pool: 110 checks, 0 failures` | tested |
| `make gen-truth` | `PASS: 72 programs agree on exits, schedules and sync exits; 1 signed divergence(s)`; no file moved | reproduced |
| `make check-truth` | 23 host tests pass; `PASS truth: pinned corpus, bounded differential and signed U-01 divergence checked; the regenerated modules type-check` | reproduced |
| `make check-cases` | up to date; its last run was on the tree of step 8: `conform cases: PASS, exit 0` | tested |
| `make check-docs` | `PASS check-docs: every path, link, citation and make target in 76 documents resolves` | tested |
| `git status --short`, after all of them | no line | tested |

The gate lines of `Test/All.lean` at the head:

- the library-root gate: 178 API and utility modules, 319 Laws-only modules, and `Effect4` never reaches Laws;
- the module and axiom gate: 782 modules and 91031 declarations, at `[propext, Quot.sound]`;
- the goal gate: 28 planned goals, and 12 declarations rest on goals. Four goals and one of the twelve are seat WORKQ's. None is of this slice.

The proof-style ratchet reads 1911 recorded uses, and it refused no new use. The slice did not edit its baseline.
The base `33b10a77` gave 1018 jobs, 768 modules and 90105 declarations, with 176 and 314 library modules.

Each run of `dune test` by this seat read the Lean corpus at this worktree's `.lake/corpus`: 408 files, 408 decoded.
Its cross-face line reads `agree=9 differ=2`, which is known and does not gate.
An earlier seat wrote that corpus in this worktree, and make judged it up to date at every run of this seat.

The same lanes ran first at `773d8354`, before the last merge, and each was green there.
That tree gave 1031 jobs, 781 modules and 90763 declarations, 24 goals and 1876 passing lines.
They ran again at the merge `71e53d99`, with the numbers of the table above.

**The Queue and Semaphore did not move.**
After `make gen-fixtures` and `make gen-truth`, `git status` names no file, at each step and at the head.
The one changed line of an earlier corpus entry is the separator after `pSemaphoreBodies`.
The two earlier runs of Pool's engine fixture did not move either: step 7 added fifty lines after them.

### What is bounded, and what is a host run

- **Proved**: the statements of section 5, for every scope, state and table of their statements.
- **Tested, and bounded**: each battery guard is one run on one schedule, at a fuel of 20000. A trace under a budget is one run at that budget. The engine's twelve runs are one schedule each, at the same fuel.
- **Reproduced on a host**: the truth lane's ten programs, on rc.112 under bun. The Lean face runs at a fuel of 1000. The host's deadline is 300 milliseconds. The agreement with rc.112 has no other evidence than these runs.
- **Read, and not run**: the pin's source for the sync entry (section 8), and the closer's early wake (section 8, the smaller finding 5).

### Narrow builds and probes

| Command | Result |
| --- | --- |
| `lake build` of each new or edited battery and law module, at each step | success |
| `lake build Tools.ArchitectureRoles` | 2 jobs, success |
| `bun test tools/target/profile.test.ts -t "selected IDs cannot vanish"` | 1 pass |
| the README's example as written, with one guard, by `lake env lean` in scratch | exit 0: the type `nat`, and the answer `7` |
| six copies of `Test/Program/PoolFaces.lean`, each with one pinned answer changed, by `lake env lean` in scratch | each copy fails exactly one guard |
| `#print axioms` of three core lemmas, in scratch | section 8 |
| the wire bytes of each step's row and of each operation, in scratch | section 8 |
| `python3 scripts/check-language.py --strict`, on the contract and on this receipt | no finding in each |

### Not run by the seat

`make check-gen`, `make check-slow`, `make check-corpus`, `make check-target`, the release ledger, the conservativity script and `make gen-semantics`.

### What the coordinator measured at the merges

The coordinator reported these results. The seat did not run them.

- At `61029f33`: the default build has 1018 jobs, 768 modules and 90154 declarations. The fixtures, the corpus and the truth lane wrote no byte. The conservativity check passes, 4 of 4.
- At `33e063a8`: 1020 jobs; 177 and 314 library modules; 770 modules and 90259 declarations.
- At `0fd28e74`: 1022 jobs; 177 and 315 library modules; 772 modules and 90441 declarations. One registry line places `Effect4.Laws.Modules.Pool.Ops` under `translation-simulation`.
- At `dc1ad4b7`: 1023 jobs; 773 modules and 90508 declarations. `dune test --force engine` has 1785 passing lines.
- At `adf6b779`: the truth lane has 73 programs, and 72 agree with 1 signed divergence. The corpus lane's 400 programs match, and no cell of its results moved. `make check-ts-reader` and `make check-target` pass.
- At `adf6b779`, the release ledger: 73 programs. 64 agree with both builds, 8 with rc.112 only and 1 with 4.0.1 only. The ten programs of Pool agree on rc.112 and on 4.0.1.
- At `c67fa03c`: 1032 jobs; 782 modules and 91031 declarations; 28 planned goals. `dune test --force engine` has 1907 passing lines. The corpus and target lanes and the release ledger pass, and no cell moved.

Each of these reports before `c67fa03c` gave 24 planned goals and 11 declarations on goals.
The seat has no report for the merge `181451a4`.

## 5. The axioms and the plan status

Each statement below is at `[propext, Quot.sound]` or less.
The batteries pin each output: `Test/Program/PoolOps.lean` for the operations, and the four earlier batteries for the closer's step.

- The model's fact of the closer's step: `drain_waits`. Its two helpers `borrowed_nil_iff` and `leases_nil_iff` hold the same ceiling by the axiom gate.
- The closer's step: `drainStep_types` and `drainStep_agrees`, and `pool_steps_agree` with its sixth part.
- The typing statements: `use_types`, `make_types` and `close_answers`.
- The attempt statements: `lease_attempt`, `withdraw_attempt`, `return_attempt`, `select_attempt`, `close_attempt`, `drain_attempt` and `make_makes`.
- Their forms at the operations' own binders: `lease_attempt_minted`, `withdraw_attempt_minted`, `return_attempt_minted` and `drain_attempt_minted`.
- Three scope laws of the operations: `use_scoped`, `close_scoped` and `make_scoped`.
- The shared rules: `has_andThen`, `has_acquireRelease`, `answers_getId`, `answers_interrupt`, `Kept.field` and `listOf_scoped`, each at `[propext, Quot.sound]`. `captured_field` and `reads_listOf` are at `[propext]`.

`#plan_status` answers `proved` for each of the fourteen placed statements of the operations, with `next goals: 0`.
The same battery pins that output. `drain_waits` answers `proved` too, in `Test/Program/PoolContract.lean`.
No statement of the slice rests on a planned goal, and the slice declares none.
The axiom gate holds every other declaration of the slice to `[propext, Quot.sound]`.

## 6. The placement of each landed statement

All are in Pool's law folder or in `src/Effect4/Laws/Modules/Waiting.lean`.

| Statements | Concept; requirement; claim | Reach | What it does not establish | Consumer |
| --- | --- | --- | --- | --- |
| `drain_waits` | `scope-lifetime-finalization`; R11; the claim `pool-drain-waits`, a helper of the proposed `pool-close-waits` | one transition of the model, on every state | a wait along a run, progress of the closer, a finalizer's run | the close's law of a run |
| `drainStep_types` | `store-typing`; R4; the cell's half of the proposed `pool-profile-preserved` | the cell's type at a resource type in normal form; every scope of names | agreement with the model | `closer_typed`, `drain_attempt` |
| `drainStep_agrees`, the sixth part of `pool_steps_agree` | `translation-simulation`; R10; the claim `pool-steps-agree` | every model state; an injective table | the wait itself, a finalizer's run | `drain_attempt` |
| The scope laws: one for each step term, each part and each operation, 23 in all | `initial-algebras-folds`; R4; steps of `operation-data-scoped` | every scope; every scoped term of a caller and every scoped body | typing, a run | `Api.Author.build` of each client |
| `use_types`, `make_types`, `close_answers` | `store-typing`; R4; the cell's half of the proposed `pool-profile-preserved` | the checker's `effTy` at every typed scope and path, at the native signature of any row table, for every kept term of a caller; a body of any effect type; a resource type that the checker types in a cell (`ResourceTy`) | a run; a string literal as a caller's term; an acquisition whose answer type is another type than the resource's | a client's admission |
| The shared typing rules: `has_andThen`, `has_acquireRelease`, `answers_getId`, `answers_interrupt`, `Kept.field`, `kept_nat` | `store-typing`; R4; helpers of a module's typing statements | every typed scope | a run; a law of the mask or of a scope | `make_types`, `use_types`, `refused_answers` |
| The seven attempt statements | `translation-simulation`; R10; parts of the proposed `pool-expansion-agrees` | one store step, from a cell that encodes any model state, with the cell's membership, at every scope; an injective table for the lease, the withdrawal and the closer's attempt | delivery, an order across steps, a cancellation law, a law of the protected lease, a wait of the close, a finalizer's run, a budget, liveness, a host | the law of a run, in a later slice |
| The four forms at the operations' own binders | the same | the same, at the names that the operation mints: two scope premises for each minted name | the same | the same |

**Two departures from the brief's table.**
The attempt statements hold on every model state, and not only on a state of the first profile.
`profile_closed` is the separate fact, and a law of a run uses both. Seat SEMW's statements have the same form.
The protected form's rule at `Has` is not written: the coordinator ruled so on the design note. Section 9 records it as a later need.

**No attempt statement says that a run reaches its step with such a cell.**
The cell's encoding, its membership, the captures and the table's injectivity are premises.

Two labels stay apart.
The scope's premises of a minted form hold at the operations' own binders for every caller's scope: proved, in section 3 of `Test/Program/PoolOps.lean`.
The comparison of each statement's term with the operation's own tree is a finite battery, at three caller scopes.

## 7. What the slice holds, part by part

### The closer's step

The model gains `drain`, its sixth transition, and the cell's type does not change (decisions row 276, point 2).
The step answers whether no lease is outstanding. Otherwise it enrols the closer at the end of the waiters.
The check and the enrolment are one transition, so each later return finds a waiter.
`drainStep` is its term: 59 nodes, with three folds. It is typed, and it agrees with the model.
The contract battery holds PP7 as a trace of the model through the closer, with the fault `drainAtOnce` red.

### The operations

`Pool.make`, `Pool.use` and `Pool.close` are library programs, in `src/Effect4/Modules/Pool/Ops.lean`.
The handle is the `Ref` of the pool's cell, and it stands after the resource type.
Each binder of an operation is minted, so an operation captures no name of its caller.
Each step is one `Ref.modify` of its own, and no step term stands inside a step term.
The contract's section "The operations over the steps" gives each operation's program and each part's.

Four things are one definition each.

- **The answer at a closed pool** is `refused`: the borrower reads its own identity and fails with the interruption of that fiber.
- **The return** is `giveBack`: the return step, and then one posted `wake` at the count 1 where the reply owes a wake.
- **The wake** is `wake`: one selection step, and then each selected hint in order (`resolveAll`).
- **The close** is `close`: the first step, one posted wake at the counted waiters, and the closer's loop.

`make` takes a proof that the size is positive, so a size of zero is refused where an author writes it.
`make` registers the close after the acquisitions, so the close runs first at the scope's end, and it waits.

### The controls on the Lean machine

`Test/Program/PoolPublic.lean` holds ten cases, one schedule each.

| Case | Its answer on the machine |
| --- | --- |
| PP1 | `[[[0],[],[],0,false,2], [[1,1,1],[2,1,1],[1,2,1],[2,2,1],[9,1]]]`: B gets A's resource, and the finalizer runs once |
| PP2 | the idle stamps are `[1,0]` after the two returns; C gets the resource 2, and D the resource 1 |
| PP3 | the first helper wakes A alone, and A's own step takes the item; A's return wakes B |
| PP4 | A is interrupted before the helper runs; the helper serves B, and A's body does not run |
| PP5, the public form | the helper selects A at the count 1, and A's own step takes the item |
| PP6 | `[true, some 77, [[5],[9,1]]]`: `make` fails with the acquisition's failure |
| PP7 | `[[[],[0],[0],1,false,1], true, false, [[0],[],[],0,true,1], [[1,9,1],[8],[2,9,1],[9,1]]]`: the finalizer's row follows H's return |
| PP8 | the interrupted waiter's entry leaves; H's return owes no wake, and B leases at once |
| the closed pool | L's exit is the interruption of fiber 1, its own; its body does not run |
| the closing pool | L's exit is the interruption of fiber 3, its own, before H's return; one waiter stays, the closer |

A snapshot is `[the idle stamps, the borrowed stamps, their leases' stamps, the number of waiters, closing, next]`.

Four changed policies stay red, each on its own case.
A return to the end of the idle stamps fails PP2. A selection at the post fails PP4.
A return that finalizes fails PP1. **A close that does not wait fails PP7**: the finalizer's row stands before H's body ends.
Each changed policy builds, so typing does not catch it.

`Test/Program/PoolOps.lean` holds the controls of the laws that the cases do not run.

- **Hygiene.** A caller's variable keeps its reading in the handle, in the acquisition and in the body, at each stem that the surface mints. A written form with fixed names is the red control.
- **Typing.** The checker's own answer on each operation's tree agrees with each typing statement, at three scopes. A handle of another type, a resource of another type and a release that could fail are refused.
- **The README's example**, with its checked answer and two red controls.

`Test/Program/PoolTraces.lean` holds nine traces. Each is one run on one schedule.

| # | Trace | Positive control | The fault's answer |
| --- | --- | --- | --- |
| 1 | a notification before the await | at the five budgets from 23 to 27, on two tapes, the borrower leases after the selection | the two tapes are two schedules |
| 2 | a cancellation between the return and the wake | interruptible: the withdrawal wins; masked: the entry stays | no withdrawal: the wake is lost, and the item stays idle while a borrower waits |
| 3 | a late delivery to an old hint | `[1, false, 1]`: the second wait is on a new hint, and the late delivery resumes nobody | one hint for every round: `[1, true, 1]`, and no exit at fuel 1000 |
| 4 | a holder interrupted inside the lease's mask | one region: the item is returned | two regions: the lease is lost, with a written yield and at the eighteen budgets from 13 to 30 |
| 5 | a waiter interrupted under a mask of the form's making | `use`: the entry leaves | the nested mask: the entry stays, and the waiter leases after its interruption |
| 6 | the returning fiber exits first | the holder's dispatcher runs the detached helper, which wakes the borrower | a supervised helper: the wake is lost, and the root has no exit |
| 7 | the receiver's continuation that grows | least fuel `61 + 3n` at seven lengths | at one unit less: no exit |
| 8 | the protected lease under a masked caller | the waiter stays, leases, and its body runs | the stand-in for the mask: the request is withdrawn, and the body does not run |
| 9 | a borrow at a closing pool, and under a masked caller | every item's record and the idle list are as they were; under `uninterruptible` the exit is still the interruption of its own fiber | none: the two are the coordinator's controls |

Traces 4 and 5 are the two red controls of `protectedBy` at Pool.
Trace 4 measures the budgets from 4 to 54, and the library's `use` loses the lease at none.
Trace 2 records the four observations of decisions row 222 apart.
Trace 7 claims no bound.
In trace 9 the masked control is at a closed pool, and the control with a holder is at a closing pool.

### The faces, the host and the engine

- `Test/Program/PoolFaces.lean`: each of the ten cases prints as a module and reads back. One use of `make`, of `use` and of the close prints and reads back alone, and its text is pinned. Each of the six step terms prints and reads back alone.
- The answer at a closed pool is one text. `use` holds `Cause.interrupt(` once, and the close and `make` hold none.
- Ten programs run on rc.112: `pPoolReuse`, `pPoolOrder`, `pPoolWaiters`, `pPoolLateWake`, `pPoolWake`, `pPoolMakeFails`, `pPoolCloseWaits`, `pPoolWithdrawn`, `pPoolClosed` and `pPoolClosing`.
- Each printed module type-checks under tsgo 7. Each agrees with the Lean machine on its exit, its compared rows and its sync exit.
- Each program is a case of the battery, so rc.112 runs the program that the battery runs.
- Three programs settle on two exits under the two entries: `pPoolWaiters`, `pPoolLateWake` and `pPoolWake`. Both faces give each exit.
- Two programs end the sync entry in the `AsyncFiberError` defect, on both faces: `pPoolCloseWaits` and `pPoolClosing`.
- **Decisions row 268's signed difference keeps no case out of the lane.** The lane runs the module's expansion on both faces, and no program calls the pin's own `Pool`.
- The engine's lane runs twelve programs on both instances: the two earlier runs, and then the same ten cases.
- The README's example is checked on the checker and on the Lean machine. It is no truth program, and the README says so.

### The rows that the slice moved

- **Corpus rows** (`harness/truth/corpus.json`): ten entries after `pSemaphoreBodies`, in the order of the list above. The corpus goes from 63 to 73 programs, and no earlier entry moves.
- **Result rows** (`harness/truth/result.json`, `harness/truth/result.md`): the same ten rows. The last line goes from 62 to 72 agreeing programs.
- **Target rows** (`Test/fixtures/target/selection.json`): the same ten names, in the same order, at the end of `programs`.
- **Generated modules**: ten new files under `harness/truth/generated/`, so 73 modules stand for 73 programs.
- **The engine's fixture** (`ocaml/engine/test/pool/pool.txt`): step 7 added ten runs after the two present ones. No other lane's fixture moved.
- **The release ledger** (`harness/truth/build-ledger.tsv`) holds one line for each corpus program. The coordinator added the ten lines at the merge `adf6b779`.
- **One pin table of the lane** (`lateSightsSync`, `harness/truth/Truth.lean`) is new. Section 8 gives it.

## 8. Findings

### Why the sync entry does not flush a child's dispatcher

Nine truth programs rest on this one fact, by the comments of their guards.
Four are Semaphore's: the cases P1 and P4, each as written and in its joined form. Five are Pool's.
It is said here once, for both faces.

On rc.112, by a reading of the vendored source. The files are `internal/effect.ts` and `Scheduler.ts`, under `vendor/effect-4.0.0-rc.112/src/`.

1. **Each fiber has a dispatcher of its own.** `currentDispatcher` of `FiberImpl` makes it at its first use, from the fiber's scheduler (lines 552 to 555 of the first file). `makeDispatcher` of `MixedScheduler` answers a new dispatcher with its own tasks (lines 188 to 190 of the second).
2. **A deferred start goes on the forking fiber's dispatcher.** `forkUnsafe` schedules the child's first evaluation there, at priority 0, when the fork does not start at once (line 5277).
3. **The sync entry flushes one dispatcher.** `runSyncExitWith` forks the program at a sync scheduler (lines 5536 to 5545). It flushes the root fiber's dispatcher (line 5542). It answers the root's exit, or the `AsyncFiberError` defect where the root has none.
4. **A dispatcher that nobody flushes runs later.** Its `scheduleTask` arms the scheduler's callback, which is a microtask in the sync mode (lines 161 and 207 to 212 of the second file). So a child's tasks run after `runSyncExit` has returned.

The seat read each of these lines in the vendored source on 2026-10-06.

On the machine, in `src/Effect4/Machine/Fibers.lean`. Each definition's docstring names the pin's line that it transcribes.

1. `RunFiber` has the field `dispatcher`: one for each fiber.
2. `start` puts a deferred start on the parent's dispatcher, at priority 0.
3. `runSyncExit` is `runFork`, and then `stepDecision.flushRoot` on the root alone. It answers the root's exit, or the defect.
4. The ordinary run, `Api.run`, flushes every armed dispatcher in its flush rounds, so a child's tasks run there.

What follows for a module. A posted helper is a detached fork with a deferred start.
So it stands on the dispatcher of the fiber that posts it.
Where a child's release or return posts it, the sync entry does not run it.
The root then goes on without the wake.

- Where the root does not wait for the wake, the two entries settle on two exits. The programs are P1 and P4 of Semaphore, and PP3, PP4 and PP5 of Pool.
- Where the root waits for it, the sync entry ends in the defect. The programs are the two joined forms of Semaphore, and PP7 and the closing pool of Pool. In Pool's two the closer waits, and the helper of H's return is on H's dispatcher.
- Where the root itself posts the helper, the sync entry runs it: the README's three examples.

Evidence. The pin's side is a reading, and the lane tests its result: both faces give each sync exit.
The machine's side is its definition, and guards of `harness/truth/Truth.lean` hold each exit.

### One pin table for three sync runs

The lane's guard held each program at the allocation order, in its fork run and in its sync run.
It took one pinned list for both runs (`lateSights`).
Three programs of Pool need two lists: `pPoolWaiters`, `pPoolLateWake` and `pPoolWake`.
Their fork runs are in the allocation order. Their sync runs move two fibers each.
The cause is the fact above, with one more: the root's close posts a later helper on the root's dispatcher.
So the Lean face's rows of the sync run never show the first helper, and they show the later one.

`lateSightsSync` pins the three sync runs, and the coordinator accepted it as a reviewed pin.
No compared field reads a moved number. The compared schedule is the fork run's.
Each of the three sync exits holds no fiber: a guard holds that it is one text under both numberings.
`pLateSeen` is the red control of that guard.

One limit. The guards measure the Lean face's numbering.
The lane compares no schedule of the sync entry, so rc.112's own order there is not measured.

### A missing withdrawal loses a wake at Pool

Trace 2's fault removes the withdrawal of an interrupted wait.
At Pool the dead entry stays at the front of the waiters.
A return's helper selects at the count 1: it takes the dead entry and resolves a hint that nobody awaits.
The item stays idle while the next borrower waits. Tested, on one schedule.

Seat SEMW's finding 1 is the same fault at Semaphore, and it loses no wake there.
**One difference between the two helpers explains it.**
Pool's helper selects by a count against the list as it stands: the first entries, whoever they are.
Semaphore's helper scans the live list: it spends one visit on the dead entry and goes on to the next.

So the law of a wake at Pool takes the withdrawal as a premise.
Every entry of the cell's waiters belongs to a request that still waits.
The coordinator's note on the law of a whole run holds the finding already.

### The engine fixture's size

`ocaml/engine/test/pool/pool.txt` grew from 345 KB to 1.79 MB. The Queue's fixture is 576 KB.
The ten public programs are 722369 bytes of canonical bytes, and the fixture writes two characters for a byte.

The cause is the size of a step's row. A term has no binder, so a step writes each shared part again.
The lease step reads the cell's current value 24 times, and it holds the removal's fold three times.
Decisions row 276, point 3, names the same cause for a step inside a step.

| Row or operation | Bytes |
| --- | --- |
| the lease step's row | 9063 |
| the return step's row | 3799 |
| the closer's step's row | 3392 |
| the withdrawal's row | 1193 |
| the close's first step's row | 654 |
| the selection's row | 610 |
| `use`, with its four rows | 18833 |
| `close`, with its four rows | 9105 |
| `make` at the size 1, with the close | 11522 |

The four rows are 78% of `use`. A case holds one to four uses and one `make`.
The programs are between 35477 and 107216 bytes.

The coordinator ruled that the ten cases stay: the engine then runs the same ten as the Lean machine and rc.112.
Three things would shrink the fixture. Each is a candidate, and no more.

- A binder in a term, so that a step names a shared part once. It changes the program syntax, so it is the owner's.
- A fixture that names a program by its content hash, with the bytes in one store for every lane.
- Another text encoding of the bytes than hexadecimal.

### Two new spellings in the engine's fixture

The fixture spells a present option and a constructor's value now, each as the engine's `show_val` writes it.
PP6 answers `some 77`. The two cases of a closed pool answer a reified exit, a constructor's value.
The engine prints the same text on both instances, so the test checks each spelling.
**The unit and an empty option stay refused.** No run holds one, so no test would check its spelling.

### An interruption has no failure type

The checker gives the cause of an interruption no failure type (`causeTy`).
So the lease answers an item with no failure, and the refusal at a closed pool adds none.
`use` therefore needed only `protectedBy_has`, the rule that seat SEMW landed.
This removed the consumer of the rule at `Has` that the brief asked for (section 9).

### A pool is made inside a scope

`make` registers the close in the surrounding scope, so its program requires that scope.
A pool made outside a scope builds. Its type requires exactly the scope's key, as `make_types` states.
Its run dies with the defect of a missing service.
Guards of `Test/Program/PoolPublic.lean` hold the three facts, and the contract and the README say it.

### One core lemma reaches `Classical.choice`

The first proof of `leases_nil_iff` used three core lemmas, and the axiom gate refused it.
Measured now by `#print axioms`, at Lean v4.33.1:

| Lemma | Its axioms |
| --- | --- |
| `List.filter_eq_nil_iff` | `[propext, Classical.choice, Quot.sound]` |
| `List.any_eq_false` | `[propext, Quot.sound]` |
| `List.map_eq_nil_iff` | none |

The seat's message of step 1 named the three together. One of them is the cause.
The landed proof follows the list (`borrowed_nil_iff`).
Another proof of the same file uses `List.any_eq_false`, and the axiom gate accepts it.
The commit `ca307963` corrects the docstring of `borrowed_nil_iff`, which named two lemmas.

### Smaller findings

1. **Lean elaboration refused a guard over a list of six-part tuples.** Lean found no decision procedure for the equality. The guard counts into lists of numbers now. A guard over four-part tuples passes.
2. **A battery definition over the fixture's text reached `Classical.choice`.** The axiom gate refused `linesOf`, a helper of the first form of `Test/Program/PoolEngine.lean`. Each guard reads the lines itself now, as AGENTS.md says.
3. **The proof of a positive size is not found inside a function.** `make A n acquire` with a variable `n` has no proof by `decide`. The batteries make a pool through `makeAt`, which branches on the size.
4. **The hook of `use` is masked, and `giveBack` holds no mask of its own.** The return runs inside the form's mask at every exit. A client that calls `giveBack` alone gets no mask.
5. **The closer can be woken early.** The close's helper takes as many waiters as the first step counted. If one of them withdraws first, the count reaches the closer. The closer then runs its step again and enrols again. Read in the terms, and not run as a case.
6. **An up-to-date build replays the gate lines.** `lake build` printed them from its cache at the head. Seat SEMW's receipt saw none on an up-to-date build.
7. **A hook of this session refused one compound command.** The command held a commit with a message file, opam's flag for its switch, and dune's flag that forces a test. The hook read it as a forced change of branch. The seat ran the commit alone, and it set no bypass.
8. **One stale count stood in a docstring of the slice.** `ResourceTy` said five steps after the sixth landed. The commit `2a89eb8e` corrects it.

## 9. Open points

### What the law of a whole run needs from this slice

The frame is the coordinator's note, `docs/research/2026-10-06-whole-run-law-prep.md`.
It has three layers: the cell's invariant, a call's lifetime, and agreement.
The third layer needs an abstract client, and this slice adds nothing to it.

**Pool, the cell's invariant** (the proposed claim `pool-profile-preserved`, R4).

The slice supplies three things.

- Every write of the cell by an operation is one of six rows, and each row has its attempt statement. From a cell that encodes a model state, the row stores a cell that encodes the model's next state.
- `make_makes`: the cell that `make` makes encodes the model's initial state, which is a state of the profile.
- `profile_closed`: each of the six transitions keeps the profile.

The law still needs four things.

1. **A client that writes the cell by the operations alone.** The handle is a `Ref` at the cell's type, and a client can write it. It is the note's first design choice. Pool adds one fact to it: the handle outlives the pool's scope by design, since a borrow at a closed pool has an answer.
2. **The table along a run.** The lease, the withdrawal and the closer's attempt take an injective table. Each enrolment renews it at a new hint. No statement says that a round's hint and a request's identity are fresh, so that the renewed table stays injective.
3. **The cell's membership at each step.** It is a premise of each attempt statement. The note's inventory says that typed state along a run gives it. The seat did not check that.
4. **The resources' values.** Each attempt statement takes one map from a resource's name to its value. `make_makes` fixes it at the acquisitions' answers, and `step_items` says that no transition changes a resource.

**Pool, a call's lifetime.**

The borrower (the proposed `pool-expansion-agrees`, with `wait-registration-no-gap`).
The slice supplies the check and the enrolment as one store step (`lease_attempt`), and the withdrawal (`withdraw_attempt`).
The law needs the module-free law of an await and its notification across commands.
It needs the withdrawal as a premise of the wake, by the finding of section 8.
It needs the uncut run as a named premise: trace 7 measures, and it claims no bound.

The wake (the proposed `pool-wake-selection`, R12).
The slice supplies one selection as a store step (`select_attempt`), and the helper as a program.
The law needs the walk over the reply: each selected hint is resolved once, in order. No statement gives it.
A wake reserves nothing: the selection changes the waiters alone, and the resumed borrower runs its own lease.

The close (the proposed `pool-close-waits`, R11).
The slice supplies the first step and the closer's attempt (`close_attempt`, `drain_attempt`).
It supplies the model's facts `close_refuses`, `step_closing` and `drain_waits`.
It supplies the typing: the close cannot fail (`close_answers`), so `make` registers it.
The law needs four things, and each is an invariant.

1. The closer's loop ends only at the reply true. It is a part of the wrapper's law of a run.
2. After that reply no lease is added. It follows from `close_refuses` and `step_closing` along the run, on top of the cell's invariant.
3. The scope runs its finalizers in the reverse order of their registration, along a run. `closeOrder_eq` is of one scope value.
4. A finalizer runs at most once for a registration, along a run.

Why the closer is not left waiting is a reading of four facts (the contract's section on the operations).
It is progress, and no clause above needs it.

**The protected form** (`protectedBy`; its users are Semaphore's two forms and Pool's `use`).

Pool is the form's second user, and it shows five things that the form's law must cover.

1. **An acquisition that fails after it committed nothing.** At a closing pool the lease's loop ends with no item. The acquisition then fails with the interruption of its own fiber, inside the mask and before the hook is installed. So the law takes a premise on the module: a failed acquisition has committed nothing. Pool's part is `close_refuses`: a refused lease changes no item and enrols nobody.
2. **An acquired value that the release reads.** The return step reads the item's stamp and its lease's stamp from the acquired value (`return_attempt_minted`). So the law carries that value from the commit to the release. Semaphore's release reads the caller's count alone.
3. **A release that the model can repeat.** `giveBack_once`: a second return of one lease changes nothing, and it owes no wake. So a clause "at most once" is enough for the cell.
4. **A release that forks.** The return posts a helper, which is detached and cannot be interrupted.
5. **The mask's facts.** The bracket of a region is proved with the later cut's stack shape as its premise (seat BRACKET). The carrying fact is open (decisions row 280). A waiter adds a cut across a wait.

Traces 4, 5 and 8 are the finite controls of the form at Pool, and PP7 with `noWait` is the close's.

**The rule at `Has`, a later need.** The design note names it `protectedBy_hasAt`.
Its shape is the protected form at three effect types: the acquisition and the release may each fail or require.
`protectedBy_has` is then its instance at an acquisition and a release with no failure and no requirement.
The slice did not write it, by the coordinator's ruling on the design note: no program needs it.
An interruption has no failure type, so Pool's lease has none.
Its first real consumer is a protected acquisition that fails with a typed failure.
The first profile excludes that: the pin's acquisition inside `use` runs after `make` (decisions row 267).

### Every other obligation that stays open

Pool's laws of a run. None is stated.

1. **`pool-expansion-agrees`** (R10): the wrapper's run for the borrower and for the closer, the wake across helpers, and the protected lease's run.
2. **`pool-profile-preserved`** (R4): the four needs above.
3. **`pool-lease-return` and `pool-close-waits`** (R11): the clauses above. One clause has no control: a cleanup reported as finished at a frontier.
4. **`pool-wake-selection`** (R12), with the withdrawal as its premise.
5. **The embedded budget** (decisions row 226; `embedded-budget-sufficient`). Trace 7 measures, and it claims no bound.
6. **The waiting claims of the semantics registry**: `wait-registration-no-gap`, `waiting-request-obligation-preserved`, `posted-task-decision-preserves` and `posted-wake-profile-agrees`. Traces 1, 2, 3 and 6 are finite controls, one schedule each.

Premises that a caller keeps. No check refuses a breach.

7. **A client writes the cell by the operations alone.**
8. **One borrower for an item.** `use` hands the resource's value to the body. A body that keeps that value after its exit has it beside the next borrower. No check refuses that.

Limits of the typing statements.

9. A string literal is no kept term, so the statements say nothing of one. A resource that is a string literal is outside `initial_types` too.
10. `make_types` takes an acquisition whose answer type is the resource's type. PP6's acquisition ends in a failure, and its answer type is `never`. The checker types PP6, and the statement says nothing of it.
11. `use_types` takes a body of one effect type at every kept reader of a resource.

The lanes.

12. **Each case and each trace is one schedule.**
13. **The truth lane measures the sync numbering on the Lean face alone** (section 8).
14. **The engine's lane** is twelve runs. It states no law of the engine's replay.
15. **The README's example is no truth program.** A program `pPoolHandoff` would be the eleventh of Pool. The truth step was closed, so it is a candidate.

The semantics registry.

16. The rows and sentences of section 11 are not entered.
17. The 23 scope laws of `Effect4.Laws.Modules.Pool.Ops` stand under the module's default concept.

## 10. How to run each lane again

Run each command at the repository's root, on a clean tree, unless its row names a folder.
`AGENTS.md` bounds Lean's threads: write `LEAN_NUM_THREADS=3` before a `lake` command.
The seat's worktree links the coordinator's install of the TypeScript packages.
So each `make` of the seat had three more flags: `-o build -o ts/eff/node_modules -o harness/truth/node_modules`.
A checkout with its own install needs none of them.
The OCaml commands need the opam switch `effect4`, and `make corpus` first.

| Lane | Command | What a green run shows |
| --- | --- | --- |
| the laws | `LEAN_NUM_THREADS=3 lake build Effect4.Laws.Modules.Waiting Effect4.Laws.Modules.Pool.Ops` | each law elaborates |
| the batteries | `LEAN_NUM_THREADS=3 lake build Test.Program.PoolContract Test.Program.PoolSteps Test.Program.PoolAgreement Test.Program.PoolRelation Test.Program.PoolScenarios Test.Program.PoolPublic Test.Program.PoolOps Test.Program.PoolTraces Test.Program.PoolFaces Test.Program.PoolEngine` | every guard, each pinned axiom list and each plan status |
| the gates | `make build`, and `lake env lean -M6144 Test/All.lean` for the gate lines alone | the three gates of `Test/All.lean`, and the proof-style ratchet |
| the engine's fixture | `make gen-fixtures`, then `git status --short` | Lean writes the committed fixture again, byte for byte |
| the engine | `make corpus`, then in `ocaml/`: `opam exec --switch=effect4 -- dune build` and `opam exec --switch=effect4 -- dune test --force engine` | `test_pool: 110 checks, 0 failures` |
| the truth lane | `make gen-truth`, then `git status --short`, then `make check-truth` | 72 programs agree, with 1 signed divergence; the modules type-check under tsgo 7 |
| the target's selection | `bun test tools/target/profile.test.ts -t "selected IDs cannot vanish"` | the selected names are the corpus's names, in order |
| the case policy | `make check-cases` | `conform cases: PASS` |
| the documents | `make check-docs`, and `python3 scripts/check-language.py --strict <file>` | every cited path resolves; no language finding |

The writer of the engine's fixture runs alone too: `lake env lean --run ocaml/engine/test/pool/write.lean`.
A red control is inside its battery. To see one fail, change its expected value and build the battery.

## 11. Choices, and proposals

Three differences from the design note:

- `protectedBy_hasAt` is not written, by the coordinator's ruling on the note's third point.
- `has_selectOptionWith_kept` is not written: the lease's selection answers a type with no failure, so no rule at `Has` was needed for it.
- Four small shared rules are added that the note did not list: `kept_nat`, `single_scoped`, `front_scoped` and `listOf_scoped`.

Choices of the seat:

- The handle stands after the resource type in each operation, as the Queue's stands after the message type.
- The refusal is a value of the loop's result: the lease's loop answers an optional item, and `use` branches on it.
- The closer is a second `Waiter` over the same wrapper, and the close is `waitRetry` under a mask of its own.
- `make` is typed by its acquisitions' own judgment (`acquireAll_has`), so a size is a number of the statement and no bound.
- A changed policy of a battery is a variant of Pool's part, and the variant with no change is the library's tree.
- The engine's public runs have names of their own, and the two earlier runs keep theirs.
- The truth lane holds the ten cases as the batteries write them. It holds no joined form.

### Proposals for the semantics registry

The seat did not edit `tools/Tools/SemanticsRegistry.lean`.
The order is the coordinator's: the scope laws, the typing statements, the attempt statements, the closer's step, and the open parts.

**The place of the scope laws.**
The 23 scope laws are steps of the claim `operation-data-scoped` (concept `initial-algebras-folds`, R4), on a module's programs.
They carry no tag, so they stand under the module's default concept, `translation-simulation`.
The Queue's and Semaphore's stand so too. The seat recommends no row, and one tag for each law in a later slice.
If a row is wanted, this is it:

| id | concept | role | title | pointer |
| --- | --- | --- | --- | --- |
| `pool-operations-scoped` | `initial-algebras-folds` | `compatibility` | Pool's use keeps the authoring scope judgment: for a scoped handle and a body that is scoped at every scoped resource, the program is scoped; make and the close have the same law (make_scoped, close_scoped), and so has each step term and each part (decisions rows 255 and 267; a step of operation-data-scoped on a module's programs; scope only: no typing and no run) | `.witness` at `Effect4.Pool.use_scoped` |

**The three typing statements.** Three claims, each with a theorem that states it:

| id | concept | role | title | pointer |
| --- | --- | --- | --- | --- |
| `pool-use-typed` | `store-typing` | `compatibility` | Pool's use keeps its body's effect type at every typed scope: for a kept handle at the reference type of Pool's cell and a body of one effect type at every kept resource, the form has the body's answer, its failure type in normal form and its requirement; the lease and the return add no failure and no requirement, and the refusal at a closed pool adds none, since an interruption has no failure type (the protected form's second user; decisions rows 267, 276 and 279; a resource type in normal form whose item record and cell record are formed; typing only: no run, no law of the mask and no return at an exit) | `.witness` at `Effect4.Pool.use_types` |
| `pool-make-typed` | `store-typing` | `compatibility` | Pool's make answers the pool's handle at every typed scope, for an acquisition of one effect type whose answer is the resource's type: its failure type is the acquisition's in normal form, so a failed acquisition fails make, and its requirement is the acquisition's with the scope's key, so a pool is made inside a scope (decisions rows 267 and 268; a positive size, and a resource type in normal form whose item record and cell record are formed; typing only: no run and no finalizer's run; an acquisition whose answer type is another type is outside the statement) | `.witness` at `Effect4.Pool.make_types` |
| `pool-close-typed` | `store-typing` | `compatibility` | Pool's close answers the unit at every typed scope, with no failure and no requirement, for a kept handle at the reference type of Pool's cell: the close's first step, the posted wake at the counted waiters, and the closer's loop over the closer's step; so it is a release that cannot fail, and make registers it (decisions rows 268 and 276, point 2; a resource type in normal form whose item record and cell record are formed; typing only: no wait along a run, no end of the loop and no finalizer's run) | `.witness` at `Effect4.Pool.close_answers` |

**The eleven attempt statements.** Each is a part of the proposed claim `pool-expansion-agrees` (R10).
Four are parts of a second proposed claim too, and the last column names it.
Each has the concept `translation-simulation` and the role `simulation`, by its tag in the source.
Seat SEMW's nine statements were entered as a sentence of R10's open part, and not as claims.
The seat recommends the same here, and it gives each row in case the coordinator enters claims.

| id | title | pointer | also a part of |
| --- | --- | --- | --- |
| `pool-lease-attempt` | One attempt of a lease is the model's lease, as one store step: from a cell that holds the encoding of a model state, the Ref.modify of the lease step answers the model's reply and stores the encoding of the model's next state, at the table renewed with the round's hint; the reply and the stored value are members of their types (every model state; premises: an injective table, the cell's membership, and the captures of the identity and of the hint; one step: no wait, no delivery, no order across steps and no law of a run) | `.witness` at `Effect4.Pool.lease_attempt` | — |
| `pool-withdraw-attempt` | The withdrawal of a request is the model's withdraw, as one store step: the entry of the request's identity leaves the cell's waiters, no other field changes, and the table does not change; a borrower's withdrawal and the closer's are this one statement (every model state; premises: an injective table, the cell's membership and the identity's capture; one step: it does not say that an interrupted wait runs it) | `.witness` at `Effect4.Pool.withdraw_attempt` | `waiting-request-obligation-preserved` |
| `pool-return-attempt` | The step of a return is the model's giveBack, as one store step: for an item's stamp and a lease's stamp that the caller's terms read, the step answers whether the lease returned and whether a wake is owed, and it stores the encoding of the model's next state; a return of a lease that holds nothing changes nothing (every model state and every table; premises: the cell's membership and the two captures; one step: it does not say that an exit runs it, or runs it once) | `.witness` at `Effect4.Pool.return_attempt` | `pool-lease-return` |
| `pool-select-attempt` | One selection of a wake is the model's select, as one store step: for a count that the caller's term reads, the step answers the records of the first waiters of the state that it finds, at most the count and in order, each with its identity's handle and its hint, and it stores the state without them (every model state and every table; premise: the cell's membership; one step: no delivery of a hint and no order across helpers) | `.witness` at `Effect4.Pool.select_attempt` | `pool-wake-selection` |
| `pool-close-attempt` | The close's first step is the model's close, as one store step: it answers whether this step began the close and how many waiters are enrolled, and it stores the encoding of the closing state (every model state and every table; premise: the cell's membership; one step: no wake and no wait) | `.witness` at `Effect4.Pool.close_attempt` | `pool-close-waits` |
| `pool-drain-attempt` | One attempt of the closer is the model's drain, as one store step: it answers whether no lease is outstanding, and it stores the encoding of the model's next state at the table renewed with the round's hint, where the closer is enrolled exactly when a lease is outstanding (every model state; premises: an injective table, the cell's membership, and the captures of the identity and of the hint; one step: no wait along a run and no end of the loop) | `.witness` at `Effect4.Pool.drain_attempt` | `pool-close-waits` |
| `pool-make-makes` | The cell that make's Ref.make stores is the encoding of the model's initial state at the acquired resources, and that state is a state of the profile: every item is idle, in the order of the acquisitions, nobody waits, and the pool is open (every table and every list of resources; premise: each resource's term reads its value; the one row that makes the cell: nothing of the acquisitions' runs and nothing of the registered close) | `.witness` at `Effect4.Pool.make_makes` | — |
| `pool-lease-attempt-minted`, `pool-withdraw-attempt-minted`, `pool-return-attempt-minted`, `pool-drain-attempt-minted` | The same statement at the names that the operation mints: for each minted name the row's scope binds it at a level, and no later binder shadows it; the item's record is the protected form's acquired value, and the return reads its two stamps (the scope premises hold at every caller's scope: proved in Test/Program/PoolOps.lean) | `.witness` at `Effect4.Pool.lease_attempt_minted`, and the three of the same form | as its first form |

**The closer's step** is entered: `pool-drain-waits`, with `drain_waits` as its theorem.
The seat read its title against the statement, and it says no more. The sixth part of `pool-steps-agree` is the step's agreement.

**Four open parts, each as the seat would have it read:**

| Requirement | The change | The sentence |
| --- | --- | --- |
| R4 | replace the present sentence | pool-profile-preserved (proposed claim; store-typing): along a run of the public operations the cell stays a member of its type and its state stays in the first profile; the model's half is profile_closed on six transitions; the cell's half is the seven typing statements of the cell and of the steps with step_keeps_cell, and each attempt statement of the operations gives the membership of the reply and of the stored value from the membership of the cell before the step; the operations are typed at every scope (use_types, make_types, close_answers), and make's type requires the scope; no statement says that a client writes the cell by the operations alone, none keeps the table injective along a run, and no goal states the run-level claim (decisions rows 267 to 269, 276) |
| R10 | replace the present sentence | pool-expansion-agrees (proposed claim; translation-simulation): Pool's expansion agrees with the first profile's public observation, under its premises on the callers, interruption, the close and the work budget; its parts on one atomic step are pool_steps_agree and the eleven attempt statements of the operations, each on every model state; the operations, the wake, the close and the refusal at a closed pool are library programs (src/Effect4/Modules/Pool/Ops.lean); the wrapper's run for the borrower and for the closer, the wake across helpers and the protected lease's run are not stated; finite controls: ten cases on the Lean machine, on the generated engine and on rc.112, one schedule each (Test/Program/PoolPublic.lean) (decisions rows 79, 226, 267 to 269, 276, 279) |
| R11 | replace the present sentence | pool-lease-return and pool-close-waits (proposed claims; scope-lifetime-finalization): a committed lease returns its item at most once, and exactly once where its exit ended; a lease that is refused at a closing pool commits nothing; the close ends only after every lease returned, and each item is then finalized once; the model's facts are giveBack_front, giveBack_once, close_refuses and drain_waits; the forms are stated, scoped and typed: use is the protected form over the lease's loop and the return, and the close is the wrapper over the closer's step, registered by make after the acquisitions (use_types, close_answers, make_types); their steps are return_attempt, close_attempt and drain_attempt; no goal states a clause, and each waits for the carrying fact of a region and for a finalizer's law of a run; finite controls: a lease in its own mask is lost under an interruption, a wait inside a mask of the form's making cannot be interrupted, the stand-in for the mask fails under a masked caller, and a close that does not wait finalizes an item that a borrower still holds (Test/Program/PoolTraces.lean, traces 4, 5 and 8; Test/Program/PoolPublic.lean, PP7) (decisions rows 222, 267, 268, 276, 279) |
| R12 | replace the present sentence | pool-wake-selection (proposed claim; reactive-scheduling): the helper selects the first count waiters of the state that it finds, and it notifies exactly those, in order; the model's fact is select_takes_first, and one selection is one store step (select_attempt); the helper is a library program, one selection step and then each selected hint in order; the selection is by count, so the law takes the withdrawal as a premise: every entry of the waiters belongs to a request that still waits; finite controls: a selection at the post serves a waiter that left, and with no withdrawal the wake is lost (Test/Program/PoolPublic.lean, PP4; Test/Program/PoolTraces.lean, trace 2) (decisions rows 221, 267) |
| R12 | in `embedded-budget-sufficient`, extend the citation of trace 7 | (Test/Program/QueueTraces.lean, Test/Program/SemaphoreTraces.lean and Test/Program/PoolTraces.lean, trace 7 of each; Pool's measures seven lengths) |
| R8 | in the sentence on the TypeScript face, after the two Semaphore programs | three Pool programs settle on two exits too, and their sync runs are pinned apart from the allocation order on the Lean face (lateSightsSync, harness/truth/Truth.lean) |

### Five sentences of the main line that say more than a statement or a guard

The seat read each in the coordinator's checkout, at `9f12459d` and again at `c67fa03c`, and wrote nothing there.

| Where | The sentence says | The statement or the guard says | A replacement |
| --- | --- | --- | --- |
| the title of `pool-steps-agree`, in the semantics registry | each step agrees "on every model state" | three of the six parts take an injective table: the lease, the withdrawal and the closer's step | after "on every model state": "through an encoding table that is injective for the lease, the withdrawal and the closer's step" |
| the property of `pool-steps-agree`, in `docs/core/semantics.md` | the same | the same | add one sentence: "The lease, the withdrawal and the closer's step take an injective table." |
| the property of `pool-lease-enrols`, in `docs/core/semantics.md` | "A lease enrols its request exactly when the pool is open and a lease holds every item." | `lease_enrols_iff` takes a state of the profile. The registry's title says so | "On a state of the profile, a lease enrols its request exactly when the pool is open and a lease holds every item." |
| the faces contract's amendment for Pool, its second item | "the recorder never sees a helper that a child posts, and it sees the later helper of the root's close" | the guards measure the Lean face's rows of the sync run. The lane compares no schedule of the sync entry | "So the Lean face's rows of the sync run never show a helper that a child posts, and they show the later helper of the root's close. The lane compares no schedule of the sync entry." |
| `docs/STATE.md`, the paragraph of this seat | "A borrow at a closing pool leaves the items and the idle list as they were. Under a masked caller it still exits with the interrupt of its own fiber." | the masked control is at a closed pool, with no holder (`closedMasked`) | "A borrow at a closed pool under a masked caller still exits with the interrupt of its own fiber." |

The sentence of the faces contract was the seat's own first, in its message of step 6.
The title of `semaphore-steps-agree` has the form of Pool's. Two of its five parts take an injective table: the take and the withdrawal.
The seat read that one statement, and no other text of Semaphore's.

The other texts that the seat read back say no more than their statements.
They are the title and the property of `pool-drain-waits`, R11's open part, and the rest of the faces contract's amendment.
One cause of that amendment is pinned by a guard for one program alone.
`pPoolCloseWaits` has its sync rows pinned, and `pPoolClosing` has only the defect.

### A proposal for the decisions register

One sentence for row 274, or for the row of this receipt.
The lane holds a program at the allocation order in each of its two runs, and a pin may name one run.
`lateSights` pins both runs of a program, and `lateSightsSync` pins a sync run alone.

### Smaller proposals

- **`pPoolHandoff`**: the README's example as an eleventh truth program of Pool.
- **One helper for a scenario's program** in `harness/truth/Truth.lean`. `semaphoreProgram` and `poolProgram` are one function, and the Queue's five programs write it out.
- **One shared definition of the wrapper's scopes for the batteries.** `Test/Program/PoolOps.lean` imports Semaphore's, and the Queue's battery has its own.
- **`resolveAll` is module-free.** It resolves each hint of a list of waiters' records. The Queue's `postAll` is its neighbour. A shared builder can hold the return that posts one helper, as seat SEMW proposed.
- **`atClose` is module-free.** It registers a cleanup in the surrounding scope. The authoring sugar could hold it beside `acquireRelease`.
- **`make_types` at an answer below the resource's type.** The statement takes equality. A form with the checker's subtyping would cover PP6's acquisition.
- **The fixture's size**: the three candidates of section 8.
- `docs/STATE.md` is the coordinator's. Its paragraph on this seat can name the receipt and the correction of the lemma's finding.

## 12. The requirements R1 to R13

The lists come from `generated/semantics.md` at the head and from `#plan_status`.
A statement of one module closes no requirement.

### What the slice advances

- **R4.** Each operation keeps scope, and each is typed at every scope: proved. The closer's step is typed: proved. `make`'s type states the scope's requirement. No open part of R4 closes.
- **R10.** Eleven attempt statements are parts of the proposed claim `pool-expansion-agrees`: proved, for one store step each. The sixth step agrees with the model: proved. The claim stays open: no law of a run is stated.
- **R11.** `drain_waits` is proved, on the model. The forms that the two proposed claims need are stated, scoped and typed. Finite checks only for a run: four traces and PP7 are controls.
- **R8.** Finite checks only. Each operation prints and reads back, and ten programs agree with rc.112.
- **R12.** Finite checks only. Traces 1, 2, 3, 6 and 7 are controls of open parts, and twelve runs are controls on the generated engine. They prove nothing of R12.

### What the slice's theorems still rest on

- No planned goal: `#plan_status` answers `proved` for each, with `next goals: 0`.
- The premises of each attempt statement: a cell that encodes a model state, the cell's membership, and the captures.
  Where the step tests an identity, an injective table is a premise too.
  No theorem says that a run reaches a step with such a cell.
- The typing statements rest on a kept term for each caller's term, and on a resource type that the checker types in a cell.
  Such a type is its own normal form, and the item's record and the cell's record at it are formed (`ResourceTy`).
  `use_types` rests on a typed body at every scope that the form's binders reach.
  `make_types` rests on an acquisition that answers the resource's type.
- `use_types` rests on `protectedBy_has`: an acquisition and a release with no failure and no requirement.

### The older open parts that the slice leaves untouched

- R1 (4 open parts), R2 (5), R3 (6), R5 (2), R6 (7), R7 (4), R9 (1) and R13 (4): untouched.
- R4: its 6 open parts stay, `pool-profile-preserved` and `semaphore-accounting-preserved` among them.
- R8: its 6 open parts stay.
- R10: its 13 open parts stay, with `pool-expansion-agrees`, `queue-expansion-agrees` and `semaphore-expansion-agrees`.
- R11: its 8 open parts stay, with `pool-lease-return` and `pool-close-waits`, and the carrying fact of a region.
- R12: its 9 open parts stay, with `pool-wake-selection`, `wait-registration-no-gap` and `embedded-budget-sufficient`.
