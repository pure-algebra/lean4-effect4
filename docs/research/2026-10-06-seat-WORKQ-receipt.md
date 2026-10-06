# 2026-10-06 seat WORKQ receipt: the two-worker crew over the public Queue

Status: receipt (history, not authority). Brief:
`docs/research/2026-10-05-claude-lead/briefs/seat-workq-brief.md`, with the dispatch message.
Design note: `docs/research/2026-10-06-seat-WORKQ-design.md`. Filed evidence:
`docs/research/2026-10-06-seat-workq-evidence/`. The coordinator sent nine messages after the
dispatch. Each ask is named below where it changed the slice.

Three phrases of this receipt, before its first item.

- A run is **funded** when the tape of its own journal leaves no row unread (`funded`,
  `Test/Dogfood/Scenario.lean`). The first unread row is the dictionary's stopped row.
- A budget **cuts a step** when the step's command loop returns commands that it did not run.
- A machine is **at rest** when it names no runnable fiber and no armed owner (`atRest`, the
  same file).

**The one thing to know before merging:** this head differs from main `c67fa03c` by two
docstrings, the evidence folder's later files and this receipt. No statement, no control and
no generated file changes. The two docstrings replace "nothing will run the root" by what the
probes tested. The working note of the whole run carries the same sentence (item 2.1).

Ten more facts stand beside it.

- **The slice's three parts are on main since `c67fa03c`.** The goal gate counts 28 planned
  goals, and 12 declarations rest on goals. The four new goals are item 1. The claim
  `queueWorkers` is proved modulo them.
- **Each of the four helper laws is proved**, and part 1 holds no planned goal.
- **Item 2.1 is a finding for the owner.** A budget's cut has two kinds on the crew, and a
  journal's verdicts show neither. One kind leaves the machine at rest with no exit of the root.
- **Item 2.2 answers the coordinator's last ask.** For each goal, the least statement that the
  cut runs at rest do not refute is the goal without `funded`. I keep the premise, and the item
  says why.
- **The budget premise changed its definition during the slice.** The design note's search
  judged it by the journal's verdicts. That reading is too weak, and item 2.3 holds the counts
  again with the tape's reading.
- **The host's `valueJson` is as it was.** The `Deferred` image stands in a writer of its own,
  `cellJson`, on each face. The pinned digest of the recordings did not move (item 9).
- **One generated file is new, and none moved by this seat's hand**: the engine's fixture
  `queue-workers.txt`. The coordinator wrote the semantics report again at the merge, and a
  scratch run at this head gives its bytes (item 8).
- **The keyed lane compares the Queue's cell up to its handles.** It is the first limit of
  item 9.
- **Five files under `harness/truth/session` changed, and `scripts/check-host-protocol.py`.**
  The coordinator accepted the script and three of the five in its second message, and two
  more in its seventh.
- **The rules held.** I edited no file of the Queue's, Semaphore's or Pool's folders, no file
  under `src/Effect4/Machine/`, and not `src/Effect4/Modules/Waiting.lean`. I edited none of the
  coordinator's seven files and no file of the truth lane.

## 1. The planned goals, each with its placement

All four stand in `Test/Dogfood/Scenario/QueueWorkers.lean`, each written with `proof_goal` and
its tag. The evidence status of each is: declared. None is proved. Each has finite controls and
a bounded search (tested; item 2.3).

| Goal | It says | Concept; requirement |
| --- | --- | --- |
| `held_within_fed` | Under every script of a funded run, no job is held more often than the host fed it. | `translation-simulation`; R10 |
| `fed_accounted` | Under every script of host acts, on a funded run at rest, the fed jobs are no more than the held ones. They may be one more where the feeder is gone. | `reactive-scheduling`; R12 |
| `queue_settled` | Under every script of host acts, on a funded run at rest, the queue is settled: the five parts of `Observation.settled`. | `reactive-scheduling`; R12 |
| `releases_once` | Under every script of a funded run, the `released` cell holds no connection twice. | `scope-lifetime-finalization`; R11 |

The statements as compiled share one shape. Here is the first, and the two at rest add two
premises.

```lean
def HeldWithinFed : Prop :=
  ∀ (total fuel : Nat) (b : Api.Built) (moves : List Move),
    Effect4.Api.Author.build (crew total) = .ok b →
    funded (Scenario.play (openedAt fuel b) moves) = true →
    (observe (Scenario.play (openedAt fuel b) moves)).heldWithin = true

-- `FedAccounted` and `QueueSettled` add, before the conclusion:
--   moves.all Move.hostAct = true →
--   atRest (Scenario.play (openedAt fuel b) moves) = true →
```

The placement of each, in the five fields.

| Goal | Concept; property | Question; consumer | Reach | It does not establish | Unlocks |
| --- | --- | --- | --- | --- | --- |
| `held_within_fed` | `translation-simulation`; an instance of the proposed claims `queue-expansion-agrees` and `waiting-request-obligation-preserved` on one program | planned goal `held_within_fed`; consumer: the claim `queueWorkers` | the program `crew`, every job count, every script of the driver's alphabet with its raw rows, every command budget at the compile budget 2000, under `funded`; decisions rows 254 and 275 | that a fed job is ever assigned; the order of two deliveries; fairness; another client; a run that is not funded. It is safety | R10 |
| `fed_accounted` | `reactive-scheduling`; an instance of `waiting-request-obligation-preserved` and `queue-expansion-agrees` | planned goal `fed_accounted`; consumer: `queueWorkers` | the program `crew`, whose callers hold no mask; scripts of host acts (`Move.hostAct`); under `funded` and `atRest`; rows 222 and 275 | that a fed job is ever assigned or finished; anything of a state that is not at rest; the statement under a masked take, where it fails (a red control) | R12, and R10 to R11 through the proposed claim |
| `queue_settled` | `reactive-scheduling`; an instance of `wait-registration-no-gap` with the Queue's profile, and of the delivery clause of `waiting-request-obligation-preserved` | planned goal `queue_settled`; consumer: `queueWorkers` | as `fed_accounted`; rows 221, 223, 238 and 240 | progress: it is an invariant at rest. Not that a waiting worker ever takes, the order of two takers, fairness or starvation freedom. The cell is read up to its handles | R12 |
| `releases_once` | `scope-lifetime-finalization`; an instance of R11's first whole-run clause, "at most once per registration, counted by identity" | planned goal `releases_once`; consumer: `queueWorkers` | the program `crew`, every script of the driver's alphabet, every command budget, under `funded`; DB-07 | the order of the releases; that a release runs; the clause for another program | R11 |

## 2. Findings

### 2.1 A budget's cut has two kinds, and a journal's verdicts show neither

This finding is for the owner. It proposes no change of the machine.

**The session's fact, apart from the scenario** (reading, and tested by the trace below).

- `applyReply` (`src/Effect4/Api/HostSession.lean`) answers `applied` as soon as its call's
  guard is gone. It takes the machine of `steppedBy`. It does not read the step's sufficiency
  flag, which the machine's source calls the step's receipt.
- `advance`, in the same file, reads that flag from `stepDecisionState`. So a control answers
  `progressed` or `frontier`.
- So a journal's verdicts do not show a cut inside a reply application. Only a control reports
  its sufficiency.
- The tape shows it. `tapeFrom` asks `Run.enoughFor` (`src/Effect4/Laws/Run.lean`) of each
  decision through `readsOn`, and it stops at the row (`tapeFrom_stop`,
  `Test/Dogfood/Scenario.lean`).

**The trace** (tested; `cut.out.txt` and `left.out.txt` of the evidence folder).

| Part | Value |
| --- | --- |
| Program | `crew 3`, built by `Api.Author.build` |
| Script | `[running, cancelWaiting, afterWaiting]`: 28 rows. Worker 2 ends job 2, waits, and the host cancels it. The host feeds job 3, and worker 1 ends jobs 1 and 3 |
| Budgets | compile 2000; command 60, and command 120 |
| Verdicts, at both budgets | `ccbpAcbbpAcbbpAccpAcbpAcbpAc`: `c` a control that progressed, `b` a held call, `p` a reply receipt, `A` a reply application. No frontier |
| Stopped row at 60 | row 27 of 28: `apply ⟨⟨1⟩, 10⟩`, the application of worker 1's last reply. Its step closes the pool. The session answers `applied` |
| The machine at the end, at 60 | the root has no exit; the cleanups are `[2, 3]`, so connection 1 is not released; fiber 1 is runnable with no task; the machine is not at rest |
| The machine at the end, at 120 | the root's exit is the success `[[2, 3, 1], 3, 0, none]`; the cleanups are `[2, 3, 1]`; the run is funded |
| The least funded budget | 119. At 118 the run is not funded (a green control pins both) |

**What each budget leaves at the stopped row** (tested; `left.out.txt`). The probe runs the
command loop of the row's answer decision at the run's budget, and it lists the commands that
the loop returns.

| Command budget | Commands that the command loop leaves | The machine at the script's end | At rest |
| --- | --- | --- | --- |
| 60 | `loop 1`, `drainDue` | worker 1 is runnable with no task; the root has no exit | no |
| 80 | `observe 1`, `exitDone 1`, `drainDue`, `drainDue` | no fiber is runnable; every connection is released; the root has no exit | yes |
| 100 | `deliver 0`, `exitDone 1`, `drainDue`, `drainDue` | the root is runnable with no task, and it has no exit | no |
| 116 | `exitDone 1`, `drainDue`, `drainDue` | the root has its exit; the observation and the machine's view are the funded run's | yes |
| 117 | `drainDue`, `drainDue` | the same | yes |
| 118 | `drainDue` | the same | yes |
| 119 | none: the run is funded | the root has its exit | yes |

**Which machine function drops the work.** It is `stepDecisionState`
(`src/Effect4/Machine/Fibers.lean`), in its arm of an answer decision. The command loop
`driveState` returns the commands that the fuel left. The helper `stepDecisionState.loop` keeps
the loop's machine and the flag `settled`, and it does not keep those commands (reading; the
table above is its test). `fireStep`, in the same file, has the same shape for a dispatcher's
task, and it skips the later tasks of the drained snapshot (reading). No run of this slice
reaches a cut of `fireStep` at rest.

**The two kinds.**

1. The cut leaves a fiber runnable with no task (the budgets 60 and 100). The run is not at
   rest. The battery's run is `starved`.
2. The cut loses the work, and the machine is at rest with no exit of the root (the budget
   80). The battery's run is `dropped`. No continuation that I ran gives the root an exit or
   moves the machine's view (tested, bounded). `after.out.txt` holds seven continuations by a
   host's acts, with a cancellation of the root among them. `continue.out.txt` holds every
   script of 29 moves up to length 3: 25,260 scripts, with raw controls and raw rows.

The budgets 115 to 118 are a border case of the machine's flag, and no third kind. The step
did its whole work, and at 116 to 118 the commands that it left are drains and one `exitDone`.

**The sweep** (tested, finite; `sweep.out.txt`). It plays the battery's 22 scripts on the crew
at each command budget from 1 to 160.

| Count | Runs |
| --- | --- |
| Funded | 1,937 |
| Not funded | 1,583 |
| Not funded and at rest | 23 |
| Of the 23, with no exit of the root | 9 |

- The 9 are two scripts that close the pool after a cancellation, each at 79 to 81. The third
  is the whole run `closed`, at 113 to 115.
- In the other 14 the root has its exit. They are the budgets just below a least funded one:
  115 to 118, 149 to 152 and 132 to 133. A probe compared ten of them with the funded run, and
  the observation and the machine's view are equal in each.
- Each script is funded from its least funded budget upward. That budget is 60 for 18 scripts.
  It is 119, 119, 134 and 153 for the four that close the pool.
- No observation of a planned goal fails on a funded run. None fails on one of the 23.

**Which open part of the semantics registry this is evidence for.** It is R12's open part
with the proposed claims `driver-continuation-split` and `driver-suspension-keeps-typed`
(decisions rows 84 and 226). The part says that a retained driver suspension keeps the commands.
Today the session retains none of them at a reply application. So the run `dropped`, continued
by a host's acts, is not the one run at a larger budget. The first has no exit of the root, and
the second has one. The same evidence serves `embedded-budget-sufficient`. At one unit below
the least budget the work of the pool's close is whole. At 39 units below, it is lost.

**The working note's paragraph** (the coordinator's ninth message). The paragraph of
`docs/research/2026-10-06-whole-run-law-prep.md` on this finding agrees with my runs in each
number and each budget. Two of its sentences say more than the runs.

- "So nothing will run the root." My runs are bounded: 25,260 continuations of the run
  `dropped`, and none gives the root an exit. No theorem says it. Two docstrings of mine said
  the same, and the head's last code commit corrects them.
- "The session does not show it." That holds for a reply application. A control shows its cut
  as the verdict `frontier`. The script `cancelled-root` has one at each of the seven budgets
  that I read, from 60 to 133.

**What goes to the owner.** Whether a reply application should report its sufficiency is a
choice of the session's observation. Whether the machine keeps the commands is the other
choice. I did not edit `src/Effect4/Api/HostSession.lean`.

### 2.2 For each goal, the least statement that the cut runs at rest do not refute

The coordinator's ninth message asks for it. The 23 runs of the sweep are not funded, they are
at rest, their scripts hold host acts only, and each keeps all four observations. So they do not
refute a goal whose premise `funded` is dropped.

| Goal | The least statement that no run of this slice refutes | The runs that are not funded and bear on it |
| --- | --- | --- |
| `held_within_fed` | the goal without `funded`: for every job count, command budget and script, no job is held more often than the host fed it | 1,583 of the sweep; 62,640 of the search's part D; 318 cuts of one row |
| `releases_once` | the goal without `funded` | the same |
| `fed_accounted` | the goal without `funded`, with its two other premises: a script of host acts, and a machine at rest | the 23 of the sweep; 10,440 of part D |
| `queue_settled` | the same form | the same |

- `atRest` cannot be dropped. The run `starved` is not at rest, and it is not settled. A funded
  run between a feed's application and its flush is not at rest either. Its buffer holds a job
  beside two waiting takers (item 2.4), so it is not settled.
- **I keep `funded` in all four statements.** Three reasons follow.

1. **The runs at rest are weak tests of the two goals at rest.** In 9 of the 23 the whole crew
   is gone. In the other 14 the step did its whole work.
2. **One budget for a whole run does not reach the middle rows.** Each row but the pool's
   close needs at most 60, and the first flush needs 60 (tested; `rows.out.txt`). So a command
   budget cuts a middle row only where it also cuts the first flush.
3. **`funded` is the premise under which a proof route stands today.** `funded_replays` makes
   the run's machine the raw replay's, where the law graph states its invariants. One step
   after a stopped row has a law (`step_takes_decision`, `Test/Dogfood/Scenario.lean`). No law
   relates a later machine to a replay.

**A probe outside the goals' domain: a budget for one row** (tested, finite; `onerow.out.txt`).
The session takes a fuel at each command, and a `Run` fixes one for all. The probe plays a
script at the battery's budget and one row at each smaller fuel. It reads nine middle rows:
applications and flushes of a feed, of a worker's reply and of a cancellation.

- 318 cuts in all. After none is the machine at rest. So none bears on the two goals at rest.
- `heldWithin` and `releasedOnce` hold after each of the 318.
- Two later flushes at the battery's fuel leave 316 of them not at rest. Two are repaired, at
  the fuels 5 and 6 of one flush.

So the second kind of cut is the pool's close alone, in every run of this slice. In the run
that `left.out.txt` reads, its first lost command is an exit observer, and no fiber's own loop.

**What a later slice can try.** The two goals over every script read as invariants of each
command, which a cut keeps. Their form without `funded` is the candidate. For the two goals at
rest, the evidence does not decide between `funded` and a weaker premise.

### 2.3 The corrected evidence: the search with the tape's reading

The design note's first search judged `funded` by the journal's verdicts: no row with the
verdict frontier. Item 2.1 shows that this reading is too weak. The note's addendum says so
where its counts stand. The search ran again with the tape's reading (tested, a finite probe;
`search.lean.txt` and `search.out.txt`). A state of the search is one script from a start state.

| Part | Alphabet and length | Start states | States | Funded | At rest, judged for the two goals at rest |
| --- | --- | --- | --- | --- | --- |
| A | 17 host moves, to length 4 | six, at 3 jobs, command budget 1000 | 6 × 88,741 | all | 383,927 |
| B | 18 moves with the start, to length 4 | the fresh run at 1, 2 and 3 jobs | 3 × 111,151 | all | 67,224 |
| C | 28 moves with raw rows, to length 3 | the six of part A | 6 × 22,765 | all | not judged: the scripts hold raw rows |
| D | 17 host moves, to length 3 | three states whose last reply application is cut, at the command budgets 60, 80, 100 and 118 | 12 × 5,220 | none | 10,440 are at rest |

- No counterexample of the four statements: each list `bad` of the output is empty.
- No observation of a goal fails on a state of part D either: each list `cutBad` is empty.
- The output's first line compares the search's row-by-row reading with `funded` itself on four
  samples. They agree.
- The evidence is bounded. It covers one program, three job counts, and scripts of at most four
  moves beyond a start state.

### 2.4 A reply application does not drain a posted helper

It is a fact of the machine that shapes every script (tested; the design note's section 2).
The Queue delivers each signal by a posted helper (decisions rows 238 and 240). The session's
reply application runs the fiber that it resumes. It leaves a helper that this fiber posted as
posted work. The exact moves of the first feed:

1. `.start`, then `.flush`: both workers wait at the empty queue.
2. `.hold feederCall`, then `.receive feederCall (ok (.nat 1))`.
3. `.apply feederCall`. After it the buffer holds job 1, and both takers are still enrolled.
   The helper's fiber 4 is runnable, and the feeder's owner 3 is armed.
4. `.flush`. Worker 1 takes job 1, notes it and calls the host.

So a flush follows each reply application of a script. A host does the same by itself: it lets
every dispatcher run after each act but the root's start.

### 2.5 Three smaller findings

- **The least command budget of each row** (tested; `rows.out.txt`). On the whole run the
  root's start needs 51 and the first flush 60. A feed's application needs 28 or 33, and its
  flush 1 or 43. A worker's reply application needs 43 to 55, and a crew member's cancellation
  26 to 47. The application that closes the pool needs 119 or 153, and the root's cancellation
  needs 134. The answer is monotone in the budget at each row.
- **Each faulty crew builds, and its printed TypeScript module type-checks.** A fault changes
  one part of the crew, and the checker types each of the seven. The host lane performs the
  crew and six faulty ones. tsgo 7.0.0-dev.20260629.1 accepts the module of each.
- **Two runs differ only by a handle's identity.** They are `parked` and `rewaiting` (item 9).

## 3. Base, head and commits

Branch `seat/workq`, in the worktree `/Users/pooks/Dev/lean4-effect4-qsteps`. The dispatch's
base was `76a6f215`. I moved the branch to main `9018a2aa` before the first edit under
`harness/`, as the coordinator's first message said.

| Commit | What it holds |
| --- | --- |
| `5bebd779` | the design note |
| `e40c087a` | part 1: the two helpers. Merged on main as `cb559bba` |
| `03c0e371` | part 2: the scenario, with `funded`, `funded_replays` and `atRest` in the support |
| `939fb0f7` | the merge of main `cb559bba`, as the coordinator's sixth message asked. Git merged `Test/All.lean` with no conflict |
| `a690260e` | the run `dropped` and its red control; the evidence of item 2.1 |
| `e1e3959c` | part 3: the faces, the engine's fixture and the host runs. Merged on main as `c67fa03c`, with the three commits before it |
| `2f0ca55e` | two docstrings say what the probes tested; two more evidence files |
| `33202664` | the merge of main `c67fa03c`, as the coordinator's ninth message asked. No file changed on both sides |
| the receipt's commit | this document, and four more evidence files with their index |

The head that holds the code is `33202664`. It differs from main `c67fa03c` by the two
docstrings of `2f0ca55e` and by documents. The wide runs of item 5 ran there.

## 4. Changed files

| File | What changed |
| --- | --- |
| `src/Effect4/Program/Authoring/Ascribe.lean` (new) | `ascribe` and `ascribeFields`: a term at a declared type, moved from `Test/Dogfood/P3WorkerQueue.lean` with its record form unchanged. It opens as decisions row 200 says |
| `src/Effect4/Laws/Modules/Ascribe.lean` (new) | `ascribeFields_normal`, `ascribe_check`, `types_ascribe`, `ascribe_untyped`, `reads_ascribe` |
| `src/Effect4/Laws/Program/Authoring/Ascribe.lean` (new) | `ascribe_scoped` |
| `src/Effect4.lean`, `src/Effect4/Laws.lean` | one import and two imports, each after the mask's module or after `Effect4.Laws.Modules.Checking` |
| `Test/Program/Ascribe.lean` (new) | the helper's battery: five groups of controls, six instances of the laws, the axiom pins and the plan status pin |
| `Test/All.lean` | two imports: `Test.Program.Ascribe` after `Test.Program.FoldHygiene`, and `Test.Dogfood.Scenario.QueueWorkers` after `Test.Dogfood.Scenario.Workers` |
| `Test/Dogfood/Scenario.lean` | section 6: the one `note`, with the collision's control. A new subsection: `openedOf`, `tapeOf`, `funded`, `funded_replays` and `atRest`. One import |
| `Test/Dogfood/P3WorkerQueue.lean` | its `ascribe` is gone, and it imports the new module. Its stage does not move |
| `Test/Dogfood/Scenario/Workers.lean`, `Atomic.lean`, `Timeout.lean` | each local `note` is gone; the last two import `ascribe` from its new home |
| `Test/Dogfood/Scenario/QueueWorkers.lean` (new) | the scenario: the program, the scripts, the observation, four planned goals, the claim, 31 named runs, 35 controls and the record with its gate |
| `Test/Dogfood/Scenario/Tape.lean` | its own `openedOf` moved to the support; one more entry of `taken`; one import |
| `Test/Dogfood/Scenario/Lowered.lean` | one more entry of `committed` |
| `Test/Dogfood/Scenario/Faces.lean` | the crew prints and reads back at two job counts, with the red control of the comparison |
| `Test/Dogfood/README.md` | the note's sentence; the scenario's row; the paragraph on `funded`; "five records"; the lane's limit in the section "The host runs" |
| `ocaml/engine/test/scenarios/queue-workers.txt` (new, generated) | the fixture of three runs |
| `harness/truth/session/Keyed.lean` | the wire `queueWorkers`; the writer `cellJson` with three guards; `emitRun` keeps out a run that is not funded |
| `harness/truth/session/keyed-recorder.ts` | one body under a choice, `imageOf`: `valueJson` without a `Deferred` image, `cellJson` with it |
| `harness/truth/session/run-keyed.ts` | the cells reader calls `cellJson`: one call and one import |
| `harness/truth/session/keyed-observation.ts` | the scenario's entries, with two small helpers |
| `harness/truth/session/keyed-protocol.test.ts` | one test of the two writers on a `Deferred` |
| `scripts/check-host-protocol.py` | the battery's name in the list `SCENARIOS` |
| `docs/ARCHITECTURE.md`, `tools/Tools/ArchitectureRoles.lean` | three rows of the map; one row of the role register, a count and two role texts |
| `docs/research/2026-10-06-seat-WORKQ-design.md` (new) | the design note, with an addendum of two corrections |
| `docs/research/2026-10-06-seat-workq-evidence/` (new) | eighteen files and their index |
| this receipt (new) | — |

## 5. Commands and results

Every Lean, Lake and `make` command ran through `/Users/pooks/Dev/lean4-effect4/scratch/lean-slot.sh`.
Each `make` call carried `-o build -o ts/eff/node_modules -o harness/truth/node_modules`. The
table writes the slot as `SLOT` and those flags as `FLAGS`. The runs are at the head `33202664`.
The same list passed at `2f0ca55e` and at `e1e3959c`, before the second merge.

| Command | Result |
| --- | --- |
| `SLOT lake build` | `Build completed successfully (1032 jobs).` |
| `SLOT make FLAGS gen-fixtures` | `PASS generate: requested producers ran in dependency order`; `git status --short` gives no line after it |
| `SLOT make FLAGS corpus` | `lake build Drivers.Corpus`, `Build completed successfully (157 jobs).` The trace did not change, so the corpus was not cut again. No tracked file moved |
| `E4_LEAN_CORPUS=…/.lake/corpus opam exec --switch=effect4 -- dune build --root …/ocaml` | exit 0 |
| `E4_LEAN_CORPUS=…/.lake/corpus opam exec --switch=effect4 -- dune test --force engine --root …/ocaml` | `== ALL PASS: 0 failure(s) ==`; 1907 lines open with `PASS`, and none with `FAIL` |
| `SLOT make FLAGS check-cases` | at `e1e3959c`: `conform cases: PASS, exit 0; .lake/conform/cases.json`. At the head: `make: Nothing to be done for 'check-cases'.` |
| `SLOT make FLAGS check-docs` | `PASS check-docs: every path, link, citation and make target in 76 documents resolves` |
| `SLOT make FLAGS check-host-protocol` | on the lane's present inputs, before the second merge: `PASS host-protocol: fresh projections, typed host programs, keyed replay and negative controls; the scenarios' scripts on their printed modules`. At the head: `make: Nothing to be done for 'check-host-protocol'.` |
| `SLOT lake exe semantics-report <a scratch folder>`, then `diff` against `generated/semantics.md` | no line differs |
| `python3 scripts/check-language.py --show` on this receipt, the design note, the evidence index and `Test/Dogfood/README.md` | no finding |

- `…` stands for `/Users/pooks/Dev/lean4-effect4-qsteps`. Each `dune` command ran with `--root`
  at the `ocaml/` folder: dune enters that folder.
- Each `dune test` read this worktree's corpus folder. Its log says
  `/Users/pooks/Dev/lean4-effect4-qsteps/.lake/corpus: 408 files, 408 decoded`.
- The engine's tests had 1816 passing lines at `e1e3959c`, and main `cb559bba` had 1785. The
  31 more are the new fixture's. The other 91 of the head's 1907 came with the second merge.
- A `make` target that says "Nothing to be done" has a marker that is newer than each of its
  inputs. The second merge and the last code commit changed no input of those two checks after
  their last run.

### The gate lines of the default build

```text
Effect4 library-root gate: 178 API/utility modules, 319 Laws-only modules; every library source is reachable; Effect4 never reaches Laws
Effect4 module and axiom gate: checked 782 modules and 91031 declarations; … semantic/test axioms are [propext, Quot.sound]; exact implementation boundary (17 module(s), 23 declaration(s)) additionally allows Classical.choice
Effect4 goal gate: 28 planned goal(s), each a theorem whose body is `sorry` outside the Effect4 root; 12 declaration(s) rest on goals; no other declaration reaches sorryAx
proof style: 1911 recorded uses and 52 recorded unread commands in 1161 entries
```

The first three lines are main's at `c67fa03c`, as the coordinator's ninth message gives them.
The proof style line is from `SLOT lake env lean Test/Audit/ProofStyle.lean`: the build took
that module from the cache and gave no line of it.

Against main `cb559bba`, the slice's parts 2 and 3 add one module, four planned goals and one
declaration that rests on goals. I measured them at `e1e3959c`: 781 modules, 91009
declarations, 28 goals and 12.

### The keyed lane's lines

```text
PASS keyed host: 57 actual rc.112 runs; 52 admitted printed programs
PASS keyed scenarios: 72 scripts performed on actual rc.112 in 267 runs: each with no reader, with its readers, and with each reader alone; 13 scripts with no host run
 55 pass
 0 fail
PASS keyed differential: 57 runs, 52 programs, 30 controls; exact exits and keyed applications
PASS keyed scenarios on effect 4.0.0-rc.112 under bun 1.4.2: … queue-workers 25 scripts (7 entries measured by the host, 8 through a reader, 2 of them zero by the run's own wait in 21 scripts; no entry waits); 13 scripts with no host run; 44 red controls
```

The lane type-checks its sources and each printed module with tsgo 7.0.0-dev.20260629.1, the
pinned `@typescript/native-preview`. The earlier scenarios' lines are as before the slice: the
check's table rows of the four are the same bytes.

### Narrow builds along the way

Each step had a narrow build before its commit.

- Part 1: the three `Ascribe` modules with their battery, and the four earlier scenarios after
  the shared `note`.
- Parts 2 and 3: `Test.Dogfood.Scenario.QueueWorkers` with `Tape`, `Lowered`, `Faces` and
  `Gate`. The last one had 483 jobs and exit 0.

### Not run

`make check-gen`, `make check-slow`, `make check-corpus`, `make check-target`, the release
ledger, the conservativity script and `make gen-semantics`: the brief's list. `make check` and
`make check-full` are not run either.

### Red or stale for a reason outside the slice

Nothing is red at the head. Two things were, and both are closed.

- `python3 scripts/check-language.py --show Test/Dogfood/README.md` reported one sentence of 43
  words, in the paragraph on `PartReach`. It stood at `9018a2aa` too. The coordinator split it
  at the merge `c67fa03c`.
- `make check-host-protocol` first failed on a missing build output of `Tools.GeneratedStamp`.
  One `lake build Tools.HostProtocol` repaired it. It was a state of the worktree, and no fault
  of a file.

## 6. Axiom output and plan status

```text
'Effect4.Modules.types_ascribe' depends on axioms: [propext, Quot.sound]
'Effect4.Modules.ascribe_untyped' depends on axioms: [propext, Quot.sound]
'Effect4.Modules.reads_ascribe' depends on axioms: [propext]
'Effect4.Program.Authoring.ascribe_scoped' depends on axioms: [propext, Quot.sound]
'Test.Dogfood.Scenario.funded_replays' depends on axioms: [propext, Quot.sound]
'Test.Dogfood.Scenario.QueueWorkers.queueWorkers' depends on axioms: [propext, sorryAx, Quot.sound]

Effect4.Modules.types_ascribe: proved; nearest []; 0 lemmas, 0 definitions
Effect4.Modules.ascribe_untyped: proved; nearest []; 0 lemmas, 0 definitions
Effect4.Modules.reads_ascribe: proved; nearest []; 0 lemmas, 0 definitions
Effect4.Program.Authoring.ascribe_scoped: proved; nearest []; 0 lemmas, 0 definitions
Test.Dogfood.Scenario.funded_replays: proved; nearest []; 0 lemmas, 0 definitions
Test.Dogfood.Scenario.QueueWorkers.queueWorkers: modulo [fed_accounted, held_within_fed, queue_settled, releases_once]; nearest []; 0 lemmas, 0 definitions
next goals: 4
```

- The first five axiom lines and the first four status lines are pinned in the batteries with
  `#guard_msgs` (`Test/Program/Ascribe.lean`, `Test/Dogfood/Scenario.lean`). The others are
  from a scratch file. The status line of the claim is shortened here: Lean gives each goal's
  full name.
- The claim reaches `sorryAx` through its four goals' bodies only. The goal gate says so for
  the whole tree.
- `#scenario_gate` passes for the record: no finding names `queue-workers`. Its red control is
  the record `wrongTop`, whose six findings the battery pins.

## 7. Evidence, and each landed theorem's placement

### What is proved, what is tested, and what is read

| Claim | Evidence |
| --- | --- |
| The four helper laws, and `funded_replays` | proved |
| `queueWorkers` | proved modulo four planned goals. It is not proved |
| The four goals | declared |
| The scenario's 35 controls on 31 named runs: 18 green and 17 red | tested: finite runs on the Lean machine |
| The helper's five groups of controls, and the collision's control | tested: finite runs |
| The search and the sweep | tested: bounded, on the Lean machine |
| The engine's three runs, on both instances, the view at each of 17, 14 and 6 positions | tested: finite runs of the generated OCaml engine |
| The host's 25 scripts on the printed module | tested, host-only: finite runs on effect 4.0.0-rc.112 under bun 1.4.2 |
| Part 1 moves no generated file | reproduced: the engine's writer run into a scratch folder, and the keyed lane's scenario fixtures before and after, byte for byte |
| The fixtures at the head | reproduced: `make gen-fixtures` wrote no byte |
| `applyReply` reads no sufficiency flag; `stepDecisionState.loop` keeps no leftover command | reading, with the trace as its test |

### The landed theorems

The statements as compiled.

```lean
theorem types_ascribe {e : TermSrc} {S T : Ty} (canonical : T.normalize = T)
    (formed : Formation.check (Formation.sites false [] (.record (ascribeFields T))) = none)
    (he : Types sig e env path types true S) (below : Ty.subN S T = true) :
    TypesEach sig (ascribe T e) env path types T

theorem ascribe_untyped {e : TermSrc} {S T : Ty} (he : Types sig e env path types true S)
    (above : Ty.subN S T = false) (const : Bool) (U : Ty) :
    ¬ Types sig (ascribe T e) env path types const U

theorem reads_ascribe (T : Ty) {e : TermSrc} {vals : List Val} {v : Val}
    (he : Reads e env path vals v) : Reads (ascribe T e) env path vals v

theorem ascribe_scoped (ty : Ty) {e : TermSrc} (h : e.Scoped) : (ascribe ty e).Scoped

theorem funded_replays (s : Run) (recorded : Run.Reached s) (h : funded s = true) :
    s.machine =
      Run.machineOf (Run.replayFrom s.built.program s.built.table s.budget.fuel (tapeOf s)
        (Api.load s.built.program s.budget.compileFuel))
```

| Theorem | Concept; property | Question; consumer | Reach | It does not establish | Unlocks |
| --- | --- | --- | --- | --- | --- |
| `types_ascribe` (`src/Effect4/Laws/Modules/Ascribe.lean`) | `store-typing`; a module's typing statements, by the registry's default for the file | a helper of R4's typing nodes; consumer: a cell made at a declared type, the scenarios' logs first, then the public `make` of a later module | the checker's `argTy` at every scope and signature; a declared type in normal form whose one-field declaration is formed; the term's type at the record's own flag is below it | program admission; a run; a target's type; `Ref.make<A>` | R4 |
| `ascribe_untyped` (the same file) | the same | the same; it is the half that makes the form no cast | the same scope; a term whose type is not below the declared type | the same | R4 |
| `reads_ascribe` (the same file) | `translation-simulation`; a helper of a module expansion's reading | a step of the proposed claim `queue-expansion-agrees`; consumer: the attempt law of a caller that makes its cell at a declared type | one evaluation of the form's tree, at every scope | typing; a store step; a model's step | R10 |
| `ascribe_scoped` (`src/Effect4/Laws/Program/Authoring/Ascribe.lean`) | `initial-algebras-folds`; the claim `operation-data-scoped` at the authoring surface | a step of that claim; consumer: the scope proof of a client that writes a term at a declared type | every scoped term | typing; behaviour | R4 |
| `funded_replays` (`Test/Dogfood/Scenario.lean`) | `translation-simulation`; the claim `run-tape-replay` at a recorded run | one application of `tape_replays` at the run's fresh open, with `Run.journal_replays`; consumer: each statement over runs that takes `funded`, the four goals first | any run that was opened and then played (`Run.Reached`), under `funded` | that a run is funded: the open claim `embedded-budget-sufficient`; equal session ledgers; anything of a run with a stopped row | R8, and the budget premise of R10 to R12 |
| `queueWorkers` (`Test/Dogfood/Scenario/QueueWorkers.lean`) | `translation-simulation`; the scenario's claim | assembles seven clauses: three theorems of the support and the four goals; consumer: the scenario's gate | as its clauses | the Queue's law of a whole run; fairness; starvation freedom; liveness. It is proved modulo four goals | R10 to R12 |

The four laws of `ascribe` stand in two files. The role register puts the scope laws of the
authoring surface below the judgments `Types` and `Reads`. The coordinator's fifth message keeps
them so, and each file's header says the reason.

### The red controls: what each plants, and which reading fails

Each red control of the scenario compares the changed observation itself. So it is red for
its stated reason, which the last column gives.

| Clause or law | Run | What is planted | The reading that shows it |
| --- | --- | --- | --- |
| receipt | `duplicate` | a second reply at one key | the session refuses the row as `pendingReply`, and the observation stays |
| selection | `applied-1-2`, `applied-2-1` | the two orders of two reply applications | the buffered job and the pending job go to different workers |
| selection | `crossed` | worker 1's reply under worker 2's key | the session refuses the row as `callOrder` |
| selection | `unreceived` | a reply application with no stored reply | the session refuses the row as `noCall` |
| retirement | `cancelled-root` | the root's cancellation | every held call is retired, and the pool closes |
| once | `kept` | a take that leaves its job in the buffer | `heldWithin` fails: job 1 is assigned twice, and it is still buffered |
| accounted | `masked` | a take under `uninterruptible` | `accounted` fails at rest on a funded run: the cancelled worker takes job 3 and exits before its note |
| accounted | `taken-back` | an offer's withdrawal that drops the newest buffered job | `accounted` fails: four fed jobs, two held |
| settled | `unwithdrawn` | a take with no withdrawal | `settled` fails at rest on a funded run: two takers, one live worker, and job 3 buffered beside them |
| settled | `silent` | a withdrawal that posts no wake | `settled` fails at rest on a funded run: job 1 is buffered beside a waiting taker |
| settled | `stays` | an offer with no withdrawal | `settled` fails at rest on a funded run: an offer pends, and the feeder is gone |
| settled | `starved` | a command budget of 60 | the run is not funded, and `settled` fails. The journal is the funded run's |
| settled | `starved` | the same | no frontier verdict; the verdicts are the funded run's; the stopped row is a reply application |
| cleanup | `twice` | a second registration of each release | `releasedOnce` fails: each connection is released twice |
| journal | `closed` | a journal with one reply application erased | the replay reaches another observation |
| funded | `starved` | a command budget of 60 | the machine's view is not the raw replay of the tape |
| funded | `dropped` | a command budget of 80 | the machine is at rest, the root has no exit, and the view is not the raw replay of the tape. The journal and the verdicts are the funded run's |

The helper's red controls are in `Test/Program/Ascribe.lean`. A bare `nil` cell refuses its
first append as `resultNotSubtype`. A wrong element is refused as `binderTerm`. A tagged string
refuses a write as `requestNotSubtype`. A wrong declared type is refused at `recordTerm`. The
collision's control is in `Test/Dogfood/Scenario.lean`: the fixed binder answers `[100, 1]`
where the minted one answers `[100, 2]`.

## 8. Each generated file that moved

| File | Part | What happened |
| --- | --- | --- |
| none | 1 | The measure of the brief's point 3: no generated file moves (reproduced; the design note's section 7). A minted binder and a fixed one give one tree by authoring elaboration, where no name collides |
| `ocaml/engine/test/scenarios/queue-workers.txt` | 3 | New: 501,972 bytes, three runs. `make gen-fixtures` wrote it, and it wrote no other byte |
| `generated/semantics.md` | the merge `c67fa03c` | The coordinator wrote it again. This seat did not write it |

- **The fixture is large.** A fixture writes its program's canonical bytes once for each run,
  and the crew's program has about 79,000 bytes. So the lane takes three runs. A fixture that
  writes one program for several runs is a candidate. It is not built: it changes the fixture's
  format and the engine's test.
- **The report at the head** (reproduced). One run of the report tool wrote into a scratch
  folder at `33202664`. `diff` finds no line that differs from the committed file.
- **What the report gained** (tested at `e1e3959c`, before the coordinator wrote it;
  `semantics-report.diff.txt`). The report's root `Test/Dogfood/Scenario/Tape.lean` imports the
  new battery since part 3. So the nodes came with no edit of the semantics registry.

| Requirement | Nodes that the report gained |
| --- | --- |
| R8 | `funded_replays` (proved) |
| R10 | `held_within_fed` (goal), `queueWorkers` (modulo) |
| R11 | `QueueWorkers.releases_once` (goal). The earlier `releases_once` is named `Workers.releases_once` there |
| R12 | `fed_accounted` (goal), `queue_settled` (goal) |

The line "Next goals" grew from 10 to 14. Two goals now share the short name `releases_once`,
one in each scenario's namespace, and the report names both with their namespace.

## 9. The runs on the OCaml engine and on the TypeScript module, and their limits

**The limits, first.**

1. **The lane compares the Queue's private cell up to its handles.** A `Deferred` handle has
   one image on both faces, `{"handle": "deferred"}`. So the lane compares how many requests
   stand in the cell and each request's other fields. It does not compare which handle stands
   where.
2. **Two cells of the scenario differ only by a handle's identity**: the runs `parked` and
   `rewaiting`. After `parked` the earliest waiting taker is worker 1's request. After
   `rewaiting` it is worker 2's. The cells differ on the Lean machine, and their images are
   equal (a green control pins both). The runs `fed` and `rewaiting-fed` show the difference in
   the assignment, which the lane does compare.
3. **Six of the 31 scripts have no host run.** A forged reply is no act of a host. Three
   scripts give another row where the machine has work for a flush. Two run at a budget that
   cuts a step.
4. **The engine holds no session.** Its three runs compare the machine's view at each position
   of a tape. The session's part of the observation has no engine run.
5. **Each run is finite.** A host run establishes no agreement for another script, no host
   adequacy and no liveness.

**The writers** (the coordinator's condition 1).

| Face | Writer | Who calls it |
| --- | --- | --- |
| Lean | `cellJson` (`harness/truth/session/Keyed.lean`) | the wire `queueWorkers`, for its one entry `queue`. Every other entry, and every other wire, keeps `valJson` |
| Host | `cellJson` (`harness/truth/session/keyed-recorder.ts`) | the cells reader alone (`run-keyed.ts`). A call's request and an exit keep `valueJson` |

- `valueJson` is its base behaviour: a `Deferred` is outside the transport profile. One test
  pins both writers on the host, and three guards pin both on the Lean face.
- A `Deferred` in any other compared value is red. The host's cells reader writes the image
  with no identity, and Lean's `valJson` writes a number.
- This differs from the design note's section 8, which put the case into `valueJson`. The
  coordinator accepted the change in its seventh message.

**The digest** (condition 2). The pinned digest of the four fixture families' recordings is
that of `cases.json`:
`dca8595e99e85654328ad1560114f1885ff7efc2c132cb1b54c4e786757626c3`. It is the same before the
harness edits, after the first form, and after the form with `cellJson`.

**The stronger form, a candidate that is not built** (the coordinator's third message). Both
faces number a handle in the order of its first sight, as the truth lane does for fibers
(decisions row 274). The lane would then compare which handle stands where. Row 275, point 6,
names the same gap for a `Ref` and a `Deferred` on the truth lane.

**What the host measures** (`host-evidence.md` of the evidence folder).

| Source | Entries |
| --- | --- |
| The host by itself | the fed jobs, the reply receipts, the reply applications, the retired calls, the root's exit, the live calls, the stored replies |
| The cells reader | the assignment, the queue's cell, the opened connections, the released connections, the count of finished jobs |
| The sleeps reader | the timers |
| The dispatchers reader | the runnable fibers and the armed owners, as a count of zero. In 21 of the 25 scripts the run's own wait gives the zero |

No entry waits. The lane performs each script with no reader, with its readers and with each
reader alone: 100 runs of the 267 are this scenario's.

## 10. What the scenario needs from the Queue's law of a whole run

The list is the four goals' own premises, as each docstring gives them, and nothing else. The
last column gives the need's row in the coordinator's working note
(`docs/research/2026-10-06-whole-run-law-prep.md`).

| # | The need | Goals | Where it stands today | The note's row |
| --- | --- | --- | --- | --- |
| 1 | In a funded run each step of the queue's cell starts at a cell that encodes a state of the first profile, for a request that keeps `Requested`. The attempt laws then give the model's reply and next state | within, accounted, settled | the attempt laws are proved for one step (`take_attempt`, `offer_attempt`, `poll_attempt`, the two withdrawals; `src/Effect4/Laws/Modules/Queue/Ops.lean`). Their premise at a reached machine is open | layer 1, the cell's invariant |
| 2 | No other step writes the queue's cell, and only a worker's note writes `assigned` | within, accounted, settled | open. It is a fact of the program `crew` | "the cell is written only by the module" |
| 3 | A take that exits with a job enters its caller's continuation once with that job | within | open | layer 2, a call's lifetime |
| 4 | A request's end is one of two. A take commits in its own step, or its interrupted wait runs its withdrawal before its fiber exits, and the withdrawal consumes nothing. An offer is accepted by a step, or its interrupted wait withdraws what is still pending (row 222) | accounted, settled | open; the Queue's acceptance traces (`Test/Program/QueueTraces.lean`) and this battery's cancellations are its finite controls | layer 2 |
| 5 | At rest no worker stands between its take's commit and its note. Both run in one task, and no interruption is taken between them, because the caller holds no mask | accounted | open. The red control `masked` shows the premise | the mask's row |
| 6 | Each posted helper runs once. It resolves its hint, and the request that awaits the hint runs its next attempt inside the helper's task (rows 238 and 240). So at rest no posted signal is outstanding | settled | open | "one law for an await and its notification across commands" |
| 7 | The model's run invariant holds along the run's steps: the first profile, the buffer's bound, and `quiet` at the signalled requests | settled | proved for the model alone (`first_run_inv`, `src/Effect4/Laws/Modules/Queue/Invariant.lean`). Its relation to a run is open | layer 1 |
| 8 | R11's first whole-run clause for the crew's three scopes, with one frame fact: a withdrawal writes the queue's cell and no scope | releases_once | open (`Effect4.Scope.close_twice` is the scope's own law) | "a finalizer runs at most once for a registration, along a run" |

Three premises stand in the statements themselves.

- **The budget**: `funded`. The proposed claim `embedded-budget-sufficient` is to supply it from
  a program's own bound. Item 2.1 says what a run without it can look like.
- **The mask**: the program is `crew`. Each worker takes, and the feeder offers, outside every
  mask.
- **Rest**, for the two goals about a state between two acts of a host: `atRest`, on a script of
  host acts.

One fact of the machine shapes the law's form (item 2.4). A reply application does not drain a
posted helper. So a delivery crosses two commands, the application and the flush after it. A
statement "at rest" reads the state after that flush.

The scenario needs no fairness, no starvation freedom and no liveness from the law, and it
states none.

## 11. The general declarations of the scenario support

The coordinator's fifth message asks for each declaration of `Test/Dogfood/Scenario.lean` that
is a general fact of `Run` and the runner's rows and names no scenario. I moved none. A later
slice moves them into the law graph beside `play_controls_eq_replay`
(`src/Effect4/Laws/Run.lean`).

**The tape, and what the coordinator named.**

| Declaration | Kind | What it needs |
| --- | --- | --- |
| `MachineView`, `machineViewOf`, `machineView` | a structure and two readers | `Api.Machine`, `awaits`, `Api.runnableFibers` |
| `Position` | a structure | `Api.Decision`, `Run` |
| `replyDecision` | a definition | `Reply` |
| `decisionOf` | a definition | `Command`, `Phase`, `readReply`, `replyDecision` |
| `readsOn` | a definition | `Run.enoughFor` |
| `tapeFrom` | a definition | `Api.Runner.result`, `decisionOf`, `readsOn`, `Position` |
| `TapeReplays`, `tape_replays` | a proposition and its theorem (R8) | `tapeFrom`, `Run.replayFrom`, `Run.machineOf`, and the steps below |
| `preflight_replyDecision`, `applyReply_applied_machine`, `applyReply_ends` | three steps over a session | `replyDecision`, `steppedBy`. They name no `Run` |
| `step_keeps_machine`, `step_takes_decision` | two steps over a run's row | `decisionOf`, `steppedBy` |
| `tapeFrom_frontier`, `tapeFrom_skip`, `tapeFrom_take`, `tapeFrom_stop` | the four equations of `tapeFrom` | `tapeFrom`, `decisionOf`, `readsOn` |
| `tapeFrom_append`, `tapeFrom_cut`, `tapeFrom_cut_replays`, `tapeFrom_position_replays` | seat CUTS's four laws (R13) | `tapeFrom`, `Position`, `tape_replays` |
| `tapeFrom_position_prefix` | a step of the fourth | the same |
| `openedOf`, `tapeOf`, `funded` | three definitions | `Run.open`, `tapeFrom`, `Position` |
| `funded_replays` | a theorem (R8) | `funded`, `tape_replays`, `Run.Reached`, `Run.journal_replays`, `Run.open_machine` |
| `atRest` | a definition | `Run.work` |

**Further candidates of the same kind**, which the message does not name.

| Declaration | Kind | What it needs |
| --- | --- | --- |
| `play_id`, `play_budget`, `play_profile` | playing rows keeps a run's name, budget and profile | `Run.play`, `Run.step_id`, `Run.step_budget`, `Run.step_profile` |
| `SessionInert`, `bindCall_inert`, `submit_inert` | holding a call and receiving a reply leave four readings of a session | `Session`, `bindCall`, `submit` |
| `Inert`, `receiptRow`, `step_receiptRow`, `play_receiptRows`, `receive_receiptRows` | the same over a run's rows | `Run.step_session_bind`, `Run.step_session_submit`, `Rows.receive` |
| `AppliedSelects`, `applied_selects` | a reply application consumes the selected call only (R6) | `applyReply` |
| `ControlRetires`, `control_retires` | a control retires the held calls whose guard it removed (R6) | `advance`, `Run.advance_step` |

**What stays.** Each of these names the driver's alphabet or a scenario's record.

- `Seen`, `Sel`, `Move`, `step`, `play`, and the readers of section 3.
- `play_opened`, `reached_play`, `replays`, `ReceiptInert` and `receipt_inert`.
- The record, the gate and the `note`.

Two things for that slice.

- `Test/Dogfood/Scenario.lean` imports `ProofGraph.Plan` and `Tools.SemanticsRegistry` for its
  gate. A module of the law graph cannot. So the moved file holds the declarations above alone.
- The registry's claims `run-tape-replay` and `journal-position-replay` point at the present
  names. Their pointers move with the declarations.

## 12. Proposals for the coordinator's files

I edited none of these files. Each row below is a proposal. The merge `c67fa03c` already holds
two things of this list.

- The battery is a root of the semantics report, in `registry.roots` and in the `Makefile`.
- The long sentence of `Test/Dogfood/README.md` is split.

| File and place | Proposal |
| --- | --- |
| `tools/Tools/SemanticsRegistry.lean`, the claims, beside `run-tape-replay` | One claim: id `funded-run-replay`, concept `translation-simulation`, the role of a simulation, witness `Test.Dogfood.Scenario.funded_replays`. Title: "The machine of a funded run is the raw replay of its tape's decisions, from the program's own load (any recorded run whose journal has no stopped row; nothing about a run with a stopped row, a session ledger or a generated engine; decisions rows 226 and 254)" |
| the same file, R10, the open part `queue-expansion-agrees` | Add: "its first application on one program is two planned goals, `held_within_fed` and `fed_accounted` (`Test/Dogfood/Scenario/QueueWorkers.lean`), with finite controls on the Lean machine, three engine runs and 25 host runs; no law of a whole run" |
| the same file, R11, the open part of the whole run | Its planned goals are now three, one program each: `Workers.releases_once`, `cleans_once` and `QueueWorkers.releases_once` |
| the same file, R12, `wait-registration-no-gap` | Add: "an instance at rest on one program is the planned goal `queue_settled`" |
| the same file, R12, `embedded-budget-sufficient` | Add: "at a run the premise has one name, `funded` (`Test/Dogfood/Scenario.lean`), and `funded_replays` says what it gives; a journal's verdicts do not decide it" |
| the same file, R12, `driver-continuation-split` and `driver-suspension-keeps-typed` | Add the evidence of item 2.1: "a finite control: at a reply application the command loop's leftover commands are not kept (the run `dropped`; one script at seven budgets)" |
| `docs/core/semantics.md`, the section on reactive scheduling, at the embedded budget | One sentence: a statement over a session's runs takes the budget premise `funded`, and a journal's verdicts do not decide it |
| `docs/STATE.md`, the paragraph "Seat WORKQ has the workers over the public Queue" | It gives 30 named runs and 33 controls. The record has 31 named runs and 35 controls, 18 green and 17 red (tested: the scratch file of item 6 gives the counts). Its last sentence, "The receipt comes next", becomes a link to this receipt |
| `docs/STATE.md`, where it gives a present count of the scenarios or of their planned goals | The counts are five scenarios and fourteen planned goals. The report's line "Next goals" lists the fourteen |
| `docs/research/2026-10-06-whole-run-law-prep.md`, the paragraph on this finding | The two sentences of item 2.1: "so nothing will run the root" is a bounded result, and a control does show its cut |
| `docs/core/api-surface.md`, section 1.2, the record builders' table | One row: "`ascribe ty e` — a term at a declared type: a record with one field declared at `ty` that holds `e`, and a read of that field; the record's check decides it" (`src/Effect4/Program/Authoring/Ascribe.lean`). One open point: `Effect4.Api` does not import the module, and a client imports it by name today |
| `docs/core/controlled-english.md`, the dictionary | A candidate entry, with the estate's wording to choose: "funded run — a run whose journal has no stopped row", anchored at `funded` |
| `lakefile.toml` | No line |
| `docs/core/decisions.md` | The rows of item 15 |

**`Test/Dogfood/README.md`, which the brief gives me.** Its plan row of p3 still says that the
program waits on the queue composite (DI-11). The crew now builds over the public Queue in the
scenario. p3's own battery still measures the queue as two host rows. So its stage does not
move, and no acceptance program moved in this slice.

Two facts that I found on the way, with no proposal attached. I found no placement in the
semantics registry for `var_push_minted`, and none for the module `Effect4.Laws.Program.Author`.

## 13. The requirements R1 to R13

The slice advances no requirement to proved. R4 gains three proved helpers of its typing
nodes: `types_ascribe`, `ascribe_untyped` and `ascribe_scoped`. R8 gains one proved node,
`funded_replays`, and the faces battery gains two finite controls of `read_print` and
`read_exact`. R10 gains the proved helper `reads_ascribe`, the claim `queueWorkers` modulo
goals, and the goal `held_within_fed`. R11 gains the goal `releases_once` on a second program.
R12 gains the goals `fed_accounted` and `queue_settled`, and the named budget premise. R6 and
R13 gain no statement. The scenario cites three proved laws of the session and the law
`replays` as they stand, and its host runs are finite checks. Reply admission stays where the
host boundary puts it. R1, R2, R3, R5, R7 and R9 have no relation to the slice. It changes no
signature of the language, no type, no service, no code entry and no host law. Each of R4, R8
and R10 to R12 stays open. The slice adds four planned goals. A tree with no open planned goal
would still not have a finished semantics.

## 14. Open obligations

1. The four planned goals of item 1. The next proof slice's consumer is the list of item 10.
2. The owner's question of item 2.1: whether a reply application reports its sufficiency, and
   whether the machine keeps the commands that a step left.
3. The premise of the four goals (item 2.2): `funded` is sufficient, and nothing shows that it
   is the least one.
4. The move of item 11's declarations into the law graph.
5. The stronger form of the lane's comparison of handles (item 9). Not built.
6. One program for several runs in a fixture (item 8). Not built.
7. p3's own battery over the public Queue. It is a slice of its own.
8. The proposals of item 12. No one has ruled them.

## 15. Proposed decisions rows (proposals only)

| Topic | Proposal |
| --- | --- |
| What seat WORKQ's receipt leaves open | (1) **A budget's cut has two kinds, and a journal's verdicts show neither.** A reply application answers `applied` whatever fuel its step had left, and the machine drops the commands that the step left. One kind leaves a fiber runnable with no task. The other leaves the machine at rest with no exit of the root. Whether an application reports its sufficiency is the owner's. No change of the machine is proposed. (2) **A statement over a session's runs takes its budget premise by one name, `funded`**: the tape of the run's own journal leaves no row unread. `funded_replays` ties it to `tape_replays`. It is a sufficient premise of the four goals, and nothing shows that it is the least one. (3) **The four goals' premises are the next proof slice's consumer**: the eight needs of the receipt's item 10. (4) **The keyed lane compares a module's private cell up to its handles.** A `Deferred` has one image in a cell, by a writer `cellJson` on each face, and it stays outside the transport profile. The stronger form numbers a handle at its first sight on both faces, and it is not built. (5) **The general declarations of the scenario support move into the law graph** in a later slice (the receipt's item 11). (6) **A fixture writes its program once for each run.** One program for several runs is a candidate |
| `ascribe` on the surface | The form has its home and four laws. Whether `Effect4.Api` exports it with the record builders is open. It is not `Ref.make<A>`, which stays a later slice of rows 42 and 43 |
