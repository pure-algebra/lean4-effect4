# 2026-10-06 seat TAPE receipt: the tape and its laws stand in the library

Status: receipt (history, not authority). Brief:
`docs/research/2026-10-05-claude-lead/briefs/seat-tape-brief.md`, with the dispatch message and
the coordinator's two messages. Design note: `docs/research/2026-10-06-seat-TAPE-design.md`.
Filed evidence: `docs/research/2026-10-06-seat-tape-evidence/`, with its index.

**The one thing to know before merging:** the semantics registry's three pointers change in
the merge, or `make gen-semantics` is red. The report's own function refuses the registry as it
stands, by three findings (reproduced: `report-stale.out.txt`). `make check-gen` writes that
group again, so it is red too (reading). The default build reads no pointer, and it passes.

Five more facts stand beside it.

- **Both steps landed, and no declaration resisted.** The stop rule was not used. Step 1 is
  the designed move. Step 2 is the coordinator's extension: the raw replay and the tape are
  core definitions.
- **No statement changed** (tested: `#check` of the 44 names at the base and at the head, equal
  up to the namespace). Each type and each definition's value is equal as a kernel term, but
  for one matcher's helper (item 5).
- **No `#guard` changed.** Ten pinned messages follow a moved name (item 5).
- **No generated file moved** (reproduced: `make gen-fixtures`, and the nine sums).
- **`make check-cases` keeps its 231 subjects** at each step. So no policy pin is needed.

## 1. Base, head and commits

Branch `seat/tape`, in the worktree `/Users/pooks/Dev/lean4-effect4-qsteps`. Base `4ff42e89`.
Nothing is pushed.

| Commit | What it holds |
| --- | --- |
| `6a66beaf` | the design note |
| `16d1d078` | step 1: 44 declarations leave `Test/Dogfood/Scenario.lean` |
| `05768d17` | step 2: seven definitions join the core module. It is the last commit that changes a declaration |
| `f9a0f0f7` | the documents: three dictionary anchors, three rows of the map, the README |
| `aac8b509` | two comments: the root's, and one wrapped line of the support's header |
| the head | this receipt, the evidence folder and the design note's addendum |

Changed: `src/Effect4/Run/Tape.lean`, `src/Effect4/Laws/Run/Rows.lean` and
`src/Effect4/Laws/Run/Tape.lean` (new); `src/Effect4.lean`, `src/Effect4/Laws.lean` and
`src/Effect4/Laws/Run.lean`; `Test/Dogfood/Scenario.lean` with `Gate.lean`, `Workers.lean`,
`QueueWorkers.lean` and `Tape.lean` of its folder; `Test/Dogfood/README.md`;
`docs/ARCHITECTURE.md`, `tools/Tools/ArchitectureRoles.lean` and
`docs/core/controlled-english.md`. No file under `src/Effect4/Machine/` changed.

## 2. Each declaration's old and new name and file

Each new name is `Effect4.Run.` and the short name. Each old name of the first, third and
fourth rows is `Test.Dogfood.Scenario.` and the short name, in `Test/Dogfood/Scenario.lean`.

| New file | Declarations |
| --- | --- |
| `src/Effect4/Run/Tape.lean`, under the `Effect4` root | `MachineView`, `machineViewOf`, `machineView`, `Position`, `replyDecision`, `decisionOf`, `receiptRow`, `openedOf`, `atRest`, `readsOn`, `tapeFrom`, `tapeOf`, `funded` |
| the same file | `machineOf`, `replayFrom`, `enoughFor`: their names stay, and they stood in `src/Effect4/Laws/Run.lean` |
| `src/Effect4/Laws/Run/Rows.lean` | `play_id`, `play_budget`, `play_profile`, `SessionInert`, `Inert`, `bindCall_inert`, `submit_inert`, `step_receiptRow`, `play_receiptRows`, `receive_receiptRows`, `AppliedSelects`, `applied_selects`, `ControlRetires`, `control_retires` |
| `src/Effect4/Laws/Run/Tape.lean` | `TapeReplays`, `tape_replays`, `preflight_replyDecision`, `applyReply_applied_machine`, `applyReply_ends`, `step_keeps_machine`, `step_takes_decision`, `tapeFrom_frontier`, `tapeFrom_skip`, `tapeFrom_take`, `tapeFrom_stop`, `tapeFrom_append`, `tapeFrom_cut`, `tapeFrom_cut_replays`, `tapeFrom_position_prefix`, `tapeFrom_position_replays`, `funded_replays` |

Each tagged theorem keeps its tag. The core file is no `module` file: it imports
`Effect4.Run` (decisions row 202). The support re-exports 26 of the names by one `export`
command, so no battery's code changes.

## 3. Commands and results

`SLOT` is `/Users/pooks/Dev/lean4-effect4/scratch/lean-slot.sh`. `FLAGS` is
`-o build -o ts/eff/node_modules -o harness/truth/node_modules`.

| Command | Result |
| --- | --- |
| `SLOT lake build`, at the base | 1032 jobs; the gate lines of the dispatch message |
| `SLOT lake build`, at `16d1d078` | 1035 jobs; 179 API and 321 Laws-only modules; 785 modules and 91035 declarations; 28 planned goals, 12 declarations on goals |
| `SLOT lake build`, at `05768d17`, `f9a0f0f7` and `aac8b509` | 1035 jobs; the same lines, with 91040 declarations |
| the statement probe, at the base and at the head | no line differs, in 130 messages; the axioms are `[propext, Quot.sound]` for 40 names and `[propext]` for 4 |
| the probe of the kernel's terms, at the base and at the head | each type and each definition's value is equal as text, but for the name of one matcher's helper; each of the base's 102 hashes is the head's, in the base's name form |
| `SLOT make FLAGS gen-fixtures`, after each step and at `aac8b509` | `PASS generate: requested producers ran in dependency order`; `git status` lists no file |
| `SLOT make FLAGS check-cases`, after each step and at `aac8b509` | `conform cases: PASS`; 231 of 231 subjects pass |
| `SLOT make FLAGS corpus` | `Build completed successfully (157 jobs)`; no tracked file moved |
| `opam exec --switch=effect4 -- dune build`, in `ocaml/` | exit 0 |
| `opam exec --switch=effect4 -- dune test --force engine`, in `ocaml/` | exit 0; 1907 lines open with `PASS`, and none with `FAIL`; the corpus has 408 files, 408 decoded |
| `SLOT make FLAGS check-host-protocol` | `PASS host-protocol`; 72 scripts in 267 runs, 13 scripts with no host run; 55 tests pass |
| `SLOT make FLAGS check-docs` | `PASS check-docs: every path, link, citation and make target in 76 documents resolves` |
| `SLOT make FLAGS check-language` | `PASS check-language self-test: 48 of 48 controls`, and no finding in the two strict documents |
| the root probe | exit 0: the `Effect4` root alone reaches the sixteen definitions, and it does not reach `tape_replays` |

- The rows that name no commit ran at `aac8b509`. The two `dune` rows and the host row also
  ran at `f9a0f0f7`, with the same lines.
- Each `dune` command took `E4_LEAN_CORPUS` at this worktree's `.lake/corpus`.
- The host lane ran effect 4.0.0-rc.112 under bun 1.4.2. It type-checks with tsgo 7, the
  pinned `@typescript/native-preview` 7.0.0-dev.20260629.1.
- The architecture driver ran into scratch. It passed its totality check on the role
  register, and then it stopped: it reads the semantics report's JSON, which I did not write.

Not run: `make check-gen`, `check-slow`, `check-corpus`, `check-target`, `check-truth`, the
conservativity script, `make gen-semantics`, `make gen-architecture`, `make check` and
`make check-full`.

## 4. The pointers, and the other edits of the coordinator's files

| File and place | The change |
| --- | --- |
| `tools/Tools/SemanticsRegistry.lean`, claim `run-tape-replay` | pointer `Effect4.Run.tape_replays` |
| the same file, claim `funded-run-replay` | pointer `Effect4.Run.funded_replays` |
| the same file, claim `journal-position-replay` | pointer `Effect4.Run.tapeFrom_position_replays` |
| the same file, R12's open part `embedded-budget-sufficient` | its text cites `funded` at `Test/Dogfood/Scenario.lean`: the file is `src/Effect4/Run/Tape.lean` |
| `generated/semantics.md` | written again. `semantics-report.diff.txt` is the change that a scratch run gives: names and order, and no status |
| `docs/core/semantics.md`, the properties `journal-position-replay` and `funded-run-replay` | each cites its theorem at `Test/Dogfood/Scenario.lean`: the file is `src/Effect4/Laws/Run/Tape.lean` |
| `docs/STATE.md` | three sentences still place `tapeFrom`, `tape_replays` or the driver's general laws in the battery |
| `ocaml/engine/test/scenarios/test_scenarios.ml`, its first comment | it names `Test.Dogfood.Scenario.machineView`: the name is `Effect4.Run.machineView` |
| `docs/core/controlled-english.md`, the entry "journal's cut" | it says "the scenario driver's reading". The reading is the tape's. I changed the three anchors alone |
| `docs/core/api-surface.md`, the row `Run` (a proposal) | the sixteen definitions of `src/Effect4/Run/Tape.lean` are reachable from the `Effect4` root, and the row does not list them |
| `docs/core/decisions.md`, row 284 | point 5 is landed, with the extension |

## 5. What stayed, what the move measured, and the limits

- **What stayed in the support.** The driver's alphabet and readers, `play_opened`,
  `reached_play`, `replays`, `ReceiptInert` and `receipt_inert`, the record, the gate and the
  `note`. Each names a move, a selector or a record. The seven pins of the moved laws stay
  too: the law graph imports no plan.
- **What stayed in `src/Effect4/Laws/Run.lean`.** Each law of the three definitions, and
  `runOf`: the extension names three definitions, and `runOf` serves `replay_eq` alone.
- **The pinned messages that changed.** Six axiom pins and one plan status
  (`Test/Dogfood/Scenario.lean`): the namespace of each name. The plan's counts also become
  0, since the plan counts what a proof brings in from the `Test` tree. Two gate pins
  (`Workers.lean`, `QueueWorkers.lean`): the namespace of `applied_selects` and
  `control_retires`. One gate pin with its fixture (`Gate.lean`): `unplaced` names
  `play_opened`, a battery's theorem with no placement, where it named `play_id`.
- **Nine more declarations, none authored** (tested). At step 1 the matcher of `decisionOf`
  gets a helper of its own, where it shared the reader `applications`'s. At step 2 `runOf`
  gets a matcher of its own, where it shared `machineOf`'s. Each new one equals the one it
  replaces: the helper as text, the matcher up to binder names.
- **Limits of the evidence.** The comparison of proof terms is by a 32-bit hash. Two
  comparisons take a scratch copy of the base's support file, since the base's build was gone.
  Each host run is a finite host run. The engine's runs and the probes are finite.

**R1 to R14.** The slice advances no requirement, and it changes no status. R6 keeps its
nodes `applied_selects` and `control_retires`, now in the law graph, and `receipt_inert` in the
battery. R8 keeps `tape_replays` and `funded_replays`, and R13 keeps the four laws of the
journal's cut, all in the law graph. R10 to R12 keep their planned goals. Four of them, on the
crew over the Queue, name `funded` or `atRest` under the new namespace. R12 gains no statement:
its budget premise `funded` is a core definition now. R1 to R5, R7, R9 and R14 have no relation
to the slice. The goal gate counts 28 planned goals before and after, and 12 declarations on
goals. A tree with no open planned goal would still not have a finished semantics.

**Open obligations.** The edits of item 4. One candidate, not built: the batteries name
`Effect4.Run` themselves, and the support's `export` goes.
