# 2026-10-06 seat TAPE design: the tape and its laws move into the library

Status: a design note (history, not authority). Base: `4ff42e89`. Brief:
`docs/research/2026-10-05-claude-lead/briefs/seat-tape-brief.md`. No file of the slice is
committed yet. The base's default build passes, with the brief's gate lines (tested).

**The one thing to know first.** Four definitions of the tape cannot be core definitions.
`readsOn` calls `Run.enoughFor`, which the law graph defines (`src/Effect4/Laws/Run.lean`). So
`readsOn`, `tapeFrom`, `tapeOf` and `funded` stand in the law graph, and nine other definitions
go to the core. Section 3 names what would lift the bar.

## 1. The homes

The slice moves 44 declarations out of `Test/Dogfood/Scenario.lean`. The list is item 11 of
`docs/research/2026-10-06-seat-WORKQ-receipt.md`: its two tables move, and its third list
stays. No statement changes, and no theorem is added.

| Module | File | Root | It holds |
| --- | --- | --- | --- |
| `Effect4.Run.Tape` | `src/Effect4/Run/Tape.lean` (new) | `Effect4` | nine executable definitions over the run API: the machine's view, the decision of a row, a receipt row, the fresh open and rest |
| `Effect4.Laws.Run.Rows` | `src/Effect4/Laws/Run/Rows.lean` (new) | `Effect4.Laws` | what a row keeps and what it changes: the three keeping laws, the inertness laws, and the two laws of R6 |
| `Effect4.Laws.Run.Tape` | `src/Effect4/Laws/Run/Tape.lean` (new) | `Effect4.Laws` | the tape (`readsOn`, `tapeFrom`, `tapeOf`, `funded`), `tape_replays` with its steps, the four laws of the journal's cut, and `funded_replays` |

- **The namespace** of each moved declaration is `Effect4.Run`. It is the namespace of
  `play_controls_eq_replay` (`src/Effect4/Laws/Run.lean`). Each short name stays. No moved
  name stands in that namespace today (reading: the three files that open it).
- **The core module is no `module` file.** It imports `Effect4.Run`, which imports the face
  `Effect4.Api`. That face imports `Effect4.Program.Admit`, a specialization site of decisions
  row 202. An importer of such a site stays non-module.
- **Each law module** imports `Effect4.Laws.Auto.Semantics` for the tags. Neither imports the
  plan (`tools/ProofGraph/Plan.lean`) or the registry.
- **The root anchors.** `src/Effect4.lean` imports the core module after `Effect4.Run`.
  `src/Effect4/Laws.lean` imports the two law modules after `Effect4.Laws.Run`.

## 2. Each declaration, and what decides its home

The rule is the brief's. An executable definition goes to the core where each of its imports
is under the `Effect4` root. A theorem goes to the law graph. A proposition is the statement
of a theorem, so it goes with its theorem.

| Declaration | Kind | New home | What decides it |
| --- | --- | --- | --- |
| `MachineView` | a structure | core | its fields' types are under `Effect4.Run`'s imports |
| `machineViewOf` | a definition | core | it calls `awaits` and `Api.runnableFibers`, both under the `Effect4` root |
| `machineView` | a definition | core | `Run.machine` |
| `Position` | a structure | core | `Api.Decision` and `Run` |
| `replyDecision` | a definition | core | `Reply` and `Api.Decision` |
| `decisionOf` | a definition | core | `Api.HostSession.readReply` |
| `receiptRow` | a definition | core | `Api.Runner.Command` |
| `openedOf` | a definition | core | `Run.open` |
| `atRest` | a definition | core | `Run.work` |
| `play_id`, `play_budget`, `play_profile` | three theorems | `Rows` | a theorem |
| `SessionInert`, `Inert` | two propositions | `Rows` | the statements of the inertness laws |
| `bindCall_inert`, `submit_inert`, `step_receiptRow`, `play_receiptRows`, `receive_receiptRows` | five theorems | `Rows` | a theorem |
| `AppliedSelects`, `ControlRetires` | two propositions | `Rows` | the statements of the two laws below |
| `applied_selects`, `control_retires` | two theorems, each tagged R6 | `Rows` | a theorem |
| `readsOn` | a definition | `Tape`, in the law graph | barred: it calls `Run.enoughFor` of the module `Effect4.Laws.Run` |
| `tapeFrom` | a definition | `Tape`, in the law graph | barred: it calls `readsOn` |
| `tapeOf`, `funded` | two definitions | `Tape`, in the law graph | barred: each calls `tapeFrom` |
| `TapeReplays` | a proposition | `Tape` | the statement of `tape_replays` |
| `preflight_replyDecision`, `applyReply_applied_machine`, `applyReply_ends`, `step_keeps_machine`, `step_takes_decision` | five theorems | `Tape` | steps of `tape_replays` |
| `tapeFrom_frontier`, `tapeFrom_skip`, `tapeFrom_take`, `tapeFrom_stop` | four theorems | `Tape` | the equations of `tapeFrom` |
| `tape_replays` | a theorem, tagged R8 | `Tape` | the pointer of the claim `run-tape-replay` |
| `tapeFrom_append`, `tapeFrom_cut`, `tapeFrom_cut_replays`, `tapeFrom_position_replays` | four theorems, each tagged R13 | `Tape` | the last is the pointer of `journal-position-replay` |
| `tapeFrom_position_prefix` | a theorem | `Tape` | a step of `tapeFrom_position_replays` |
| `funded_replays` | a theorem, tagged R8 | `Tape` | the pointer of the claim `funded-run-replay` |

Each old name is `Test.Dogfood.Scenario.` and the short name. Each new name is `Effect4.Run.`
and the same short name. The derived instance `instDecidableEqMachineView` moves with its
structure.

The brief's sentence names the keeping laws and the inertness laws. The receipt's second table
also holds `applied_selects` and `control_retires`, with their propositions. They state facts
of any session, and they name no scenario. So I move them by the same rule.

## 3. The definitions that cannot be core definitions

| Definition | The import that bars it |
| --- | --- |
| `readsOn` | `Effect4.Laws.Run`: it defines `Run.enoughFor`, and the `Effect4` root never imports the law graph |
| `tapeFrom` | the same, through `readsOn` |
| `tapeOf`, `funded` | the same, through `tapeFrom` |

Five more definitions are propositions: `TapeReplays`, `SessionInert`, `Inert`,
`AppliedSelects` and `ControlRetires`. None is executable, and no tool calls one.

**What would lift the bar** (a proposal, outside the slice). `Run.enoughFor`, `Run.replayFrom`
and `Run.machineOf` are definitions of `src/Effect4/Laws/Run.lean`. Each calls definitions of
the core only (reading): `stepDecisionState` and `replayEval`
(`src/Effect4/Machine/Fibers.lean`), `interpOf` and `evaluatorFor`
(`src/Effect4/Program/Compile.lean`). A slice that moves those three to the core lets the four
barred definitions follow. This slice edits no existing library module, so it does not move
them.

## 4. How the batteries read the moved names

`Test/Dogfood/Scenario.lean` keeps the driver's alphabet, the readers of section 3, `replays`,
`receipt_inert`, the record, the gate and the `note`. It imports the three new modules. Inside
its namespace it re-exports the moved names that the scenario tree uses, by one `export`
command. So `tapeFrom` in a battery resolves as before: at the namespace
`Test.Dogfood.Scenario`, before any opened namespace. A battery's own `machineView`
(`Test/Dogfood/Scenario/Routing.lean`) and its own `MachineView`
(`Test/Dogfood/Scenario/Workers.lean`) still shadow the library's, as they shadowed the
support's.

The alternative is one `open Effect4.Run (…)` line in each battery. It changes five batteries
and one line of `harness/truth/session/Keyed.lean`, and it gives the same resolution. I take
the `export`, since it leaves the batteries' code as it is.

## 5. What changes besides the move

No `#guard` changes. Four kinds of pinned message change, and each change follows from a
moved name.

| Pin | File | The change |
| --- | --- | --- |
| Six `#print axioms` pins | `Test/Dogfood/Scenario.lean` | the namespace of each name |
| One `#plan_status` pin | the same file | the namespace of each name; each count of lemmas and of definitions becomes 0 |
| Two gate pins | `Test/Dogfood/Scenario/Workers.lean`, `Test/Dogfood/Scenario/QueueWorkers.lean` | the namespace of `applied_selects` and of `control_retires` |
| One gate pin and its fixture | `Test/Dogfood/Scenario/Gate.lean` | the fixture `unplaced` names `play_opened`, where it names `play_id` today |

- **The plan's counts.** `#plan_status` counts what a proof brings in from the current root's
  tree (`tools/ProofGraph/Plan.lean`). In a battery that tree is `Test`. The lemmas and the
  definitions leave it, so each count becomes 0. The standing and the nearest nodes stay.
- **The gate's fixture.** `unplaced` controls the refusal of a battery's theorem with no
  placement at a requirement. `play_id` becomes a theorem of the law graph. With it the
  fixture would repeat the control `unplacedLaw`. `play_opened` stays a battery's theorem with
  no placement.
- **Docstrings.** A docstring that cites a moved declaration with the old path gets the new
  path. That holds in the moved text and in the batteries.

## 6. The steps and the checks

1. Before the first edit: the statements and the kernel terms of the 44 declarations, written
   at the base into the scratch folder.
2. One commit moves the declarations: three new modules, two root imports, the support, the
   pins and the docstrings. A narrow build of the new modules and of the scenario batteries
   comes first, then the default build.
3. One commit holds the documents: `docs/ARCHITECTURE.md`, three rows of
   `tools/Tools/ArchitectureRoles.lean`, `Test/Dogfood/README.md` and the three anchors of
   `docs/core/controlled-english.md`.
4. The acceptance of the brief: the statements compared by `#check`, the gate lines,
   `make gen-fixtures` with `git status`, the engine's tests, `make check-host-protocol`,
   `make check-docs` and `make check-language`. I add `make check-cases`, since the core gains
   a module.

## 7. For the coordinator's files

| File | The change at the merge |
| --- | --- |
| `tools/Tools/SemanticsRegistry.lean`, the claim `run-tape-replay` | pointer `Effect4.Run.tape_replays`, where it is `Test.Dogfood.Scenario.tape_replays` |
| the same file, the claim `funded-run-replay` | pointer `Effect4.Run.funded_replays`, where it is `Test.Dogfood.Scenario.funded_replays` |
| the same file, the claim `journal-position-replay` | pointer `Effect4.Run.tapeFrom_position_replays`, where it is `Test.Dogfood.Scenario.tapeFrom_position_replays` |
| `generated/semantics.md` | written again after the pointers change |

The receipt lists each citation of a moved declaration in a file that I do not edit.
