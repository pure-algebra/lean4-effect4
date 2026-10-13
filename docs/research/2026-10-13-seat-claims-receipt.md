# 2026-10-13 seat CLAIMS receipt: the application and claim records

Status: receipt (history, not authority). Brief: `docs/research/2026-10-13-seat-claims-brief.md`.
Packet: `docs/research/2026-10-07-packet-application-claims.md` (a design and a sketch).

**The one thing to know before merging:** the five to-do claims are theorems. Four are proved.
`add_empty_calls_nothing`, and so the claim `serves`, rests on one planned goal of the law graph,
`Effect4.Run.CallTree.request_leads`. The routing claim rests on that goal too. Their statements
read every recorded run under decided premises, not the packet's single scripts. Keep the three
to-do modules out of the semantics registry's roots (row 336 (9)).

## Base and head

Branch `seat/claims`, base `289e469a4`, code head `2723e65ef`; the commit of this receipt follows
it. The coordinator merged slices 1 and 2 into `refactor/phase1-phase3` at `00697b398`.

| Commit | Slice |
| --- | --- |
| `ff7fa17ba` | 1, APP |
| `db3b05f3b` | 2, RECORD |
| `49842ac87` | 3, PROTOCOL (and the reuse repair of slice 1) |
| `f448b1988` | 4, MODEL |
| `088976939` | 6, TREE |
| `b3beb1883` | 6, the tree equations by `aesop` (row 376 (3)) |
| `1a58f8666` | 5, the record half of QUERY-APP |
| `2723e65ef` | a docstring of the record module |

## Work log

The log grows slice by slice. Each entry names the slice, its files and its evidence.

### What the tree held at the base (reading)

- `denoteRows` (`src/Effect4/Laws/Program/DenoteRows.lean`) gives the packet's N1 to N5. A node is a
  row's position and a request, an answer is an exit, and `catchIf` is in the fragment.
- N7 and N8 exist as theorems: `denoteRows_eq_session` and `denoteRows_eq_session_host`
  (`src/Effect4/Laws/Api/SessionMeaning.lean`), and `runWith_denotes`
  (`src/Effect4/Laws/Api/HostDrive.lean`). Each relates the root's exit and the stores, never the
  held calls.
- The held calls reach the tree through `bound_in_tree` (`src/Effect4/Laws/Run/CallTree.lean`),
  which rests on the planned goal `request_leads`. `held_in_tree`
  (`Test/Dogfood/Scenario/Routing/Calls.lean`) reads it at the driver's `held`.
- The decided check `hostAnsweredCheck` and its soundness `hostAnsweredCheck_sound`
  (`src/Effect4/Laws/Api/SessionMeaning.lean`) already decide whether a host gave a run's answers.
  A model's agreement with a run is that check at the model read as a host (`reactorHost`).
- The pinned `Effects` package holds `Program.Sat` and `Program.Sat.sound`
  (`Effects/Coalgebra/Sat.lean`). `Sat` is a postcondition of a call tree under a protocol.
  `Sat.sound` says that every host meeting the protocol runs the tree only to values in it. It is the packet's `Typed` at a protocol with no demand, with its
  soundness proved.
- `Test/Api/SessionMeaning.lean` holds an in-memory repository reactor over the four to-do rows,
  `repository`. It is the packet's reference model, written once already.
- The routing scenario's two goals, which the packet expected to wait, are theorems now.
- `Module` gained definitions (`defs`, PROC-4) after the packet. A program with a definition
  block is outside `StraightRows`, so the entries stay top-level programs (the packet's design).

### Slice 1, APP (commit `ff7fa17ba`)

- New `src/Effect4/Program/Authoring/Application.lean`: `Application.Entry`, `Entry.applied`,
  `Application` (rows, services, layers, defs, entries), `entry?`, `entryNames`, `rowDefs`,
  `moduleOf`, `table`, `moduleOf_table` (by `rfl`), `openProgram`. A module file (row 200).
- The root `src/Effect4.lean` imports it at its end.
- `Test/Dogfood/Scenario/Todo.lean`: `application`, `builtAt`, `openTy`, and five battery lines.
  The value is named `application`, since `app` is the atom lift `Effect4.Program.Authoring.app`.
- Tested: each entry builds at its argument with the request's type. Each open program has that
  type at its parameters' types. An applied entry is its open program under one bind, at one
  argument. Control: an unbound parameter refuses the build and the open program.
- Probed (scratch, not landed): `kernel_rfl` proves the elaboration of an entry at a free argument
  and the call tree's first node at a free id. A false equation fails in the kernel (red control).

### Slice 2, RECORD (commit `db3b05f3b`; merged by the coordinator at `00697b398`)

- New `Test/Dogfood/Application.lean`: `Kind`, `Grade`, `Premise`, `Note`, `Record`,
  `Note.problems`, `Record.problems`, `Record.ofKind`, `Record.premisesAt`. No gate: the scenario
  gate checks the scenario, and `#guard` reads the notes.
- New `Test/Dogfood/Scenario/Todo/Claims.lean`: two goals, `add_empty_calls_nothing` and
  `complete_failure_escapes`, and the claim `serves`. It holds the observation, six named runs,
  eight controls, the record and seven red controls of the notes. `Test/All.lean` imports both at its end.
- Each statement is a session form that a theorem of the tree reaches: the held calls through
  `bound_in_tree`, the exit through `denoteRows_eq_session`. The packet's form "under one script"
  needed a machine proof per script; the forms here read every recorded run.
- Tested: `#plan_status serves` prints modulo the two goals; a scratch red control (a control that
  fails) makes `#scenario_gate` refuse.

### Slice 3, PROTOCOL (commit `49842ac87`)

- New `src/Effect4/Program/RowProtocol.lean` (a module file): `RowProtocol` (`pre`, `post`),
  `formed`, `admits`, `keeps`, and `RowProtocols` with `at?`, `formed`, `admits`, `keepsAt`.
- `Application` gains `protocols` and `protocolsFormed`. Its declarations become one `Module`
  (`declarations`). So `table` and `openProgram` reuse `Module.table` and `Module.rowDefs`. Slice
  1 had copied `Module.rowDefs`'s formula, a duplicate under row 376 (3).
- New `src/Effect4/Laws/Program/Validated.lean`: `declaredProtocol`, `rowsProtocol`,
  `keptTapeHost`, `keptTapeHost_meets`, `rowsHost_meets`, `conforms`, and the theorem
  `conforms_sat`. The `Effect4.Laws` root imports it at its end.
- The to-do application declares the packet's two protocols. Measured again at the base: the atom
  `eq` has no type at two Booleans, so `sameFlag` writes the comparison with `and`, `or`, `not`.
- `complete_answers_requested` is a planned goal over settled, conforming runs. Its red control:
  a typed answer for another to-do reaches the root, the run is settled, and it does not conform.

### Slice 4, MODEL (commit `f448b1988`)

- The reference model is the one that `Test/Api/SessionMeaning.lean` already held: `repository`
  over `Repo` moves into `Test/Dogfood/Scenario/Todo.lean`, section 7, and the battery reads it
  there. The battery's hand copy of a guarded reactor handler, `reactorHandler`, goes. It was
  `Run.guardRows` over `Run.reactorHost`, read as a handler, and the battery now writes that.
- `Validated.lean` gains `agrees` (`hostAnsweredCheck` at the model read as a host) and the
  theorem `agrees_hostRun` (H9 with the check's soundness).
- `SettledRun` names the premises of the host's meaning once. `list_after_add` and
  `complete_idempotent` are planned goals over settled runs that the model validates. Green runs:
  the model drives `add`, `list` and `complete` twice (`Run.runWith`). Red runs: a host that
  forgets what it stores, and a host whose `setDone` flips the flag.

### Slice 6, TREE (commits `088976939`, `b3beb1883`)

- New `Test/Dogfood/Scenario/Todo/Tree.lean`: a built entry is its elaboration
  (`builtAt_program`); the entries are in `StraightRows`; the tree forms; and the trees under the
  model.
- The five planned goals become theorems in place, each through an existing theorem of the
  session's meaning: `held_in_tree`, `denoteRows_eq_session`, `conforms_sat` and
  `agrees_hostRun`.
- `#auto_census Test.Dogfood.Scenario.Todo.Tree using aesop` closed 17 of 30 theorems from their
  statements; those proofs are `aesop` now. `kernel_rfl` stays on four equations that the search
  does not close. The census closed none of `Validated.lean` (0 of 4) or `Claims.lean` (0 of 6).
- The `Todo.lean` line that compared an entry with its open program at one id is dropped:
  `complete_elaborates` covers every id (row 301).

### Slice 5, QUERY-APP (commit `1a58f8666`, the record half only)

- The packet's slice edits `tools/Tools/Query.lean`, which this seat's brief does not give it.
  The seat stops at that boundary (see the open obligations).
- In bounds: `Record.claimsOf` answers what the record claims of one program, by kind, with
  inherited laws for each program the application holds. One battery line reads it. It replaces
  `Record.ofKind` and `Record.premisesAt`, which had no reader.
- Not landed: the table of inherited laws with decided premises. Each of its theorems would have
  no consumer until the query function reads the table (`AGENTS.md`, "no proofs to nowhere").

## Changed files

| File | Change |
| --- | --- |
| `src/Effect4/Program/Authoring/Application.lean` | new: `Application`, `Application.Entry`, `Entry.applied`, `declarations`, `moduleOf`, `table`, `moduleOf_table`, `openProgram`, `protocolsFormed`, `entry?`, `entryNames` |
| `src/Effect4/Program/RowProtocol.lean` | new: `RowProtocol` (`formed`, `admits`, `keeps`) and `RowProtocols` (`at?`, `formed`, `admits`, `keepsAt`) |
| `src/Effect4/Laws/Program/Validated.lean` | new: `declaredProtocol`, `rowsProtocol`, `keptTapeHost`, `conforms`, `agrees`, and the theorems `conforms_sat`, `agrees_hostRun`, `keptTapeHost_meets`, `rowsHost_meets` |
| `src/Effect4.lean`, `src/Effect4/Laws.lean` | one import each, at the end |
| `Test/Dogfood/Application.lean` | new: the claim record (`Kind`, `Grade`, `Premise`, `Note`, `Record`, `problems`, `claimsOf`) |
| `Test/Dogfood/Scenario/Todo.lean` | the application, its protocols, the reference model (moved in), battery lines |
| `Test/Dogfood/Scenario/Todo/Tree.lean` | new: the tree forms and the trees under the model |
| `Test/Dogfood/Scenario/Todo/Claims.lean` | new: the five claims, `serves`, the observation, 15 named runs, 14 controls, the record, the notes' red controls |
| `Test/Api/SessionMeaning.lean` | reads the model from `Todo.lean`; its handler copy replaced by the library's composition |
| `Test/All.lean` | two imports, at the end |

## Commands and results

Each command ran in `/Users/pooks/Dev/lean4-effect4-claims` through
`/Users/pooks/Dev/lean4-effect4/scratch/lean-slot.sh`.

| Command | Result |
| --- | --- |
| `lake build Effect4.Program.RowProtocol Effect4.Program.Authoring.Application Effect4 Effect4.Laws.Program.Validated Effect4.Laws Test.Dogfood.Scenario.Todo Test.Dogfood.Scenario.Todo.Claims Test.Api.SessionMeaning Test.Program.CallInstance Test.Program.DenoteRowsContract Test.Dogfood.Scenario.TodoPaged` (slice 3) | exit 0, 1505 jobs |
| `lake build Effect4.Laws.Program.Validated Effect4.Laws Test.Dogfood.Scenario.Todo Test.Dogfood.Scenario.Todo.Claims Test.Api.SessionMeaning Test.Program.CallInstance Test.Program.DenoteRowsContract Test.Dogfood.Scenario.TodoPaged` (slice 4) | exit 0, 1480 jobs |
| `lake build Test.Dogfood.Scenario.Todo Test.Dogfood.Scenario.Todo.Tree Test.Dogfood.Scenario.Todo.Claims Test.Api.SessionMeaning Test.Program.CallInstance Test.Program.DenoteRowsContract Test.Dogfood.Scenario.TodoPaged` (slice 6) | exit 0, 1163 jobs |
| `lake build Test.Dogfood.Application Test.Dogfood.Scenario.Todo.Claims` (slice 5's half) | exit 0, 1157 jobs |
| `lake env lean` on a scratch file: `#plan_status serves …` | `serves`: modulo `[Effect4.Run.CallTree.request_leads]`; `add_empty_calls_nothing`: modulo the same; the other four: proved |
| `lake env lean` on a scratch file: `#auto_census … using aesop` | `Validated` 0 of 4; `Tree` 17 of 30; `Claims` 0 of 6 |
| `lake env lean` on a scratch red control: a broken control under `#scenario_gate` | the gate refuses it (slice 2) |
| `lake env lean` on a scratch red control: a false equation under `kernel_rfl` | the kernel refuses it (slice 1 probe) |

Every reader of each changed definition was built: the readers of `Todo.lean` are
`Test/Api/SessionMeaning.lean`, `Test/Program/CallInstance.lean`,
`Test/Program/DenoteRowsContract.lean`, `Test/Dogfood/Scenario/TodoPaged.lean` and the two new
modules. `Test.All` was not built (the owner asks for it). No behaviour gate is reached. No
existing definition outside `Test` changed. Two gate tools import the `Effect4` root
(`tools/Conform/Effect4/LcnfMl.lean`, `tools/Conform/Effect4/LcnfSemantics.lean`). Each emits from
a fixed root list, which reaches no new declaration.

## Axiom output

`#axiom_audit Effect4.Program.RowProtocol Effect4.Program.Authoring.Application
Effect4.Laws.Program.Validated Test.Dogfood.Application Test.Dogfood.Scenario.Todo
Test.Dogfood.Scenario.Todo.Tree Test.Dogfood.Scenario.Todo.Claims Test.Api.SessionMeaning`:
474 declarations within `[propext, Quot.sound]`, 2 of them modulo planned goals
(`add_empty_calls_nothing` and `serves`), 0 planned goals.

## Evidence

- Proved: `conforms_sat`, `agrees_hostRun`, `complete_failure_escapes`,
  `complete_answers_requested`, `list_after_add`, `complete_idempotent`, and the tree helpers.
- Proved modulo the planned goal `request_leads`: `add_empty_calls_nothing` and `serves`.
- Tested, as finite probes of one script each on the Lean machine: the scenario's 14 controls,
  the lines of `Todo.lean` and the notes' red controls.
- Not run: the to-do scenario has no host lane and no run on the generated OCaml engine. Every run
  is a Lean run.

## Landed theorems and their placement

`conforms_sat` (`src/Effect4/Laws/Program/Validated.lean`):

- Concept: `host-session-protocol`; property: the host as a relation between the machine's calls
  and its answers (R6's open part).
- Question: proposed registry claim `run-conforms-postcondition` (role adequacy); consumer:
  `Test.Dogfood.Scenario.Todo.complete_answers_requested`.
- Reach: H9's fragment and premises: `StraightRows`, one fiber, and a recorded run that is
  funded, at rest, driven by a host and exited. The premise `conforms` reads the run's own tape.
- Does not establish: that a host conforms on another run; the demand on requests, which the
  proof does not read; progress. It adds no check at the reply receipt.
- Unlocks: R6, a claim under a declared protocol read on a real run by a decided premise.

`agrees_hostRun` (`src/Effect4/Laws/Program/Validated.lean`):

- Concept: `translation-simulation`; property: a run is the meaning under its host.
- Question: proposed registry claim `run-agrees-model` (role simulation); consumers:
  `list_after_add` and `complete_idempotent`.
- Reach: H9's; the premise `agrees`, decided by `hostAnsweredCheck`.
- Does not establish: that a host agrees with the model on another run; progress.
- Unlocks: R6, a claim under the laws of the rows read on a real run.

The five clauses and `serves` (`Test/Dogfood/Scenario/Todo/Claims.lean`), one block:

- Concept: `host-session-protocol`; property: the meaning of the row table agrees with the
  session, read at the to-do programs. Each carries `@[semantics "host-session-protocol"
  (requirement := R6)]`, which the scenario gate asks of a battery's claim.
- Question: the clauses of `serves`; consumer: `serves`, the to-do record's claim.
- Reach: the entries at every argument the statement names; every recorded run of the driver;
  premises `SettledRun`, `conforms` or `agrees` where stated.
- Does not establish: that a host conforms or agrees; a run of the generated OCaml engine or the
  printed module; progress.
- Unlocks: nothing in the requirement rows, by row 336 (9): no root of the semantics registry
  loads the module.

`moduleOf_table` (`src/Effect4/Program/Authoring/Application.lean`) is a connector, by `rfl`. Each
theorem of `Test/Dogfood/Scenario/Todo/Tree.lean` names the claim it is a step of.

## Reused declarations (row 376 (3))

- The program side: `Module`, `Module.table`, `Module.rowDefs`, `rowNamesOf`, `elaborateModule`
  (`src/Effect4/Program/Authoring.lean`); `bind`, `succeed`
  (`src/Effect4/Program/Authoring/Lifts.lean`); `termTy` (`src/Effect4/Program/Typing/Rules.lean`);
  `evalTerm` (`src/Effect4/Machine/Term.lean`); `nativeSignature`
  (`src/Effect4/Program/Native.lean`); `effTy` (`src/Effect4/Program/Typing.lean`);
  `Decision.decide` (`src/Effect4/Program/Decision.lean`).
- The build: `Effect4.Api.Author.build_retains` (`src/Effect4/Laws/Api/AuthorBuild.lean`).
- The scenario form: `Scenario`, `Clause`, `NamedRun`, `Control`, `play`, `script`, `answer`,
  `ok`, `failed`, `refusals`, `held`, `funded`, `atRest`, `openedOf`, `replays`
  (`Test/Dogfood/Scenario.lean`); `#scenario_gate` (`Test/Audit/ScenarioGate.lean`).
- The meaning: `denoteRows`, `meaningRows`, `seqRows` (`src/Effect4/Laws/Program/DenoteRows.lean`);
  `hostRun`, `rowsHost`, `tapeHost` (`src/Effect4/Laws/Program/HostRuns.lean`);
  `denoteRows_eq_session`, `denoteRows_eq_session_host`, `hostAnsweredCheck`,
  `hostAnsweredCheck_sound`, `reactorHost`, `appliedExits`, `hostDriven`
  (`src/Effect4/Laws/Api/SessionMeaning.lean`); `reactorHost_answer`
  (`src/Effect4/Laws/Api/HostDrive.lean`); `guardRows` (`src/Effect4/Laws/Program/RowProtocol.lean`).
- The call tree: `held_in_tree` (`Test/Dogfood/Scenario/Routing/Calls.lean`) over `bound_in_tree`,
  `NoCauseHandler`, `treeWaits`, `treeWaits_eq` (`src/Effect4/Laws/Run/CallTree.lean`);
  `SourceScope.ExternalOnly`, `SourceScope.ConcreteReplies`
  (`src/Effect4/Laws/Program/HostSource.lean`); `StraightRows`.
- The pinned `effects` package: `Effects.Protocol`, `Protocol.sum`, `Protocol.top`,
  `Comodel.guard`, `Comodel.guard_meets`, `Comodel.Meets.route`, `Comodel.run_vis_some`,
  `Program.Sat`, `Program.Sat.sound` (`Effects/Coalgebra/Protocol.lean`, `Comodel.lean`,
  `Sat.lean`).
- Tools: `proof_goal`, `#plan_status`, `@[semantics]`, `#axiom_audit`, `#auto_census`,
  `kernel_rfl`.
- Duplicates removed: `Application.rowDefs` (a copy of `Module.rowDefs`'s formula, in slice 1);
  `Test.Api.SessionMeaning.reactorHandler` (a copy of `guardRows` over `reactorHost`); a second
  reference model, by moving `repository`.

## Open obligations

1. **Slice 5's query wiring.** `tools/Tools/Query.lean` is outside this seat's files. Three
   options:
   - (a) give seat CLAIMS that file, `Test/Program/QueryControls.lean` and `Test/fixtures/query/`;
   - (b) give the request's row table to seat APPCHECK, which checks at a real application (row
     373 (7)), and the operation `claims` to CLAIMS;
   - (c) wait for slice 13, so the query reads one stored application with its claims.

   Recommendation: (b), then the operation over a claim table passed as data. Its row type should
   be a library type that the record reuses. Then the tool and `Record.claimsOf` share one
   mechanism.
2. **`held_in_tree` is general**, and it stands in the routing scenario's file, which the to-do tree
   now imports. Proposal: move it to `src/Effect4/Laws/Run/CallTree.lean` (outside this seat's
   files).
3. **The demand of a declared protocol** (`pre`) is decided by `conforms` and read by no theorem.
   Its home is the tree's `Typed` judgment (`src/Effect4/Laws/Effects/Protocol.lean`): the
   packet's analysis CALLS (slice 7).
4. **Dictionary entries** for `docs/core/controlled-english.md` §3, a file outside this seat's
   files. The proposed words, each with its anchor:
   - application (`Application`), entry (`Application.Entry`), declared protocol (`RowProtocol`);
   - reference model (`repository`), conforms (`conforms`), agrees (`agrees`);
   - note (`Note`), claim kind (`Kind`), premise grade (`Grade`).

   No avoid word is proposed.
5. **Registry claims**, as proposals: `run-conforms-postcondition` and `run-agrees-model` above.
   The to-do claims stay out of the registry (row 336 (9)).

### The packet's slices 7 to 13, as they stand

| Slice | State at head |
| --- | --- |
| 7, CALLS | `denoteRows` exists; the law that `programRows` bounds the tree's calls is one induction. Its consumer, the query's computed facts, waits on item 1 |
| 8, TYPED-ROWS | landed in substance: `declaredProtocol` is a protocol of the row signature, and `conforms_sat` is the bridge from `conforms`. Open: the demand (item 3) |
| 9, REGION | the routing goals are theorems by other means (`tree_needs_token`, a direct machine proof). The region view itself is not built; its consumer, the claims at an address, waits |
| 10, LAWS | not built. The reference model is the first form of the laws, and `agrees` validates a run against it. Laws as data wait for a second consumer |
| 11, KEPT | not built; waits on 9 and on a decision of each claim on a sketch |
| 12, MONITOR | waits on a ruling: it changes reply admission. `conforms` gives the validated grade without it |
| 13, STORED | PROC-5 landed on main (`4e75f71a4`, after this seat's base): a definition block has a meaning. One module with several exports is now in reach; the export name stays open (the sugar packet, slice NAMES) |

## Proposed decisions rows (proposals only)

1. **Slice 5's files** (domain): item 1's options, with its recommendation.
2. **An entry or a definition** (representation): with PROC-5 landed, an application's entries
   could become the definitions of one module. Recommendation: keep entries top-level programs
   until H8 and H9 cover a program with a definition block, then decide with slice 13.
3. **The to-do statements** (meaning, recorded for review): the packet's goals read one script or
   a drive by the model. The landed statements read every recorded run, with the premises of the
   host's meaning, and two runs validated by the model. They claim no progress: the packet's form
   of `list_after_add` asserted that the runs finish, which no theorem gives.
