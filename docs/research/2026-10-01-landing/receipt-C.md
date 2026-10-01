# Seat C receipt: the assembled state split at the cut, M7 declared, the ledger as the one list

Seat C of the 2026-10-01 landing. Brief: `docs/research/2026-10-01-landing/brief-C.md` (main
checkout, `c9f273a2`, with its Amendments section of `e7f9756f`, applied); plan: `plan.md` there (§0 items 3, 5, 7; §1 O2, O4; §2; §4; §5). Base
`bb269fde` on `refactor/phase1-phase3`; worktree `/Users/pooks/Dev/lean4-effect4-seat-C`, branch
`seat/C`. Evidence words: **proved** (a kernel theorem compiled here, axioms printed at
`[propext, Quot.sound]` or less), **reproduced** (another seat's proved fact compiled again here),
**tested** (a finite check run here: a `#guard`, a `grep`, a build's report), **stamped** (not
used), **assumed** (not run here; where the source is a reading of code or notes, the text says
"reading" and names the lines read).

## One thing first

**The merge of `refactor/phase1-phase3` (seats E, F and B merged) into `seat/C` that the coordinator
asked for is not done: the permission system denied `git merge` in this worktree, and I stopped at
that boundary.** This receipt therefore describes `seat/C` at `570142a9`, before the merge. A
read-only `git merge-tree --write-tree` run before the denial reports no textual conflict (tested),
but the merge has semantic repairs this seat could not make or test (section "The merge, not
done"): seat B's batteries `FramesNotKripke.lean` and `ProtocolPosts.lean` read the base's
`TypedState` with a queue argument, the old `savedPosition_of_saved` and a generated stores
component that ended in `trivial`, all restated here; seat B's repairs of `E4-TYPED-CE-010` and
`-012` are expected to make this branch's red controls `AwaitLoad.loadsTyped_false` and
`capstone_false` stop compiling (they then become positive controls) and to close `M6Stack`. At
`570142a9` itself: one of the eighteen, `step_deliver`, is refuted (proved,
`step_deliver_refuted_by_absent_scope`: `fiberPre` admits `.scopeExit` on an absent scope), and M5
and the capstone over `J` are refuted (proved) by `E4-TYPED-CE-009` and `-010`. The statements
changed shape (`TypedState` lost its queue argument; current code is typed by `J`'s `LiveCode` and
`I`'s `ReadCode`; H1's names left `src/` for `Test/.../H1Shapes.lean`), and the generated `Preds`
gained `ScopeExitOk` (the un-refused `ScopeState.closed.exit`), so every `Preds` instance on
another branch needs one line. M5 reduces to `denoteR_typed` only for programs without
layer-reference sites (tested; an owner decision, proposed below).

## Base and head

Base `bb269fde`. Commits on `seat/C`: `da71a491` (step 1, red by design), `4b6ea8fd` (step 2),
`d7487711` (row 137's order), `293aa874` (step 3), `b41d0808` (step 4), `12fb3716` (step 5),
`65c361d2` (step 6), `56a63f07` (`E4-TYPED-CE-010` restated against M5 over `J`), `6379c0a9`
(`E4-TYPED-CE-009` and `-010` against M5 and the capstone; `rreachable_load`), `570142a9` (seat B's
`preds_savedOk_mono` line declared), and the commit that adds this receipt (its child; its hash is
in the handback). No merge (denied; see "The merge, not done"). No push.

## Step 1 — the refutation re-established (commit red by design)

`Test/Counterexamples/Machine/Semantics/StaleCode.lean`, imported from `Test/All.lean` beside
`M6Capstone`. Restates the formal pass's probe A (`proofs/probes/StaleCode.lean`), the
verifier's `verify-probes/VerifySplit.lean` and probe C (`proofs/probes/HaltTyped.lean`) against
the merged typed state at the base (H1's `CodeInert`, the scheduler facts, H2's `ExitOk`); the cut
and split sections start from the synthesis seat's `ports-at-dceae006/HeadCut.lean` (its
compilation at `dceae006` is `port-HeadCut.log` beside it; the battery was compiled again here, at
`bb269fde`).

Coordinator corrections applied (messages of 2026-10-01): `capstone_false_finished9` and the
other finished-run refutations are not restated (at the base the finished run at budgets 7 and 9
is covered by H1's published-exit disjunct, `m7_root_inert`, `m9_root_inert`, proved), so
`E4-TYPED-CE-011` claims the cut only; probe C's facts are restated as holding by design at the
base (`CodeInert` tolerates a halt).

Command: `LEAN_NUM_THREADS=4 lake env lean -DwarningAsError=true
Test/Counterexamples/Machine/Semantics/StaleCode.lean` → exit 0, 51 axiom lines, 48 at
`[propext, Quot.sound]`, 3 at `[propext]` (`answerFree`, `halt_fiber?`, `halt_race?`), 0 with
`sorryAx` or `Classical.choice` (tested, `grep -c`). Then `LEAN_NUM_THREADS=4 lake build
Test.Counterexamples.Machine.Semantics.StaleCode` → exit 0 (378 jobs).

Proved at the base (reproduced: the formal pass and the synthesis port proved them first): the cut (`window6`, `m6_root_running`, `residue6_shape`, `residue6_machine`,
`m6_not_inert`, `window_untyped`, `capstone_false_window`, `ledger_jointly_false_window`); the
finished run covered by H1 (`finished7m`, `budget7_is_fuel_frontier`, `budget7_not_finished`,
`finished9`, `m9_root_stale`, `m7_root_inert`, `m9_root_inert`); the seat's split against the lift
(`seat_split_not_decisionLift`, red) and the running-keyed controls (`running_clause_vacuous_at_m6`,
`running_exempt_at_m6`, positive); the observation-level positive controls (`exitsTyped6`,
`exitsTyped7`); `worldValid_not_upward_closed`; probe C at the base (`typedState_halt`,
`queueOk_nil`, `halting_result_typed`, `typed_not_imply_running`), with the transport through the
generated skeleton that the base's machine-dependent `statePreds` forces (`finNameOk_tr`,
`scopeStateOk_tr`, `storesOk_tr`, `dispatcherOk_tr`, `runFiberOk_tr`, `countdownAt_halt`,
`storedObserverOk_halt`).

## Step 2 — row 134's split (`J`/`I`), the adapters restated, the statements over `J`

`src/Effect4/Laws/Program/Typed/Assembly.lean`. Encoding choice (the semantics are the brief's
and the coordinator's phrasing): the generated bundle is instantiated once, `preds root`, with
`SavedOk` = the stack and provenance only (`SavedPosition root w final saved`); current code is
typed by two hand clauses beside it, `LiveCode` (`J`: fibers neither exited nor running) and
`ReadCode` (`I`: running fibers a queued `loop`/`deliver` reads). In H1's vocabulary this is "a
running fiber that no queued `loop` or `deliver` continues is inert, read at the empty queue for
`J` and the real queue for `I`". Reason for the encoding (tested at step 1): H1's `statePreds root
m commands` made the generated bundle depend on the machine and the queue, so every transport
between two machines or two queues rebuilt the whole generated skeleton (stores, scope entries,
memo maps, dispatcher buckets, finalizer names by cases; see `StaleCode.lean`'s `H1` section,
nine lemmas for one halt). With the bundle independent of both, `J` after a step is `I`'s
projection, the fire snapshot splits off the queue by a list lemma, and `typedState_halt` for the
new generated part is three lines.

New definitions: `SavedPosition` (stack and provenance), `TypedState` (no queue argument),
`ReadsCode`, `LiveCode`, `ReadCode`, `MachineLive` (`running : m.stuck = none`; row 139's clauses
join at step 4), `MachineTyped` (`J`), `ConfigTyped` (`I`), `StepPreserves` (over `I`, dispatch
premise kept), `RTask`, `SnapshotTyped` (`O`), `LawfulSource` (rows 111–116 stand-in),
`LoadsTyped`, `DecisionKeeps`, `ReachableTyped` (the M5/M6b/M6c propositions, named once).
Removed from `src/` (kept as exact copies in `Test/.../H1Shapes.lean` for the historical
controls): `TerminalFiber`, `TerminalPosition`, `CodeInert`, `statePreds`, the queue argument of
`TypedState`.

Proved here (no command case): `savedPosition_of_saved`, `pending_below`,
`machineTyped_of_configTyped`, `machineTyped_not_halted`, `evaluate_entry` (the decision lift's
loop-entry premise holds for this split at every machine, a cut included),
`stepKeeps_of_stepPreserves`, `driveState_typed_of_stepPreserves` (Codex's two adapters restated
over `I`), `mem_taskCmds`, `taskCmd_owner`, `taskCmd_not_registrationDone`, `taskCmd_not_reads`,
`taskCmd_tail`, `registrationTail_mono`, `registrationQueue_append_tasks`,
`queueOk_append_tasks`, `readsCode_append_tasks`, `configTyped_append_tasks`,
`guarded_stepKeeps_of_stepPreserves` (the eighteen `StepPreserves` are exactly
`∀ ts, StepKeeps hostOrder interp (Guarded J I O ts)`), `admittedReplay_noHostAnswer`,
`reachable_of_ledger` (M6c from M5 and M6b through `replayEval_lift`), `capture_lookup`.

Batteries: `Test/Counterexamples/Machine/Semantics/H1Shapes.lean` (new support module, imported by
both batteries); `StaleCode.lean` (step-1 refutations retargeted to `H1Shapes`, historical; new
positive controls `liveCode_m6`, `machineTyped_m6`, `machineTyped_m9` — `J` holds at the cut and at
the finished run at an explicit world, `rootWorld` —, `capstone_window_holds`, `evaluate_entry_m6`;
probe C side by side: `H1.typedState_halt` holds under H1, the new `typedState_halt` holds for the
generated part, `machineTyped_not_halted_here` and `halting_result_outside` exclude every halted
machine from `J` and `I`); `M6Capstone.lean` (the reviewed and old bundles given back their full
saved-code clause; H1 sections retargeted to `H1Shapes`; new positive controls `machine_typed`,
`config_typed`, `result_config_typed`, `deliver_keeps_config` — H1's terminal witness keeps `I` —,
`completed_liveCode`; new red control `step_deliver_refuted_by_absent_scope`).

**New finding (proved): the queue-discard witness `E4-SCHED-CE-020` refutes the new
`step_deliver`.** With `stuck = none` in `J`, the worker's typed scope-exit callback for the absent
scope 0 halts the machine, and `fiberPre` admits `.scopeExit` on any scope
(`Laws/Program/Typed/Residual.lean:132`), so the input is a typed configuration and the output
is outside `J` (`M6Capstone.H1HaltAmendment.step_deliver_refuted_by_absent_scope`). The repair is a
scope-liveness premise on the scope-reading fiber rows (seat B's file; exact hunk below).

Commands: `LEAN_NUM_THREADS=4 lake build Effect4.Laws.Program.Typed.Assembly` → exit 0
(`M3bAssembly: 1 open, 1 proved, 2 total; ceiling 1`; `M6Ledger: 20 open, 0 proved, 20 total;
ceiling 20`); `LEAN_NUM_THREADS=4 lake build Effect4.Laws
Test.Counterexamples.Machine.Semantics.H1Shapes Test.Counterexamples.Machine.Semantics.M6Capstone
Test.Counterexamples.Machine.Semantics.StaleCode Test.Counterexamples.Machine.Semantics.ValueMembership
Test.Program.H2PartOne Test.Program.TypedStack` → exit 0 (538 jobs; the three dependents I do not own
build unchanged). `lake env lean -DwarningAsError=true` on the batteries: `StaleCode` 64 axiom
lines (61 `[propext, Quot.sound]`, 3 `[propext]`), `M6Capstone` 118 axiom lines (112 `[propext, Quot.sound]`, 6 `[propext]`) after the new
controls, none with `sorryAx`/`Classical.choice` (tested, `grep -c`).

## Step 2b — row 137's checker order at the raw sites in seat C's files (coordinator correction 3)

`CompletionStrong`'s reference arm (`Assembly.lean`), `FiberColumnsBelow` and `RacePayload.live`,
`RacePayload.programs` (`Scheduler.lean`) compare a declared type as the checker does,
`Ty.sub a.normalize b.normalize` (`Program/Checker.lean:222`), inline until seat A's `Ty.subN`
lands (then a rename). Narrow build exit 0 (538 jobs). Commit `d7487711`.

## Step 3 — M7 declared (row 138), its route proved, R4's bridge proved

`Assembly.lean`: `M7Fragment` (lawful source, empty host table, checked, closed, answer-free
tape), `ExitsFit`, `StoresFit`, `M7Exits`, `M7Stores`, `M7NoHalt`; the ledger scope `M7`
(`exits_typed` M7a, `stores_typed` M7b, `never_halts` M7c), each docstring naming the frame
machine (not "the compiled machine"), the OCaml engine outside until row 28, and R1's exception
(the service half of Σ_app with the row table fixed empty; DI-57's host-free part is R6's).
Proved: `obsTyped_of_machineTyped` (`J` types the observation), `replay_stuck_eq`,
`m7_of_capstone` and `m7_of_ledger` (M7a–c from `typedState_load` and `decision_preserves`
through `replayEval_lift`, `replay_rel`, `bookMeans_obs`, `BookMeans.stuck`), R4's
`replayEval_machine_prefix` and `replayR_bmeans_reachable` (every reference replay machine is
`BMeans`-related to a `Guard.Reachable` native machine at the empty table: the replay is a prefix
fold at constant budget; proved in about thirty lines, as the verifier expected).
Positive controls in `StaleCode.lean`: `m7_exits_at_cut`, `m7_exits_finished`,
`m7_no_halt_at_cut` (M7a and M7c's conclusions on the frame machine's replay of probe A's tape),
`cut_native_reachable` (R4 at the cut).

Probe-author lesson met again (tested): `m7_no_halt_at_cut` first written as an `Eq.trans` chain
over the concrete replay's `stuck` made the elaborator evaluate the replay (killed, exit 137, at
5.7 GB after 121 s under `-M6144`; bisected, the three other variants compile in 7 s); restated
through the generic `replay_stuck_eq` it compiles in 6 s.

Commands: `LEAN_NUM_THREADS=4 lake build Effect4.Laws.Program.Typed.Assembly` → exit 0
(`M7: 3 open, 0 proved, 3 total; ceiling 3`); the step-2 narrow build set → exit 0 (538 jobs);
`StaleCode.lean` under `lake env lean -M6144 -DwarningAsError=true` → exit 0 in 6 s, 68 axiom
lines, none with `sorryAx` or `Classical.choice`.

## Step 4 — row 139: halting freedom and liveness in `J` and `I`

`MachineLive` (in `J`) now carries `running : m.stuck = none` (step 2), `ambientScopes` (every
fiber context's ambient scope is held by the store: `forkScoped`'s link) and `dueOwners` (every
scheduled owed resume names an existing owner: `drainOwed`'s `postTask`; vacuous on today's
stores, which owe only `now` resumes). The stored and the queued scope-finalizer drops carry scope
liveness in `Scheduler.lean` (`StoredObserverOk` in `ObserverState`, `ObserverCommandOk` in
`QueueOk.observer`; `fireObserver` halts on an absent scope). `QueueOk.links` (in `I`): a queued
`link` names a live scope and an existing target (`linkScope`'s halting arms). Race-id liveness for
codes that name a race is `RegistrationState` (the only race halt is `registerRace` on the
registration marker, which both code clauses leave to it). Scope-handle validity (organization
M4) is the declared goal `M7.exitHandles_valid` (`ExitHandlesValid`: every recorded success exit's
value is `validIn` the stores on every reachable machine; the exit connector's premise). Probe C
flipped: `machineTyped_not_halted` (step 2).

The halting-site census these clauses answer (reading of `Machine/Fibers.lean` and
`Laws/Program/EvaluateR.lean` at `bb269fde`; each arm is an obligation of the command proof that
reaches it):

| Halting site | Reached by | Excluded by |
| --- | --- | --- |
| `postTask` unknown owner (`Fibers.lean:709-716`) | `drainDue`, the clock edits | `MachineLive.dueOwners` |
| `registerRace` unknown race (`:937-944`) | `loop` on a registration marker | `RegistrationState` (+ seat B: `fiberPre .raceRegister := False`) |
| `linkScope` unknown scope or target (`:1005-1036`) | `link`; `runIn` evaluated in `loop` | `QueueOk.links`; seat B's `runIn` pre |
| `fireObserver` scope drop (`:1668-1671`) | `observe`, `enrollRace` | `ObserverCommandOk`, `StoredObserverOk` |
| `FiberAction.closeScope` (`:1514-1523`) | `loop` | seat B: `fiberPre .closeScope` scope live |
| `FiberAction.interruptAs` unknown target (`:1534-1546`) | `loop` | seat B: `fiberPre .interruptAs` target declared |
| `FiberAction.join` unknown target (`:1604-1608`) | `loop` (await) | `fiberPre .await` (`Γ` declared) and `WorldValid.fibers` |
| `prepareScopedExitR` (`EvaluateR.lean:309-319`) | `loop`, `deliver` | seat B: `fiberPre .scopeExit` scope live (`step_deliver_refuted_by_absent_scope`) |
| `forkScoped` with an absent ambient scope (`:1474-1489` → `link`) | `loop` | `MachineLive.ambientScopes` (seat A's `HandleFits` scope arm via `ServiceOk` later) |

Red controls (`M6Capstone.Liveness`): `link_absent_halts`, `drop_absent_halts` (the halting
arms, by `decide +kernel`) and `link_absent_refused`, `drop_absent_refused` (the clauses refuse
exactly those configurations). The positive controls of steps 2–3 (`machineTyped_m6`,
`machineTyped_m9`, `machine_typed`, `config_typed`, `result_config_typed`, `config_input`)
carry the new fields.

Commands: `LEAN_NUM_THREADS=4 lake build Effect4.Laws.Program.Typed.Assembly
Test.Counterexamples.Machine.Semantics.H1Shapes` → exit 0 (`M7: 4 open`); batteries under
`lake env lean -M6144 -DwarningAsError=true`: `M6Capstone` exit 0, 123 axiom lines, `StaleCode`
exit 0, 68, none with `sorryAx`/`Classical.choice`; the narrow build set → exit 0.

## Step 5 — row 140: the ledger as the one list

`Assembly.lean`, `Scheduler.lean`, `Sources.lean`, `State.lean`.

**The decision edits and the fire snapshot.** `DecisionLift`'s thirteen fields
(`Laws/Machine/Lift.lean:308-355`) at `J`, `I`, `O = SnapshotTyped` and `AnswerOk`: `step` is the
eighteen (`guarded_stepKeeps_of_stepPreserves`, step 2); the other twelve are named propositions
(`EditNil`, `EditEvaluate`, `EditDrain`, `EditRan`, `EditTask`, `EditSkip`, `EditYield`,
`EditInterrupt`, `EditMiddleware`, `EditClockNone`, `EditClockSome`, `EditAnswer`), the lift seat's
`M6Edits` (`2026-09-30-pass/lift/Lift.lean:849-871`) restated over the split. Six are proved here
because the split makes them bookkeeping: `edit_nil` (`queueOk_nil`), `edit_evaluate`
(`evaluate_entry`), `edit_ran` and `edit_middleware` (`machineTyped_congr`: `J` moves between
machines with the same fibers, races, store, counters and halt), `edit_skip`
(`queueOk_append_tasks`), `edit_task` (the task's commands read no code, `not_readsCode_taskCmds`;
the queue facts survive the `ranTask` event, `queueOk_emit`, through `observerCommandOk_congr`).
The six with content are the structure `DecisionEdits` (drain, yield, interrupt, the two clock
steps, answer). `decisionLift_of_ledger` assembles the lift from the eighteen and `DecisionEdits`;
`decisionKeeps_of_ledger` gives `decision_preserves`'s proposition from them by
`stepDecisionState_lift` (proved). New in `Scheduler.lean`: `countdownAt_congr`,
`storedObserverOk_congr`, `observerCommandOk_congr`.

**The split's re-establishment.** `Reestablishes` (`J` after each command from `I` before it) is
proved from the eighteen (`reestablishes`): `I` contains `J`, so it is `ConfigTyped.machine` of
each command fact and costs no proof of its own. It is declared and closed in `M6Edits` so the
ledger shows it.

**Row 148.** `DenotesTyped root` (a checked point denotes, at the node its path names, a program
typed at the point's certificate, at every world) and `TermFits table` (term soundness at `Fits`,
at any row table, since term typing reads only the signature's atoms) are declared as
`M3bAssembly.denoteR_typed` and `M3bAssembly.evalTerm_fits` (M5's ledger, beside
`typedState_load`).

**M5's builder and its reduction (proved).** `machineTyped_load`: a root whose loaded code is
typed at every world, with no race marker at its head, loads into `J` at the initial world
(`machineLive_of_quiet` gives row 139's clauses on the quiet initial machine). `loadsTyped_of_denotesTyped`:
`DenotesTyped root` gives `LoadsTyped` for a program with no layer-reference sites. **Finding
(tested):** the premise is needed. `Api.typeOf` certifies the program's expansion
(`Program/Typing.lean:61-64`); the checker refuses a layer reference (`Program/Checker.lean:259`);
`loadR` loads the program as written and resolves references by redirect at run time
(`Laws/Program/DenoteR.lean:733-737`). The typed corpus's `layer.ref` program has
`Api.typeOf = some _`, a non-empty `refSites []`, and a checker refusal at the root
(`Test/Program/TypedSplit.lean`, three `#guard`s), so `PointTyped` fails at its root point and
`denoteR_typed` says nothing about its loaded code. Wave 2's M5 needs either a redirect agreement
(the raw program's denotation at a point equals the expansion's) or `denoteR_typed` stated over the
expansion with the loader loading it; the choice is the owner's (proposed row below).

**Stack monotonicity (row 135).** `StackMono root` and `SavedMono root` declared in scope `M6Stack`
(seat B's `M3bWorld` is in `Residual.lean`, not mine): false at these definitions by the algebra
pass's `stackAccepts_not_mono` (proved there with `FitsExit`; at `ExitOk` assumed, not checked
here). `savedMono_of_stackMono` (proved): the saved half follows from the stack half and
`M3bWorld.typedProg_mono`'s proposition. When seat B's Kripke closure merges, `M6Stack` is closed by
B's theorems (`#obligation_proved`) or deleted.

**The refused source row.** `ScopeState.closed.exit` is un-refused as `.custom "ScopeExitOk"`
(`Sources.lean`), stated in `preds` as `Fits w (reifyExitVal ex) (.exitOf .unknown .unknown)`
(DI-94's release type; `Fits`' `unknown` arm is `Live`). `Stores.externals` stays refused. The
producer's group (`make check-typed-state`'s eight targets, run one at a time with
`LEAN_NUM_THREADS=4`): `Effect4.Laws.Program.Typed.Frames` exit 0 (State's report: `typed state: 17
predicates, 11 carrier predicates, 1 refusals`, was `10`, `2`; the frame-rule reports unchanged:
`15 checked theorems, 81 reused clauses, 9 explicit premises` and `47 …, 71 …, 33 …`),
`Test.Audit.PositionCensus` exit 0 (the gate's report: `9 custom`, no `refused` position, one
refused row listed), `Test.Audit.PositionAnalysis` 0, `Test.Audit.TypedStateDecl` 0 after its
`Preds` instance gained the field, `Test.Audit.FrameRules` 0, `Test.Audit.ProofGraph` 0,
`Test.Audit.Obligations` 0, `Test.Program.TypedStateRulesRed` 0. The two expected outputs that
record the producer's report (`State.lean`'s and `PositionCensus.lean`'s `#guard_msgs`) were
updated to the producer's output; no generated file exists for this group (`docs/GENERATED.md`
§"Declarations generated during elaboration"). `Preds` gained a field, so the two other `Preds`
instances gained one line: `ValueMembership.lean`'s reviewed bundle (`ScopeExitOk _ _ _ := True`,
the row was refused when that judgment was reviewed) and `Test/Audit/TypedStateDecl.lean`'s
`readsMetadata`. `StaleCode.lean`'s `scopeStateOk_tr` closed arm is now `exact h`.

**Rows 111–112.** `LoadsTyped` and `ReachableTyped` take `LawfulSource root` (step 2; today
`Table.lawful root.table = true`; seat A's evidence field replaces the body). `w.serviceTy` does not
exist at the base; the exact clause for `TypedState` (`J`'s first field) is in "Lines for seat A".

Ledger after step 5 (the build's report): `M3bAssembly: 3 open, 1 proved, 4 total; ceiling 3`;
`M6Ledger: 20 open, 0 proved, 20 total; ceiling 20`; `M7: 4 open, 0 proved, 4 total; ceiling 4`;
`M6Edits: 6 open, 7 proved, 13 total; ceiling 6`; `M6Stack: 2 open, 0 proved, 2 total; ceiling 2`.

New battery `Test/Program/TypedSplit.lean` (imported from `Test/All.lean` after `StaleCode`):
`#print` of `J`, `I` and their clauses, the production `preds` and `ScopeStateOk`; `#print axioms`
for every theorem in `Assembly.lean` (48) and `Scheduler.lean` (11) and the ledger's eight checked
theorems; the layer-reference guards.

Commands: `LEAN_NUM_THREADS=4 lake build Effect4.Laws.Program.Typed.Assembly` → exit 0 (the
ledger lines above); the dependents (`H1Shapes`, `StaleCode`, `M6Capstone`, `ValueMembership`,
`Test.Program.H2PartOne`, `Test.Program.TypedStack`, `Test.Audit.IndexedColumnActual`), each
`LEAN_NUM_THREADS=4 lake build <module>` → exit 0; `LEAN_NUM_THREADS=4 lake env lean
-DwarningAsError=true Test/Program/TypedSplit.lean` → exit 0, 67 axiom lines, every one within
`[propext, Quot.sound]` (tested, `grep`).

## Step 6 — T1–T4

**T2, the capstone's docstring.** `M6Ledger.typedState_reachable` lists the live refutations at
this commit, `E4-TYPED-CE-009` (seat A, row 137) and `E4-TYPED-CE-010` (seat B, row 136), and not
the repaired `E4-PROV-CE-005`. `E4-TYPED-CE-011`, live at the base (step 1), is repaired by step
2's split (positive control `StaleCode.capstone_window_holds`), and `E4-TYPED-CE-014` by `J`'s
`stuck = none`; the docstring says so. Added: `M6Ledger.step_deliver`'s docstring names its live
refutation (`E4-SCHED-CE-020`'s witness under `J`, proved,
`M6Capstone.H1HaltAmendment.step_deliver_refuted_by_absent_scope`) and `step_loop`'s names the
same hazard through `loop` (assumed: a reading, not checked).

**T3, controls in `src/`.** None in `Assembly.lean`, `Sources.lean`, `Scheduler.lean` (tested:
`grep` for `example`, `#guard`, `#eval`, `#check`, `#print`, concrete programs; `State.lean`'s one
`#guard_msgs` is the producer's report, not a control). Seat A's: `World.lean`'s
`heapNotMonotone` (`:265`), `worldGood` (`:272`), `worldBad` (`:278`), the scope
`WorldControlWanted` (`:281-294`: `stores_ordered`, `heap_good`, `heap_bad`,
`world_order_refuses`, `invalid_refl`) and their proofs at `:726-760`. Seat B's: `Contracts.lean`'s `namespace Example`
(`:86-105`).

**Codex's comment-only corrections, re-read** (`bd142695`): `M6Capstone.lean`'s header and the
two comments at `ReviewedRReachable`/`current_m6_capstone_false` hold for the new statements; the
second now adds that the refuted conclusion is `J`'s first clause, so `J` fails there too.
`Assembly.lean`'s capstone sentence on the historical host-free obstructions (`E4-PROV-CE-005`,
`-006`, `E4-SCHED-CE-016`, "local repairs in F, G and H1") is replaced by the live list: H1's
repair is superseded by the split, and `E4-SCHED-CE-016`'s key-freshness repair stays in `J`
(`TypedState`'s internal keys) and `I` (`QueueOk.keys`).

**T4, the label.** "M7" on the old machine repair (the S2 spike's "M7 — the scope hooks can say
unknown", `docs/research/2026-09-03-spike-s2-stores-witnesses.md:417`) is now "S2-M7" at
`Laws/Machine/Witnesses.lean:60`, `:1059`, `:1062`, `Laws/Machine/Clauses.lean:827`, `:1627` (the
same label, same file, not in the brief's list) and `Laws/Machine/StoresLaws.lean:640`. Left for
the coordinator (machine files, no seat's): `Machine/Fibers.lean:565`, `:573`, `:1004`,
`Machine/Stores.lean:1928`, `:1963`. T4's other collisions (`World`, two `pure_inv`, two
`Reachable`, `Denote.ExitOk` beside `Typed.ExitOk`) are in files no brief gives me: owed.

Commands: `LEAN_NUM_THREADS=4 lake build Effect4.Laws.Machine.Witnesses
Effect4.Laws.Machine.Clauses Effect4.Laws.Machine.StoresLaws` → exit 0 (203 jobs);
`LEAN_NUM_THREADS=4 lake build Effect4.Laws.Program.Typed.Assembly
Test.Counterexamples.Machine.Semantics.M6Capstone` → exit 0 (ledger unchanged from step 5).

**After step 6: `E4-TYPED-CE-010` against the restated M5** (`56a63f07`).
`Test/Counterexamples/Machine/Semantics/AwaitLoad.lean` copies the synthesis seat's tracked port
(`ports-at-dceae006/HeadAwaitLoad.lean`; amendment 1; its `root_code_refused` is reproduced here)
and proves `loadsTyped_false` (`:107`):
at the typed corpus's `awaitFiber.value`, fuel 5, `LoadsTyped` is false, because `J`'s `LiveCode`
types the loaded root (not exited, not running, no race marker) and `root_code_refused` (`:73`,
the port's) refuses its code at every load world. So M5 as restated over `J` is refuted at this
commit (proved) until seat B's await-by-value post lands (row 136). `step_loop`'s docstring and
`M6Stack`'s now cite `E4-TYPED-CE-012` (the coordinator's register names it; at `dceae006`
`step_loop_refuted` refutes the old statement; not re-run against the split here, so "expected to
carry" is assumed).

**Follow-ups after step 6.** `6379c0a9`: `RawOrderLoad.lean` copies the synthesis seat's tracked
port `HeadM5Fits.lean` (amendment 1; `leaf_false`, `fiber_inv` and `m5_false`'s body reproduced)
and reads the loaded root's code through `J`'s `LiveCode`: `m5_false` (`:76`), `loadsTyped_false`
(`:129`) and `capstone_false` (`:133`) prove `E4-TYPED-CE-009` against M5's and the capstone's
statements over `J`; `AwaitLoad.capstone_false` does the same for `E4-TYPED-CE-010`; the empty
tape reaches the load (`rreachable_load`, `replayR_nil_machine`, `Assembly.lean`, beside
`reachable_of_ledger`), and the capstone's docstring names the four refutations. `570142a9`:
seat B's ledger line `preds_savedOk_mono` (row 87's transport for the bundle's `SavedOk`) declared
in `M6Stack`, open here (`StackAccepts` is not closed under world growth until B's frames merge).

## The final build

`LEAN_NUM_THREADS=4 lake build Effect4.Laws Test.All`. The first run (after step 6) built 710 of
710 jobs and failed only at the module-closure gate, because I had written `AwaitLoad.lean` into the
tree during the run without importing it (`Test/All.lean:147: … is not reachable from the Test.All
audit root`; 6 min 54 s). After each follow-up commit the build was run again (incremental); the
last run, on `570142a9`: exit 0, `Build completed successfully (712 jobs)`, 1 min 41 s, with the
gate's report "`Effect4 module and axiom gate: checked 495 modules and 69613 declarations;
semantic/test axioms are [propext, Quot.sound]; exact implementation boundary (15 module(s), 23
declaration(s)) additionally allows Classical.choice`" (tested). Axiom lines in this seat's
batteries, in the last run's log: `StaleCode` 68, `M6Capstone` 123,
`TypedSplit` 69, `AwaitLoad` 7, `RawOrderLoad` 5, `H1Shapes` 1, `ValueMembership` 51; none with
`sorryAx` or `Classical.choice` (tested, `grep`; long names wrap their `[propext,\n Quot.sound]`).

## The merge, not done

Asked (coordinator, after seat B merged on `refactor/phase1-phase3`): merge that branch into
`seat/C` here, repair seat B's two batteries and its hunks under the split, rebuild
`Effect4.Laws Test.All`, and write this receipt with the merge commit named. Done: nothing of the
merge. `git merge --no-ff --no-commit refactor/phase1-phase3` in this worktree was denied by the
permission system, and so was a following read of seat B's merged sources for the repairs; I tried
no other route. The worktree is clean at `570142a9` (tested, `git status --short` empty).

Tested before the denial (read-only): `git merge-tree --write-tree --name-only HEAD
refactor/phase1-phase3` with `HEAD = 6379c0a9` and the branch at `b9d0d19f` printed the tree
`b7a47d36` and no conflicted path; `570142a9` since then touches only `Assembly.lean`'s `M6Stack`,
a file seat B did not edit (receipt-B, "No edit in `Assembly.lean`").

Expected at the merge (assumed: from seat B's receipt, "For seat C", not from building the merge):

1. `M6Capstone.lean`: B's three-lambda hunk (the closed `answer` and `resume` arms) applies
   textually; keep it.
2. B's `Test/Program/FramesNotKripke.lean` (`typed_of`, `afterGood_typed`, the queue proofs) and
   `Test/Program/ProtocolPosts.lean` (`AwaitLoad.OldLoaded`) build typed states through `TypedState`
   with a queue argument, the old `savedPosition_of_saved`, `QueueOk` without `links`, and a stores
   component whose closed-exit arm was `trivial`. Under the split: `TypedState root rootTy w m` (no
   queue), `savedPosition_of_saved root w ty saved typed`, `links` (vacuous on a queue with no
   `link`: `fun _ _ _ _ _ h => nomatch h` after `cases` on membership, as `M6Capstone`'s
   `config_typed` does), the closed-exit arm `(preds root).ScopeExitOk`; where a construction is
   historical, the `H1Shapes` route (`StaleCode.lean`, `M6Capstone.lean`) is the model.
3. `AwaitLoad.loadsTyped_false` and `capstone_false`: seat B repaired the await-by-value post
   (receipt-B: `E4-TYPED-CE-010` repaired), so `root_code_refused` should stop compiling; keep the
   refutation over the old post as history and add the positive control (`J` at the load of
   `awaitFiber.value` by `machineTyped_load` with B's typed await code).
4. `M6Stack`: closed by B's `Contracts.stackAccepts_mono` and `savedOk_mono` (`#obligation_proved`
   with an argument-order adapter) and `preds_savedOk_mono` by B's proof read through the
   split's bundle, or the scope deleted in favour of B's `M3bWorld`.
5. `step_deliver_refuted_by_absent_scope`: if B's `fiberPre` now carries scope liveness on
   `.scopeExit` (B's receipt names scope liveness on the scope rows' store pres), the control stops
   compiling and becomes the refusal of that input; if not, "Lines for seat B" item 1 still applies.
6. B's `storeTyped_of_typedState` for wave 2's `loop` arm becomes `MachineTyped root rootTy w m →
   StoreTyped w` here (owed after the merge: `StoreTyped` is B's).
7. Then `LEAN_NUM_THREADS=4 lake build Effect4.Laws Test.All`, and the receipt's numbers re-read.

## Every changed path (`bb269fde..570142a9`, plus this receipt)

| Path | Change |
| --- | --- |
| `src/Effect4/Laws/Program/Typed/Assembly.lean` | the split `J`/`I`, the ledger scopes `M3bAssembly`, `M6Ledger`, `M6Edits`, `M6Stack`, `M7`, the adapters, M5's builder and reduction, M7's route, R4's bridge, `rreachable_load` |
| `src/Effect4/Laws/Program/Typed/Scheduler.lean` | row 137's order (`FiberColumnsBelow`, `RacePayload`), the scope-drop arms, the congruences |
| `src/Effect4/Laws/Program/Typed/Sources.lean` | `ScopeState.closed.exit` un-refused as `ScopeExitOk` |
| `src/Effect4/Laws/Program/Typed/State.lean` | the producer's report (`11 carrier predicates, 1 refusals`) |
| `src/Effect4/Laws/Machine/Witnesses.lean`, `Clauses.lean`, `StoresLaws.lean` | "M7" → "S2-M7" in six comments |
| `Test/All.lean` | imports `StaleCode`, `AwaitLoad`, `RawOrderLoad`, `TypedSplit` after `M6Capstone` |
| `Test/Audit/PositionCensus.lean` | the gate's report (`9 custom`, one refused row) |
| `Test/Audit/TypedStateDecl.lean` | `readsMetadata` gains `ScopeExitOk` |
| `Test/Counterexamples/Machine/Semantics/StaleCode.lean` (new) | step 1's refutations (historical), the split's controls, M7's controls, probe C side by side |
| `Test/Counterexamples/Machine/Semantics/H1Shapes.lean` (new) | H1's definitions as merged at `bb269fde`, for the historical controls |
| `Test/Counterexamples/Machine/Semantics/AwaitLoad.lean` (new) | `E4-TYPED-CE-010` against M5 and the capstone over `J` |
| `Test/Counterexamples/Machine/Semantics/RawOrderLoad.lean` (new) | `E4-TYPED-CE-009` against M5 and the capstone over `J` |
| `Test/Counterexamples/Machine/Semantics/M6Capstone.lean` | the reviewed bundles' full saved-code clause; H1 sections on `H1Shapes`; the split's controls; `step_deliver_refuted_by_absent_scope`; `Liveness` |
| `Test/Counterexamples/Machine/Semantics/ValueMembership.lean` | its reviewed `preds` gains `ScopeExitOk _ _ _ := True` |
| `Test/Program/TypedSplit.lean` (new) | `J`/`I` printed, axioms of every landed theorem, the layer-reference guards |
| `docs/research/2026-10-01-landing/receipt-C.md` (new, force-added) | this receipt |

## `J` and `I` as printed

`#print` in `Test/Program/TypedSplit.lean` (as `proofs/probes/PrintTypedState.lean` prints the
generated structures); the constructor lines, which repeat the fields, are omitted.

```
structure MachineTyped (root : ProgramSource) (rootTy : EffTy) (w : World) (m : RState) : Prop
  typed : TypedState root rootTy w m
  code  : LiveCode root w m
  live  : MachineLive m

def TypedState root rootTy w m :=
  WorldValid rootTy w m ∧ RStateOk (preds root) w m ∧
    ActiveDelivery root w m ∧ SchedulerState m ∧ ObserverState root w m ∧ RegistrationState root w m

def LiveCode root w m :=
  ∀ f ∈ m.fibers, f.exit = none → f.running = false → raceRegistrationR f.frame.current = none →
    ∀ ty, w.Γ f.id = some ty → Contracts.SavedOk (TypedProg root) ExitOk (frameProtocols root) w ty f.frame

structure MachineLive (m : RState) : Prop
  running       : m.stuck = none
  ambientScopes : ∀ f ∈ m.fibers, ∀ scope, f.context.ambientScope = some scope →
                    (m.state.scopes.entryAt scope).isSome = true
  dueOwners     : ∀ o ∈ m.state.deferreds.due, ∀ owner priority,
                    o.mode = WakeMode.scheduled owner priority → (m.fiber? owner).isSome = true

structure ConfigTyped (root : ProgramSource) (rootTy : EffTy) (w : World) (m : RState)
    (commands : List RCmd) : Prop
  machine : MachineTyped root rootTy w m
  code    : ReadCode root w m commands
  queue   : QueueOk root w m commands

def ReadCode root w m commands :=
  ∀ f ∈ m.fibers, f.running = true → ReadsCode f.id commands → raceRegistrationR f.frame.current = none →
    ∀ ty, w.Γ f.id = some ty → Contracts.SavedOk (TypedProg root) ExitOk (frameProtocols root) w ty f.frame

def ReadsCode id commands := ∃ yielding, Cmd.loop id yielding ∈ commands ∨ Cmd.deliver id yielding ∈ commands

structure QueueOk (root : ProgramSource) (w : World) (m : RState) (commands : List RCmd) : Prop
  payload   : ∀ command ∈ commands, RCmdOk (preds root) w command
  authority : ∀ command ∈ commands, CommandAuthorityR m command
  delivery  : ∀ command ∈ commands, CommandDeliveryOk root w m command
  owners    : (commands.filterMap (Guard.commandOwner m)).Nodup
  registration : Guard.RegistrationQueue.RegistrationQueue commands
  keys      : ReservedKeysR m (commands.flatMap Guard.commandKeys)
  observer  : ∀ source exit observer, Cmd.observe source exit observer ∈ commands →
                ObserverCommandOk root w m source exit observer
  enroll    : ∀ race child, Cmd.enrollRace race child ∈ commands → EnrollRaceOk root w m race child
  noRaceAfterInterrupt : ∀ host yielding race, ¬ Cmd.afterInterrupt host yielding (ParkKind.race race) ∈ commands
  links     : ∀ mode scope target interruptor extra, Cmd.link mode scope target interruptor extra ∈ commands →
                (m.state.scopes.entryAt scope).isSome = true ∧ (m.fiber? target).isSome = true

def StepPreserves root rootTy cmd :=
  ∀ w m rest, m.stuck = none → ConfigTyped root rootTy w m (cmd :: rest) →
    have r := driveStep (interpR root.program) m cmd rest
    ∃ w', w.leHost w' ∧ ConfigTyped root rootTy w' r.fst r.snd

def preds root : Preds World :=
  { SavedOk      := fun w e x => ∀ ty, expectOf w e = some ty → SavedPosition root w ty x
    PendingOk    := fun w _ ps => ∀ p ∈ ps, ∃ id, (w.Θ id p.token).isSome = true
    exit         := fun w e ex => ∀ ty, expectOf w e = some ty → ExitOk w ty ex
    ResumeOk     := fun w _ target token code => Contracts.ResumeOk (TypedProg root) w target token code
    ServiceOk    := fun w _ ctx => ServicesFit w ctx.services
    RaceOk       := fun w _ races => ∀ r ∈ races, ∃ resultTy, RacePayload root w r resultTy
    PromiseTable := fun w s => ∀ o ∈ s.deferreds.due, ∀ ty, w.Θ o.waiter o.token = some ty →
                      CompletionStrong w ty o.code
    HeapCell     := fun w key v => ∀ ty, w.Ρ key = some ty → Fits w v ty
    PromiseCell  := fun w key cell => ∀ a e, w.Π key = some (a, e) →
                      ∀ c, cell.completion = some c → CompletionStrong w ⟨a, e, Requirement.empty⟩ c
    CaptureOk    := fun w _ c => CaptureTyped root w c
    ScopeExitOk  := fun w _ ex => Fits w (reifyExitVal ex) (Ty.unknown.exitOf Ty.unknown) }

def ScopeStateOk P w e x := match x with
  | .empty | .openEmpty => True
  | .openInline key finalizer => FinNameOk P w e finalizer
  | .openMap entries => ∀ v0 ∈ entries, FinNameOk P w e v0.snd
  | .closed exit => P.ScopeExitOk w e exit
```

`SavedPosition root w final saved := ∃ tin, StackAccepts (TypedProg root) ExitOk (frameProtocols
root) w tin final saved.stack ∧ InterruptProvenance saved` (the stack and provenance; current code is
`LiveCode`'s and `ReadCode`'s).

## The per-command table of `I`'s code lines

As written in `Assembly.lean`'s module docstring (reading of `Machine/Fibers.lean` at `bb269fde`,
Codex's H1 resolution README for the census H1 left open):

| Command | Reads the fiber's current code? | Typing in `I` |
| --- | --- | --- |
| `loop id` | yes: `iteration` evaluates it (`:1857-1860`) | `ReadCode`: the code with its stack at `Γ id` |
| `deliver id` | yes: the evaluator pops the delivered value (`:1861-1864`) | `ReadCode` |
| `finish id ex` | no: `exitFiber` publishes `ex` or installs the middleware program (`:1983-1988`, `:1772-1803`) | `QueueOk.payload`: `ex` at `Γ id` (row 133) |
| `registrationDone race` | the marker's head only (`CommandAuthorityR`); replaced by the settle program, or parked (`:1912-1931`) | `RegistrationState`: the race token's result meets the saved stack |
| `afterInterrupt host kind` | no: replaced by `asVoid(awaitCode kind)` (`:1939-1944`) | `QueueOk.delivery`: `AfterInterruptReply`, `StackReply` |
| `raceCancel race host` | no: walks to `afterInterrupt host (awaitAll visited)` (`:1945-1955`) | `QueueOk.delivery`: `FiberListColumns`, `StackReply unit` |
| `closeParAwait host fibers` | no: pushes the iterator frame, installs the await-all park (`:1971-1979`) | `QueueOk.delivery`: the iterator protocol, `StackReply` |

No other command reads a running fiber's code: `evaluate` reads the flags and is a no-op on a
running fiber (`:1849-1856`); `resume` overwrites a parked fiber's code (`:1865-1878`); `launch` and
`enrollRace` spawn and observe while the host waits for its `registrationDone` (`:1879-1911`);
`interruptTarget` records an interrupt and overwrites only an idle interruptible target's code
(`interruptRecord`, `:803-824`); `trackChild`, `observe`, `exitDone`, `link`, `drainDue` and `wake`
read no code. A fiber whose current code is a race registration marker is typed by
`RegistrationState`, not by `TypedProg`: `beginRace` alone installs the marker
(`Laws/Program/InterpR.lean:320`), so both code clauses skip it.

## The ledger, before and after

Per scope, as `#typed_state_obligations` reports. After: the last final build's log, on
`570142a9` (tested). Before: counted from the base's sources (`git show bb269fde:…`, the
`#proof_wanted` and `#obligation_proved` lines and the ceilings; the base was not rebuilt here).

| Scope | Before (`bb269fde`) | After (`570142a9`) |
| --- | --- | --- |
| `M3bAssembly` (M5) | 1 open, 1 proved, 2 total; ceiling 1 | 3 open, 1 proved, 4 total; ceiling 3 (`+ denoteR_typed`, `evalTerm_fits`) |
| `M6Ledger` (M6) | 20 open, 0 proved, 20 total; ceiling 20 | 20 open, 0 proved, 20 total; ceiling 20 (restated over `I`/`J`) |
| `M6Edits` (R3) | absent | 6 open, 7 proved, 13 total; ceiling 6 |
| `M6Stack` (rows 135, 87) | absent | 3 open, 0 proved, 3 total; ceiling 3 |
| `M7` (row 138) | absent | 4 open, 0 proved, 4 total; ceiling 4 |
| `M3bWorld`, `M4Handshake`, `Test.IndexedColumnDraft` (not this seat's) | 1, 1, 1 open | unchanged |
| the whole tree (79 report lines, deduplicated) | 24 open, 436 proved, 460 total (derived: after minus this seat's additions) | 39 open, 443 proved, 482 total |

Open in this seat's scopes: 21 before, 36 after; every addition is a declaration the formal pass
or seat B found missing (T1; B's row 87 line), and seven of the new goals are closed here. After
the merge with seat B, `M6Stack`'s three should close from B's `Contracts.stackAccepts_mono`,
`savedOk_mono` (`M3bWorld`, 0 open on B's branch per receipt-B) and the bundle's shape (assumed).

## Theorems landed in `src/` (name, file:line at head, axioms)

All printed by `Test/Program/TypedSplit.lean`; the trust ceiling is `[propext, Quot.sound]`.

| Theorem | Where | Axioms |
| --- | --- | --- |
| `savedPosition_of_saved` | `Assembly.lean:127` | `[propext, Quot.sound]` |
| `pending_below` | `Assembly.lean:150` | `[propext, Quot.sound]` |
| `QueueOk.fresh` | `Assembly.lean:200` | `[propext, Quot.sound]` |
| `machineTyped_of_configTyped` | `Assembly.lean:272` | `[propext, Quot.sound]` |
| `machineTyped_not_halted` | `Assembly.lean:277` | `[propext, Quot.sound]` |
| `evaluate_entry` | `Assembly.lean:287` | `[propext, Quot.sound]` |
| `stepKeeps_of_stepPreserves` | `Assembly.lean:326` | `[propext, Quot.sound]` |
| `driveState_typed_of_stepPreserves` | `Assembly.lean:336` | `[propext, Quot.sound]` |
| `mem_taskCmds` | `Assembly.lean:364` | `[propext, Quot.sound]` |
| `taskCmd_owner` | `Assembly.lean:387` | `[propext, Quot.sound]` |
| `taskCmd_not_registrationDone` | `Assembly.lean:392` | `[propext, Quot.sound]` |
| `taskCmd_not_reads` | `Assembly.lean:399` | `[propext, Quot.sound]` |
| `taskCmd_not_link` | `Assembly.lean:406` | `[propext, Quot.sound]` |
| `taskCmd_tail` | `Assembly.lean:414` | `[propext, Quot.sound]` |
| `registrationTail_mono` | `Assembly.lean:419` | `[propext]` |
| `registrationQueue_append_tasks` | `Assembly.lean:447` | `[propext, Quot.sound]` |
| `queueOk_append_tasks` | `Assembly.lean:489` | `[propext, Quot.sound]` |
| `readsCode_append_tasks` | `Assembly.lean:562` | `[propext, Quot.sound]` |
| `configTyped_append_tasks` | `Assembly.lean:577` | `[propext, Quot.sound]` |
| `guarded_stepKeeps_of_stepPreserves` | `Assembly.lean:595` | `[propext, Quot.sound]` |
| `machineTyped_congr` | `Assembly.lean:624` | `[propext, Quot.sound]` |
| `queueOk_emit` | `Assembly.lean:707` | `[propext, Quot.sound]` |
| `envTyped_append` | `Assembly.lean:720` | `[propext, Quot.sound]` |
| `capture_lookup` | `Assembly.lean:744` | `[propext, Quot.sound]` |
| `machineLive_of_quiet` | `Assembly.lean:817` | `[propext]` |
| `machineTyped_load` | `Assembly.lean:828` | `[propext, Quot.sound]` |
| `envTyped_nil` | `Assembly.lean:886` | `[propext, Quot.sound]` |
| `loadsTyped_of_denotesTyped` | `Assembly.lean:893` | `[propext, Quot.sound]` |
| `savedMono_of_stackMono` | `Assembly.lean:931` | `[propext, Quot.sound]` |
| `admittedReplay_noHostAnswer` | `Assembly.lean:941` | `[propext, Quot.sound]` |
| `reachable_of_ledger` | `Assembly.lean:963` | `[propext, Quot.sound]` |
| `replayR_nil_machine` | `Assembly.lean:977` | `[propext, Quot.sound]` |
| `rreachable_load` | `Assembly.lean:987` | `[propext, Quot.sound]` |
| `queueOk_nil` | `Assembly.lean:1004` | `[propext, Quot.sound]` |
| `not_readsCode_taskCmds` | `Assembly.lean:1012` | `[propext]` |
| `edit_nil` | `Assembly.lean:1095` | `[propext, Quot.sound]` |
| `edit_evaluate` | `Assembly.lean:1097` | `[propext, Quot.sound]` |
| `edit_ran` | `Assembly.lean:1100` | `[propext, Quot.sound]` |
| `edit_middleware` | `Assembly.lean:1104` | `[propext, Quot.sound]` |
| `edit_skip` | `Assembly.lean:1108` | `[propext, Quot.sound]` |
| `edit_task` | `Assembly.lean:1114` | `[propext, Quot.sound]` |
| `decisionLift_of_ledger` | `Assembly.lean:1125` | `[propext, Quot.sound]` |
| `decisionKeeps_of_ledger` | `Assembly.lean:1146` | `[propext, Quot.sound]` |
| `reestablishes` | `Assembly.lean:1163` | `[propext, Quot.sound]` |
| `obsTyped_of_machineTyped` | `Assembly.lean:1239` | `[propext, Quot.sound]` |
| `replay_stuck_eq` | `Assembly.lean:1253` | `[propext, Quot.sound]` |
| `m7_of_capstone` | `Assembly.lean:1260` | `[propext, Quot.sound]` |
| `m7_of_ledger` | `Assembly.lean:1289` | `[propext, Quot.sound]` |
| `replayEval_machine_prefix` | `Assembly.lean:1307` | `[propext, Quot.sound]` |
| `replayR_bmeans_reachable` | `Assembly.lean:1328` | `[propext, Quot.sound]` |
| `reifyExitVal_fits` | `Scheduler.lean:32` | `[propext, Quot.sound]` |
| `observerDeliveredExit_fits` | `Scheduler.lean:36` | `[propext, Quot.sound]` |
| `observer_exitValue_typed` | `Scheduler.lean:44` | `[propext, Quot.sound]` |
| `countdownAt_congr` | `Scheduler.lean:159` | `[propext, Quot.sound]` |
| `storedObserverOk_congr` | `Scheduler.lean:181` | `[propext, Quot.sound]` |
| `observerCommandOk_congr` | `Scheduler.lean:201` | `[propext, Quot.sound]` |
| `registrationState_load` | `Scheduler.lean:263` | `[propext, Quot.sound]` |
| `observerCommand_resume_typed` | `Scheduler.lean:329` | `[propext, Quot.sound]` |
| `requestOfR_load_none` | `Scheduler.lean:341` | `[propext, Quot.sound]` |
| `schedulerState_load` | `Scheduler.lean:354` | `[propext, Quot.sound]` |
| `observerState_load` | `Scheduler.lean:399` | `[propext, Quot.sound]` |
| `M3bAssembly.capture_lookup.checked` | ledger (`#obligation_proved`) | `[propext, Quot.sound]` |
| `M6Edits.nil.checked` | ledger (`#obligation_proved`) | `[propext, Quot.sound]` |
| `M6Edits.evaluate.checked` | ledger (`#obligation_proved`) | `[propext, Quot.sound]` |
| `M6Edits.ran.checked` | ledger (`#obligation_proved`) | `[propext, Quot.sound]` |
| `M6Edits.task.checked` | ledger (`#obligation_proved`) | `[propext, Quot.sound]` |
| `M6Edits.skip.checked` | ledger (`#obligation_proved`) | `[propext, Quot.sound]` |
| `M6Edits.middleware.checked` | ledger (`#obligation_proved`) | `[propext, Quot.sound]` |
| `M6Edits.reestablish.checked` | ledger (`#obligation_proved`) | `[propext, Quot.sound]` |

The table lists every theorem in the two files. Present at the base by name: `QueueOk.fresh`,
`capture_lookup`, `envTyped_append`, `pending_below` (re-checked under the new definitions),
`savedPosition_of_saved`, `stepKeeps_of_stepPreserves`, `driveState_typed_of_stepPreserves`
(restated over `I`), and `Scheduler.lean`'s `reifyExitVal_fits`, `observerDeliveredExit_fits`,
`observer_exitValue_typed`, `registrationState_load`, `observerCommand_resume_typed`,
`requestOfR_load_none`, `schedulerState_load`, `observerState_load` (re-checked). Every other row
is new from this seat. The ledger's declarations (`M3bAssembly.*`, `M6Ledger.*`, `M6Edits.*`,
`M6Stack.*`, `M7.*`) are `⟨⟩` markers and carry no axioms.

## The battery theorems that carry the evidence (file:line at head; all `[propext, Quot.sound]` or less)

| Theorem | Where | Kind |
| --- | --- | --- |
| `window_untyped`, `capstone_false_window`, `ledger_jointly_false_window` | `StaleCode.lean:228`, `:239`, `:278` | red, historical: `E4-TYPED-CE-011` at the base's statements (`H1Shapes`) |
| `seat_split_not_decisionLift` | `StaleCode.lean:339` | red: a split keyed on queued `finish` breaks the lift's entry premise |
| `running_clause_vacuous_at_m6`, `running_exempt_at_m6` | `StaleCode.lean:366`, `:387` | positive: the split keyed on `running` |
| `liveCode_m6`, `machineTyped_m6`, `machineTyped_m9`, `capstone_window_holds`, `evaluate_entry_m6` | `StaleCode.lean:586`, `:816`, `:820`, `:824`, `:830` | positive: `J` at the cut and at the finished run; the new capstone's proposition holds at the cut |
| `m7_exits_at_cut`, `m7_exits_finished`, `m7_no_halt_at_cut`, `cut_native_reachable` | `StaleCode.lean:842`, `:846`, `:850`, `:854` | positive: M7a and M7c's conclusions on probe A; R4 at the cut |
| `exitsTyped6`, `exitsTyped7`, `worldValid_not_upward_closed` | `StaleCode.lean:407`, `:408`, `:412` | probe A's observation-level controls |
| `H1.typedState_halt`, `H1.halting_result_typed`, `H1.typed_not_imply_running` / `typedState_halt`, `machineTyped_not_halted_here`, `halting_result_outside` | `StaleCode.lean:529`, `:564`, `:571` / `:864`, `:883`, `:889` | probe C, old and new side by side |
| `machine_typed`, `config_typed`, `result_config_typed`, `deliver_keeps_config`, `completed_liveCode` | `M6Capstone.lean:1640`, `:1648`, `:1690`, `:1705`, `:1711` | positive: H1's terminal witness keeps `I` (`E4-SCHED-CE-019` under the split) |
| `config_input`, `output_outside`, `step_deliver_refuted_by_absent_scope` | `M6Capstone.lean:2340`, `:2360`, `:2373` | red: `E4-SCHED-CE-020`'s witness refutes the new `step_deliver` |
| `link_absent_halts`, `drop_absent_halts`, `link_absent_refused`, `drop_absent_refused` | `M6Capstone.lean:2398`, `:2403`, `:2408`, `:2414` | red/positive: the halting arms and the clauses that refuse them |
| `loadsTyped_false`, `capstone_false` (with the port's `root_code_refused`) | `AwaitLoad.lean:107`, `:128` (`:73`) | red: `E4-TYPED-CE-010` against M5 and the capstone over `J` |
| `m5_false`, `loadsTyped_false`, `capstone_false` | `RawOrderLoad.lean:76`, `:129`, `:133` | red: `E4-TYPED-CE-009` against M5 and the capstone over `J` |
| the three `#guard`s on `layerRef` | `TypedSplit.lean` | tested: M5's reduction needs a reference-free program |

## Statements changed (old at `bb269fde` / new at head)

| Statement | Old | New |
| --- | --- | --- |
| `TypedState` | `TypedState root rootTy w m (commands := [])` := `WorldValid ∧ RStateOk (statePreds root m commands) w m ∧ ActiveDelivery ∧ SchedulerState ∧ ObserverState ∧ RegistrationState` | `TypedState root rootTy w m` := the same six with `preds root` (no machine, no queue); `J = MachineTyped` adds `LiveCode` and `MachineLive` |
| the bundle's `SavedOk` | `SavedPosition root w m commands position ty saved` := `∃ tin, (¬ CodeInert m commands position → TypedProg root w tin saved.current) ∧ StackAccepts … ∧ InterruptProvenance saved` | `SavedPosition root w ty saved` := `∃ tin, StackAccepts … ∧ InterruptProvenance saved`; current code is typed by `LiveCode` (`J`: not exited, not running) and `ReadCode` (`I`: running, read by a queued `loop`/`deliver`), race markers left to `RegistrationState` |
| `CodeInert` | `m.stuck.isSome = true ∨ TerminalPosition m commands position` (H1) | removed from `src/` (kept in `Test/.../H1Shapes.lean`); the halted disjunct is gone (row 139), the queued-finish disjunct is `I`'s `finish` line (`QueueOk.payload`), the published-exit disjunct is `LiveCode`'s `f.exit = none` |
| `StepPreserves root rootTy cmd` | `∀ w m rest, m.stuck = none → TypedState … w m (cmd :: rest) → QueueOk root w m (cmd :: rest) → ∃ w', w.leHost w' ∧ TypedState … w' r.1 r.2 ∧ QueueOk root w' r.1 r.2` | `∀ w m rest, m.stuck = none → ConfigTyped root rootTy w m (cmd :: rest) → ∃ w', w.leHost w' ∧ ConfigTyped root rootTy w' r.1 r.2`; `ConfigTyped` contains `J`, so a step that halts violates it |
| `typedState_load` (M5) | `Api.typeOf root.program root.table = some rootTy → ClosedEff rootTy → ∃ w, TypedState root rootTy w (loadR …)` | `LoadsTyped`: `LawfulSource root → Api.typeOf … = some rootTy → ClosedEff rootTy → ∃ w, MachineTyped root rootTy w (loadR …)` |
| `decision_preserves` (M6b) | `∀ w m, TypedState … w m → AnswerOk w m d → ∃ w', w.leHost w' ∧ TypedState … w' (stepDecisionState …).1` | `DecisionKeeps`: the same over `MachineTyped` |
| `typedState_reachable` (M6c) | `Api.typeOf … → ClosedEff rootTy → RReachable root fuel m → ∃ w, TypedState root rootTy w m` | `ReachableTyped`: `LawfulSource root → … → RReachable root fuel m → ∃ w, MachineTyped root rootTy w m` |
| `ScopeState.closed.exit` | refused (`True` in `ScopeStateOk`) | `P.ScopeExitOk w e exit`, production `Fits w (reifyExitVal ex) (.exitOf .unknown .unknown)` |
| new | — | `QueueOk.links`; `MachineLive` (`running`, `ambientScopes`, `dueOwners`); `StoredObserverOk`/`ObserverCommandOk`'s scope-drop arm reads the scope store; M7a–c and scope-handle validity (`M7`); the twelve edit propositions and `DecisionEdits` (`M6Edits`); `DenotesTyped`, `TermFits` (`M3bAssembly`); `StackMono`, `SavedMono` and `preds_savedOk_mono` (`M6Stack`) |

Probe C's facts, side by side (row 139; `StaleCode.lean`): old (H1) `H1.typedState_halt` (a halt keeps
H1's typed state), `H1.halting_result_typed`, `H1.typed_not_imply_running` — proved, holding by
design at the base; new `machineTyped_not_halted` (`J` implies `stuck = none`),
`machineTyped_not_halted_here`, `halting_result_outside` (no halted machine is in `J` or `I`),
and `typedState_halt` for the generated part alone — proved.

## Plan §5

1. **Repeated proofs that disappeared.** H1's bundle depended on the machine and the queue
   (`statePreds root m commands`), so every machine edit re-walked the generated skeleton: probe C's
   one halt took nine transport lemmas in `StaleCode.lean`'s `H1` section (thirteen theorems,
   145 lines with the facts themselves: `finNameOk_tr`, `scopeStateOk_tr`, `storesOk_tr`,
   `dispatcherOk_tr`, `runFiberOk_tr`, `halt_fiber?`, `halt_race?`, `countdownAt_halt`,
   `storedObserverOk_halt`). With `preds root` independent of both, one
   congruence (`machineTyped_congr`, with `countdownAt_congr`, `storedObserverOk_congr`,
   `observerCommandOk_congr`) moves `J` across every edit that keeps the fibers, races, store and
   counters, and serves `edit_ran`, `edit_middleware` and `edit_task`; `J` after a step is
   `ConfigTyped.machine` (`reestablishes`, three lines), not a per-command re-establishment; the fire
   snapshot splits off the queue by one list lemma (`queueOk_append_tasks`); six of
   `DecisionLift`'s thirteen premises are closed once here where the lift seat declared twelve.
   Nothing that existed was retired as a duplicate judgment (the eighteen command proofs do not
   exist yet). Owed consumption: `savedMono_of_stackMono` has no consumer until the command proofs.
2. **Program-to-execution connections closed** (all proved): `machineTyped_load` (`J` at load from
   the root code's typing); `loadsTyped_of_denotesTyped` (M5 from `denoteR_typed`, for a program
   without layer-reference sites); `decisionLift_of_ledger`/`decisionKeeps_of_ledger` (M6b from the
   eighteen and the six content edits); `reachable_of_ledger` (M6c from M5 and M6b); `m7_of_ledger`
   (M7a–c from M5 and M6b through `replayEval_lift`); `replayR_bmeans_reachable` (R4: every
   reference replay machine is `BMeans`-related to a native `Guard.Reachable` machine at the empty
   table); `rreachable_load` (the capstone at the load is M5). The numbers that count, open per
   scope in this seat's scopes: M5 3, M6 20, `M6Edits` 6, `M6Stack` 3, M7 4 (36); none of the
   eighteen and not M5 is proved here, by the brief.
3. **The eventual claim.** M7 (a–c and scope-handle validity), once the ledger closes, covers the
   frame machine (the reference `replayR`), at the empty host table, on answer-free tapes, with
   observation `obs`, over `J`. The OCaml engine is outside it until row 28 is ruled. Nothing landed
   here is "verified lowering" or general host safety.

## Lines for seat A (their files; exact text)

1. **`Membership.lean` `HandleFits`, the scope arm (row 139).** Read the scope store as the cell
   and promise arms read their tables (`World.state` is the store, `WorldValid.state`; `Stores.le`
   keeps scope entries, so `fits_mono` still holds):
   ```lean
     | some .scope => target = Ty.scopeTarget ∧ (w.state.scopes.entryAt index).isSome = true
   ```
   When it lands, `MachineLive.ambientScopes` (my stand-in in `J`) follows from `ServiceOk` for a
   context whose ambient scope is a scope handle at a scope-typed key; delete the field then, or
   keep it as a corollary (seat C's file; one line).
2. **Row 112, `w.serviceTy`.** When `World.serviceTy` lands, `TypedState` (`Assembly.lean`, seat
   C's) gains one conjunct beside `WorldValid`: `w.serviceTy = <the source's service table, seat A's
   field name>`, and `initialWorld` (in `Typed/Validity.lean`) sets it from the source; `ServicesFit`
   reads `w.serviceTy`. `LawfulSource`'s body (`Assembly.lean`) becomes seat A's evidence field on
   `ProgramSource` (row 114); the statements keep the premise's name.
3. **`evalTerm_fits` closes `M3bAssembly.evalTerm_fits`:**
   `#obligation_proved Effect4.Program.Typed.M3bAssembly.evalTerm_fits := fun table w env vals t ty v
   hty henv hev => <seat A's theorem> …`. The declared statement is at any row table
   (`termTy (nativeSignature table) …`); if seat A's is at the default table, the bridge is
   `termTy (nativeSignature table) env t = termTy (nativeSignature []) env t` (term typing reads only
   `atomOf` and `constAtom`, `Program/Native.lean:316-320`; by the term fold, not `rfl`).
4. **The positive M5 control.** Seat A's `prog3_loads_typed` (the loaded code typed at every world)
   gives `J` at load through `machineTyped_load` (with `noMarker` by `rfl` for a concrete program),
   which is M5's proposition (`LoadsTyped`) at that program.
5. **T3.** `World.lean`'s controls move to `Test/`: `heapNotMonotone` (`:265`), `worldGood`
   (`:272`), `worldBad` (`:278`), the scope `WorldControlWanted` (`:281-294`) and their proofs at
   `:726-760`.
6. **`E4-TYPED-CE-009`** (row 137) stays live against `LoadsTyped` until `Fits`' handle arms compare
   in the checker's order; my four sites already do (`Assembly.lean` `CompletionStrong.ofRefGet`,
   `Scheduler.lean` `FiberColumnsBelow`, `RacePayload.live`, `RacePayload.programs`), a rename to
   `Ty.subN` when it lands.

## Lines for seat B (their files; exact text)

Written against `bb269fde`; seat B's merged branch may already carry part of item 1 (its receipt
names scope liveness on the scope rows' store pres) and items 2 and 3 (`E4-TYPED-CE-010`, `-012`
repaired there). Re-read at the merge.

1. **`Residual.lean` `fiberPre`, the halting arms (row 139; repairs the refutation of
   `step_deliver`).** Replace the `True` arms at `:129-133` for the scope- and target-reading rows:
   ```lean
     | .suspend _ | .interrupt _ | .interruptScoped _ | .interruptAll _ _
     | .awaitNewChildren _ => True
     | .interruptAs target _ => (w.Γ target).isSome = true
     | .runIn target scope =>
       (w.Γ target).isSome = true ∧ (w.state.scopes.entryAt scope).isSome = true
     | .guard_ _ | .unguard _ | .finishFinalizer _ | .construction
     | .foreignRelease _ _ | .closeWalk _ _ _ | .closeIter _ _ _
     | .cancelRace _ | .dropObservers _ | .frontier _ _ => True
     | .scopeExit _ scope _ | .closeScope scope _ => (w.state.scopes.entryAt scope).isSome = true
     | .raceRegister _ => False
   ```
   and `| .forkIn child _ scope _ => PointTyped root w child cert ∧ (w.state.scopes.entryAt
   scope).isSome = true`. Reasons (the halting-site census, step 4): `FiberAction.interruptAs`
   halts on an unknown target (`Machine/Fibers.lean:1534-1546`; `WorldValid.fibers` turns a
   declaration into existence); `runIn` and `forkIn` reach `linkScope` (`:1005-1036`);
   `scopeExit` reaches `prepareScopedExitR` (`Laws/Program/EvaluateR.lean:309-319`) and
   `closeScope` `FiberAction.closeScope` (`:1514-1523`), both halting on an absent scope; the
   `raceRegister` marker is installed only by `parkCode` (`Laws/Program/InterpR.lean:320`) and
   typed by `RegistrationState`, so a typed program that performs it directly would make
   `registerRace` halt on an unknown race (`:937-944`; assumed, from reading). The pres are monotone along
   `leHost` (scope entries persist, `Γ` grows). After this hunk,
   `M6Capstone.H1HaltAmendment.callback_typed`, and with it `config_input`, no longer holds at a
   world without scope 0, so the red control `step_deliver_refuted_by_absent_scope` stops compiling;
   the merge replaces it by its repaired form, the refusal of that input
   (`¬ ConfigTyped (rootProgram : ProgramSource) unitTy w machine (command :: rest)` at every `w`).
2. **Row 135.** `M3bWorld.stackAccepts_mono`/`savedOk_mono` (their names) close my `M6Stack`
   declarations: `#obligation_proved Effect4.Program.Typed.M6Stack.stackAccepts_mono := …`, or
   delete `M6Stack`. `savedMono_of_stackMono` (`Assembly.lean`) derives the saved half from the
   stack half and `typedProg_mono`.
3. **Row 136, `E4-TYPED-CE-010`.** The await-by-value post at `exitOf ty.answer ty.error` repairs
   `AwaitLoad.loadsTyped_false` (M5 under `J` at the typed corpus's `awaitFiber.value`).
4. **T3.** `Contracts.lean`'s `namespace Example` (`:86-105`) moves to `Test/`.
5. `Frames.lean`: the un-refused row changed no frame-rule report (`15 …, 81 …, 9 …` and
   `47 …, 71 …, 33 …`, tested); no hunk.

## Lines for the coordinator's files (proposed text)

**`docs/core/decisions.md`** (status lines to append):

- Row 133: "Superseded by row 134's split (seat C, `4b6ea8fd`): the queued-finish exemption is `I`'s
  `finish` line (`QueueOk.payload`), the published-exit one is `LiveCode`'s `f.exit = none`, the halt
  extension is gone (`J` has `stuck = none`)."
- Row 134: "Landed by seat C (`4b6ea8fd`, `b41d0808`): `J = MachineTyped` (`TypedState` with the
  machine- and queue-independent `preds`, `LiveCode`, `MachineLive`), `I = ConfigTyped` (`J`,
  `ReadCode`, `QueueOk`); `StepPreserves` over `I` is exactly the lift's `step` premise
  (`guarded_stepKeeps_of_stepPreserves`); `decision_preserves` and `typedState_reachable` over `J`;
  the entry premise holds (`evaluate_entry`); `J` holds at the cut and the finished run of probe A
  (`StaleCode.machineTyped_m6`, `machineTyped_m9`); no configuration capstone (no consumer)."
- Row 138: "Declared by seat C (`293aa874`): scope `M7` (`exits_typed`, `stores_typed`,
  `never_halts`, `exitHandles_valid`) over `M7Fragment`; route proved (`m7_of_ledger`,
  `replayR_bmeans_reachable`)."
- Row 139: "Landed by seat C (`b41d0808`): `MachineLive` (`stuck = none`, ambient scopes live,
  scheduled owed resumes owned), `QueueOk.links`, the scope-drop arms of the observer clauses,
  race-id liveness by `RegistrationState`, scope-handle validity declared (`M7.exitHandles_valid`).
  Open: seat A's `HandleFits` scope arm; seat B's `fiberPre` pres (receipt-C, lines for seat B);
  `step_deliver` is refuted until they land (`step_deliver_refuted_by_absent_scope`)."
- Row 140: "Declared by seat C (`12fb3716`): `M6Edits` (6 proved, 6 open, and the re-establishment
  proved as `I`'s projection), `M6Stack` (until seat B's `M3bWorld`), `M3bAssembly` gains
  `denoteR_typed` and `evalTerm_fits`; `ScopeState.closed.exit` un-refused as `ScopeExitOk`; the
  R4 bridge proved (`replayR_bmeans_reachable`). Not done here: `Book` proved once on the native
  machine and transported."
- Row 148: "Declared by seat C (`12fb3716`) in `M3bAssembly`; `loadsTyped_of_denotesTyped` proves
  M5 from `denoteR_typed` for programs without layer-reference sites."
- Row 87 (beside seat B's line): "`preds_savedOk_mono` declared in `Assembly.lean`'s `M6Stack`
  (seat C, `570142a9`); open until seat B's closed frames are merged into the split."
- **New row (proposed): M5 for programs with layer references.** "`Api.typeOf` certifies a
  program's expansion (`Program/Typing.lean:61-64`) while `loadR` loads the program as written and
  resolves references by redirect (`Laws/Program/DenoteR.lean:733-737`), and the checker refuses
  a reference (`Program/Checker.lean:259`), so `denoteR_typed` at the root point is vacuous for
  such a program (tested: `Test/Program/TypedSplit.lean`, the corpus `layer.ref`). Options: (a)
  load the expansion (`loadR p.expandRefs`); (b) a redirect-agreement lemma (the raw program's
  denotation at a point equals the expansion's at the redirected point) with `denoteR_typed` over
  the expansion; (c) restrict M5 to reference-free programs. Recommendation: (b), since it keeps the
  loader and the face unchanged and is one lemma of the denotation." (owner)

**`docs/core/system-map.md` §8:**

- R1's exception: as written on main; add "declared as scope `M7` in `Laws/Program/Typed/Assembly.lean`
  over `M7Fragment` (lawful source, empty row table, checked, closed, answer-free tape); route
  proved (`m7_of_ledger`)."
- R9: replace "'never halts' is M7's corollary (row 52)" by "'never halts' is declared as M7c
  (`M7.never_halts`) and follows from `J` (`machineTyped_not_halted`), so from M5 and M6
  (`m7_of_ledger`, proved); its content is the halting arms of the eighteen command proofs
  (row 139's census)".
- R12: add "M7c leaves a frontier as the only unfinished end of an answer-free run at the empty
  host table once the ledger closes; it says nothing about what the frontier awaits."

**`Test/Counterexamples/REGISTER.md`:**

- `E4-TYPED-CE-011`: REPAIRED 2026-10-01 by row 134's split (seat C): positive controls
  `StaleCode.capstone_window_holds`, `machineTyped_m6`, `machineTyped_m9`, `evaluate_entry_m6`;
  the cut refutations retained against `Test/.../H1Shapes.lean` (`window_untyped`,
  `capstone_false_window`, `ledger_jointly_false_window`).
- `E4-TYPED-CE-014`: REPAIRED 2026-10-01 (`J`'s `stuck = none`): `machineTyped_not_halted`,
  `StaleCode.machineTyped_not_halted_here`, `halting_result_outside`; H1's facts side by side
  (`StaleCode.H1.typedState_halt`, `halting_result_typed`, `typed_not_imply_running`).
- `E4-TYPED-CE-009`: add "restated against M5 and the capstone over `J` (seat C):
  `Test/Counterexamples/Machine/Semantics/RawOrderLoad.lean`, `m5_false`, `loadsTyped_false`,
  `capstone_false`".
- `E4-TYPED-CE-010`: add "restated against M5 and the capstone over `J` (seat C, before seat B's
  repair merges): `Test/Counterexamples/Machine/Semantics/AwaitLoad.lean`, `loadsTyped_false`,
  `capstone_false`".
- `E4-TYPED-CE-012`: add "under row 134's split `J` keeps the saved-stack clause at the world, so
  `step_loop_refuted` is expected to carry (not re-run); `M6Stack` declares the two laws".
- `E4-SCHED-CE-019`: add "under row 134 the terminal witness keeps `I`
  (`M6Capstone.H1TerminalAmendment.deliver_keeps_config`, `result_config_typed`)".
- `E4-SCHED-CE-020`: status back to SEEDED: "H1's halt tolerance is superseded by row 139; the
  witness refutes the restated `step_deliver` (`M6Capstone.H1HaltAmendment.
  step_deliver_refuted_by_absent_scope`) until seat B's scope-liveness pre on `fiberPre`".

**`docs/DESIGN-ISSUES.md`**, DI-94: "The stored closed-scope exit is stated at `Exit<unknown,
unknown>` in the typed state (`preds.ScopeExitOk`, seat C, `12fb3716`)."

## What is owed

- **The merge with `refactor/phase1-phase3`** and its repairs ("The merge, not done"): denied
  here; the coordinator's or the owner's to run, or a permission to grant.
- **The eighteen command proofs** (wave 2), each showing its halting arms unreachable from `I`
  (the census in step 4); `step_deliver` and `step_loop` wait on seat B's `fiberPre` pres, and
  `step_loop` on seat B's Kripke closure (`E4-TYPED-CE-012`). Statements only here, by the brief.
- **The six content edits** (`M6Edits`: `drain`, `yield`, `interrupt`, `clockNone`, `clockSome`,
  `answer`). `drain` and the clock steps move a dispatcher's or the clock's owed work into the
  snapshot and must re-establish `QueueOk` for it; `answer` is the lift seat's `answer_of_split`
  shape (`AnswerDecision.lean:94-112`) over `I`.
- **M5** (`typedState_load`): `denoteR_typed` (wave 2, with seat E's `seq_typed`), `evalTerm_fits`
  (seat A), and the owner's decision on programs with layer references (proposed row above). It is
  refuted at this commit by `E4-TYPED-CE-009` (`RawOrderLoad.loadsTyped_false`; seat A) and
  `E4-TYPED-CE-010` (`AwaitLoad.loadsTyped_false`; seat B, repaired on its merged branch). `loadsTyped_of_denotesTyped` also carries `noMarker`
  (the loaded head is not a race marker): true of every denotation by reading (only `parkCode`
  builds the marker, `InterpR.lean:320`), not proved; one structural lemma over `denoteR`.
- **`M6Stack`** (seat B), and **M7**: `exits_typed`, `stores_typed` and `never_halts` follow from
  M5 and M6b by `m7_of_ledger` (proved); `exitHandles_valid` (scope-handle validity, organization
  M4) is beyond `J` while `HandleFits`' scope arm checks only the spelling; with seat A's arm it is
  expected to follow from `ExitOk` on recorded exits through `fits_live` (assumed, not checked).
- **`w.serviceTy` in `TypedState`** after seat A's field (row 112); `LawfulSource`'s body after
  seat A's evidence field (rows 111, 114).
- **`MachineLive.ambientScopes`** becomes a corollary of seat A's scope arm of `HandleFits`;
  remove or derive it then.
- Row 140's "`Book` proved once on the native machine and transported" is not done here.
- T4's other collisions (`World`, the two `pure_inv`, the two `Reachable`, `Denote.ExitOk` beside
  `Typed.ExitOk`) are in files no brief gave this seat; the "M7" label in `Machine/Fibers.lean`
  (`:565`, `:573`, `:1004`) and `Machine/Stores.lean` (`:1928`, `:1963`) is left for the
  coordinator.
- The register, decisions and system-map lines above are the coordinator's to write.
- Bounded evidence: the controls are finite probes on probe A's program, H1's terminal witness,
  `E4-SCHED-CE-020`'s witness and the corpus's `awaitFiber.value`/`layer.ref`; the general facts
  are the theorems in the `src/` table. No host evidence was run (no OCaml, no TypeScript).
