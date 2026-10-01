# Seat C brief: the assembled state split at the cut, M7 declared, the ledger as the one list

Written 2026-10-01 by the coordinator. Base: `bb269fde` on `refactor/phase1-phase3`. Worktree
`/Users/pooks/Dev/lean4-effect4-seat-C`, branch `seat/C` (created; `.lake` current). Read
`docs/research/2026-10-01-landing/plan.md` (§0 items 3, 5, 7, §1 O2 and O4, §2, §4) and decisions
rows 106, 133, 134, 138, 139, 140, 148 first. The pass's material:
`docs/research/2026-10-01-formal-pass/proofs/` (`note.md` G1, G3, G4, R1–R4, T1–T4, §4 the proof
route; `verify.md` §1, items 1–9 of "what the seat missed", the receipt tables;
`probes/{StaleCode,HaltTyped,WindowScout4,PrintTypedState}.lean`;
`verify-probes/{VerifySplit,VerifyScout1..5}.lean`), `.../organization/` (`verify.md` §3 M3, M4;
`verify-ExitOkConnector.lean`), Codex's H1 receipt and evidence
(`docs/research/2026-09-30-seat-codex-slice6-receipt.md` "After addendum 6", H1;
`...-evidence/after-addendum-6/H1/resolution/README.md`: the native boundary review of which
commands read current code). Read by absolute path from the main checkout; never edit or build
there.

**The one thing.** `decision_preserves` and the capstone are false as declared because a budget
cut drops the queue and the typed state then types a running fiber by a stale code slot
(`E4-TYPED-CE-011`, proved at budgets 6 and 9 on a checked host-free program). Row 134 fixes the
statements with the split the lift already supports, keyed on `running`; row 138 declares M7; row
139 puts halting-freedom and liveness into the machine-only predicate; row 140 makes the ledger
the one list. You own `src/Effect4/Laws/Program/Typed/{Assembly,Sources,Scheduler,State,
TypedStateDecl,PositionGate,Vocabulary}.lean`, `Laws/Machine/Lift.lean` (only if a lemma is
missing; `DecisionLift` stays unchanged), the generated typed-state skeleton's inputs if a source
row changes (`tools/` producer: run `make check-typed-state`'s group as `docs/GENERATED.md` says
and commit byte-identical or regenerated output), and `Test/Counterexamples/Machine/Semantics/
M6Capstone.lean`. Seat A owns `Membership.lean`, `World.lean`, `Admission.lean`; seat B owns
`Contracts.lean`, `Stack.lean`, `Residual.lean`, `Frames.lean`. Statements only for the eighteen
command goals and M5: this seat proves no `step_*`, no `typedState_load`.

## The work, in order

1. **Re-establish the refutation** as a battery `Test/Counterexamples/Machine/Semantics/
   StaleCode.lean` (imported from `Test/All.lean` beside `M6Capstone`): probe A's twenty theorems
   and `VerifySplit`'s thirteen, restated against the merged `TypedState` (its last steps need the
   new shape, `rerun-on-0c534f06/README.md`): `capstone_false_window`, `capstone_false_finished9`,
   `ledger_jointly_false_window`, `m6_root_running`, `running_clause_vacuous_at_m6`,
   `budget7_is_fuel_frontier`, `worldValid_not_upward_closed`, `seat_split_not_decisionLift`, and
   `HaltTyped.lean`'s four (`typedState_halt`, `halting_result_typed`, `typed_not_imply_running`).
   Heed the probe authors' lessons (`proofs/note.md` §5: `decide +kernel` on a replay, never
   elaborator `decide`; `classify (replayR …)` exhausts memory; `Api.typeOf` needs `rfl'`; a false
   replay claim under `decide +kernel` exhausts memory, so refutations of replay facts are proved
   as positive negations). Commit red.
2. **Row 134: the split.** In `Assembly.lean` (and `TypedStateDecl.lean`/`State.lean` where the
   generated predicate is assembled): `J` (machine-only) := world validity, the store columns,
   every recorded `exit` and `finalizing` exit typed at Γ, the code of every fiber that is neither
   exited nor running typed (`SavedOk` restricted by `running`), `stuck = none`, the liveness
   clauses of step 4; `I` (configuration) := `J` plus, for each running fiber, typing by the queued
   command that continues it (`loop`/`deliver` by the saved stack, `finish` by its exit as row 133
   rules, the race and interrupt commands by their installed code; the per-command list is the
   reference code-site census H1 left open: write it as a table in the docstring, one line per
   command that reads current code, from Codex's H1 resolution README and `Machine/Fibers.lean`),
   plus `QueueOk` (rows 106, 133). `CodeInert`'s halted disjunct goes (a halted machine is outside
   `J`); its queued-finish disjunct becomes `I`'s `finish` line. `StepPreserves` is
   `StepKeeps (Guarded J I O)` in the lift's terms with the dispatch premise `m.stuck = none` kept;
   `decision_preserves` and `typedState_reachable` are stated over `J`; a configuration capstone
   over `I` is declared only if you find a consumer (say which). `DecisionLift` is unchanged; show
   the entry premises hold for this `J` (the verifier's `seat_split_not_decisionLift` is the red
   control for the other split; `running_clause_vacuous_at_m6` the positive one). Probe A's
   `exitsTyped6`/`exitsTyped7` become positive controls for `J`. The two lift adapters Codex
   landed (`stepKeeps_of_stepPreserves`, `driveState_typed_of_stepPreserves`) are restated.
3. **Row 138: M7 declared** in a new ledger scope `M7` beside `M6Ledger`: M7a (every exit the
   observation records fits its declared type), M7b (the stores fit), M7c (no halt: `stuck = none`
   on every reachable machine), at the empty host table, on answer-free tapes, with observation
   `obs`, over `J`, from `typedState_load` and `decision_preserves` through `replayEval_lift`;
   "the frame machine", not "the compiled machine"; the OCaml engine outside until row 28. Write
   R1's exception into the docstring (the service half of Σ_app, the row table fixed empty; the
   coordinator writes §8). R4's bridge: one lemma, every `replayR` machine is `BMeans`-related to a
   `Guard.Reachable` machine at the empty table (the replay is a prefix fold at constant budget),
   stated in `Assembly.lean` or `Laws/Machine/Refinement.lean` and proved if it is the few lines
   the verifier expects, else declared with its obstacle named.
4. **Row 139: halting-freedom and liveness** in `J`: `stuck = none`; the scope arm of
   `HandleFits` reads the scope store (this is `Membership.lean`'s arm: seat A's; write the exact
   arm for seat A and, until it lands, add the scope-liveness clause to `J` beside `HandleFits`);
   race-id liveness for codes that name a race (`RegistrationState` covers `raceRegister`); a
   typed scope on queued `link`; scope-handle validity declared as a ledger goal
   (organization M4; `verify-ExitOkConnector.lean`'s premise). `HaltTyped.lean`'s
   `typedState_halt` flips to its negation on `J`.
5. **Row 140: the ledger as the one list.** Declare beside the eighteen: the decision edits and
   the fire snapshot (`DecisionLift`'s thirteen fields, `Lift.lean:308-355`; the lift seat's
   `M6Edits`, `docs/research/2026-09-30-pass/lift/Lift.lean:849-871`), stack monotonicity (seat B
   proves it; declare if B has not landed), the `J`/`I` split's re-establishment lemma (`J` after
   each step from `I` before it), M7a–c, `denoteR_typed` and `evalTerm_fits` by name (row 148; the
   latter is seat A's to prove). Un-refuse `ScopeState.closed.exit` in `Sources.lean` with
   `Fits w (reifyExitVal ex) (exitOf unknown unknown)` (DI-94's `Live`) and keep
   `Stores.externals` refused; regenerate the skeleton if a source row changed. Rows 111–112 in
   the statements: `typedState_load` and `typedState_reachable` quantify over lawful sources
   (seat A adds the evidence field to `ProgramSource`; until it lands, write the statement with
   the premise named and a `TODO`-free docstring saying which seat supplies it) and read
   `w.serviceTy` as a static world component tied to the source.
6. **T1–T4**: the capstone's docstring (`Assembly.lean:230-240`) lists the live refutations
   (`E4-TYPED-CE-009`, `-010`, `-011`) and not the repaired `E4-PROV-CE-005`; the controls in
   `src/` move to `Test/` (`World.lean`'s `worldGood`/`worldBad`/`heapNotMonotone` are seat A's
   file: list them; `Contracts.Example` is seat B's: list it; yours: any in `Assembly.lean`,
   `Sources.lean`, `Scheduler.lean`); the comment-only corrections Codex made in `Assembly.lean`
   and `M6Capstone.lean` are re-read against the new statements; "M7" as a label on the old machine
   repair (`Laws/Machine/Witnesses.lean:60,1059`, `Clauses.lean:827`, `StoresLaws.lean:640`) gets
   a different word in those comments (they are no seat's files; one-word comment edits need no
   build of dependents).

## Checks

Per step: `LEAN_NUM_THREADS=4 lake build Effect4.Laws.Program.Typed.Assembly` and its direct
dependents (`grep -rl "Typed.Assembly" src Test`); the batteries by `lake env lean
-DwarningAsError=true`; `#print axioms` for every theorem landed; the ledger report
(`#typed_state_obligations … ceiling`) with the new scopes' counts in the receipt; `make
check-typed-state` (or the group's producer as `docs/GENERATED.md` names it) if a source row
changed, output committed or byte-identical. At the end `LEAN_NUM_THREADS=4 lake build
Effect4.Laws Test.All` once. No other generator.

## Receipt

`docs/research/2026-10-01-landing/receipt-C.md` (force-added): the one thing first; base and
head; every changed path; the new `J` and `I` printed (as `PrintTypedState.lean` does); the
per-command table of `I`'s code lines; the ledger before and after (declared, proved, open, per
scope); the statements changed with old and new text; the theorems (name, file:line, axioms);
the exact lines for seats A and B and for the coordinator's files (rows 133, 134, 138, 139, 140,
148; system map §8 R1's exception, R9, R12); what is owed.

## Amendments (2026-10-01, after the synthesis and the owner's ratification; these win over the text above)

1. **Step 1 uses the tracked ports** at `ports-at-dceae006/`: `HeadCut.lean` (19 theorems) and
   `HeadAwaitLoad.lean`, with their axiom logs. Copy from them; do not re-port.
2. **`E4-TYPED-CE-011` claims the cut only:** at the merged head the finished run at budget 9 is
   covered by H1's published-exit disjunct (`HeadCut.m9_root_inert`, proved). Drop
   `capstone_false_finished9` from step 1; keep the cut theorems (`window_untyped`,
   `capstone_false_window`, `ledger_jointly_false_window`) and the positive controls
   `running_exempt_at_m6` and `running_clause_vacuous_at_m6`. `HaltTyped`'s facts hold by design
   at the merged head (`CodeInert` tolerates a halt): record the old and new statements side by
   side; under row 139 the halted disjunct goes and `stuck = none` enters `J`.
3. **Row 137's sites in this seat's files:** `Assembly.lean:40` (`CompletionStrong.ofRefGet`) and
   `Scheduler.lean:55`, `:67`, `:69` (`FiberColumnsBelow`, `RacePayload`) compare in the checker's
   order (`sub (normalize a) (normalize b)` inline until seat A's `Ty.subN` lands).
4. **Row 134 in the merged vocabulary:** a running fiber that no queued `loop` or `deliver`
   continues is inert; `J` reads that at the empty queue, `I` at the real queue; `DecisionLift`
   unchanged.
5. **Ratified by the owner (2026-10-01):** rows 134 and 138 as recommended; row 133's halt
   extension is superseded by row 134; R1's exception is ruled (M7 at the empty row table; the
   OCaml engine outside M7 until row 28).
6. Seats E (`a561d604`) and F (`efcf1ae2`) are merged on `refactor/phase1-phase3`: F moved
   `Admitted`/`foldl_lift`/`admitted_true` into a new `History` section of
   `Laws/Machine/Lift.lean` (statements unchanged), so a lemma this seat adds to `Lift.lean` goes
   beside it; the coordinator resolves the merge. Row 150 (the `FoldLift` route) lands after this
   seat merges.
