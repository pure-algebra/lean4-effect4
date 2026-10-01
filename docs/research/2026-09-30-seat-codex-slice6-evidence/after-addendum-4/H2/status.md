# H2 part one: measured stop, no implementation landed

**The one thing first.** The eight authorized source-body repairs pass in the copied-declaration harness. Two additional existing test helpers fail, and their unchanged statements are each refuted by checked counterexamples. The measured lower bound is therefore ten existing bodies. Addendum 5's ninth-body rule stops integration; it does not exempt test bodies. No H2 source, test or register change is applied.

Base: `80f5fbe7a99371d0ec04216ff621176f5dc72ce7`. H1's candidate was restored first, and the original Assembly rebuilt successfully (`../H1/restored-assembly`). The unchanged source is copied freshly by `h2-part-one-candidate/prepare.py`. Membership's source hash remains unchanged. The preparation README and manifests labeled uncompiled are the historical candidate description; the actual executions below supersede only their compilation status. Proposed test migrations remain uncompiled and unauthorized.

## Measured sequence

Each check uses `check.py`, `LEAN_NUM_THREADS=1`, `lake env lean -M4096 -DwarningAsError=true`, serially in the designated worktree. Exact commands, cwd, exits and elapsed times are in the sibling command/result JSON files; raw logs remain unchanged.

| Run | Exit | Observation |
| --- | --- | --- |
| baseline | 0 | Fresh copied pre-H2 four-module baseline compiles. |
| mechanical | 1 | 59 substitutions plus the authorized clean-failure premise. Exactly eight primary failing theorem regions, named below; no non-theorem primary error. |
| repaired | 0 | Exactly the eight named existing bodies repaired, plus seven new local exclusion lemmas. |
| repaired-axioms | 0 | All eight bodies and seven helpers print at `[propext, Quot.sound]` or less. |
| existing-tests | 1 | Actual current cancel_typed and lookup_typed statements/bodies copied, changing only TypedProg qualification. Compiler attributes failures to these two additional existing regions. |
| controls | 0 | Thirteen control theorem prints at the ceiling. |
| lookup-refutation | 0 | Four new diagnostic facts, including the old lookup statement's refutation, at the ceiling. No proposed replacement theorem is compiled. |
| cancel-refutation | 0 | Two new diagnostic facts, including the old cancellation statement's refutation, at the ceiling. |
| field-only-red | 0 | The baseline field-only counterexample strengthened_output_false and eight companion facts print at the ceiling. |

The mapping commands are `python3 h2-part-one-candidate/map_errors.py <probe.map.json> <run.log>`; mechanical.errors.json, repaired.errors.json and existing-tests.errors.json retain full compiler attribution. These are declaration regions rather than automatic necessary-repair counts. Here the independent semantic refutations establish that both additional statements require amendment, beyond conjunction syntax.

## The eight and the two extras

Authorized eight, exactly as the addendum: Admission strongExit_success, strongExit_of_clean, cleanExit_of_never; Residual strongExit_bool, settling_fork, strongExit_mono; Stack strongExit_failure_of_error, popR_typed. The two sites of popR_typed count once. `h2-eight-repairs/README.md` and the eight-body manifest record each statement delta, premise and local lemma. The only nonmechanical existing library signature amendment is strongExit_of_clean's explicit NoShapeDefect premise.

Additional body 9: `Test.Program.TypedControl.cancel_typed`. It takes only cleanExit of the cancellation cause. Cause.die badName is clean, and successful cancellation reaches that forbidden failure. `H2CancelDiagnostic.old_cancel_statement_false` proves its unchanged statement false under the new TypedProg. Proposed statement amendment: add `NoShapeDefect (EffTy.pure .unit) (.failure cause)`, then pass that evidence through its continuation. This does not require all failures to be interrupts.

Additional body 10: `Test.Program.LoadedAdmission.lookup_typed`. Its implication says a decoded context has fitting services, but never requires decoding to succeed. Unit satisfies that implication vacuously, and lookup returns badName. `H2LookupDiagnostic.old_lookup_statement_false` proves the unchanged statement false. Proposed statement amendment: add `isContext : ∃ ctx, Val.context? v = some ctx`, retaining the existing ServicesFit implication. This does not require the requested service to be present; missingService remains admitted.

`PROPOSED-test-migrations/` is a separate uncompiled proposal for downstream adaptations, not a cap exemption, completed repair, or claim that ten is the final total. Do not apply it without an owner amendment and fresh test measurement. The four-module production patch passes git apply --check, but is not applied. No production obligation ceiling or register status changes. M3bWorld remains ceiling 1, M3bAssembly 1, M6Ledger 20; the harness omits registration commands and therefore does not prove these obligations.

## Controls and boundary

Base FitsExit and cleanExit continue to admit badName. The candidate ExitOk and current TypedProg reject badName and notImplemented. Ordinary user die remains admitted. missingService remains admitted for empty and nonempty requirement rows. This matches the owner's two-defect ruling and does not implement held part two. FieldOnlyRed embeds the pre-H2 judgment and the earlier local full badDefect clause solely to reproduce the historical field-only failure.

The harness concatenates the four exact candidate modules into a distinct namespace and records source/declaration maps. It omits imports already supplied by the production Assembly import and post-namespace proofgraph commands. This is checked Lean evidence for those copied declarations, not a production closure build, complete test migration, reachable-run proof or backend claim. Failed mechanical and existing-test outputs are intentional measurements, not passing evidence. There is no full battery or generator run for this held item.
