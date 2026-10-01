# H2 part-one preparation

The four-module candidate retains the authorized eight source-body repairs. Integration still needs a fresh measured count: two existing test-helper statements become false, and other test bodies require conjunction adaptations. Nothing in this packet exempts test bodies from the owner's strict cap. All Lean files here are uncompiled drafts; this seat ran no Lean, lake, build, make, generator, commit, or repository write.

Authority: addendum 5 at `56da0e1e`, read from the main checkout, plus the later explicit user clarification. `NoShapeDefect (_ty : EffTy) : ExitV → Prop` excludes only `badName` and `notImplemented`. `missingService` is admitted at every requirement row, including empty rows. The type argument stays in the interface. Base Membership/FitsExit is unchanged.

## Reproducible stages

`prepare.py` reads the live four modules and writes only under `/private/tmp`. The initial generation used HEAD `e5cc184ba820ab4ea79b38fd32820421514812b9`. Its source-manifest records every changed occurrence, source and candidate hashes, the unchanged Membership hash, ceilings, and the eight authorized declaration names. Admission has 4 substitutions, Residual 25, Stack 26, Assembly 4: 59 total. It inserts `NoShapeDefect`/`ExitOk`, the explicit `shape` premise on `strongExit_of_clean`, and truthful Admission/Assembly comments; existing proof bodies are otherwise unrepaired.

`/private/tmp/h2-eight-repairs/prepare.py` reads that immutable mechanical candidate and writes `/private/tmp/h2-part-one-repaired`. It changes exactly the eight named existing source bodies and adds seven local helpers. The independent repair manifest and per-body notes are in that directory and `/private/tmp/h2-eight-repairs/README.md`. Membership and hookLaws_interpR stay unchanged. This separation preserves the first compiler measurement.

`make_harness.py` concatenates a selected candidate into a fresh namespace. It records a source line and declaration map, omits imports already supplied by the original Assembly import, and omits only post-namespace proofgraph commands. It checks copied declarations, not production import closure, production obligation registration, or ceiling discharge. Run baseline before mechanical and repaired probes. `map_errors.py` attributes diagnostic regions; its count is not automatically a count of necessary repairs.

`emit_apply_patch.py` creates `for-apply/core.patch`, containing the four repaired modules plus the Stack module-doc correction about sanitized failures retaining separate shape evidence. By default it only verifies source hashes, emits under `/private/tmp`, and runs `git apply --check`. `--apply` is an explicit integration action for root after validation and the cap ruling; it has not been used. No proposed test change is included.

## Root's serialized measurement commands

Run from `/Users/pooks/Dev/lean4-effect4-slice6`, one at a time. These commands are proposed, not receipts:

```sh
lake env lean -DwarningAsError=true /private/tmp/h2-part-one-candidate/probes/Baseline.lean > /private/tmp/h2-part-one-candidate/probes/Baseline.log 2>&1
lake env lean -DwarningAsError=true /private/tmp/h2-part-one-candidate/probes/PartOne.lean > /private/tmp/h2-part-one-candidate/probes/PartOne.log 2>&1
python3 /private/tmp/h2-part-one-candidate/map_errors.py /private/tmp/h2-part-one-candidate/probes/PartOne.map.json /private/tmp/h2-part-one-candidate/probes/PartOne.log > /private/tmp/h2-part-one-candidate/probes/PartOne.errors.json
lake env lean -DwarningAsError=true /private/tmp/h2-part-one-repaired/probes/Repaired.lean > /private/tmp/h2-part-one-repaired/probes/Repaired.log 2>&1
python3 /private/tmp/h2-part-one-candidate/map_errors.py /private/tmp/h2-part-one-repaired/probes/Repaired.map.json /private/tmp/h2-part-one-repaired/probes/Repaired.log > /private/tmp/h2-part-one-repaired/probes/Repaired.errors.json
lake env lean -DwarningAsError=true /private/tmp/h2-part-one-controls/ExistingTestsFirstPass.lean > /private/tmp/h2-part-one-controls/ExistingTestsFirstPass.log 2>&1
python3 /private/tmp/h2-part-one-candidate/map_errors.py /private/tmp/h2-part-one-controls/ExistingTestsFirstPass.map.json /private/tmp/h2-part-one-controls/ExistingTestsFirstPass.log > /private/tmp/h2-part-one-controls/ExistingTestsFirstPass.errors.json
```

The final probe copies the actual existing `Test.Program.TypedControl.cancel_typed` and `Test.Program.LoadedAdmission.lookup_typed` statements and proof bodies; only TypedProg's namespace is qualified to the repaired candidate. It provides actual compiler attribution without repository mutation. Do not treat predictable failures as measured until this runs.

The independent counterexamples and new controls are separate:

```sh
lake env lean -DwarningAsError=true /private/tmp/h2-part-one-controls/RepairedControls.lean > /private/tmp/h2-part-one-controls/RepairedControls.log 2>&1
lake env lean -DwarningAsError=true /private/tmp/h2-part-one-controls/FieldOnlyRed.lean > /private/tmp/h2-part-one-controls/FieldOnlyRed.log 2>&1
lake env lean -DwarningAsError=true /private/tmp/h2-part-one-controls/LookupDiagnostic.lean > /private/tmp/h2-part-one-controls/LookupDiagnostic.log 2>&1
lake env lean -DwarningAsError=true /private/tmp/h2-part-one-controls/CancelDiagnostic.lean > /private/tmp/h2-part-one-controls/CancelDiagnostic.log 2>&1
```

Controls prove base FitsExit still admits badName, cleanExit still admits badName, ExitOk/current TypedProg refuse badName and notImplemented, ordinary user die remains admitted, and missingService remains admitted at both empty and nonempty rows. The field-only red embeds the exact pre-H2 four-module baseline and the retained side-audit `strengthened_output_false`; the original local full badDefect clause is frozen there as history, not copied into production. Its named baseline dependencies are fully qualified, so it cannot accidentally test the strengthened TypedProg instead of the reviewed one.

`LookupDiagnostic` uses `v = Val.unit`: the old `∀ ctx, context? v = some ctx → ServicesFit` premise is vacuous; serviceLookupR returns badName. A separately named proposed helper requires `∃ ctx, context? v = some ctx`. `CancelDiagnostic` uses `Cause.die .badName`, which is clean: the exact old cancellation helper then produces a forbidden typed exit. Its proposed amendment is the explicit shape premise, matching the production wrapper's new premise. These test signature amendments are separate proposals, not silently integrated changes.

## Eight source bodies and statements

| Module | Exact existing declaration | Beyond judgment substitution |
| --- | --- | --- |
| Admission | strongExit_success | Pair base membership with success exclusion. |
| Admission | strongExit_of_clean | Add `shape : NoShapeDefect ty (.failure c)`; pair unchanged base clean-failure theorem with shape. |
| Admission | cleanExit_of_never | Use the first projection. |
| Residual | strongExit_bool | Repaired success wrapper. |
| Residual | settling_fork | Pair the existing fiber-declaration witness with success exclusion. |
| Residual | strongExit_mono | Transport first projection, retain second. This is E's adapter, separately identified from the seven legacy bodies. |
| Stack | strongExit_failure_of_error | Transport base failure membership, retain type-independent exclusion. |
| Stack | popR_typed | Two value hooks consume first projection; three clean injections get interruption exclusion; local preemption takes original-cause exclusion and transports through sanitize. |

Everything remains in namespace `Effect4.Program.Typed`. The statement-level move covers BodyTyped.fin, TypedProg pure/control payloads/inversions, fiberPost exit positions, IteratorAnswer, async-finalizer protocol posts, HookLaws, WalkTyped and concrete saved/stack predicates, CompletionStrong, preds.SavedOk/exit, and active delivery. Generated queue/stored positions inherit their judgment through the concrete preds/CompletionStrong bundle; there is no generated-file edit. M3bWorld remains ceiling 1, M3bAssembly 1, M6Ledger 20, and M4/M5Hooks 0. No M5–M7 proof is introduced.

## H1 sequencing

The live source used here has no `Typed/Scheduler.lean`. If H1 lands first, regenerate from live; never overwrite a newer Assembly. The four-module harness and apply script deliberately refuse an existing/imported Scheduler. The draft H1 Scheduler has 14 textual FitsExit occurrences, 13 in code and one in a docstring. They include race accepted/cleanup exits, countdown buffers/resumes, observer exits, and StackReply. A full mechanical replacement also changes reifyExitVal_fits and observerDeliveredExit_fits; the observer_exitValue_typed awaitValue branch must construct strengthened pure typing. These are candidate extra existing-body failures outside the named eight. Even keeping the two value helpers at base FitsExit still leaves the TypedProg-producing observer wrapper to remeasure. Do not silently repair or exempt it.

## Tests and final integration checks

`/private/tmp/h2-test-migrations/PROPOSED-test-migrations.patch` contains an exact uncompiled proposal for eight existing test files plus a new `Test/Program/H2PartOne.lean`. Both false test-helper amendments are labeled in the manifest. The old Reviewed/ReviewedLoad/ExactSpelling counterexamples remain unchanged. The new file is reachable through the explicit test imports in that proposed patch; no root import edit is needed. This patch is **outside the four-module apply patch**, and no cap exemption is assumed.

Direct existing consumers include TypedResidual, TypedStack, AsyncHookContract, TrivialPosts, ValueMembership and M6Capstone; TypedControl and LoadedAdmission must also be checked because they use the judgments through those imports. Proposed eventual serial narrow checks, only after scope is resolved: build Admission, Residual, Stack, Assembly and those eight tests; run `/private/tmp/h2-eight-repairs/Axioms.lean` for all fifteen source bodies/helpers, plus each changed test's axiom prints. Retain actual before/after ceiling output from production builds; concatenated harnesses omit that registration by design. No full battery or make sweep is implied by this preparation.

Register edits remain deferred until passing integration: CE007 repaired by shared placement; update CE003's repair column; propose CE008 SEEDED for the full missingService/frame transport question in the receipt, per addendum 5's final instruction. Do not mark CE008 repaired, change decisions.md, implement part two, or weaken stack/reachability statements.

## Checks actually run by this seat

Python syntax checks passed for all preparation/mapping scripts. Mechanical generation ran: 59 substitutions and zero proof repairs; the repaired stage reported exactly eight source bodies and seven new helpers. Fresh baseline/mechanical/repaired/control/diagnostic files and maps were generated. Both the four-module final core patch and separate proposed test patch passed `git apply --check`. Membership's hash and all named source/test files remain unchanged in the worktree. No Lean elaboration, axiom trust, theorem truth, or integration success is claimed.
