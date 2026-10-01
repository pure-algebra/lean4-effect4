# CE008 test integration draft

This is an uncompiled candidate. Only `/private/tmp` was written. Root owns the serialized Lean lane and must check the candidate before applying the register's landing statuses.

`integration.patch` contains the test append and register changes. `ce008-controls.patch` and `register.patch` contain the same changes separately. `baseline/` records the exact read inputs; `candidate/` records the proposed output. `manifest.json` records both SHA-256 hashes and maps every new theorem to its original audit name.

The test append has one namespace, `Test.Program.H2PartOne.MissingServiceTransport`, and five theorem/axiom-print pairs: `loop_admitted`, `input_ok`, `provenance`, `output_eq`, `output_bad`. It preserves the original actual stack, loop contract and `popR` calculation. `FullNoShapeDefect` and `FullExitOk` are local experimental predicates that include the held missing-service exclusion; they do not shadow or alter live part-one admission. No full SavedOk, typed machine, reachable run, general preservation result, or part-two repair is claimed. The loop's answer is never, so its success continuation requirement is vacuous; the failure branch of the actual stack walk supplies the counterexample.

The existing 27 test theorem/print pairs are unchanged, including root's fully qualified RRace and Option ExitV annotations. The result has 32 theorem/print pairs. The original standalone diagnostic showing error-column-only transport is false remains in the audit; it is not duplicated here.

Register changes follow addenda 5–6: CE007 is REPAIRED by shared part-one admission, references the exact copied historical field-only probe as historical evidence, and identifies current refusals; CE008 is SEEDED by the retained actual saved-frame witness; CE003 changes only its repair column, retaining its original status, attacked statement and still-true counterexample.

Static validation performed (exit 0; no Lean):

```sh
cd /private/tmp/h2-independent-review/ce008-integration/baseline
git apply --check /private/tmp/h2-independent-review/ce008-integration/integration.patch
```

Root's narrow check after applying the test append (run only in the designated worktree's single Lean lane):

```sh
cd /Users/pooks/Dev/lean4-effect4-slice6
lake env lean -DwarningAsError=true Test/Program/H2PartOne.lean
```

The five new local theorems are already printed in that file. Root's final trust check must cover the new definitions as well as the theorem prints. No source, runtime, protocol or generated file changes are present in this patch.
