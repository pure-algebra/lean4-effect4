# H2 part one: exactly eight local proof repairs

The draft is uncompiled. `prepare.py` is restricted to `/private/tmp`, reads the separate mechanical candidate, and writes a separate repaired tree, patch, and manifest. It does not write source in the repository or alter its mechanical input. Root owns all Lean/build execution, failure attribution, integration, and commits. A ninth existing body must be reported without repair.

Authority is addendum 5 at `56da0e1e`, with the user's later clarification: preserve the two-argument `NoShapeDefect ty ex` interface but ignore `ty` in part one; exclude only `badName` and `notImplemented`. `missingService` stays admitted, including under empty requirements. The base `FitsExit` definition and proofs are unchanged. The H1 terminal-state probe is preserved separately at `/private/tmp/H1TerminalSavedWitness.candidate.lean`.

Expected mechanical input: `/private/tmp/h2-part-one-candidate/src/Effect4/Laws/Program/Typed/{Admission,Residual,Stack,Assembly}.lean`, from rulings. The input must already contain the judgment substitutions, definitions, and explicit `(shape : NoShapeDefect ty (.failure c))` premise on `strongExit_of_clean`; its original body must remain for first measurement.

Run after the mechanical candidate exists:

```sh
python3 /private/tmp/h2-eight-repairs/prepare.py
```

The output is `/private/tmp/h2-part-one-repaired`. `eight-body-repairs.patch` is relative to the mechanical candidate, not the repository. `eight-body-manifest.json` lists the exact eight names and old/new declaration-block hashes. `Assembly.lean` is copied unchanged. Helpers are inserted into the existing Admission and Stack modules; no additional library module or import is needed.

| Existing body | Statement/premise change, beyond the mechanical ExitOk substitution | Local repair |
| --- | --- | --- |
| Admission.strongExit_success | None | Pair existing value membership with vacuous success exclusion. |
| Admission.strongExit_of_clean | Explicit `NoShapeDefect ty (.failure c)` premise, inserted in mechanical phase | Pair unchanged base `fitsExit_of_clean` result with that premise. Cleanliness does not exclude defects. |
| Admission.cleanExit_of_never | None | Apply unchanged base `cleanExit_of_never_fits` to first projection. |
| Residual.strongExit_bool | None | Call repaired `strongExit_success`. |
| Residual.settling_fork | None | Keep allocated-fiber declaration witness in first conjunct; add success exclusion. |
| Residual.strongExit_mono | None; this is E's adapter, reported separately from seven legacy bodies | Apply `fitsExit_mono` to first projection and retain second. |
| Stack.strongExit_failure_of_error | None | Apply base `fitsExit_failure_of_error` to first projection and retain exclusion, definitionally independent of type in part one. |
| Stack.popR_typed | External statement otherwise unchanged | Add original-cause exclusion to its local preemption helper and supply it from `hex.2` in three branches; add recorded/pending-cause exclusion to three injected clean failures; pass `hex.1` to the two value-consuming iterator/loop hooks. |

New helpers: `noShapeDefect_of_interrupts`, `noShapeDefect_stripFail`, `noShapeDefect_combine`, `noShapeDefect_sanitize`, `recorded_noShapeDefect`, `pendingCause_noShapeDefect`, and `sanitize_noShapeDefect`. They use only finite reason membership, `Cause.mem_stripFail`, `Cause.mem_combine`, and existing interruption provenance. They do not change the frame or operation contracts or add a reachability premise. No failure-transport field is added to the hook protocols. `hookLaws_interpR` is unchanged.

`Axioms.lean` names all eight changed bodies and all seven helpers. For a namespaced concatenated harness, retain the same names with the harness's namespace. The original before/after ceiling reports still belong to root's compilation; this script changes no obligation registration or ceiling.

Static validation so far: Python syntax check passed; the transform ran successfully on a representative input made from the tracked original mechanical four-file candidate, adjusted to the agreed `ty` argument and explicit clean-failure premise. The resulting diff was inspected: exactly the eight named bodies, seven new helpers, and one explanatory comment at failure transport; no ninth body. This does not establish elaboration, theorem truth, or axiom compliance.

Keep first mechanical log and mapped failure attribution separate from repaired-harness results. Do not hand-fix a new failure in another existing theorem, even if it appears mechanical. Attribute and report it under addendum 5's stop rule.
