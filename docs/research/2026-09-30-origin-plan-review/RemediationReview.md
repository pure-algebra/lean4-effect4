**Ratify the fork-ledger remediation as a plan revision. Revise the M6/API portion before ratifying its full proof scope.** Reviewed at `be15b062`; no implementation or decision record was changed.

The remediation addresses the earlier review's main ledger findings: forks only, explicit lookup facts, comparison including source paths, a deliberately failing comparison control, hand proofs before automation, and regeneration before integration. Two details belong in the written contract:

- State unique ledger child IDs, IDs below the allocation counter, correspondence with actual fibers, and missing-ID behavior. A counter that increases is not sufficient by itself. Restrict the old/new behavior comparison to reachable, well-formed machines and their member fibers. Current `statusOf m f` accepts arbitrary supplied fibers and reads their own origin; lookup cannot agree for every such input.
- Prove the local lookup/freshness facts before moving the reader proofs. The final proof over reachable runs can remain after migration. Preserve unconditional append statements separately.

The M6/API amendment needs three changes.

1. **Runtime admission and semantic answer requirements are complementary layers.** Keep the transition proof's typed-answer requirement and prove that the runtime boundary establishes the appropriate requirement. Do not state that admission simply makes the raw incoming answer well typed in the old state. `externalValue` can accept a number as an allocation request, create an external handle, and deliver that handle (`src/Effect4/Program/Compile.lean:1354–1382`). The connection must cover the prepared answer, the updated store, and any newly allocated typing information. Delayed reference reads need their own treatment too: admission checks current contents, while the semantic completion condition uses the cell's declared type.

2. **Name the missing reference-runner work.** M6 currently uses `RState` and `replayR`, which has no row-table argument. The existing `run_eq_ref` statement expressly excludes external registration, conversion/allocation, and prepared answers (`src/Effect4/Laws/Program/RuntimeR.lean:203–210`). Thus the proposed connection is more than one lemma for all external replies. Recommended scope: repair the current M6 statement with permitted answers on its current reference fragment; retain executable runtime admission as the public contract; give the external-row connection its own explicit slice. Do not describe the broader public guarantee as proved until that slice and its admission connection pass.

3. **Preserve both budgets in the checked typed replay.** `Typed.replay` accepts separate execution and compilation limits (`src/Effect4/Api.lean:460–472`). `Api.replayChecked` currently compiles using execution fuel (`:354–359`). A direct substitution changes existing valid executions. Extend the checked path to preserve both limits, freeze the refusal-bearing return type, and require accepted runs to agree with raw replay at the same limits. Preserve the existing distinction between refusal, unfinished execution, and program failure.

Changing `Typed.replay` is a reasonable explicit strengthening of that API, not a consequence that follows automatically from repairing M6. Raw `Api.replay` and `replayAdmitted` deliberately leave decision admission to the caller (`Api.lean:278–284,425–436`); retain their documented roles. The live session checks replies again at application and disallows direct answer decisions on its control path (`Api/HostSession.lean:204–215,239–243`).

The sleep example is useful but does not by itself test external answer typing. Checked replay rejects both a numeric and a Unit answer injected into a sleep, because sleep is not an external call. The new probes therefore also include a real external row with positive and negative type controls.

Fresh verification:

```text
lake env lean -M6144 -DwarningAsError=true docs/research/2026-09-30-origin-plan-review/RemediationProbe.lean
exit 0
Remediation probes: all 12 finite guards passed.
```

The [probe](RemediationProbe.lean) and [output](remediation-probe.log) confirm the unchecked typed replay example, the exact sleep refusal, ordinary clock completion, external-row acceptance/refusal, numeric-to-handle conversion, and the budget difference. These are finite checks, not the missing universal admission proof. The previous six-theorem M6 counterexample remains in [Probe.lean](Probe.lean).

Only these review artifacts were added. Existing implementation, plan, and `STATE.md` were not edited by this review. No commit or push was made.
