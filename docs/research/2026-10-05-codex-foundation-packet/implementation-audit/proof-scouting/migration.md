# Migration proof scouting

M0 can proceed without a new Lean theorem. Before M2 lands, retain transitive proof impact and the exact scope of each migrated witness.

Evidence: source reading and inspection of retained artifacts. No Lean, runtime probe, build, generator, installation, or repository edit runs.
Reviewed HEAD: `4977c4f3db4db51903ed9437022fd0f27d6fa41f`. Decisions row 248 governs the incremental migration.
The migration plan already identifies its direct dependency join as incomplete. These recommendations make its acceptance evidence concrete.

## 1. Ask the existing dependency walker which claims reach changed definitions

**Finding.** A401 F11 names four direct registry matches. It explicitly leaves transitive dependencies unresolved.
`ProofGraph.Plan.walk` reports nearest selected theorem nodes and counts of supporting definitions.
`Tools.Semantics.planJson` exports those counts, without their declaration names.
The retained report gives `Effect4.Program.Agreement.run_eq_meaning` 905 definitions and no nearest nodes.
It therefore cannot answer which of those definitions belongs to M2 or M6.
This is a concrete missing query, not an incorrect proof-status result.

**Smallest change.** Add an impact query using `ProofGraph.reachedAxiomsMany` with the slice's changed declarations as stop leaves.
Filter its returned leaves to those declarations. Use a fresh memo for each loaded environment and stop predicate. Never reuse it across slice revisions.
Its existing `usedConstantsOf` follows types, values, and inductive constructors.
Include registry witnesses, requirement tops, placed goals, and affected census witnesses as roots.
Report unloaded roots and budget exhaustion explicitly. Neither means no dependency.
Keep the existing plan and statuses. This query needs no second graph representation.

The query can return reached change leaves first. A witness path can wait until a consumer needs one.
Retain the base declaration statements, then compare the migrated statements and their status after the authorized narrow builds.
An unchanged theorem name or a fresh `proved` label alone does not establish an unchanged claim.

**Placement and consumer.** This is evidence tooling for existing `decision-keeps-typed`, `run-eq-meaning`, and scope claims.
Their concepts remain `reactive-scheduling`, `translation-simulation`, and `scope-lifetime-finalization`; consumers remain M6/M7 and R11.
It proposes no new mathematical theorem.
**Premises.** Complete changed-declaration set, loaded relevant roots, fresh environment, and unchanged stop set within one memo.
**Observation.** Which roots reach the changed definitions; their before/after statements and derived proof status.
**Exclusions.** This follows the elaborated constant dependency graph only. It does not infer callback behavior, future instantiations, dynamic host dependencies, or semantic necessity.
It establishes neither host agreement nor proof preservation across changed definitions.
**Immediate prerequisite.** M2's brief names its actual changed declarations. Validate direct, indirect, type-only, and unrelated controls in that tooling slice.

Sources: `ProofGraph.reachedAxiomsMany` and `usedConstantsOf` in `tools/ProofGraph/Axioms.lean`;
`ProofGraph.Plan.walk` in `tools/ProofGraph/Plan.lean`; `Tools.Semantics.planJson` in `tools/Tools/Semantics.lean`;
A401 audit F11; migration plan F5 and exclusions.

## 2. Carry the census build through its witness join

**Finding.** The present census gate joins IDs, kinds, and signed divergences.
`Test.Audit.RuntimeCoverage.Row` has no build field. Its emitted row also has none.
`checkWitnesses` checks theorem existence, while `checkRowShape` checks authored coverage labels.
These checks cannot detect a release source row accidentally paired with evidence still attributed to rc.112.
M1's proposed source build column must reach this join, not only the generator output.

**Smallest change.** Join `(row ID, build, kind)` between generated source rows and emitted Lean evidence rows.
For each promoted row, retain the source reading and state which clause each existing theorem witnesses.
A theorem may remain valid for both builds. It needs no duplicate solely to carry two source attributions.
Distinguish a local rule witness from a claim about composed machine execution.
Equal source-span bytes establish the former attribution only to the extent of that row's sentence and hypotheses.
For affected composed claims, use recommendation 1 before retaining their scope.
Keep coverage state, proof status, and runtime version as separate facts in the report.

**Placement and consumer.** Evidence ownership for the row's existing concept and witnesses; M1 and every later migration slice consume it.
For scope rows this serves `scope-lifetime-finalization` and R11. It does not introduce a generic host-equivalence claim.
**Premises.** Pinned vendor bytes, identified source span, reviewed row sentence, and the actual witness statement.
**Observation.** The same source build labels the source row and its claimed Lean evidence.
**Exclusions.** This join does not prove the theorem describes the source or that the entire mixed machine agrees with either host.
**Immediate prerequisite.** M1 chooses its mixed-row format and updates both emitted formats together.
Its acceptance controls should reject a build-only mismatch and preserve a legitimately shared witness.

Sources: `Test.Audit.RuntimeCoverage.Row`, `checkRowShape`, `checkWitnesses`, and `emitRuntimeCoverage` in `Test/Audit/RuntimeCoverage.lean`;
`scripts/check-effect-runtime-census.sh`; `scripts/report-effect-runtime-coverage.sh`; migration plan F2–F3.

## 3. M0 acceptance prerequisite: compare each observation separately

**Status.** This is an acceptance prerequisite, not a finding against M0 implementation.
The M0 worktree is clean at `f3086de1d8a395d39480cbd361622f919a069996` during this read.
Its targeted harness and script inventory shows no draft migration ledger. The original selector and observation fields remain.
An in-progress implementation may already be addressing this requirement.

**Evidence.** The audit records release agreement for `pProvideMerge` as `True,False,True`: exit, schedule, and synchronous exit.
The same pattern holds for `pProvideTwice` and `pMergeAll`.
A whole-program label of “pin only” is too coarse if it permits arbitrary release disagreement.
It could accept a new release result mismatch while the known difference concerns scheduling.
The migration plan's stop rule requires distinguishing those causes.

**Smallest change.** Retain separate expected observations for each program and build.
Accept equality or an identified, exact known difference. Represent an unavailable run separately from disagreement.
Preserve the runner's existing `signedU01` pattern: exact exit pair, compared schedules, sync agreement, and parked status.
For the three scope programs, preserve result agreement while allowing only their reviewed schedule difference.
Recheck the ledger after T3b changes generated programs, as F4 already requires.
Keep runtime, compiler, generated-module identity, and host-answer tapes attached to each run.

**Placement and consumer.** Finite evidence for `translation-simulation` and R8; M0's gate and later slice receipts consume it.
This is not a proof of `run-eq-ref`, which relates two local models at the empty host table.
**Premises.** Named program bytes, runtime/package build, compiler, inputs, recorder, and compared observation.
**Observation.** Exit, compared schedule, and synchronous exit individually; explicit missing-run status where applicable.
**Exclusions.** Unmeasured programs, arbitrary schedules, infinite behavior, and general agreement with the mixed machine.
**Immediate prerequisite.** The M0 ledger format names these dimensions.
Acceptance controls should reject an altered result under a known schedule-only exception and reject missing required observations.

Sources: `signedU01` and the comparison/verdict code in `harness/truth/run-truth.ts`;
`scripts/check-truth.py`; A401 `out/truth-401/summary.tsv`; migration plan F2, F4, and F5.

## Receipt

Read-only commands: `cat`, `sed`, `rg`, `git rev-parse HEAD`, and Python JSON inspection.
Two exploratory searches named absent files (`Graph.lean`, `check-truth.sh`, and `tools/Main.lean` across searches).
They returned nonzero; the existing file inventory supplied the actual paths used above.
No gate or proof execution is claimed. The retained generated report is inspected as an artifact, without claiming it is fresh at HEAD.
`migration.receipt.json` records source hashes and static inspection results.
