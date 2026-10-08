# Module-authoring foundation receipt

The shared foundation covers captured folds and construction across Queue, Semaphore, Pool and Latch.
Existing module behavior and typing statements retain their assumptions.
This landing establishes no whole-module compatibility result across schedules.

## Baseline and integration

The implementation starts at `88a660b3`.
The integration incorporates Claude's committed work through `d327beff`.
Checked source head: `6dc5826d`.
The branch is `codex/module-folds`.
No push or full sweep belongs to this slice.

The plan is `docs/research/2026-10-08-seat-module-gaps-plan.md`.
The author examples are `docs/research/2026-10-08-module-authoring-foundation.md`.
The retained boundary controls are `docs/research/2026-10-08-seat-module-boundary-probe.lean`.
The targeted axiom gate is `docs/research/2026-10-08-seat-module-foundation-trust.lean`.

## Findings resolved

| Finding | Landed resolution |
| --- | --- |
| CW-01 | Named input declarations supply both indexed inputs and named source arguments. Named item and fold binders lift captured step data. |
| CW-02 | One structural requirements fold carries scope alignment and deferred identity interpretation through every constructor. |
| CW-03 | Shared map, filter, conditional map, any, removal and first-match removal builders carry their value equations once. |
| CW-04 | Native option consumption supplies head-or-default. Pool removes its head-reading fold. |
| CW-05 | One typed item list supplies arbitrary tuple arity. Existing two-item and three-item result types and flat encodings remain. |
| CW-06 | One linear integration branch owns roots, the semantics registry and the landing. Independent workers own separate source files. |

Record construction takes field names in any order and derives their types from the declared required-field schema.
Formation, normality and canonical name order remain separate checked properties.
Typed empty values derive their subtype premise once through the shared construction law.
The opaque carrier interpretation supplies no deferred identity comparison law.

Pool's selected-item pass uses one fold after a composed filter-and-map repeats its filter.
The retained measurement probe reports 28 nodes and one fold for that pass.
Pool lease reports 167 nodes and five folds.
These measurements describe stored terms; they establish no execution-cost theorem.

Latch adds initial construction, registration and first-match withdrawal against independent model transitions.
Cleanup searches live waiters before the attached scheduled batch.
Duplicate registrations and an empty batch retain the specified behavior.

The authoring explanation tool now distinguishes a passing check from the remaining premises of its shared law.
A Step check alone proves neither the caller's inputs nor its scope or identity interpretation.

## Proof placement and consumers

| Declarations | Concept and claim | Reach and consumer |
| --- | --- | --- |
| `Step.sound`, `src/Effect4/Laws/Modules/Step.lean` | `translation-simulation`, `step-language-sound`, R10 | Canonical records and caller input readings; fold alignment and identity interpretation where used. Module value equations consume it. |
| `Step.typed`, same source | `store-typing`, `step-language-typed`, R4 | Native atom typing, typed inputs, formation and normality facts; fold scope alignment where used. Module typing consumes it. |
| `Step.scoped`, `src/Effect4/Laws/Modules/Step/Scope.lean` | `initial-algebras-folds`, helper of `operation-data-scoped`, R4 | Scoped caller sources. Module operation scope laws consume it before program admission. |
| `Step.Lists.eval_map`, `eval_filter`, `eval_filterMap`, `eval_removeFirst`, `src/Effect4/Laws/Modules/Step/Lists.lean` | Helpers of `step-language-sound`, R10 | Ordinary carrier list equations. Queue, Semaphore, Pool and Latch model connectors consume them. |
| `packTuple_image`, `src/Effect4/Laws/Modules/Tuples.lean` | Helper of `step-language-sound`, R10 | Exact flat tuple encoding at each arity. Shared reading and Queue's result connector consume it. |
| `latch_registration_agrees`, `src/Effect4/Laws/Modules/Latch/Registration.lean` | `translation-simulation`, `latch-registration-agrees`, R10 | Initial state, registration and withdrawal observations. Withdrawal retains table injectivity and scope alignment. |

The independent review compares all existing public agreement and typing headers against `88a660b3`.
All 66 compared statements retain their assumptions: Queue 23, Pool 17, Semaphore 18 and Latch 8.
Queue, Pool and Semaphore model files remain byte-identical to that baseline.
Latch adds the authorized transition models.

Queue retains arbitrary payload values under its reading contract.
A concrete reader applies its take connector to a unit value under a natural-number declaration.
That reading establishes no membership or typing of the payload.
The typed statements retain their own premises.

## Checks

The reported final Lake commands use `LEAN_NUM_THREADS=3` and run serially in the integration worktree.
The final combined build passes: 1,172 jobs.
It checks the changed foundations, their direct consumers, the proof-style ratchet and the semantics report's required inputs.
It runs neither `lake build Test` nor the whole-library axiom gate.

```sh
LEAN_NUM_THREADS=3 lake build \
  Test.Program.StepLanguage Test.Program.StepConstruction Test.Program.StepConstructors \
  Test.Program.StepFolds Test.Program.StepInputs Test.Program.StepLists Test.Program.StepTuples \
  Test.Schema.Identity Test.Schema.Modeled Test.Program.LatchSteps Test.Program.LatchRegistration \
  Test.Program.SemaphoreData Test.Program.SemaphoreAgreement Test.Program.SemaphoreSteps \
  Test.Program.SemaphoreOps Test.Program.SemaphoreScenarios Test.Program.QueueData \
  Test.Program.QueueAgreement Test.Program.QueueSteps Test.Program.QueueOps \
  Test.Program.QueueScenarios Test.Program.PoolData Test.Program.PoolAgreement \
  Test.Program.PoolSteps Test.Program.PoolOps Test.Program.ModuleDefinitions \
  Test.Program.PartsControls Effect4.Laws Test.Audit.ProofStyle Test.Audit.Explain \
  semantics-report Test.Program.TypedProgBindRed Test.Program.ProtocolPosts \
  Test.Dogfood.P1HttpCache Test.Dogfood.P2HandlerLayers Test.Dogfood.P3WorkerQueue \
  Test.Dogfood.P4RateLimiter Test.Dogfood.P5LedgerService Test.Dogfood.Scenario \
  Test.Dogfood.Scenario.Workers Test.Dogfood.Scenario.Routing Test.Dogfood.Scenario.Atomic \
  Test.Dogfood.Scenario.Timeout Test.Dogfood.Scenario.Tape Test.Dogfood.Scenario.QueueWorkers
```

| Command | Result |
| --- | --- |
| `LEAN_NUM_THREADS=3 lake env lean docs/research/2026-10-08-seat-module-foundation-trust.lean` | Pass: 2,641 declarations in 70 changed modules; only `propext` and `Quot.sound` |
| `LEAN_NUM_THREADS=3 lake env lean docs/research/2026-10-08-seat-module-boundary-probe.lean` | Pass: positive and negative controls |
| `LEAN_NUM_THREADS=3 lake env lean /private/tmp/module-authoring-guide.lean` | Pass: the guide's first two examples, map result `[3, 4]` and fold result `7` |
| `LEAN_NUM_THREADS=3 python3 scripts/check-conform.py cases` | Pass, exit 0; `.lake/conform/cases.json`, 480 build jobs |
| `LEAN_NUM_THREADS=3 lake exe semantics-report .lake/gen/semantics-report` | Pass; the producer writes the semantic report |
| `cp .lake/gen/semantics-report/semantics.md generated/semantics.md` | Saves producer output without hand edits |
| `python3 scripts/check-docs.py` | Pass: every reference resolves |
| `python3 scripts/check-language.py --strict` followed by the 25 changed research Markdown paths below | Pass: no finding in those notes |
| `LEAN_NUM_THREADS=3 lake env lean /private/tmp/module-report-ruling-projection.lean` | Pass: the final ruling update changes no input consumed by the report |
| `git diff --check` | Pass |

The guide check extracts its first two Lean blocks and appends the stated result guards.
The selected-declaration axiom gate excludes the three named Lean elaborator modules, as the library gate does.
The source import traversal finds 222 core modules, no Laws import, and every changed library and battery module reachable.
This traversal supplements the selected checks; it is not the whole-library gate.

An early integration attempt fails on stale size pins and old Queue scope proofs before their final commits arrive.
One overlapping retry is stopped; its output supplies no evidence.
The reported final checks run serially and supersede those attempts.
The final documentation-only rebase leaves `src`, `Test` and `tools` byte-identical to the tested source.


The initial targeted axiom gate refuses four Latch declarations through one library lemma.
`List.erase_eq_eraseP` reaches `Classical.choice`.
`removeFirst_eval` now uses `List.erase_eq_eraseP'` and `Bool.beq_comm`, each with only `propext`.
The proof retains the same statement and behavior.
The selected-declaration rerun passes: 2,641 declarations across 70 modules use only the permitted proof dependencies.

## Remaining boundaries

Exact encoding, membership, codec admission, handle allocation and simulation remain separate claims.
The pure transition laws establish neither cancellation delivery nor posted-flush execution, progress, liveness or scheduling compatibility.
The public API controls check admitted programs, finite execution and TypeScript printing.
They do not run a TypeScript compiler or compare an external Effect runtime.
The existing handle-reading refusal remains a separate target restriction.

Subterm sharing remains open because `Term` has no local binding constructor.
Row 331's module declaration, fixed wrapper reply records and transaction implementation belong to later slices.
Row 332 places the library rename and public entry modules after this landing.
Row 333 fixes the host-session obligations separately from these pure transition laws.
The definition-block host-session repair is a separate landing, `1253079c`.
A transaction's read set, isolation and work bound each need their own placed statement.
The size of a stored `Step` does not bound arbitrary input-list traversal.

## Changed paths

```text
Test/All.lean
Test/Audit/AxiomGate.lean
Test/Audit/Explain.lean
Test/Program/LatchRegistration.lean
Test/Program/LatchSteps.lean
Test/Program/PoolData.lean
Test/Program/PoolSteps.lean
Test/Program/QueueData.lean
Test/Program/QueueSteps.lean
Test/Program/SemaphoreData.lean
Test/Program/SemaphoreSteps.lean
Test/Program/StepConstruction.lean
Test/Program/StepConstructors.lean
Test/Program/StepFolds.lean
Test/Program/StepInputs.lean
Test/Program/StepLanguage.lean
Test/Program/StepLists.lean
Test/Program/StepTuples.lean
Test/Schema/Identity.lean
Test/Schema/Modeled.lean
docs/STATE.md
docs/core/decisions.md
docs/core/semantics.md
docs/research/2026-10-08-module-authoring-foundation.md
docs/research/2026-10-08-seat-deferred-identity-receipt.md
docs/research/2026-10-08-seat-field-inference-receipt.md
docs/research/2026-10-08-seat-latch-registration-receipt.md
docs/research/2026-10-08-seat-module-boundary-probe.lean
docs/research/2026-10-08-seat-module-boundary-receipt.md
docs/research/2026-10-08-seat-module-cons-receipt.md
docs/research/2026-10-08-seat-module-construction-receipt.md
docs/research/2026-10-08-seat-module-foundation-trust.lean
docs/research/2026-10-08-seat-module-gaps-plan.md
docs/research/2026-10-08-seat-module-gaps-receipt.md
docs/research/2026-10-08-seat-module-input-items-receipt.md
docs/research/2026-10-08-seat-module-input-transparency-receipt.md
docs/research/2026-10-08-seat-module-inputs-receipt.md
docs/research/2026-10-08-seat-module-scope-receipt.md
docs/research/2026-10-08-seat-module-semaphore-named-receipt.md
docs/research/2026-10-08-seat-module-semaphore-receipt.md
docs/research/2026-10-08-seat-pool-data-receipt.md
docs/research/2026-10-08-seat-pool-lists-receipt.md
docs/research/2026-10-08-seat-pool-measure-final-receipt.md
docs/research/2026-10-08-seat-queue-ops-receipt.md
docs/research/2026-10-08-seat-queue-step-data-receipt.md
docs/research/2026-10-08-seat-queue-typing-receipt.md
docs/research/2026-10-08-seat-step-lists-receipt.md
docs/research/2026-10-08-seat-step-measure-probe.lean
docs/research/2026-10-08-seat-step-measure-receipt.md
docs/research/2026-10-08-seat-tuples-plan.md
docs/research/2026-10-08-seat-tuples-receipt.md
generated/semantics.md
src/Effect4.lean
src/Effect4/Laws.lean
src/Effect4/Laws/Modules/Cons.lean
src/Effect4/Laws/Modules/Construction.lean
src/Effect4/Laws/Modules/Latch/Model.lean
src/Effect4/Laws/Modules/Latch/Registration.lean
src/Effect4/Laws/Modules/Latch/Steps.lean
src/Effect4/Laws/Modules/Option.lean
src/Effect4/Laws/Modules/Pool/Data.lean
src/Effect4/Laws/Modules/Pool/Ops.lean
src/Effect4/Laws/Modules/Pool/Passes.lean
src/Effect4/Laws/Modules/Pool/Reading.lean
src/Effect4/Laws/Modules/Pool/Steps.lean
src/Effect4/Laws/Modules/Pool/Typing.lean
src/Effect4/Laws/Modules/Queue/Data.lean
src/Effect4/Laws/Modules/Queue/OfferData.lean
src/Effect4/Laws/Modules/Queue/Ops.lean
src/Effect4/Laws/Modules/Queue/Passes.lean
src/Effect4/Laws/Modules/Queue/Steps.lean
src/Effect4/Laws/Modules/Queue/Typing.lean
src/Effect4/Laws/Modules/Semaphore/Data.lean
src/Effect4/Laws/Modules/Semaphore/Ops.lean
src/Effect4/Laws/Modules/Semaphore/Steps.lean
src/Effect4/Laws/Modules/Semaphore/Typing.lean
src/Effect4/Laws/Modules/Step.lean
src/Effect4/Laws/Modules/Step/Annotations.lean
src/Effect4/Laws/Modules/Step/ErasedCompiler.lean
src/Effect4/Laws/Modules/Step/Lists.lean
src/Effect4/Laws/Modules/Step/Rename.lean
src/Effect4/Laws/Modules/Step/Requirements.lean
src/Effect4/Laws/Modules/Step/Scope.lean
src/Effect4/Laws/Modules/Tuples.lean
src/Effect4/Laws/Schema/Identity.lean
src/Effect4/Modules/Latch/Registration.lean
src/Effect4/Modules/Latch/Steps.lean
src/Effect4/Modules/Pool/Cell.lean
src/Effect4/Modules/Pool/Data.lean
src/Effect4/Modules/Pool/Passes.lean
src/Effect4/Modules/Pool/Steps.lean
src/Effect4/Modules/Queue/Cell.lean
src/Effect4/Modules/Queue/Data.lean
src/Effect4/Modules/Queue/Steps.lean
src/Effect4/Modules/Semaphore/Cell.lean
src/Effect4/Modules/Semaphore/Data.lean
src/Effect4/Modules/Semaphore/Steps.lean
src/Effect4/Modules/Step.lean
src/Effect4/Modules/Step/Elab.lean
src/Effect4/Modules/Step/Elab/Inputs.lean
src/Effect4/Modules/Step/Inputs.lean
src/Effect4/Modules/Step/Lists.lean
src/Effect4/Modules/Step/Rename.lean
src/Effect4/Schema/FieldRef/Elab.lean
src/Effect4/Schema/Identity.lean
src/Effect4/Schema/Modeled.lean
src/Effect4/Store/Carrier/Image/Containers.lean
tools/Tools/Explain.lean
tools/Tools/SemanticsRegistry.lean
```
