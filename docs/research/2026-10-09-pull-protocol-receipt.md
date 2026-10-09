# Pull protocol module receipt

The first Pull slice is ready for integration on `codex/pull-protocol`.
It adds shared outcome handlers and moves Stream onto them, without changing the core program representation.
Its laws concern the existing denotation; its target evidence covers finite emitted callers.
Whole-stream execution and native Done correspondence remain open.

## Commits and ownership

Base: `7334f1197cf5b535541ce1dfc7789a5082c07115`.
Implementation and verification head: `19eb80829574db2357f2a83d4178fa297986cfaa`.
Worktree: `/Users/pooks/.codex/worktrees/module-semaphore/lean4-effect4`.
This receipt follows that implementation commit and changes no implementation or evidence bytes.

The primary checkout advances independently to `8a36f2008de04d7ff313d7cb5290c4cd1ac54d71` during this slice.
The changed paths at that primary head and this slice do not overlap from the common base.
Claude owns the visual pipeline and related owner rulings there.
The bounded session-tail inspection checks its repository and excludes internal thinking fields.
No message, edit, merge or push changes that session or its primary worktree.

Two GPT-6.1 Sol agents cover Stream integration, module inventory, adversarial review, and the emitted packet.
The coordinator owns the single Lake lane and reproduces every reported build and runtime result.
The source review finds no actionable defect in the bounded Pull design.

## Changed files

| Area | Paths |
| --- | --- |
| Pull operations | `src/Effect4/Library/Pull/Ops.lean` |
| Pull scope and meaning | `src/Effect4/Laws/Library/Pull/Scope.lean`, `src/Effect4/Laws/Library/Pull/Protocol.lean` |
| Stream consumers | `src/Effect4/Library/Stream/Ops.lean`, `src/Effect4/Library/Stream/ArrayOps.lean`, `src/Effect4/Laws/Library/Stream/Ops.lean` |
| Library and test reachability | `src/Effect4/Library.lean`, `src/Effect4/Laws.lean`, `Test/All.lean`, `Test/Program/Pull.lean` |
| Claim placement | `docs/core/semantics.md`, `tools/ProofGraph/Registry.lean`, generated `generated/semantics.md` |
| Source ownership and exposure | `tools/Tools/ArchitectureRoles.lean` |
| Reproducible target packet | `harness/pull-protocol/Produce.lean`, `observe.ts`, `run.py`, `README.md` |
| Design and inventory | `docs/research/2026-10-09-pull-protocol-plan.md`, `docs/research/2026-10-09-module-authoring-inventory.md` |
| Scoped proof audit | `docs/research/2026-10-09-pull-protocol-audit.lean` |
| Retained evidence | `docs/research/2026-10-09-pull-protocol-evidence/` |

`git diff --name-only 7334f119 19eb8082` gives every individual changed path.
The retained evidence contains exact emitted declarations, compiler inputs, commands, pins, hashes, observations and focused build logs.

## Behavior and authoring

`Pull.chunkValue` and `Pull.endValue` construct the existing protocol values.
`Pull.matchAnswer` selects the batch or completion handler and passes its payload.
`Pull.catchDone` handles completion and unwraps normal batches.
`Pull.matchEffect` selects success, completion or failure after the input finishes.
A selected handler's failure escapes without entering another handler.
The selected handler receives the stores left by the input.

`Stream.drain` uses the shared selection helper and its scope law.
`Stream.arrayPull` uses the shared value constructors.
Those replacements expand to the prior core trees.
The core keeps one `Eff`, with no new machine primitive or stored data type.

The public battery checks the existing `eff_module` route with `ProtocolDefinitions`.
A module declares the result column once, including for an always-failing operation.
Its bodies need neither repeated protocol ascriptions nor an artificial successful branch.
Inline callers still need a declared protocol type when inference sees only one variant or no successful value.
The retained negative controls identify that authoring limit.
A stored array source supplies its declared result column to Pull without a caller annotation.

The inventory records compiler-stage owners, proof boundaries and minimal authoring improvements.
Its next ergonomic proposal derives Source metadata from existing operation declarations.
It keeps graph editing and TypeScript output aligned with the primary checkout's row 336 ruling.

## Proof placement

| Question and role | Declaration and consumer | Premises and observation | Remaining boundary |
| --- | --- | --- | --- |
| `pull-protocol-selection`, compatibility, `translation-simulation`, R10 | `Pull.matchEffect_protocol`; registry, public handlers and future Channel composition | Exact input exit and resulting stores, aligned source/value scopes, and successful authoring elaboration of every handler; observes the selected handler's exit and final stores | No arbitrary scheduler, native Done adapter, nonempty-batch admission or whole-stream run |
| Selection helpers of that claim | `matchAnswer_meaning`, `matchEffect_meaning`, private source-tree construction; consumed by `matchEffect_protocol` | Existing selection and cause-match denotation, actual binder scopes and the input's resulting stores | No generic handler typing theorem |
| `pull-completion-recovery`, compatibility, `translation-simulation`, R10 | `Pull.catchDone_meaning`; registry and completion recovery | Input and answer-handler authoring elaboration; input failures keep their cause and stores, and selected-handler failures escape | Exact answer selection uses the separate helper; no host completion correspondence |
| Constructor reading, helpers of protocol selection | `chunkValue_reads`, `endValue_reads`; public battery readers and later Pull producers | Payload terms read their carrier values; observes the existing protocol image | No nonempty premise or codec admission |
| Constructor typing, `step-language-typed`, `store-typing`, R4 | `chunkValue_types`, `endValue_types`; public numeric reader and later typed producers | Native atom typing, the pair atom's literal-type policy, and payload typing at each flag | No full callback typing or execution result |
| Source scope, helpers of protocol selection and `elaborate_scoped` | Pull scope laws; `Stream.drain_scoped` and public operations | Scoped caller programs, terms and handlers | Scope alone establishes no reading or typing |

The generated report records both new registered claims as proved, with no planned-goal dependencies.
Each reaches only `propext` and `Quot.sound`.
`claims.json` retains those producer results.

## Reproduced checks

Every Lean build uses `LEAN_NUM_THREADS=3` and the pinned Lean `4.33.1`.
The lakefile enforces `warningAsError=true`.
Only one Lake process runs at a time.

| Command | Result |
| --- | --- |
| `LEAN_NUM_THREADS=3 lake build Effect4.Laws.Library.Pull.Protocol Effect4.Library.Stream.ArrayDefs Effect4.Laws.Library.Stream.Ops Effect4.Laws.Library.Stream.Array Test.Program.Pull Test.Program.StreamArray Tools.ArchitectureRoles ProofGraph.Registry` | Pass at the committed implementation head; retained in `final-build.log` |
| `LEAN_NUM_THREADS=3 lake build Effect4.Laws semantics-report Test.Program.TypedProgBindRed Test.Program.ProtocolPosts Test.Dogfood.P1HttpCache Test.Dogfood.P2HandlerLayers Test.Dogfood.P3WorkerQueue Test.Dogfood.P4RateLimiter Test.Dogfood.P5LedgerService Test.Dogfood.Scenario Test.Dogfood.Scenario.Workers Test.Dogfood.Scenario.Routing Test.Dogfood.Scenario.Atomic Test.Dogfood.Scenario.Timeout Test.Dogfood.Scenario.Tape Test.Dogfood.Scenario.QueueWorkers` | Pass; these are the producer's declared roots, not the whole battery |
| `LEAN_NUM_THREADS=3 lake exe semantics-report /tmp/effect4-pull-semantics` | Pass; its Markdown output supplies `generated/semantics.md` |
| `LEAN_NUM_THREADS=3 lake build Test.Program.Pull` | Pass after the final controls; 37 guards and two concrete constructor readers |
| `LEAN_NUM_THREADS=3 lake env lean docs/research/2026-10-09-pull-protocol-audit.lean` | All 161 selected declarations pass the axiom ceiling; the core imports no Laws module |
| `python3 harness/pull-protocol/run.py --skip-build --install /Users/pooks/Dev/lean4-effect4/ts/release/node_modules --out docs/research/2026-10-09-pull-protocol-evidence` | Eight positive callers and two wrong-catch controls pass |
| `python3 scripts/check-docs.py` | All referenced paths, links, citations and make targets resolve |
| `python3 scripts/check-language.py --strict harness/pull-protocol/README.md docs/research/2026-10-09-pull-protocol-plan.md docs/research/2026-10-09-module-authoring-inventory.md` | No findings in the new documents |

The initial draft fixes missing explicit reader arguments and reason annotations before the final builds.
Those are repaired draft errors, not retained production defects.
No full test sweep runs.

## Target evidence

Compiler: tsgo `7.0.0-dev.20260629.1`.
Runtime: Bun `1.4.2`, Effect `4.0.1`.
The compiler reports no diagnostics for the exact emitted declarations and retained helper imports.
The runtime answers the fixed numeric observations already checked on the Lean machine.

The positive observations cover payload delivery, end leftovers, input failure, retained state, finalizer failure and escaping handler failures.
Both deliberately wrong wrappers also compile.
They answer 99 where the correctly placed outer handler answers 42.
The observation distinguishes behavior that type checking alone accepts.

This compares finite emitted callers with fixed observations.
It does not compare Effect's native Pull implementation or convert mixed Done causes.
It establishes no universal TypeScript execution theorem or asynchronous progress.
Current source hashes, emitted hashes and compiler-input hashes match the retained packet receipt.

## Integration and next work

Integrate the implementation commit and this receipt together.
The primary STATE document remains with Claude's active visual work.
After integration, add this slice to its module entry and retain the bounded claim descriptions.

Channel transformations are the next module slice under the existing Pull-to-Channel-to-Stream order.
Derive their adapters from existing declared columns before introducing additional author metadata.
SynchronizedRef's effectful update follows the existing Ref and Semaphore composition.
Its proof must account for interruption between successful client completion and the committed write.
PartitionedSemaphore and PubSub still need their waiter identity, cancellation, delivery and lifetime connections.

## Retained whitespace

`compiled-inputs/control.ts` retains the exact bytes of `harness/truth/control.ts`, including its terminal blank line.
The ordinary whitespace check reports that single inherited line.
The check permits only that path and verifies byte equality with its source.
Every other changed file passes the ordinary whitespace check.
