# Channel transforms and module declarations receipt

Integrate this as a bounded Channel transformation slice on `codex/channel-transforms`.
It adds batch and completion maps, named operation declarations, and declaration-derived Stream sources.
The target producer uses explicit branch ascriptions until the already ruled `ifCase` printer lands.
Handle headers remain outside the existing reader's domain.
Neither limit changes the claims proved here.

## Commits and ownership

Base: `9d489341525ea4a55bb9da512ae35809c0175093`.
Implementation and verification head: `34e516559a7102feca81d7f5c551af8966097cca`.
Worktree: `/Users/pooks/.codex/worktrees/module-semaphore/lean4-effect4`.
This receipt follows the implementation commit and changes no implementation or evidence bytes.

The primary checkout independently integrates the preceding Pull slice at `b86307621589d7a9f4c408c16da35c8fd22a8ded`.
The changed paths from this slice's base do not overlap at that primary head.
Claude owns the visual work there.
The bounded session inspection verifies its repository and excludes internal thinking fields.
This slice makes no edit, message, merge or push in that checkout or implementation session.

Three GPT-6.1 Sol agents cover the generator, Channel semantics, public callers, target packet and independent reviews.
The parent owns the single Lake lane and reproduces the checks below.
The independent naming probe finds a real metadata-type capture, which the shared generator now repairs.

## Changed files

| Area | Paths |
| --- | --- |
| Named declarations | `src/Effect4/Program/Authoring/Module.lean`, `Test/Program/ModuleDeclarations.lean` |
| Channel operations | `src/Effect4/Library/Channel/Ops.lean`, `Test/Program/Channel.lean` |
| Channel scope and dispatch | `src/Effect4/Laws/Library/Channel/Scope.lean`, `src/Effect4/Laws/Library/Channel/Protocol.lean` |
| Source adapter and declaration law | `src/Effect4/Library/Stream/Definitions.lean`, `src/Effect4/Laws/Library/Stream/Definitions.lean` |
| Root reachability | `src/Effect4/Library.lean`, `src/Effect4/Laws.lean`, `Test/All.lean` |
| Claim placement and source ownership | `docs/core/semantics.md`, `tools/ProofGraph/Registry.lean`, `tools/Tools/ArchitectureRoles.lean`, generated `generated/semantics.md` |
| Target packet | `harness/channel-transforms/Produce.lean`, `run.py`, `observe.ts`, `README.md` |
| Design and authoring inventory | `docs/research/2026-10-09-channel-transforms-plan.md`, `docs/research/2026-10-09-module-authoring-inventory.md` |
| Scoped audit | `docs/research/2026-10-09-channel-transforms-audit.lean` |
| Positive and negative evidence | `docs/research/2026-10-09-channel-transforms-evidence/`, `docs/research/2026-10-09-channel-transforms-branch-refusal/` |

## Authoring and behavior

`eff_module` exposes each existing `DefSrc` through a named `definitions` field.
The ordered `defs` list projects those fields; it no longer duplicates the metadata.
Generated calls, installation and `using self` recursion retain their existing interfaces.
Direct record construction now supplies `definitions` rather than a writable `defs` field.
Exact generated references prevent operation and parameter names from capturing the metadata type.
The controls include a module named `Definitions`, colliding names, group parameters, recursion, relative namespaces and explicit root namespaces.

`Channel.map` and `Channel.mapEffect` transform one whole batch after one upstream invocation.
`Channel.mapDone` and `Channel.mapDoneEffect` transform only the completion payload.
Their upstream is a named declaration; their state argument is its entire packed request.
Callbacks author ordinary source terms and programs, never stored runtime closures.
No new `Eff` constructor, machine operation or stored data type enters the tree.

`Source.fromDefinitions` derives element and completion types from the pull declaration.
It checks the whole normalized protocol shape, the open and close state relationships, and the unit close answer.
Every invocation comes from the corresponding declaration's name.
A mismatch returns the declaration and the failed column relationship.
The ordinary module checker still owns formation, argument typing, errors, requirements and body admission.

Input failures bypass the transformations with their full causes and resulting stores.
Transformation failures escape with their resulting stores.
The existing Stream consumer owns opening, stopping after End and closing.
The controls check retained writes, packed captures, composition and exactly one close on success and selected failures.
Input and mapped batch nonemptiness remain producer premises.
This profile ignores the native output index and uses decisions row 331's End-value representation.

## Proof placement

| Question and role | Declaration and consumer | Reach and premises | Remaining boundary |
| --- | --- | --- | --- |
| `stream-source-declarations`, compatibility, `store-typing`, R4 | `Source.fromDefinitions_declarations`; source construction and the claim registry | Accepted adapter; normalized protocol and state relationships; observes derived columns and invocation names | Supplied declarations, not arbitrary installed blocks; no body admission, nonempty batch, execution or host behavior |
| `channel-batch-transform`, compatibility, `translation-simulation`, R10 | `Internal.mapEffectOf_protocol`; Channel dispatch and the claim registry | Exact input observation, actual wrapped-handler elaborations and aligned source/value scopes; observes the selected handler's complete exit and stores | Conditional denotation; no execution of stored calls, scheduler behavior or whole-stream simulation |
| `channel-completion-transform`, compatibility, `translation-simulation`, R10 | `Internal.mapDoneEffectOf_protocol`; completion dispatch and the claim registry | The same premises; input failure propagates, while success selects its completion or unchanged-batch handler | The same stored-call and host boundaries |
| Dispatch helper | `bindAnswer_protocol`; both Channel claims | Shared bind and Pull-selection semantics with actual minted scopes | No independent compatibility grade |
| Scope helpers | `invoke_one_scoped`, internal and public map scope laws; public operations and Channel proof modules | Scoped state and callback under its payload reader | Scope alone proves no typing, reading or stored-call execution |
| Named declaration projection | Generated `defs`; source adapter and installed callers | One generated declaration list and exact field references | No coherence theorem for manually forged call records |

The generated report marks all three new registered claims proved, with no planned-goal dependencies.
Their only reached axioms are `propext` and `Quot.sound`.
`claims.json` retains the producer's statements and results.
The denotation does not execute stored definition calls.
The finite module controls exercise the definition-aware machine separately.

## Reproduced checks

Every Lean command uses `LEAN_NUM_THREADS=3` and Lean `4.33.1`.
The lakefile enforces `warningAsError=true`.
Only one Lake process runs at a time in this worktree.

| Command or check | Result |
| --- | --- |
| `lake build Test.Program.ModuleDeclarations Test.Program.Channel Test.Program.AuthoringModule Test.Program.ModuleDefinitions Test.Program.StreamArray Effect4.Library Effect4.Laws.Library.Channel.Protocol Effect4.Laws.Library.Stream.Definitions Tools.ArchitectureRoles ProofGraph.Registry` | Pass; `final-build.log` retains the output, including the existing Queue, Semaphore and Stream callers |
| `lake build Effect4.Library Effect4.Laws semantics-report Test.Program.TypedProgBindRed Test.Program.ProtocolPosts Test.Dogfood.P1HttpCache Test.Dogfood.P2HandlerLayers Test.Dogfood.P3WorkerQueue Test.Dogfood.P4RateLimiter Test.Dogfood.P5LedgerService Test.Dogfood.Scenario Test.Dogfood.Scenario.Workers Test.Dogfood.Scenario.Routing Test.Dogfood.Scenario.Atomic Test.Dogfood.Scenario.Timeout Test.Dogfood.Scenario.Tape Test.Dogfood.Scenario.QueueWorkers` | Pass; these are the semantic producer's roots, not the whole battery |
| `lake exe semantics-report .lake/gen/channel-semantics` | Pass; its Markdown output supplies `generated/semantics.md` |
| `lake build ProofGraph.ProofStyle` | Pass; supplies the scoped parser audit |
| `lake env lean docs/research/2026-10-09-channel-transforms-audit.lean` | All 757 selected declarations pass the existing axiom ceiling; imported core roots exclude Laws; new law files pass parsed proof-style checks |
| `python3 harness/channel-transforms/run.py --skip-build --install /Users/pooks/Dev/lean4-effect4/ts/release/node_modules --out docs/research/2026-10-09-channel-transforms-evidence` | Eight positive cases and two wrong-transform controls pass |
| `python3 scripts/check-docs.py` | Every referenced path, link, citation and make target resolves |
| `python3 scripts/check-language.py --strict harness/channel-transforms/README.md docs/research/2026-10-09-channel-transforms-plan.md docs/research/2026-10-09-module-authoring-inventory.md docs/research/2026-10-09-channel-transforms-receipt.md` | No findings in these documents |
| Controlled-English comparison for `docs/core/semantics.md` against the base | No new findings; existing findings remain outside this slice |
| Retained packet hashes | Current source, emitted declarations and compiler inputs match the receipt |

The first generator draft exposes nested-name collisions and two incorrect Lean API expressions.
The final generator repairs them before these checks.
No full test sweep runs.

## Target evidence and retained limits

Compiler: tsgo `7.0.0-dev.20260629.1`.
Runtime: Bun `1.4.2`, Effect `4.0.1`.
The final packet reports no compiler diagnostics.
Both runtimes give the fixed numeric observations for the selected modules.
The wrong batch transform answers 10 instead of 30; the wrong completion transform answers 42 instead of 43.
Both controls compile, so the observed values detect mistakes that type checking alone accepts.

The raw branch producer passes Lean module checking and emission but fails tsgo with `TS2375`.
Its batch and completion branches reproduce decisions row 218's deferred TypeScript branch printer gap.
Row 266 already records the corresponding error-column case.
The failure packet retains the original source, emitted bytes and compiler diagnostics.
The successful packet uses existing checked source ascriptions on both producer values.
It makes no claim that arbitrary boolean branches now compile on the target.

Every module retains the expected reader refusal, `ReadRefusal.shape "definition"`, and lists its unreadable headers.
Existing Queue and Semaphore controls expect the same result.
The target packet establishes no read-back result or native Channel comparison.
Its finite executions establish no universal target simulation or asynchronous progress.

The `copiedMetadata` control retains another boundary.
An adapter can accept copied declaration columns that differ from the independently installed module at the same name.
The declaration theorem states only the supplied-column relationships.
The normal generated record supplies matching metadata and definitions; arbitrary copies require an additional module-relative check.

## Integration and next work

Integrate the implementation and receipt commits together.
The primary STATE and decisions register remain with the coordinator.
The authoring inventory records the compiler stages, their existing carriers and their evidence boundaries.

The shared `ifCase` printer is the next ergonomic repair under the existing ruling.
Its target syntax, prelude helper, reader and erasure laws must land together.
Stateful Channel filtering and early stopping then need repeated-pull, empty-batch, index and lifetime contracts.
Use the existing loops and module declarations before proposing another representation.
A broader execution claim must connect the current dispatch laws to stored-call execution and whole-stream cleanup.

## Retained whitespace

Both evidence folders retain the exact `compiled-inputs/control.ts` bytes from `harness/truth/control.ts`.
Each contains its source's terminal blank line.
The raw compiler diagnostic in `2026-10-09-channel-transforms-branch-refusal/failure.txt` also retains its terminal blank line.
Its digest is recorded in that folder's `boundary.json`.
The whitespace check permits only these three paths, verifies helper byte equality, and checks the diagnostic digest.
Every other changed file passes the ordinary whitespace check.
