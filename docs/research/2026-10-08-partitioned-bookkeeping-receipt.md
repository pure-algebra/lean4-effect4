# PartitionedSemaphore bookkeeping integration

The scalar bookkeeping slice is ready for integration; the PartitionedSemaphore waiting wrapper is still open.
The registered theorem covers source readings of initialization, availability, attempted acquisition, and reservation arithmetic.
The reservation connection requires insufficient availability and a request within capacity.

## Base and ownership

Base: `979be0ad8b86f356dc83aa7f6bdab46228684a32`.
Branch: `codex/partitioned-bookkeeping`.
Worktree: `/Users/pooks/.codex/worktrees/module-semaphore/lean4-effect4`.
Implementation and verification head: `98e5d6f8443e2d8d1b07db232cf5af2aa708118d`.
This receipt follows that head without changing its implementation or checks.
Read the exact changed paths with `git diff --name-only 979be0ad8b86f356dc83aa7f6bdab46228684a32 98e5d6f8443e2d8d1b07db232cf5af2aa708118d`.

The implementation lands here as `4aeda4f2`, from the independent worktree's `93f3fd43`.
Its verification receipt lands as `271f980a`, from `a6d3199e`.
Claude owns program splice and edit-session work in the primary checkout.
The observed primary head advances to `cb1478a4` during this slice.
The cloud organization seat owns the broader analysis design.
This slice changes neither seat's files in the primary checkout and sends neither seat a message.

## Production changes

The [slice plan](2026-10-08-partitioned-bookkeeping-plan.md) places the obligations before implementation.
The [core receipt](2026-10-08-partitioned-core-receipt.md) records the six implementation and law files.

`Model.Counts` and its four transitions import no Step or machine implementation.
`Cell` derives the type and carrier connection from that structure.
`Data` declares named inputs and stored steps.
`Steps` supplies four public source builders through `Effect4.Library`.
The law modules connect those builders to the independent model through the existing shared Step laws.

The integration changes the library and law imports, the semantics registry, and the architecture placement.
It registers three new batteries in `Test/All.lean`.
The public program battery imports only `Effect4.Author`, `Effect4.Library`, and `Effect4.Run`.
The emission battery checks the existing Forms-to-Eff-to-checked-module route.
The [focused harness](../../harness/partitioned-bookkeeping/README.md) compiles and executes the exact emitted declarations.

The source profile contains natural capacities and requests, including zero.
These scalar fields are a subrecord for later state.
They do not replace waiter identities, live partition order, a persistent cursor, or unsettled reservations.

## Proof placement and use

| Question | Declaration and consumer | Reach | Remaining boundary |
| --- | --- | --- | --- |
| `partitioned-semaphore-bookkeeping`, `translation-simulation`, role simulation, R10 | `Effect4.PartitionedSemaphore.Model.bookkeeping_agrees`, `src/Effect4/Laws/Library/PartitionedSemaphore/Steps.lean`; concrete readers in the new bookkeeping battery | Four source readings from input images; reservation keeps both branch premises | No registration, cancellation, delivery, wrapper, schedule, or host result |
| Independent value equations, helpers of that claim | `Model.initial_eval`, `available_eval`, `tryTake_eval`, and `reserve_eval`, law `Data.lean`; each feeds its matching reading law | Existing carrier interpretation agrees with independent scalar arithmetic | No allocation or whole-state invariant |
| `step-language-typed`, `store-typing`, role compatibility, R4 | `initial_types`, `available_types`, `tryTake_types`, and `reserve_types`, law `Steps.lean`; concrete typing readers and later operation callers | Input typing and the native atom signature give each term's type | Type membership is no branch premise, handle allocation, or codec admission |
| Checked emission, R8 | `Api.emitModule` and `Api.readModule`, exercised by `Test.Program.PartitionedSemaphoreFaces` | Each finite caller reads back to its checked program | Rendering and host execution require separate evidence |

The semantics registry adds the scalar claim and keeps `partitioned-semaphore-expansion-agrees` as an explicit proposed R10 open part.
The latter needs registration, partial reservations, ordered selection, contextual identities, inline delivery, cancellation settlement, and protected acquisition.
No planned goal or general theorem states that whole-module connection in this slice.

The four typing connectors remain useful even when no registered claim reaches them.
The concrete battery applies each one, and later operation typing consumes their conclusions.
The load report counts direct theorem citations; it is not a deletion rule or a behavior result.
The earlier plan/report measurement mismatch remains outside this module slice.

## Checked behavior and countercontrols

The finite machine callers allocate actual Refs and observe replies and all three scalar fields after updates.
They cover zero capacity, zero requests, capacity acquisition, insufficient availability, excessive requests, repeated acquisition, and accumulated reservations.
The public checker refuses a wrong request type and a wrong cell type.
A reservation call outside its source branch can type.
The strengthened control starts with four available permits and requests two.
Misusing reservation clears all four, although the unmet need is zero.
The valid acquisition leaves two available.
This observation explains why the source connection retains its branch premise.

The emitted packet checks thirteen callers and one deliberately wrong update.
The wrong update has the correct success reply but leaves five permits available after requesting five.
Both programs type-check; their stored-state observations differ.
The packet keeps emitted files, compiler inputs, input hashes, version pins, and actual observations.

The compiler is tsgo 7.0.0-dev.20260629.1.
The runtime is Bun 1.4.2 with Effect 4.0.1.
These checks compare emitted scalar callers with their expected Lean-machine observations.
They do not compare a native PartitionedSemaphore wrapper or establish a general TypeScript execution theorem.

## Independent probes and shared semantics

The waiting seat commits its packet as `f2a3b871`, followed by the graph-name correction `c0660aed`.
The source is `git:c0660aed:docs/research/2026-10-08-module-waiting-semantics.md`.
The root reads the retained source and independently replays its runner.
The retained output matches: eleven positive observations and five rejected wrong predictions.

Cancellation of a partially reserved request feeds its refund through allocation.
A successor's client runs before the canceled request's outer exit cleanup, in the retained Effect 4.0.1 execution.
Queue cancellation instead retains the accepted prefix of a partially blocked batch offer.
It discards only the unaccepted suffix.
These finite observations distinguish provisional reservations from committed work.

Keep the existing `Waiter.attempt`, `Waiter.withdraw`, `waitRetryAt`, `waitAnswer`, and `protectedBy` interfaces.
Their common work is registration, notification, and the restored interruption boundary.
Each module still owns cancellation settlement and the meaning and delivery of a notification.
A common waiter record must not impose one resource refund rule.
A future `waitAnswerAt` needs the decided-answer contract before use in protected PartitionedSemaphore acquisition.

The waiting seat independently reads the six production files at `a6d3199e`.
It finds no concrete defect in the source arithmetic, branch premises, model separation, or shared proof connections.
That independent review is source-based; the root supplies the compiled and execution checks.

## Authoring and live-view findings

The module author supplies one scalar structure and four named steps.
Deriving supplies type metadata and carrier conversion; shared laws supply reading and typing transport.
Three remaining author burdens deserve shared machinery:

- Carrier proof inputs still use positional tuples even though the step's input context already has names.
- Deriving in a `module` file needs a local string-definition import for the field-order proof.
- Concrete modules repeat the value-equation, source-reading, and typing connections around the same shared Step laws.

Keep independent model equations as author obligations.
A future input packer should read the existing named context and reject unknown, duplicate, missing, or wrongly typed inputs.
A deriving repair should keep implementation imports inside the macro's owned machinery.
Neither improvement needs a new stored program representation.

The rendering scout commits its note as `9fbff639`.
The source is `git:9fbff639:docs/research/2026-10-08-live-rendering-scout.md`.
The root independently replays its thirteen finite address and hole-table controls.
The proposed shared functions are inspection of an exact snapshot, checked edit application, and production of display data.
They keep source identity, application and hole tables, addressed context, and applicable evidence together.

An address can name different nodes after an edit, even when both nodes have the same type.
An omitted program requires its retained hole table for the next check.
A subtree edit can shift later display rows and global geometry.
A table-splice law therefore does not establish subtree-only repaint.

The existing execution functionality uses `Run` and checked `Runner` commands.
The proposed `Live` spelling remains an unchecked interface sketch at the reviewed base.
Stored-syntax display paths and expanded-program call paths need an explicit connection.
The rendering note records those boundaries for the organization work and changes no production rendering code.

## Verification record

The root runs the following checks in the isolated integration worktree.

| Command | Result |
| --- | --- |
| `LEAN_NUM_THREADS=3 lake build Effect4.Laws.Library.PartitionedSemaphore.Steps Test.Program.PartitionedSemaphoreFaces` | Pass, 897 jobs after correcting the test's tuple constructor |
| `LEAN_NUM_THREADS=3 lake build Test.Program.PartitionedSemaphoreBookkeeping Effect4.Laws ProofGraph.Registry Tools.ArchitectureRoles Tools.LoadPaths ProofGraph.Plan` | Pass, 1146 jobs |
| `python3 harness/partitioned-bookkeeping/run.py --skip-build --install /Users/pooks/Dev/lean4-effect4/ts/release/node_modules --out docs/research/2026-10-08-partitioned-bookkeeping-evidence` | Pass, thirteen positive callers and the detected wrong update |
| Scoped compiled audit in `2026-10-08-partitioned-bookkeeping-audit.lean` | The initial and final passes check 108 declarations, allowed axioms, core/law separation, the exact claim pointer, and no open claim goal |

The semantics report's declared roots also build as a focused producer prerequisite: 988 jobs.
The report generator rebuild after the open-part entry passes: 27 jobs.
The full command list is the one in the Makefile's semantics producer, without its broad `build` prerequisite.
No `lake build Test`, whole-library axiom gate, full sweep, merge into the primary branch, or push runs.

The first caller draft names a tuple constructor in the wrong namespace; the corrected store representation passes.
That draft failure is no semantic detector result.
A Python bytecode-cache write is refused by the worktree sandbox; Python source parsing and the actual runner later pass.
A draft text-only import scan mistakes documentation for imports; the final audit uses Lean's import parser and compiled module graph.
A brief LoadPaths rebuild overlaps report generation after a mistimed poll; both finish without production source overlap.
The final verification runs serially within the worktree.


## Final verification

The [final evidence](2026-10-08-partitioned-bookkeeping-evidence-final/receipt.json) records the strengthened control's source bytes.
Earlier execution evidence remains unchanged in the worktree.
The final source, emitted files, and compiler inputs match all 44 hashes in the execution receipt.

| Command | Result |
| --- | --- |
| `LEAN_NUM_THREADS=3 lake build Test.Program.PartitionedSemaphoreFaces Test.Program.PartitionedSemaphoreBookkeeping Tools.LoadPaths` | Pass, 958 jobs after correcting a comment delimiter |
| `python3 harness/partitioned-bookkeeping/run.py --skip-build --install /Users/pooks/Dev/lean4-effect4/ts/release/node_modules --out docs/research/2026-10-08-partitioned-bookkeeping-evidence-final` | Pass, thirteen positive callers and the detected wrong update |
| `LEAN_NUM_THREADS=3 lake env lean -DwarningAsError=true docs/research/2026-10-08-partitioned-bookkeeping-audit.lean` | Pass; output retained as `2026-10-08-partitioned-bookkeeping-evidence-final/scoped-audit.txt` |
| `LEAN_NUM_THREADS=3 lake build semantics-report` | Pass, 27 jobs after correcting the observation description |
| `LEAN_NUM_THREADS=3 lake exe semantics-report .lake/gen/partitioned-bookkeeping-report` | Pass; its Markdown replaces `generated/semantics.md` byte for byte |

The audit checks all 108 compiled declarations against `[propext, Quot.sound]`.
It checks actual core and law import closures and parses battery registrations with Lean's import parser.
The semantics registry points to the exact aggregate, whose proof rests on no open goal.

The load report measures thirteen theorems, one root, and nine load-bearing theorems in this slice.
It reports eight local, twenty-four tree, ten core, and zero instance edges: a 75% reuse ratio.
The four typing connectors have no registered-root path in that report.
Anonymous concrete readers still compile against each connector; later operation typing also needs those connectors.
That report's “unconsumed” classification is not an unused-code finding.

The [extracted claim](2026-10-08-partitioned-bookkeeping-evidence-final/claim-status.json) retains the generated statement, status, axioms, and input hashes.
The report marks the scalar claim proved with no open proof dependency.
The generated statement retains both reservation premises.
The full module connection remains a proposed R10 open part.
The generated diff adds only this slice's placement, its open part, and disambiguated labels for an existing same-named theorem.

The independent waiting and rendering packets remain on their own branches.
This integration references their evidence without merging their research files or changing their production trees.
