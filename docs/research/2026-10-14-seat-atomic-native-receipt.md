# Atomic source and initialization receipt

The stage history endpoint remains open.
Do not treat these local producers as `Atomic.Store.shop_stages`.
The endpoint keeps its universal statement.
The coordinator owns the finalizer endpoint and the shared command connection.

## Placement

Concept: store-typing R4 and scope-lifetime-finalization R11.
Claim: `atomic`, through `Atomic.Store.shop_stages` in `Test/Dogfood/Scenario/Atomic/Store.lean`.
Role: local initialization, source entry, answer classes and native head producers.
Observation: the existing `Store.StagesFit` relation over the actual machine observation.
Reach: the admitted shop, actual source points, native interpreter views and arbitrary compilation fuel.
These proofs establish neither progress nor host equivalence.

## Checked slices

Proof head: `24fa40a03`.
The worktree starts from `5f07927c8`.
The coordinator receives application commits separately from dependency snapshots.

| Commit | Result |
| --- | --- |
| `e775164d6` | Actual charged initialization preserves the exact heap or exposes its real application entry. |
| `475b9c4f5` | Actual decision and deposit source sites supply stage-sensitive operation heads. |
| `24fa40a03` | Actual request body callbacks retain their owner and connect yield, decision, branch, deposit and return. |

`AllocationIteration.pending_iteration_or_entry` retains the actual charged or injected source input.
Its entry certificate retains the actual source point and the older saved suffix.
`Atomic.Initialization.pending_stages` proves the original stage observation for exact pending initialization cuts.

`StageRequest.body_code` proves the complete actual request body annotation.
Its source point retains every metadata field.
Its continuations refresh only the completed-fiber view through the existing interpreter.
The decision and deposit use distinct answer classes.
A returned admission cannot fund another deposit after the stage advances.

`StageGraph.code_other` transports a nonacting request through another request's stage change.
Its premises retain that owner's stage and cleanup flag.
The saved callback certificate reads the incoming answer class in the later world.
The graph reuses the existing contextual finalizer family.
It adds no compiler, callback or command traversal.

## Verification

All Lean commands use `/Users/pooks/Dev/lean4-effect4/scratch/lean-slot.sh`.

| Command | Result |
| --- | --- |
| `lake build Test.Dogfood.Scenario.Atomic.Initialization` | Passed, 1244 jobs. |
| `lake env lean scratch/AllocationIterationAudit.lean` | 343 declarations; zero planned goals and zero declarations modulo goals. |
| `lake build Test.Dogfood.Scenario.Atomic.StageGraph` | Passed, 1184 jobs. |
| `lake env lean scratch/AtomicStageGraphAudit.lean` | 293 declarations; zero planned goals and zero declarations modulo goals. |
| `lake build Test.Dogfood.Scenario.Atomic.StageCleanup` | Passed, 1188 jobs. |
| `lake env lean scratch/AtomicRequestAudit.lean` | 380 declarations; zero planned goals and zero declarations modulo goals. |

Every recorded audit stays within `propext` and `Quot.sound`.
These results describe the committed slices above.
They do not certify later uncommitted edits.
No outside implementation gate applies to these proof-only changes.

## Open producers

The actual finalizer source callbacks and protected request entry compile at `6b9af73f2`.
The root and daemon source roles remain separate work.
The numeric heap relation must advance with the same stage world as each actual write.
The application must retain completed request exits and positive cleanup observations.
The shared coupled command connection must consume these producers and the exact initialization entry.
Only that history producer can discharge `shop_stages`.

The coordinator owns `FinalizerRun.once_placed_outside_census`.
Its universal weighted command balance remains the missing producer.
No concrete counterexample justified changing that statement.

## Actual initializer suffix

Commit `b977193b0` removes an initializer bind annotation with no actual source constructor.
Before entry, saved edges carry mask restorations or the actual synthetic yield wrapper.
The root answer class excludes the wrapper input class.
`AllocationIteration.EntryAt.mask_suffix` therefore reads only masks from the real entry stack.
`AllocationEntrySuffix.MaskSuffix.path` transfers that stack into any supplied model's mask edges.
The proof does not assume an empty stack.

Command: `lean-slot.sh lake build Test.Dogfood.Scenario.Atomic.Initialization`.
Result: success, 1247 jobs.
Command: `lean-slot.sh lake env lean scratch/AllocationSuffixAudit.lean`.
Result: 294 declarations within `[propext, Quot.sound]`, zero goals, zero declarations modulo goals.

Commit `8951ee9a2` retains the actual pending iteration's unchanged fiber counter.
Commit `6b9af73f2` connects the actual protected request source and cleanup callbacks.
The request-source build succeeds with 1191 jobs.
Its audit covers 137 declarations within the whitelist, with zero goals and modulo declarations.

These are local producers on the path to `shop_stages`.
The history endpoint remains open.

## Scheduler pauses during requests

Commit `5f442e9f6` carries the actual scheduler yield wrapper through the request model.
The ignored pause answer retains the owner's stage and cleanup flag.
Its failure class also retains the incoming failure class.
The existing constant-continuation theorem supplies the saved edge.
The proof adds no callback or stack-pop traversal.

Command: `lean-slot.sh lake build Test.Dogfood.Scenario.Atomic.StageEntry`.
Result: success, 1191 jobs.
Command: `lean-slot.sh lake env lean scratch/AtomicPauseAudit.lean`.
Result: 416 declarations within `[propext, Quot.sound]`, zero goals and zero modulo declarations.

The numeric heap transition relation, root and daemon roles, and coupled history assembly remain open.

## Actual pending driver and observed cleanup causes

`shop_stages` remains open at this landing.
The three commits supply checked producers and cause classes for its actual history connection.
They do not establish the active Atomic command invariant.

Base: `f846c59ae`.
Heads: `8544d49c9`, `9c3c991bd`, and `96b0f699f`.

`FramePathOrder` reads an actual member from an increasing saved path.
Timeout consumes its endpoint bound for authored finalizer custody.

`AllocationCommandStep.coupled_decision_of_entry` supplies the common initialization attachment.
It consumes the existing active command producer and actual entry contracts.
Its pending side retains exact heap contents, fiber counters, frame classes, parked demands, and actual dispatcher replies.
The machine, command queue, and detached snapshot share one returned proof world.
The existing coupled scheduler supplies the history construction.
The proof adds no scheduler or evaluator recursion.

The original `StagesFit` cleanup implication concerns the exact downstream singleton exit.
`NeedsCleanup` identifies nonempty causes containing only typed failure reasons.
`MarkedCause` retains an actual non-fail reason through combination and annotation.
Such a cause excludes `NeedsCleanup`, including after a finalizer failure merge.
The finalizer's successful cleanup still supplies the real positive cleanup entry before restoration.
The original `shop_stages` statement remains unchanged.
Paused values retain their frozen stage fields.
Paused failures skip the saved constant and retain only the incoming failure class.
`FailureControls` checks the distinction at a deposited, uncleaned world.

Changed files:

- `Test/Dogfood/Scenario/Atomic/FailureControls.lean`
- `Test/Dogfood/Scenario/Atomic/FailureWitness.lean`
- `Test/Dogfood/Scenario/Atomic/StageCleanup.lean`
- `Test/Dogfood/Scenario/Atomic/StageFinalizer.lean`
- `Test/Dogfood/Scenario/Atomic/StageGraph.lean`
- `Test/Dogfood/Scenario/Atomic/StageObservation.lean`
- `Test/Dogfood/Scenario/Atomic/StageWorld.lean`
- `src/Effect4/Laws/Contracts/FramePathOrder.lean`
- `src/Effect4/Laws/Machine/DispatcherPredicate.lean`
- `src/Effect4/Laws/Program/AnswerSlots/AllocationAdministrativeFields.lean`
- `src/Effect4/Laws/Program/AnswerSlots/AllocationCommandStep.lean`
- `src/Effect4/Laws/Program/AnswerSlots/AllocationConfiguration.lean`
- `src/Effect4/Laws/Program/AnswerSlots/AllocationDecisionEdits.lean`
- `src/Effect4/Laws/Program/AnswerSlots/AllocationDriver.lean`
- `src/Effect4/Laws/Program/AnswerSlots/AllocationFields.lean`
- `src/Effect4/Laws/Program/AnswerSlots/AllocationFixed.lean`
- `src/Effect4/Laws/Program/AnswerSlots/AllocationInterruption.lean`
- `src/Effect4/Laws/Program/AnswerSlots/AllocationNativeCut.lean`
- `src/Effect4/Laws/Program/AnswerSlots/AllocationQueue.lean`
- `src/Effect4/Laws/Program/AnswerSlots/AllocationSettlement.lean`
- `src/Effect4/Laws/Program/AnswerSlots/AllocationTasks.lean`
- `src/Effect4/Laws/Program/NativeConfiguration.lean`
- `src/Effect4/Laws/Program/PrimitiveDispatcher.lean`

Verification commands use `/Users/pooks/Dev/lean4-effect4/scratch/lean-slot.sh`.

- `lake build Effect4.Laws.Program.AnswerSlots.AllocationCommandStep Test.Dogfood.Scenario.Atomic.StageRoles Test.Dogfood.Scenario.Atomic.StageObservation Test.Dogfood.Scenario.Atomic.FailureControls` succeeds: 1301 jobs.
- `lake env lean scratch/audit-allocation-driver.lean` audits 291 declarations within `[propext, Quot.sound]`.
- `lake env lean scratch/audit-atomic-failure.lean` audits 367 declarations within the same whitelist.
- Both audits report zero planned goals and zero declarations modulo planned goals.

Logs: `scratch/build-allocation-driver7.log` and `scratch/audit-allocation-combined.log`.
No outside-host agreement or progress claim follows.

Remaining consumers: the active root, daemon, and request native producer; its joint command invariant; actual entry activation; and the original observation readout.
The separate Finalizer endpoint remains the coordinator's work.

## Actual terminal return slice

`Atomic.Store.shop_stages` remains open and keeps its original statement.
The next consumer joins native actor results with the active command and history invariant.

- Shared native connectors: `653e189c9`.
- Root, daemon and request interruption roles: `058b5bece`.
- Shared completed-return permissions: `e71339659`.
- Actual request terminal dispatch: `3fdf6563d`.
- Dependency synchronization only: `4699c565f`; the coordinator already owns these exact dependencies.

`External.Native.step_frame_running` keeps the exact outer answer class for ordinary native heads.
`External.Native.finalizer_dispatch` joins actual installation and contextual ordinary return under one result predicate.
`Contextual.resume_value_finished` and `Contextual.resume_cause_finished` retain the actual completed exit permission.
`StageGraph.native_exit` consumes these proofs for the actual request finalizer dispatcher.
All serve store-typing R4 and scope-lifetime-finalization R11 through `Atomic.Store.shop_stages`.
They establish local native transitions, not an active history invariant or progress.

Commands use `/Users/pooks/Dev/lean4-effect4/scratch/lean-slot.sh`.

- `lake build Test.Dogfood.Scenario.Atomic.StageRoles`: build succeeds, 1279 jobs.
- `lake build Test.Dogfood.Scenario.Atomic.StageReturn`: build succeeds, 1199 jobs.
- `lake env lean scratch/audit-atomic-active.lean`: 398 declarations within `[propext, Quot.sound]`; zero goals and zero modulo goals.
- `lake env lean scratch/audit-atomic-return.lean`: 402 declarations within `[propext, Quot.sound]`; zero goals and zero modulo goals.

The last audit includes `DaemonIteration`, completing the earlier interruption slice's module list.
No host behaviour or bounded execution claim follows from these proof checks.
