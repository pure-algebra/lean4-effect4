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

## Actual fork and contextual command slice

`Atomic.Store.shop_stages` remains open with its original statement.
The actual root, daemon and active command history join remains the next consumer.

The base is `ec4fb9adb`; the proof heads are `17908e822` and `faa652b25`.
`JointCommands` keeps strict application assertions in one contextual premise and postcondition.
It instantiates the existing `GhostCommands.step` with a trivial auxiliary frame assertion.
It assumes actual application transitions and establishes no application history by itself.

`RootGraph.fork_parent`, `fork_child` and `fork_rows` join the actual allocated handle, child source role and older rows.
`RootGraph.native_exit` proves the actual root terminal dispatcher result.
`DaemonGraph.terminal_frame`, `timer_edge` and `action_frame` retain actual terminal, cancellation and administrative frames.
`StageGraph.native_rows` retains exact nonacting rows and their published exits through a request native step.
`StageWorld.final_exit_future` retains certified published outcomes when another fiber advances the world.
These helpers serve store-typing R4 through `Atomic.Store.shop_stages`.
They prove neither progress nor a host observation claim.

The daemon annotation drops its unused arbitrary suspension constructor.
Actual source suspensions still enter through the existing source-point and loop constructors.
The endpoint and the machine remain unchanged.

Changed paths are the shared `AnswerFlowJointCommands.lean` leaf and eleven Atomic leaves in `faa652b25`.
All commands run through `/Users/pooks/Dev/lean4-effect4/scratch/lean-slot.sh`.

- `lake build Test.Dogfood.Scenario.Atomic.RootSpawn Test.Dogfood.Scenario.Atomic.DaemonReturn Test.Dogfood.Scenario.Atomic.StageRows Effect4.Laws.Machine.AnswerFlowJointCommands` succeeds, 1292 jobs.
- `lake env lean scratch/audit-active-native.lean` audits twelve modules.
- The audit reports 420 declarations within `[propext, Quot.sound]`, zero planned goals and zero modulo goals.
- `git diff --check` succeeds.

The next proof joins remaining native park and store results with active machine, queue and detached-task assertions.
The checked allocation attachment then carries those actual assertions through control histories.
No bounded or host-only evidence replaces that open producer.

## Actual root and active machine assertions

The coordinator must retain the open history obligation.
`Atomic.Store.shop_stages` remains a planned goal with its original statement.

The prior native head is `9ebfe742d`.
The shared producer head is `0efa224a1`; the Atomic head is `020ec4e73`.
Skip `bc7b8ec80`: it copies the coordinator's checked parked-shape dependencies without changes.

`StatePreservation.primitive_at` generalizes the existing primitive proof over actual current-operation permissions.
Its former unconditional hook theorem remains a wrapper.
`NativeFrameRows.primitive_row_facts` retains whole stored rows through the existing primitive producer.
`NativeActionRows` supplies whole-row instances through its existing action proof.
The former frame assertions remain wrappers.
`PrimitiveCounter.evaluatePrim_nextId_of_actions` isolates allocation to the actual action branch.
The former nonaction counter theorem remains a wrapper.

The complete actual root native and charged-iteration producers retain one chosen world.
They join the heap, allocation counter, returned root and nonacting source roles.
The actual action producer also retains its exact store equality.
The daemon and request producers supply their actual stored-row and counter assertions.

`StageConfiguration.Configuration` joins heap, freshness, counter, live or dormant rows and publication metadata.
Recorded-cause metadata applies only to actual request identities.
No request exists before entry, and actual child births start without a recorded cause.
`Configuration.published` reads actual request exits.
`Configuration.stages` supplies the unchanged original stage observation from the complete machine assertion.

The checked edit producers cover actual observer admission, token cleanup and admitted interruption.
The checked disposition producer covers continuation, delivery, parking, completion, commands and stopped cuts.
A completed running row remains dormant until its actual finish command publishes the certified exit.
Live queued commands retain stronger actual source-role permission separately.
`StageStoreFields` proves actual root, daemon and request evaluation retains the deferred store.
It consumes `primitive_at` and the existing reference-kernel store equation.

These declarations serve store-typing R4 and reactive-scheduling R11 through `Atomic.Store.shop_stages`.
They establish no progress, lowered execution claim or host agreement.
The actual joint command and outside-decision producer remains open.
The next consumer joins `NativeCut`, command classes and the checked allocation attachment.

Changed paths are four shared modules in `0efa224a1` and twelve Atomic modules in `020ec4e73`.
All Lean commands use the serialized slot script.

- `lake build Test.Dogfood.Scenario.Atomic.StageStoreFields` succeeds, 1306 jobs.
- `lake env lean scratch/audit-atomic-root-rows.lean` succeeds.
- The audit reports 398 and 10 declarations within `[propext, Quot.sound]`.
- Both audit groups report zero planned goals and zero declarations modulo planned goals.

The pending initializer does not yet certify an empty deferred due list at entry.
Timeout owns that shared strengthening through the existing allocation producer.
The Atomic native join remains under construction and does not assume that missing fact.

## Actual native joins and waiting replies

The endpoint remains open after these commits.
The command and outside-decision producers remain its consumers.
The original `Atomic.Store.shop_stages` statement stays unchanged.

The actor join chooses one world for the heap, stored rows, returned actor and completion permission.
`StageNativeJoin.native_cut` supplies that join in `2ddb1fe7f`.
The task producer retains the returned dispatcher and stored dispatchers together in `475c982b6`.
`156c8a265` reconciles that producer with the coordinator's child bounds and actual source roles.
The coordinator already owns the dependency bytes in `d921f04ef`; integration skips that commit.

`5f917f7dd` generalizes the existing parked-head producer over its supplied predicate.
Its old interfaces remain instances of that producer.
`812b1dc4c` supplies the Atomic predicate and its actual matching-token resume consumer.
The predicate excludes action heads at actual parks.
The existing root action producer retains its real emitted edits and unchanged parked field.
Root replies retain their captured answer class and saved suffix.
Request void replies retain their exact current code and saved suffix.
The guard excludes inactive rows when the actual parked row supplies reply permission.

These declarations serve store-typing R4 and reactive-scheduling R11 through the same endpoint.
They establish neither progress nor host agreement.

- `lake build Effect4.Laws.Program.NativeActionRows Test.Dogfood.Scenario.Atomic.StageTasks Test.Dogfood.Scenario.Atomic.NativeEffects` succeeds, 1335 jobs.
- `lake env lean scratch/audit-row-reconcile.lean` reports 109 declarations within `[propext, Quot.sound]`.
- `lake build Test.Dogfood.Scenario.Atomic.StageWaits` succeeds, 1336 jobs.
- `lake env lean scratch/audit-stage-waits.lean` reports 288 declarations within `[propext, Quot.sound]` after constructive repairs.
- Both audits report zero planned goals and zero declarations modulo planned goals.

The audit initially rejects existential choice and classical contradiction in two new reply proofs.
The repaired proofs inspect the actual timer witness and eliminate the impossible request identity explicitly.
The rejected proofs do not enter the commits.

Timeout supplies the pending clean-record and deferred-store strengthening in `18dde0dc6`.
The coordinator integrates that packet as `8899de418`.
This receipt records that handoff; this worktree has not independently rebuilt that dependency packet.

The remaining command certificates retain actual finish-stack emptiness and the receiving endpoint of interruption waits.
The existing `Moves.FinishOrigin.stack` supplies finish-stack emptiness without another evaluator walk.
The charged loop join and terminal command assembly remain under check beyond the commits above.

## Actual reply admission and initialization entry

The original `Atomic.Store.shop_stages` remains open.
Its observation and `ControlHistory` hypotheses remain unchanged.

- `d7656e627` generalizes the existing primitive command and edit producer through `Moves.WordProfile`.
- `05115009e` joins native owners, charged iteration, actual receiving suffixes, and terminal cleanup.
- `b1923f42c` proves actual old-token continuation recovery through interruption, interference, and actor installation.
- `a421b0dad` excludes wake tasks and commands that the pending initializer never produces.
- `28349b132` retains reply admission only at actual matching tokens and admits ignored reference-read results at their receiving classes.
- `7200d3563` seeds the complete active configuration from actual initialization entry and classifies actual native messages.

The 1344-job native and terminal build passes.
The corresponding audit accepts 202 declarations without goals or proofs modulo goals.
The later 1357-job task admission build passes.
Its audit accepts 607 declarations at `[propext, Quot.sound]`, without goals or proofs modulo goals.
The source-entry and native-word audit accepts six declarations with the same result.
The pending command producer also compiles after the wake restriction.

The source-entry proof retains the actual root point and mask suffix.
It constructs no empty-stack assumption.
The task proof uses the existing dispatcher producer with a supplied assertion.
It adds no evaluator or scheduler induction.

The remaining endpoint work joins actual settlement, command permissions, detached tasks, and outside controls.
`ControlHistory` excludes external answer decisions.
The interpreter's clock producer supplies a successful unit reply directly.
The earlier timer-origin concern therefore adds no premise to this endpoint.

## Actual native settlement and waiting-command join

The original `Atomic.Store.shop_stages` goal remains open.
This slice retains the actual native result's completion stack and root receiving suffix.
The same chosen world retains the configuration through addressed messages.
The existing message fold also retains every waiting command's actual reader.
Matching-token reply admission and stored tasks survive actual interruption.

Placement: store-typing R4 and reactive-scheduling R11.
Consumer: the actual native P/Q/R producer for `Atomic.Store.shop_stages`.
Reach: the existing Atomic source roles, admitted native messages and actual actor installation.
This slice establishes no progress or host-answer admission.

Verification:
- `lean-slot.sh lake build Test.Dogfood.Scenario.Atomic.StageMessages Test.Dogfood.Scenario.Atomic.StageQueueUpdate Test.Dogfood.Scenario.Atomic.StageTaskAdmission Test.Dogfood.Scenario.Atomic.StageActivation` succeeds: 1363 jobs.
- `lean-slot.sh lake env lean scratch/audit-stage-messages.lean` audits 195 declarations within `[propext, Quot.sound]`.
- The audit reports zero planned goals and zero declarations modulo planned goals.

Remaining: native emitted/follow-up commands, detached snapshots, fixed commands and the control-history attachment.
The original endpoint statement stays unchanged.

## Actual native emitted commands and disposition

`StageNativeQueue.native_nested_queue` types the actual emitted command word at the chosen native world.
Its interruption waits use the actual root suffix or daemon frame.
The existing quiet primitive profile excludes request interruption waits.
`StageDisposition.NativeCut.settle_outcome_queue` types the actual scheduler follow-up.
It retains the same waiting readers through parked, deferred and stuck outcomes.
These declarations serve the preceding native P/Q/R consumer.

Verification:
- `lean-slot.sh lake build Test.Dogfood.Scenario.Atomic.StageNativeQueue` succeeds: 1362 jobs.
- `lean-slot.sh lake env lean scratch/audit-stage-nativequeue.lean` audits four declarations within `[propext, Quot.sound]`.
- The audit reports zero planned goals and zero declarations modulo planned goals.

The complete pending-suffix transport, detached-snapshot join and command-history instance remain open.
`Atomic.Store.shop_stages` remains unchanged and open.
