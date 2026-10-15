# Queue callback proof slice

Both public job goals remain open. This slice proves local callback and operation facts, not their history producer.

The action dependency is coordinator commit `88e21d671`, imported by explicit code paths as `ac2cff7af`.
Its files match the borrowed snapshots used by the checks.
The coordinator owns the root imports.

## Revisions

- Base: `471298e58`.
- Shared arm dependency: `a832f0f2e`, applied locally as `7f8d76e78`.
- Classified cause adapter: `59067b91d`.
- Source suspension contract: `a25283b40`.
- Concrete queue callback consumers: `b86b33bde`.
- Parent and child action helpers: `ce624f78e`.

## Placement

Proof role: steps of `QueueWorkers.Assertions.jobs_step` and `QueueWorkers.Assertions.rest_step`.
Concept: translation-simulation R10 and store-typing R4.
Shared callback and action facts also serve scope-lifetime-finalization R11.
Evidence status: kernel-checked local proofs.
Reach: actual source callbacks, native allocation and assignment cuts, and the strict notification source fragment.

`QueueWorkersJobBinding.callback` retains the job appended by the actual successful worker continuation.
`QueueWorkersJobBinding.assignment_native` consumes that slot through the actual assignment source census.
Its consumer needs no separate job-membership premise.

`QueueWorkersJobBinding.request_callback` retains the actual published key and its selected logical request.
`QueueWorkersJobBinding.request_bound` preserves that key across appended hint and retry bindings.

`QueueWorkersNotificationFlow.stable_laws` consumes the existing generated predicate family and shared actual arm producer.
Its source predicate excludes cause handlers, exit frames and finalizers.
`ClassifiedInputEmbedding.family_over` uses the actual successful input for readiness.
Its cause obligations consume `ClassifiedCauseTransfer`, rather than deriving readiness from every cause.
The earlier `ClassifiedEmbedding` interface remains an instance.

`CodeClosure.suspend_body_at` owns the existing direct-fragment source-body branch proof.
`Qualified.suspend_at` consumes its constructor contract.
Generator, invocation and parameter branches remain outside that fragment.

`NativeActionFlow.with_fiber_parent_path` checks the acting parent's mask body separately from child programs.
`NativeActionRows.with_fiber_frame_rows_at` seeds actual new children under a supplied identity lower bound.
The earlier action interfaces remain instances.

## Changed files

Shared files:

```text
src/Effect4/Laws/Machine/AnswerFlowClassifiedEmbedding.lean
src/Effect4/Laws/Program/CodeClosure/Suspension.lean
src/Effect4/Laws/Program/CodeClosure/Qualified/Callbacks.lean
src/Effect4/Laws/Program/NativeActionFlow.lean
src/Effect4/Laws/Program/NativeActionRows.lean
```

Application files:

```text
Test/Dogfood/Proofs/QueueWorkersCustody.lean
Test/Dogfood/Proofs/QueueWorkersCustodySource.lean
Test/Dogfood/Proofs/QueueWorkersCustodyTransfers.lean
Test/Dogfood/Proofs/QueueWorkersCustodyAssignment.lean
Test/Dogfood/Proofs/QueueWorkersCustodyAssignmentSource.lean
Test/Dogfood/Proofs/QueueWorkersCustodyRetry.lean
Test/Dogfood/Proofs/QueueWorkersCustodySegments.lean
Test/Dogfood/Proofs/QueueWorkersCustodyNotificationSource.lean
Test/Dogfood/Proofs/QueueWorkersCustodySelections.lean
Test/Dogfood/Proofs/QueueWorkersCustodyCredits.lean
Test/Dogfood/Proofs/QueueWorkersRequestKeys.lean
Test/Dogfood/Proofs/QueueWorkersCustodyFlow.lean
Test/Dogfood/Proofs/QueueWorkersNotificationFlow.lean
Test/Dogfood/Proofs/QueueWorkersNotificationCallbacks.lean
Test/Dogfood/Proofs/QueueWorkersNotificationFamily.lean
Test/Dogfood/Proofs/QueueWorkersJobBinding.lean
```

The two imports below reach all sixteen application files:

```lean
import Test.Dogfood.Proofs.QueueWorkersJobBinding
import Test.Dogfood.Proofs.QueueWorkersNotificationFamily
```

The coordinator adds these imports to `Test/All.lean`.
Unused potential probes and the separate retry-source probe are not committed.

## Verification

The shared slot script serializes every Lean command.
The checked worktree is `/private/tmp/meanings-queue-current`.

```sh
/Users/pooks/Dev/lean4-effect4/scratch/lean-slot.sh bash -c 'lake build Test.Dogfood.Proofs.QueueWorkersJobBinding Test.Dogfood.Proofs.QueueWorkersNotificationFamily Effect4.Laws.Program.NativeActionRows Effect4.Laws.Program.AnswerSlots.InitializedActionFacts ProofGraph.AxiomAudit && lake env lean QueueFlowAudit.lean'
```

Result: build passed, 1344 jobs.
Log: `/private/tmp/queue-current-family-actions4-audit.log`.
The focused audits report 403, 75 and 8 declarations within `[propext, Quot.sound]`.
Each reports zero declarations modulo planned goals and zero planned goals.

```sh
/Users/pooks/Dev/lean4-effect4/scratch/lean-slot.sh lake env lean QueueFlowAudit.lean
```

The expanded audit names every application module listed above.
Result: 787 declarations within `[propext, Quot.sound]`, zero declarations modulo planned goals, zero planned goals.
Log: `/private/tmp/queue-current-all-owned-audit.log`.
The audit also repeats the three focused checks.

The checked action dependency contains `NativeActionScope`, `AnswerSlots.Actions` and `AnswerSlots.TypedActions`.
Commit `ac2cff7af` records their exact checked coordinator contents.
The earlier proof commits do not edit those dependency files.
No machine, program syntax, value syntax or host implementation changes occur.
No outside-implementation behaviour gate is reached by this proof-only slice.

## Remaining work

The concrete worker and feeder source graph must supply the current phase and actual classified callback inputs.
The native producer must preserve that graph and the conserving ledger together.
The shared initialization and coupled driver must carry that producer through actual histories.
These obligations remain before `jobs_step` can be replaced.

`rest_step` additionally needs actual offer-acceptance and withdrawal authority.
A spent feeder credit alone does not prove that its queued offer has completed.
The live-member and idle-member observations still need their source and host-profile connection.
These are safety observations, not progress claims.

## Concrete binding continuation

The endpoint obligations remain open.
These commits connect actual source captures and native results; they do not supply the complete active history invariant.

| Commit | Checked consumer |
| --- | --- |
| `2f224e613` | Ordinary post-assignment and connection regions exclude queue and assignment writes. |
| `17a9e7701` | The actual worker job binder captures its classified answer and funds its exact assignment write. |
| `e366ffca6` | The worker's uniform saved binder and the native take share the returned custody world. |
| `cd13057b8` | Both workers retain their actual request keys and separately allocated wake keys through their take heads. |
| `c8377b965` | Both notification prefixes retain the actual take tuple before the option branch. |

`QueueWorkersJobGraph.assignment_input` reads the actual assignment head.
`QueueWorkersJobGraph.assignment_step` spends its protected occurrence and retains conservation.
`QueueWorkersTakeBinding.take_step` reads the actual take head and returns its classified tuple in the same world.
`QueueWorkersAllocationBinding.hint_callback` retains the immutable request key when it appends the actual hint key.
The hint input requires a waiting request; a broader pending class would also admit a request that already holds a job.

`QueueWorkersJobFamilies.take_notifications` consumes both actual `postAll` source regions.
Its remaining premise is the local producer for the actual option branch.
`AnswerFlow.indexed_family` joins existing member families by mapping their returned paths into one stack relation.
It performs no callback, compiler or machine traversal.

The native model names requests by their deferred indices.
The custody proof uses separate logical tokens.
This keeps `Table.handle` injective without extending a finite native-key map.

```sh
/Users/pooks/Dev/lean4-effect4/scratch/lean-slot.sh lake build Test.Dogfood.Proofs.QueueWorkersReadonlySource
/Users/pooks/Dev/lean4-effect4/scratch/lean-slot.sh lake env lean QueueReadonlyAudit.lean
/Users/pooks/Dev/lean4-effect4/scratch/lean-slot.sh lake build Test.Dogfood.Proofs.QueueWorkersJobGraph
/Users/pooks/Dev/lean4-effect4/scratch/lean-slot.sh lake env lean QueueJobGraphAudit.lean
/Users/pooks/Dev/lean4-effect4/scratch/lean-slot.sh lake build Test.Dogfood.Proofs.QueueWorkersJobFamily
/Users/pooks/Dev/lean4-effect4/scratch/lean-slot.sh lake env lean QueueJobCutsAudit.lean
/Users/pooks/Dev/lean4-effect4/scratch/lean-slot.sh lake build Test.Dogfood.Proofs.QueueWorkersTakeBinding Test.Dogfood.Proofs.QueueWorkersAllocationBinding Test.Dogfood.Proofs.QueueWorkersJobFamily
/Users/pooks/Dev/lean4-effect4/scratch/lean-slot.sh lake env lean QueueNativeCutsAudit.lean
/Users/pooks/Dev/lean4-effect4/scratch/lean-slot.sh lake build Test.Dogfood.Proofs.QueueWorkersJobFamilies Test.Dogfood.Proofs.QueueWorkersTakeBinding
/Users/pooks/Dev/lean4-effect4/scratch/lean-slot.sh lake env lean QueueNotificationJoinAudit.lean
```

The corresponding narrow builds report 1332, 1387, 1388, 1391 and 1400 successful jobs.
The audits report 32, 47, 10, 209 and 138 declarations within `[propext, Quot.sound]`.
Every listed audit reports zero declarations modulo planned goals and zero planned goals.
The logs are `/private/tmp/queue-readonly-source2-build.log`, `/private/tmp/queue-readonly-audit.log`,
`/private/tmp/queue-job-graph6-build.log`, `/private/tmp/queue-job-graph-audit.log`,
`/private/tmp/queue-job-family2-build.log`, `/private/tmp/queue-job-cuts-audit.log`,
`/private/tmp/queue-allocation-take2-build.log`, `/private/tmp/queue-native-cuts-audit.log`,
`/private/tmp/queue-take-notifications2-build.log` and `/private/tmp/queue-notification-join-audit.log`.

The active history still needs the waiting cleanup, retry completion, feeder offer entry, offer withdrawal and root terminal custody producers.
Full reply admission also needs the count-cell invariant and delayed-reference reply permission in the same active invariant.
The resting-state endpoint additionally needs actual offer acceptance and its live-member observations.

The successful option branch also checks at every fuel.
`QueueWorkersTakeOptionBranch.body` reads the captured tuple after both notification answers.
Its remaining premise supplies only the actual waiting body, for the same still-waiting token.
It does not assume conservation or the endpoint observation.

```sh
/Users/pooks/Dev/lean4-effect4/scratch/lean-slot.sh lake build Test.Dogfood.Proofs.QueueWorkersTakeOptionBranch
/Users/pooks/Dev/lean4-effect4/scratch/lean-slot.sh lake env lean QueueOptionAudit.lean
```

Result: 1402 successful build jobs.
The audit reports 179 declarations within `[propext, Quot.sound]`, zero modulo planned goals and zero planned goals.
Logs: `/private/tmp/queue-take-option-branch2-build.log` and `/private/tmp/queue-option-audit.log`.

## Actual worker take continuation

The queue history producer remains open.
Neither `Assertions.jobs_step` nor `Assertions.rest_step` changes in this slice.
The base is `2a630ab46`.
The preceding cleanup commit is `5b8920a95`.

`QueueWorkersTakeFlow.attempt` consumes the actual take term and its captured request and hint.
It proves both notification continuations, the option selection, the authored wait, its protected cleanup, and its retry result.
The proof reads the actual classified callback answer.
It assumes no waiting-body or option-branch conclusion.
The saved finalizer keeps the actual captured exit.
The binder requires an input class belonging to its worker.
`take_notifications_future` retains the actual future-world witness.
The earlier notification API is its wrapper.

The narrow command is `lean-slot.sh lake build Test.Dogfood.Proofs.QueueWorkersTakeFlow`.
It passes with 1413 jobs.
The output is `/private/tmp/queue-take-flow-build2.log`.
The audit command is `lean-slot.sh lake env lean /private/tmp/queue-take-flow-audit.lean`.
It checks 262 declarations within `[propext, Quot.sound]`, with zero modulo declarations and zero planned goals.
The output is `/private/tmp/queue-take-flow-audit.log`.
These checks establish the local take producer, not the actual history invariant.

The remaining consumers are the worker retry hook, the outer worker, the feeder, and root publication.
The active command producer must carry the queue table together with custody, actual frames, and queued permissions.
The rest proof also needs accepted-offer custody and actual waiting failure origin.
No machine, program syntax, or external reply profile changes.

## Actual classified retry and worker return

The queue history producer remains open.
Both endpoint goals remain unchanged.
The preceding commit is `cb457c00f` on base `2a630ab46`.

`QueueWorkersRetryFlow.loop_entry` starts the actual source loop with its classified empty cursor.
`QueueWorkersRetryFamily.hooks` consumes the actual returned option through the existing `TypedRecursiveHooks` producer.
Its saved family reuses `recursive_family_of_typed`.
An empty cursor enters the complete waiting body.
A successful cursor returns its own held occurrence.
`QueueWorkersRetryReturn.some_body` unwraps that occurrence at the worker's job input class.
`QueueWorkersTakeSelection.return_body` generalizes the existing selection proof; `some_body` remains its original wrapper.
`QueueWorkersCountSource.counter_term` identifies every counter successor update.
Its heap and history consumers remain open.

The narrow command is:

```sh
/Users/pooks/Dev/lean4-effect4/scratch/lean-slot.sh lake build Test.Dogfood.Proofs.QueueWorkersRetryFamily Test.Dogfood.Proofs.QueueWorkersRetryReturn Test.Dogfood.Proofs.QueueWorkersCountSource
```

It passes with 1419 jobs.
The output is `/private/tmp/queue-retry-consumers-build3.log`.
The audit command is `lean-slot.sh lake env lean /private/tmp/queue-retry-audit.lean`.
It checks 233 declarations within `[propext, Quot.sound]`, with zero modulo declarations and zero planned goals.
The output is `/private/tmp/queue-retry-audit.log`.

The active history still needs the complete worker and feeder bindings, table custody, live-row transport, delayed-reply permission, and terminal publication.
The rest proof retains its original bound.
Funded histories exclude command-budget cuts; the automatic-yield segment bound remains a separate obligation.
No actual counterexample to that bound is established here.

## Actual request allocation through worker result

The queue history producer and both endpoint goals remain open.
The preceding commit is `a19a13819`.
`QueueWorkersRequestFlow.allocate_body` connects the actual request allocator to the complete retry and result binder.
The callback consumes the allocator's actual classified key.
`QueueWorkersRetryReturn.option_body` covers both actual option classes.
The empty option executes its authored failure and grants no successful job.
The successful option returns the same held occurrence.

The narrow command is `lean-slot.sh lake build Test.Dogfood.Proofs.QueueWorkersRequestFlow`.
It passes with 1418 jobs.
The outputs are `/private/tmp/queue-request-flow-build2.log` and `/private/tmp/queue-request-flow-build3.log`.
The audit command is `lean-slot.sh lake env lean /private/tmp/queue-request-audit.lean`.
It checks 26 declarations within `[propext, Quot.sound]`, with zero modulo declarations and zero planned goals.
The output is `/private/tmp/queue-request-audit.log`.
The worker mask, outer worker, feeder and whole-history consumers remain open.

## Actual worker take and assignment binding

Both queue endpoint goals remain open.
The preceding commit is `69dc28301`.
`QueueWorkersTakeWrapper.body` connects the actual mask getter to request allocation and the complete take continuation.
Its input class reads `Val.savedMask flag`, the native getter's actual value.
`getter_path` reuses `SourceScope.masked_path` and the existing saved-mask proof.
`QueueWorkersWorkerBinding.body` connects that take result to its worker's actual assignment and existing readonly tail.
The job binder consumes its actual classified Nat answer.
It grants no job permission to an unrelated successful value.
This source chain does not establish whole-history custody or waiting failure origin.

The narrow command is:

```sh
/Users/pooks/Dev/lean4-effect4/scratch/lean-slot.sh lake build Test.Dogfood.Proofs.QueueWorkersWorkerBinding Test.Dogfood.Proofs.QueueWorkersRetryFamily
```

It passes with 1422 jobs.
The output is `/private/tmp/queue-worker-binding-build4.log`.
The audit command is `lean-slot.sh lake env lean /private/tmp/queue-worker-binding-audit.lean`.
It checks 331 declarations within `[propext, Quot.sound]`, with zero modulo declarations and zero planned goals.
The output is `/private/tmp/queue-worker-binding-audit.log`.
The feeder, root terminal publication and actual coupled command history remain open.

## Independent actual counter history

Both queue endpoint goals remain open.
The preceding commit is `b546e9440`.
`QueueWorkersCountCell.history` proves that reference four is absent or Nat-valued in every admitted history of the actual crew.
It assumes neither `Jobs` nor `Rest`.
`source_keeps` uses the existing source census and actual reference footprint.
`current_keeps` covers the real initializer allocation and the stable native writer.
The history consumer reuses `Initialized.decision_lift` and `RefInvariant.history`.
It adds no command or scheduler traversal.

The common driver rebuild exposes two predicate-inference failures after the action contract consolidation.
The coordinator authorizes explicit source predicates at the existing `ActionProgramsAt.mono` calls in `InitializedNative` and `InitializedAdmin`.
Both repaired calls retain their original statements and implementations.
No other identical call remains in those direct dependencies.

The narrow command is `lean-slot.sh lake build Test.Dogfood.Proofs.QueueWorkersCountHistory`.
It passes with 1395 jobs.
The output is `/private/tmp/queue-count-history-build3.log`.
The audit command is `lean-slot.sh lake env lean /private/tmp/queue-count-history-audit.lean`.
It checks 55 declarations within `[propext, Quot.sound]`, with zero modulo declarations and zero planned goals.
The output is `/private/tmp/queue-count-history-audit.log`.
The remaining delayed-reply consumer still needs the actual admitted reply and its saved input class.

## Actual feeder commit and publication

Both queue endpoint goals remain open.
The base is `db598aa50`.
`QueueWorkersOfferNative.source_step` connects the actual captured offer term to its renewed queue table and spent request class.
The same returned world retains conservation and counted custody.
`allocation_step` publishes the real deferred key for the existing holding request.
`getter_path` retains the actual saved flag and unpublished request suffix.
The unpublished input requires an absent key; a later callback cannot publish that request again.
`entry_input` connects this input to the already selected offer-entry observation.
The active command and history consumers remain unfinished.

`QueueWorkersWorkerBinding.body` now consumes `QueueWorkersJobGraph.assignment_body` directly.
The duplicate assignment proof is removed.
The narrow command is `lean-slot.sh lake build Test.Dogfood.Proofs.QueueWorkersOfferNative Test.Dogfood.Proofs.QueueWorkersWorkerBinding`.
It passes with 1423 jobs.
The output is `/private/tmp/queue-offer-allocation-build.log`.
The audit command is `lean-slot.sh lake env lean /private/tmp/queue-offer-allocation-audit.lean`.
It checks 285 declarations within `[propext, Quot.sound]`, with zero modulo declarations and zero planned goals.
The output is `/private/tmp/queue-offer-allocation-audit.log`.
The new test consumer is `Test.Dogfood.Proofs.QueueWorkersOfferNative`.

## Actual compiler bodies and shared native callback builders

Both queue endpoint goals remain open.
The base is `edbfb5a40`.
The coordinator delegates this shared refactor for actual worker and feeder binders.
`ActualIndexedCompileContract.bind` supplies the actual first child's compiled-body equality.
`actual_indexed_compile_closure` owns the existing compiler induction.
The original `IndexedCompileContract` retains its exact fields, field order and public theorem.
Its adapter ignores the additional equality.

`Qualified.contA_with` owns the existing value-callback case analysis.
Its supplied native success builders cannot introduce an authored `cont` callback.
The supplied source leaves retain compiler-produced continuations.
`Qualified.contA_at` remains the original qualified-fold instance.
`AuthoredBinders.compile`, `resolve`, `embed` and `value_callback` consume both shared interfaces.
Their correlated fold retains the real source binder and its actual compiled first child.
The callback theorem retains the direct-source qualified-name premise.
It does not admit excluded generator names or establish a command history.

The narrow command is `lean-slot.sh lake build Effect4.Laws.Program.CodeClosure.AuthoredBinders Effect4.Laws.Program.CodeClosure.Callbacks Effect4.Laws.Program.AnswerSlots.TypedCompile`.
It passes with 412 jobs.
The output is `/private/tmp/queue-actual-compiler-build.log`.
The audit command is `lean-slot.sh lake env lean /private/tmp/queue-actual-compiler-audit.lean`.
It checks 326 declarations within `[propext, Quot.sound]`, with zero modulo declarations and zero planned goals.
The output is `/private/tmp/queue-actual-compiler-audit.log`.
The coordinator must add the library-root import for `Effect4.Laws.Program.CodeClosure.AuthoredBinders`.

## Actual feeder chain

The job and rest endpoints remain open.
Commit `b09683d8a` proves the feeder's actual allocation, hint, commit and tail chain.
The hint uses the source's Boolean deferred type.
The entry getter retains its saved interruptibility value.
The worker constructor consumes the actual compiled take body.
The mixed saved family reuses the existing family and embedding producers.

Concept: store-typing R4 and translation-simulation R10.
Consumer: `QueueWorkers.Assertions.jobs_step`, followed by `rest_step`.
Reach: local source and callback closure at actual captured inputs.
This slice establishes no complete run invariant.

Verification:

- `lean-slot.sh lake build Test.Dogfood.Proofs.QueueWorkersOfferWrapper Test.Dogfood.Proofs.QueueWorkersJobSourceFamilies Test.Dogfood.Proofs.QueueWorkersWorkerBinding` passes 1429 jobs.
- `/private/tmp/queue-offer-wrapper-build8.log` records the build.
- `lean-slot.sh lake env lean /private/tmp/queue-offer-chain-audit.lean` passes.
- The audit checks 260 declarations with `propext` and `Quot.sound` only.
- The audited declarations depend on no planned goal.
- `/private/tmp/queue-offer-chain-audit.log` records the audit.

The remaining producer must join actual source control, job custody and the physical queue table.
The two endpoint statements remain unchanged by this slice.
