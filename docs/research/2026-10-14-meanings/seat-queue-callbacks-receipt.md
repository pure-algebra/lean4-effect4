# Queue callback proof slice

Both public job goals remain open. This slice proves local callback and operation facts, not their history producer.

The action helpers require the coordinator's checked `ActionProgramsWith` and `scopedFork` dependency.
The coordinator owns that dependency commit and the root imports.

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

The checked action dependency uses borrowed coordinator snapshots of `NativeActionScope`, `AnswerSlots.Actions` and `AnswerSlots.TypedActions`.
Those files are not part of these commits.
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
