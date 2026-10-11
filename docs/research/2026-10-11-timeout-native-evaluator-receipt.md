# Timeout native evaluator receipt

The original three Timeout goals remain open.
This slice closes every ordinary native source case, charged loop iteration and settling queue.
The actual command and decision history remains the next consumer.

## Placement

Concept: host-session-protocol.
Requirement: R6.
Claim: `Test.Dogfood.Scenario.Timeout.stale_never_applies`, clause four.
Evidence kind: universal Lean proofs.
Reach: actual Timeout native evaluation under the stated source, active fiber and live exit hypotheses.
Consumer: native loop and delivery commands, then `Run.Frame.HistoryOf`.
These safety assertions establish neither progress nor exact cleanup log correspondence.

`HostTimeoutLocalSteps.evaluate_native_state` covers all fifteen source heads and actual native interception.
Its synchronous cases consume the checked outer cell shapes.
Its finalizer cases retain the saved successful body through the unit cleanup program.
Its action cases include race creation, masks, race cancellation and observer cancellation.

`HostTimeoutIteration.iteration_state` covers deferred interruption, operation charging and the actual forced-yield wrapper.
`HostTimeoutSettle.settle_state` consumes the returned fiber assertion and the entire installed command queue.
Finished iterations supply body exits and scratch mask stacks through the existing `IterKind` assertion.

Nested overwrite commands read the installed returned fiber.
`EvaluationAt` therefore indexes their assertion by `result.machine.update result.fiber`.
This matters when race cancellation leaves the old stored frame unchanged before installation.
Scheduler flag changes use the coordinator's existing `StackLinks` carrier.
No runtime field, source statement, admission rule or original theorem premise changes.

## Verification

Base: `cfac990e`.
Head: the commit containing this receipt.

Command: `LEAN_NUM_THREADS=3 lake build Test.Dogfood.Proofs.HostTimeoutSettle`.
Result: success, 1094 jobs.

Command: `LEAN_NUM_THREADS=3 lake env lean docs/research/2026-10-10-goals-packet/codex/TimeoutFlowAudit.lean`.
Result: 1140 declarations within `[propext, Quot.sound]`.
The audit reports zero planned goals and zero declarations modulo planned goals.
`git diff --check` passes for the landed paths.

Changed files:

- `Test/Dogfood/Proofs/HostTimeoutLocalSteps.lean`.
- `Test/Dogfood/Proofs/HostTimeoutIteration.lean`.
- `Test/Dogfood/Proofs/HostTimeoutSettle.lean`.
- `docs/research/2026-10-10-goals-packet/codex/TimeoutFlowAudit.lean`.
- This receipt.

Coordinator dependency hashes remain in `docs/research/2026-10-11-timeout-command-custody-receipt.md`.
Those dependency copies remain excluded.
The unrelated RaceFirst edit and KernelRfl helper remain excluded.
No push runs.

This slice changes proofs only.
The coordinator owns the outside implementation gates.
No outside implementation comparison runs in this slice.

## Remaining obligations

The full command assertion must cover registrationDone, launch, cancellation and countdown observer work.
The command, task and decision closure must reach actual accepted native history.
The original success clause then consumes root membership and `HostAppliedObservation.applied_body_seen`.
The approved retry goal and cleanup goal remain open.
