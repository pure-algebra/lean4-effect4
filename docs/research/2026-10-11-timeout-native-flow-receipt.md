# Timeout native value flow

The native evaluator now retains the ordered success classes through every allowed primitive case.
The original Timeout goals remain open.
The coordinator must import `Test.Dogfood.Proofs.HostTimeoutEvaluation` from `Test/All.lean`.

## Placement

Concept: host-session-protocol.
Requirement: R6.
Question: `Timeout.stale_never_applies`, clause four.
Proof role: transfer laws for the command assertion.
Evidence status: checked, without planned goals.
Scope: the actual native evaluator, conditional on the concrete source and ordered stack assertions.

`HostTimeoutFrames.pop_from` follows the actual hook, arm selection, skipped handler, and scratch masks.
`HostTimeoutFrames.get_cont` includes the deferred interrupt case.
`HostTimeoutFrames.resume_value` and `resume_cause` consume the selected frame and its remaining ordered stack.
`HostTimeoutFrames.step_frame` covers exactly the primitives delegated by the native dispatcher.

`HostTimeoutEvaluation.finalizer_or` follows the actual selected finalizer program and restoring continuation.
`race_settle` retains the accepted exit through native race cancellation.
`evaluate_native` covers every allowed native primitive and source interception.
Its result retains the expected frame class or finishes with an exit at that class.
Consumer: the reached command assertion and `Timeout.stale_never_applies` clause four.

## Representation

`StackAt` inspects the existing `List NCode`; it introduces no stored program representation.
Saved source finalizers have names `.fin point`.
This restriction excludes the stateful scoped-exit callback from the concrete Timeout relation.
Source suspensions have names `.body point`.
Native race and countdown parks have separate assertions and use the native dispatcher.

A later generic extraction must reuse `Contracts.FramePath` for the shared path carrier.
The current predicates remain specific to Timeout.

## Landing

Base: `23928207`.
The coordinator's observation reader is already present through local commit `4c86c7fd`.

Changed files:

- `Test/Dogfood/Proofs/HostTimeoutFlow.lean`.
- `Test/Dogfood/Proofs/HostTimeoutNative.lean`.
- `Test/Dogfood/Proofs/HostTimeoutFrames.lean`.
- `Test/Dogfood/Proofs/HostTimeoutEvaluation.lean`.
- `docs/research/2026-10-10-goals-packet/codex/TimeoutFlowAudit.lean`.
- This receipt.

The existing unrelated `RaceFirst.lean` fix stays out of the commit.
The owner's untracked `KernelRfl.lean` stays out of the commit.

## Verification

Command: `LEAN_NUM_THREADS=3 lake build Test.Dogfood.Proofs.HostTimeoutEvaluation`.
Result: success, 1065 jobs.

Command: `LEAN_NUM_THREADS=3 lake env lean docs/research/2026-10-10-goals-packet/codex/TimeoutFlowAudit.lean`.
Axiom output: 650 declarations within `[propext, Quot.sound]`.
The audit reports zero planned goals and zero declarations modulo planned goals.

The slice changes only proof assertions and proof bodies.
It introduces no runtime, compiler, source program, or host reader change.
No outside implementation comparison runs in this slice.
No finite execution establishes these universal transfer laws.

## Remaining obligations

The command assertion must correlate each live resume token with its pending frame's incoming success class.
It must retain that correlation through dispatcher snapshots, race callbacks, accepted exits, and posted resumes.
It must retain the applied-body prefix through actual reply application and reached history.
The final root exit must then feed `HostAppliedObservation.applied_body_seen`.

The count and cleanup claims still need their heap assertions.
The retry claim still needs returned-form provenance and the four-attempt bound.
These proofs establish neither progress nor finalizer execution.
They establish no host admission or outside implementation equivalence.
