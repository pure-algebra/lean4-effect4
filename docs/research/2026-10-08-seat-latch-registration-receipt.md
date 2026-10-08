# Latch registration and cleanup specification

The independent model now records registration and cleanup before their generated steps land.
The implementation keeps these definitions separate from `Step`.

## Base and files

The module-authoring base is `88a660b3`.
The immediate implementation base is `f08fd378`.
The head is the commit carrying this receipt.

- `src/Effect4/Laws/Modules/Latch/Model.lean`
- `Test/Program/LatchSteps.lean`
- this receipt

## Behavior and placement

`Latch.Model.awaitLatch` records the callback registration in rc.112's `class Latch`.
`Latch.Model.withdraw` records that registration's cleanup.
The source is `vendor/effect-4.0.0-rc.112/src/internal/effect.ts`, lines 5624–5639.
The plan is `docs/research/2026-10-08-seat-module-gaps-plan.md`.
The consumer is the pending extension of `latch-steps-agree`, under `translation-simulation`, R10.

An open latch answers immediately and changes no waiter.
A closed latch appends the registration to its waiters.
Cleanup removes the first matching waiter.
Only when no waiter matches does cleanup inspect the scheduled batch.
Removing the final pending registration keeps the scheduled flush.
A detached batch no longer belongs to this state.

The controls include duplicate identities to distinguish first removal from filtering every match.
The wrapper must establish fresh registration identities on its reachable states.
No premise silently removes the duplicate-identity controls from this pure specification.

## Verification

```sh
LEAN_NUM_THREADS=3 lake build Test.Program.LatchSteps
LEAN_NUM_THREADS=3 lake env lean /private/tmp/module-latch-await-axioms.lean
```

The final build passes with no warnings.
The initial battery build failed on a multiline record expression.
The corrected expression passes the same build.
Both new definitions have no axiom dependencies.

The battery checks immediate answers, closed enrolment, cleanup order, duplicate identities, and detached batches with reentrant enrolment.
These are finite model evaluations.
They establish no generated-step agreement, callback execution, scheduler result, or native compatibility claim.
