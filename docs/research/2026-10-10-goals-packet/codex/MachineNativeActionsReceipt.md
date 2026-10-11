# Native fiber-action custody

The original Workers release bound remains open. This slice closes every non-parallel native fiber-action case and its actual interpreter producer.

Base: c86c7c5f. Parent dependencies are CommandStacks, CommandStackSteps, CommandDebit and ObserverDebit. Their worktree copies remain uncommitted.

## Placement

1. Concept: scope-lifetime-finalization. These helpers serve R11 release custody.
2. Question: `Execution.history` supplies `Workers.Assertions.releases_step`. `NativeActionDebit.native_action` feeds its evaluator accounting.
3. Reach: every actual fiber action under source ownership, sequential source, distinct fiber and scope identities, fresh registration keys and the existing saved-frame assertion.
4. Limit: this slice proves no complete evaluator, command-shape or history closure. It changes no original scenario statement or reply admission.
5. Unlock: native evaluator assembly now consumes an action theorem whose interpreter producer discharges every numeric demand premise.

## Interface

`NativeActionDebit.action` checks all fiber-action constructors. The sequential-source premise excludes parallel cleanup through the existing `ActionAt` source witness.

`NativeActionDebit.native_action` consumes actual `withFiberOf` output and existing `FrameAt` ownership. It derives the clean residual stack and action reservation.

State-first scope close uses `ScopeTransfer.close`. Forks transfer into the new child, and races transfer into the existing entrant pool. Countdown, interruption and scope-link actions retain the off-owner bound.

The small `demand` projection reads the existing action alphabet. Proposed traversal exemption: `Effect4.Program.ReleaseCustody.NativeActionDebit.demand`, for this accounting projection.

## Evidence

`LEAN_NUM_THREADS=3 lake build Effect4.Laws.Program.ReleaseCustody.NativeActionDebit` passes, 552 jobs.

`LEAN_NUM_THREADS=3 lake env lean docs/research/2026-10-10-goals-packet/codex/MachineNativeActions.lean` passes.

The readers apply native action and actual scope-close accounting at `Api.Built` carriers.

The axiom audit checks 253 declarations within `[propext, Quot.sound]`, with zero planned goals and zero declarations modulo goals.

Open work: full primitive and native evaluation, command sequencing, and admitted-history funding. The retained parallel-close probe still bounds generic accounting. No behavior gate runs in this proof-only slice.
