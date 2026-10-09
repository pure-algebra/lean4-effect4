# Waiting cancellation controls

These finite host controls test cancellation settlement with another waiter and with already accepted Queue messages.
They add no production declaration or general theorem.

## Run

From the worktree root, run:

```sh
sh docs/research/2026-10-08-module-waiting-probe/run.sh
```

The runner verifies selected input fingerprints, checks the probe with pinned tsgo 7, and compares runtime output with retained bytes.
`inputs.json` names the measured runtime, compiler, Bun version, selected input count, and equal source pairs.
The selected hashes do not cover the entire imported package graph.
The compiler uses strict checking and skips dependency declaration interiors.

## Controls

| Control | Positive observation | Wrong prediction |
| --- | --- | --- |
| Refund serves a successor | B acquires before canceled A's outer exit cleanup; no permit remains free | No refund leaves B waiting; posted delivery finishes A first; credit-only cleanup leaves one free permit |
| Reservation ownership settles | B's return restores one permit; the original holder's return restores capacity | Refund and successor acquisition cannot each claim the same free permit |
| Queue accepted prefix stays | Cancellation removes pending 30 and retains accepted 20 beside original 10 | Rollback removes 20; unconditional completion adds 30 |

The second row supplies a positive settlement control.
The wrong predictions in the first and third rows are executable checks.
`observations.json` retains each measured comparison and the control counts.

No sleeps, timing thresholds, or scheduler replacement enter these controls.
The traces observe the default scheduler's selected runs.
They establish no fairness, general cancellation-after-selection law, or whole-module simulation.
The batch Queue control concerns latest (Effect 4.0.1) and its richer batch profile.
Current production Queue wrappers expose only the single-message offer.

The [semantics note](../2026-10-08-module-waiting-semantics.md) maps the result to the existing interfaces and proof graph.
