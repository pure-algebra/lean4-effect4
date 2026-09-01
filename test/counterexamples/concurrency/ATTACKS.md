# Concurrency representative attacks

These attacks belong to the bounded Fiber/scheduler/interruption and binary
`raceFirst` representatives. Stable IDs live in `../REGISTER.md`; executable
Lean witnesses live beside their owning representative under
`Effect4Test/Counterexamples/Concurrency/`.

## E4-CONC-CE-001 — untaped race

- **BROKE:** scheduler execution is deterministic without recording a choice.
- **WITNESS:** one initial state admits a worker-first step and a waiter-first
  step with different traces.
- **CLASS:** semantic nondeterminism.
- **FIXED-BY:** `SchedulerDecision.schedule`, `DecisionTape`, and a determinism
  theorem quantified over the same tape.

## E4-CONC-CE-002 — interrupt versus complete

- **BROKE:** interruption and completion commute, or their ordering may be
  omitted from replay evidence.
- **WITNESS:** interrupt-first records delivery; completion-first records
  completion. In each exact two-decision tape the second action refuses
  without changing that stopped machine, so the traces and replay results
  differ even when the terminal alphabet has only one value.
- **CLASS:** ordering ambiguity.
- **FIXED-BY:** both actions are first-order decisions, their order is retained
  by tape and trace, and `interrupt_complete_order_distinct` supplies the
  admitted production witness.

## E4-CONC-CE-003 — masked interruption

- **BROKE:** an interrupt request always becomes terminal interruption
  immediately.
- **WITNESS:** a masked fiber stays runnable with a pending request; unmasking
  changes it to finalizing interruption and clears the pending bit.
- **CLASS:** lifecycle collapse.
- **FIXED-BY:** explicit mask and pending-request state plus deferral and
  delivery-on-unmask laws; completion is admitted only after the mask is
  restored with no pending interruption.

## E4-CONC-CE-004 — lost finalizer

- **BROKE:** a terminal error projection contains enough information to prove
  cleanup safety.
- **WITNESS:** two machines project to the same interrupted terminal, while one
  ran cleanup and the other did not.
- **CLASS:** information erasure.
- **FIXED-BY:** machine state and observable trace outside the terminal arm,
  with cleanup count and lifecycle constrained by public laws.

## E4-CONC-CE-005 — double join

- **BROKE:** joining consumes the stored terminal result or may rerun cleanup.
- **WITNESS:** two observations return the same success and leave the cleanup
  count at one.
- **CLASS:** non-idempotent observation.
- **FIXED-BY:** join is read-only over stored terminal state; cleanup is a
  separate at-most-once transition.

## E4-CONC-CE-006 — empty operational relations

- **BROKE:** determinism and safety implications establish an adequate
  operational semantics by themselves.
- **WITNESS:** `EmptyStep := False` and `EmptyRuns := False` satisfy arbitrary
  one-step, two-step, and run postconditions whenever every law is guarded by
  a `Step` or `Runs` premise.
- **CLASS:** specification vacuity.
- **FIXED-BY:** `Machine.WellFormed`, admitted-total `Step`, exhaustive
  `stepEval` equations and trace deltas, total finite replay defined recursively
  through `Step`, fixed projections, inhabited positive clauses for every
  decision constructor, exact nil-tape classification, and one nonempty finite
  finished run.

## E4-CONC-CE-007 — duplicate cleanup history

- **BROKE:** a cleanup counter bounded by one proves observable at-most-once
  cleanup.
- **WITNESS:** a raw machine satisfies the pre-repair lifecycle and count
  admission but records the same cleanup identity twice.
- **CLASS:** trace/state incoherence.
- **FIXED-BY:** `Event.cleanupId?`, `Machine.cleanupEventIds`, the exact
  transition equation, and finite admission fields requiring cleanup event
  identities to be unique, closed over fibers, and equivalent to count one;
  `cleanup_events_at_most_once` exposes the run-level guarantee.

## E4-CONC-CE-008 — erased winner choice

- **BROKE:** scheduler state and scheduler decisions determine the binary race
  winner without an explicit race choice.
- **WITNESS:** one tied machine paired with the left winner and the same
  machine paired with the right winner has identical scheduler projection but
  distinct winner projection.
- **CLASS:** nondeterminism erasure.
- **FIXED-BY:** `RaceDecision.selectWinner`, `RaceState.winner`, and distinct
  fixed tapes for the two tie resolutions.

## E4-CONC-CE-009 — first completion collapsed into first success

- **BROKE:** first-completion and first-success racing are interchangeable.
- **WITNESS:** on the two-entry probe `[failed, succeeded]`, first completion
  observes the failed entry while first success observes the later successful
  entry.
- **CLASS:** semantic conflation.
- **FIXED-BY:** the representative is explicitly binary first completion over
  opaque `τ`; it contains no success predicate.  First-success semantics waits
  for the owning result classification.

## E4-CONC-CE-010 — early return before loser cleanup

- **BROKE:** the selected winner's terminal observation is enough to settle a
  race.
- **WITNESS:** the winner is done with a retained terminal value while the
  loser is finalizing, has cleanup count zero, and has no cleanup event.
- **CLASS:** resource-lifecycle truncation.
- **FIXED-BY:** `RaceState.Settled` requires both contenders done with cleanup
  done, and the settlement laws recover count-one and cleanup-event evidence.

## E4-CONC-CE-011 — masked loser misclassified

- **BROKE:** a selected masked loser with a pending interruption is settled or
  refused when the finite tape is depleted.
- **WITNESS:** the existing scheduler accepts `exitMask loser`, advances the
  loser to interruption finalization, and leaves cleanup pending.
- **CLASS:** frontier/refusal collapse.
- **FIXED-BY:** `RaceReplayResult.frontier`, post-selection loser-only unmask
  and cleanup decisions, and the masked-loser empty-tape frontier theorem.

## Claim limit

All eleven witnesses are finite. They do not prove a production implementation,
an exhaustive scheduler model, fairness, liveness, or Effect compatibility.
