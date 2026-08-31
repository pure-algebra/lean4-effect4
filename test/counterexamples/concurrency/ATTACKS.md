# Fiber representative attacks

These attacks belong to the bounded Fiber/scheduler/interruption
representative. Stable IDs live in `../REGISTER.md`; executable Lean witnesses
live in
`Effect4Test/Counterexamples/Concurrency/FiberRepresentative.lean`.

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

## Claim limit

All six witnesses are finite. They do not prove a production implementation,
an exhaustive scheduler model, fairness, liveness, or Effect compatibility.
