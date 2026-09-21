# Foundations contract preflight: the proposed interrupt fix is refuted

The 2026-09-21 adversarial input found a real catch-skipping issue but did not resolve it.
The production stack judgment is unchanged. The brief's stop condition applies to the
dependent slice 4 residual/control contract and slice 5 stack theorem. This amendment records
checked counterexamples and reopens the design; it does not silently replace a frozen law.

## Exact failures

`E4-SCHED-CE-006` starts with an interruptible flag of false, a recorded interrupt,
`deferredInterrupt = false`, and `[restoreMask true, resume onFailure recovery]`. The input
correlation holds vacuously. Actual `popR` restores the mask, skips recovery, and returns the
original Nat failure. `ExitFits` at the output error `never` is false, as is the proposed
exception `(entry.interruptible = true ∧ entry.interruptedCause.isSome = true)`. Any proposed
`StrongExit` retaining `CompletionOk` inherits this contradiction. The record also meets
`InterruptProvenance`; `reviewed_catch_skip` proves the proposed guard-miss-only premise
and `reviewed_catch_run` supplies the ordinary pure handler result. These are exact universal equations at any interpreter and world,
not a replay-reachability proof.

`E4-SCHED-CE-007` sets `deferredInterrupt = true` on an interruptible pending-interrupt frame.
The input correlation again holds. Actual `deliverR` does not replace this failing exit:
its interception is success-only, and the failure path clears the flag before stack popping.
The resulting outcome is still the original typed failure.

`E4-TYPED-CE-003` instantiates the review's StrongCause and StrongExit formulas with an
arbitrary stronger value predicate. `badShapeExit` is admitted for every such predicate:
its reason is Die, so no Fail-payload condition applies. Preserve ordinary defect behavior
and prove the absence of badShape production from admitted source/control separately.

Checked files:
- `Test/Counterexamples/Machine/Semantics/InterruptDelivery.lean`
- `Test/Counterexamples/Machine/Semantics/StrongExitDefect.lean`

The narrow builds pass at the existing `[propext, Quot.sound]` ceiling. The receipt retains
commands and logs. Earlier elaboration failures were repaired and are not proof evidence.

## Old contract, proposed change, and remaining decision

Production `FrameAccepts.resume.skip` demands output exit typing for every failure as well
as guard misses. The input proposal removes the all-failures disjunct. That makes the caught
Nat-to-never example admissible, but requires a replacement delivery theorem. The proposed
replacement theorem is false for the state above. No replacement has been ratified here.

A usable replacement must track actual mask changes and original-exit propagation through
all visited frames, including finalizers that can still run while interrupted. Classifying
only the final result as aborted cannot by itself justify those intermediate inputs. The
source-admission domain must still include ordinary error-removing catches. If a proposed
reachable invariant rules out the state, its initialization and preservation must be proved.
The audit's claimed source trace has not been reproduced as a decision tape by these tests.

The certificate-indexed generic protocol, C2 indexed heap preservation, and C3/C4 abstract
representation composition are independent of this choice. They may land as separate checked
foundations. They do not complete M3a, the answer manifest, source admission, or its settling
program cases. Those remain explicitly pending; no replacement runtime or second stored IR
is introduced.

## Other corrections to the input report

The answer manifest checker and concrete TypedProg were planned, not implemented, at the
review base. Inventory coverage alone would not prove delivery adequacy. `RProgram` is a
reference proof carrier with continuations; canonical stored syntax is the separate `Eff`
sort. `denoteR` takes a root, current term and Point and its implementation uses fuel. Raw
matching asynchronous replies still need the prefix-sensitive AnswersOk restriction. Arena
and Projects laws are conditional interfaces, not verified OCaml, C or TypeScript instances.
