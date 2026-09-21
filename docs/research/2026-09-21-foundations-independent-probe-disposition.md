# Independent foundations: disposition of the additional probe

The independent D12 and C2–C4 contracts stand without a scheduler amendment. The supplied
runtime patch and replacement stack theorem remain proposals. Six retained calls into the
pinned rc.112 implementation expose a missing distinction in their justification: entering
the run loop, evaluating a failure, and selecting a continuation are different boundaries.

The input is retained in `2026-09-21-foundations-independent-input.md`. The command is:

```sh
bun docs/research/2026-09-21-foundations-slice4-evidence/VendorInterruptProbe.ts
```

`vendor-probe.json` records all six passing controls. They call the actual pinned
`FiberImpl.getCont`, `FiberImpl.runLoop` and exit evaluators from manually constructed
fiber states. They are finite host probes, not a source-admission or reachability proof.
`vendor-sha256.json` pins the two implementation files used by the probe.

## Deferred interruption needs a named comparison boundary

`internal/effect.ts:684–686` returns `deferredInterruptCont` for either continuation kind.
That does not establish that every caller invokes it. The failure evaluator in
`internal/core.ts:539–546` repeatedly discards continuations while the fiber is interruptible
and has a recorded interruption. The direct failure fixture therefore yields the original
failure, while the direct success fixture invokes the deferred continuation and returns
the interrupt cause. This matches the distinction exposed by `E4-SCHED-CE-007`; that
counterexample alone does not establish a vendor mismatch or authorize a runtime repair.

The outer `runLoop`, at `internal/effect.ts:639–642`, can replace its input with the recorded
interrupt *before* the primitive evaluator runs. The sixth control checks this different
boundary. Comparing `deliverR` to that outer loop requires an explicit simulation boundary
and an invariant connecting states at that boundary. Neither choosing `getCont` alone nor
choosing the outer loop alone supplies that missing connection.

The proposed `deferredInterrupt && interruptible` guard also differs from raw `getCont` on
the manually constructed masked/deferred fixture. Whether such a state is admitted at the
chosen boundary must be established by initialization and preservation, not assumed away.
The present landing changes no evaluator or interruption rule.

## Potential restoration is not evidence of an actual preempted walk

The proposed `WalkPreempted` searches for an unmasking frame anywhere in the stack. In the
fifth control, a masked catch is selected before a later restoration is visited. The catch
runs and the restoration remains on the stack, even though the proposed predicate is true.
It is therefore an overapproximation of potential unmasking, not a witness that this walk
was preempted. The fourth control checks the opposite order: a visited restoration enables
catch skipping, as in `E4-SCHED-CE-006`.

A final-result disjunction still does not type inputs to intermediate finalizers or the
residual code returned by a walk that selects a continuation. The replacement contract must
describe visited transitions and the remaining stack, with correlations for the delivered
exit and recorded interruption. A source-reachable restriction is usable only with its own
proofs. This is a limit of the proposed contract, not an impossibility claim about all
static type systems.

## Defect safety needs an observation and an admission domain

The separation of exit typing from malformed-control production is appropriate, but the
input's displayed formula is not a Lean statement over the current carriers:

- `TypedProg` is the proposed predicate on reference `RProgram`; `replayR` takes `NativeEff`
  (`Laws/Program/RuntimeR.lean:51`).
- `Run.observe` takes a public `Run` and returns an `Observation` record
  (`Run.lean:243`); a reference `RState` and `badShapeExit : ExitV` cannot fill those slots.
- `reasonAdmits` admits Die reasons independently of the typed-error column. Source
  admission, typed answers and initial validity must be stated separately; exit typing
  alone does not exclude a host-supplied defect with the same value as `badShapeExit`.
- The theorem must distinguish absence of malformed-control production from absence of a
  particular observable defect value. Fuel exhaustion and an unanswered decision remain
  live frontiers, as required by the machine contract.

No replacement safety theorem is frozen here. The existing strong-exit counterexample is
retained, and the dependent admission/delivery design remains open in the slice receipt.

## What the independent proofs provide to implementation

D12 chooses one ghost certificate per operation and retains it through every future-world
answer. `Typed.mono` still requires transport of each certified precondition and of the
result predicate. It does not make arbitrary store validity monotone. The unit-certificate
adapter recovers the former typing rules on exactly the same `Program` carrier.

C2 connects an actual `refStep` kernel row to predicates indexed by heap position. Its
premises require the selected kernel to retain that cell's predicate; its conclusion
retains every cell, the answer predicate, heap length and all other lookups. Allocation is
separate. This can be combined with slice 3's world transport without replacing the
actual-transition validity obligation by world order alone.

The brief's allocation walkthrough previously used C2 to justify `refMake`. The retained
`allocation_is_separate` control checks `refMake.refKernel = none`, so that application
cannot meet C2's row premise. The walkthrough now uses the existing `refMake_extension` and
table insertion laws for allocation, and C2 for the following non-allocating `refGet` row.

C3 composes projections with both the concrete and intermediate validity predicates. C4
induces a forward relation that retains concrete validity, the same answer and the
concrete-none to model-none observation. The signatures are generic in carriers, operations
and answers. They assume no OCaml representation. Effectful or relational target steps,
changed key/value carriers, initialization and whole-machine lifting require their own
named connections; the deterministic `Option` interface does not silently cover them.

The target and evidence matrix remains the one in the
[monotonicity and refinement review, §3](2026-09-21-foundations-monotonicity-and-refinement-review.md#3-store-semantics-to-abstract-representations-to-target-implementations).
The new mathematical laws are proved conditional theorems. The six runtime controls are
finite host evidence. No OCaml container, Lean-to-C compilation route, new C heap, JavaScript
container or compiler artifact gains an implementation grade from this landing.
