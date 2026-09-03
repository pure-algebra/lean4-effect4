# Contract: checked region stack safety

Every admitted region run avoids the existing malformed-state outcome
`RunResult.stuck`, for every fuel and every service result. Failure,
unanswered decisions, fuel exhaustion and tape refusal remain valid outcomes.
This independent D2 packet is frozen from
`5b29edb4b33ebf7e7afb28f110dc7119e0ed1fef` on 2026-09-03.

The existing classifier at `Effect4/Semantics/Runs.lean:44-46` returns true
only for `.frontier (.stuck _)`; the other endpoint forms return false.

## Ownership and exact public surface

Production owner: `Effect4/Semantics/RegionSafety.lean`, importing the existing
region runner and `Effect4.Semantics.RegionTotal` as needed. All three public
theorems live in `Effect4.Flow`. Their exact ascriptions are frozen in
`Effect4Test/Semantics/RegionSafetyContract.lean`.

| Public theorem | Required judgment |
| --- | --- |
| `runRegionsCause_checked_not_stuck` | For every type `Ty` with decidable equality, state type `σ`, alphabet, checked region flow, stateful region service, operation naming function, fuel, tape, input, initial log and state: the `RunResult` inside the complete `runRegionsCause` result has `.stuck = false`. |
| `runRegions_checked_not_stuck` | The same quantifiers and judgment for the existing wire projection `runRegions`. |
| `interpretRegionsWF_checked_not_stuck` | For every checked flow and the same stateful service, naming, tape, input, log and state: the result of `interpretRegions` applied to `denoteRegionsWF` has `.stuck = false`. No fuel argument or budget premise. |

These are derived theorems over the existing carriers. No new canonical
carrier, wrapper runner, replacement classifier or public invariant is
required. Helpers and an inductive stack invariant may remain private. The
mandatory assurance route is the existing region/semantics route in
`docs/TRACE-DAG.md`; the reachable-stack obligation remains open until the
universal theorem, corollaries, ownership-proof review and trust receipts are
verified. This packet does not close finalizer-machine or host connections.

## Proof and semantic requirements

The theorem starts at the checked flow's entry with its existing one-element
input environment and empty stack. Its proof must derive the facts supplied
by current admission and establish a reachable-stack invariant through the
actual region runner. A suitable private `StackAt flow label stack` relates an
empty stack to the outside label; a nonempty stack names the current region,
resolves that region's row, and relates its tail to that row's parent.
Equivalent private representations are allowed if they prove the same
ownership facts. A nonempty-stack test alone is insufficient: a wrong head
can close the wrong region without producing `stuck`.

Extract validator facts for entry ownership, resolving blocks and operands,
plain successor labels, enter parent/body labels, acquire target/release
validity, and leave continuation ownership. Preserve environment lengths and
the stack relation through each recursive transition. A failed acquisition
does not register; failed operations and releases remain within the theorem.
The proof may induct on runner fuel. The wire corollary follows the existing
projection, and the fuel-free standard-handler corollary may use
`runRegionsCause_eq_interpretWF` at its sufficient budget internally.

The public statements have no successful-run, successful-release,
empty-failure, complete/compatible-tape, positive-fuel or `fuelFor` premise.
They accept arbitrary wire inputs and arbitrary stateful region services.
Do not redefine `RunResult.stuck`, change validation, discard result branches,
or replace the runner with a safe wrapper to make them true. Existing runner,
Scope, RegionTotal, signatures, contracts and counterexamples remain intact.
Independent acceptance includes inspection of the private invariant and
declaration dependencies, not only a successful theorem name check.

The fuel-free corollary uses the existing standard `regionHandler` through
`interpretRegions`. It does not quantify over arbitrary handlers of
`RegionSig`: such a handler can answer `none` at acquisition or leave, and the
existing denotation intentionally preserves the resulting stuck branch.

## Independent controls and deliberate invalid states

The battery reuses nested scopes, two resources, body and release failure,
region-free execution and a resource-bearing decision cycle. It keeps the
full nested failure list, tests zero and insufficient fuel, unanswered tapes
before and after looping, mismatched decisions, successful completion with an
unused suffix, arbitrary wire input, and a service that changes state before
failing acquisition. Admission controls prevent vacuous rejected examples.

Two raw internal starting states show the boundary. Entering an acquisition
with an empty stack produces the existing stuck result. Leaving with a head
named 99 instead of the block's region 1 closes region 99 and finishes without
stuck; a correct-head control closes region 1. These invalid starting states
do not contradict the public entry-from-empty theorem. They reject a proof
that treats arbitrary stacks as reachable or mistakes nonemptiness for
ownership. A nonstandard scope-handler control separately produces stuck
under the fuel-free denotation, so the standard-handler restriction is real.

Finite controls do not replace the universal theorem or ownership proof.

## Verification and expected red state

```text
lake env lean Effect4Test/Semantics/RegionSafetyContract.lean
lake env lean Effect4Test/Semantics/RegionSafetyAxiomReport.lean
```

Before production exists, missing `RegionSafety.olean` is an import failure,
not sufficient declaration-red evidence. In scratch, replace only the new
import with `Effect4.Semantics.RegionTotal`: all controls must pass and the
three named declarations must be rejected as missing. A second scratch copy
removes only `SAFETY-SURFACE` and verifies the controls alone. Change the
empty-stack control from `stuck = true` to `stuck = false` in a third copy;
it must fail at that assertion. Restoring it must pass again.

The axiom report checks the exact three public names. Allowed axiom union:
`propext`, `Quot.sound`; no `sorryAx`, `Classical.choice`, `native_decide` or new
axioms. The coordinator owns the production build, root imports, known-red
wiring, graph status and shared coordination commit. This breaker commits
only the three packet files and runs narrow Lean checks.

### Breaker receipt, 2026-09-03

Scratch directory: `/tmp/effect4-region-safety-breaker`. The source file has
31 concrete guards; each expected observation is reached before the missing
public-declaration checks in the scratch red copy.

| Command | Observed result |
| --- | --- |
| `lake env lean /tmp/effect4-region-safety-breaker/Controls.lean` | Exit 0; all 31 existing-meaning controls pass. |
| `lake env lean /tmp/effect4-region-safety-breaker/InvalidStackMutant.lean` | Exit 1 only at the changed assertion that the invalid empty-stack run has `stuck = false`. |
| `lake env lean /tmp/effect4-region-safety-breaker/Controls.lean` after the mutant | Exit 0 again. |
| `lake env lean /tmp/effect4-region-safety-breaker/Red.lean` | Exit 1: exactly the three absent public identifiers; no control or expected-type error. |
| `lake env lean /tmp/effect4-region-safety-breaker/AxiomsRed.lean` | Exit 1: exactly the same three unknown public constants. |
| `lake env lean Effect4Test/Semantics/RegionSafetyContract.lean` | Exit 1: missing `RegionSafety.olean`, recorded separately from the declaration-red checks. |
| `lake env lean Effect4Test/Semantics/RegionSafetyAxiomReport.lean` | Exit 1: the same missing object file. |

Scratch transformations are the import replacement and marked-section
removal described above. The mutant changes one guard only. Production,
validation and prior packets were untouched; no package build or host gate
ran for this freeze.
