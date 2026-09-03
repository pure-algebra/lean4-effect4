# Contract: fuel-free region denotation

Independent breaker continuation of D2, frozen 2026-09-03 from
`70bd0176af70893a00c8011d0735a6427a9b5649`. This packet adds the missing total
region meaning. It does not revise the existing region runner, signature,
fuelled meaning, failure carrier, earlier contracts, or host claims.

## Ownership and public surface

Production owner: `Effect4/Semantics/RegionTotal.lean`, importing
`Effect4.Semantics.RegionDenotation` and optionally `Approximation`. All four
names are in `Effect4.Flow`; exact Lean ascriptions are frozen in
`Effect4Test/Semantics/RegionTotalContract.lean`.

| Name | Required shape |
| --- | --- |
| `denoteRegionsGo` | `{alphabet : FlowAlphabet Ty} → (flow : RegionFlow Ty) → CyclesWF flow.erase → BlockId → Env → Tape → Program (RegionSig alphabet) ((RunResult × Tape) × Failures)` |
| `denoteRegionsWF` | `[DecidableEq Ty] → {alphabet : FlowAlphabet Ty} → CheckedRegionFlow alphabet → Tape → Val → Program (RegionSig alphabet) ((RunResult × Tape) × Failures)` |
| `denoteRegionsFuel_eq_denoteRegionsWF` | Every checked region flow, tape, input and fuel satisfying `fuelFor flow.flow.erase tape ≤ fuel`: its existing fuelled Program at the entry and `[input]` equals `denoteRegionsWF flow tape input`. |
| `runRegionsCause_eq_interpretWF` | For every lawful monad, region service, operation naming function, tape, input, initial log and sufficient fuel: `runRegionsCause` equals interpretation of `denoteRegionsWF`, including complete failures, residual tape and log. |

No generalized helper is required to be public. Existing `LoopBudget` and
non-choice reachability helpers may be reused. Do not redeclare canonical
carriers, signatures, region validation, or runner operations.

Public declaration record: all four names are derived declarations over the
existing native `RegionFlow`, `CheckedRegionFlow`, `RegionSig`, `Program`,
`RunResult`, `Tape` and `Failures`; none introduces a carrier or duplicates
their owners. `denoteRegionsGo` and `denoteRegionsWF` add the fuel-free face,
while the two equalities connect it to the existing fuelled face and runner.
Their mandatory assurance route is the existing region/semantics proof graph
in `docs/TRACE-DAG.md`, whose fuel-free region edge remains open until this
packet's universal equality, runner corollary, recursive-body review and axiom
receipts close it. Finite controls alone do not close that edge.

## Required meaning and proof boundary

`denoteRegionsGo` is a genuinely fuel-free recursive definition. Its recursive
calls descend by finite tape consumption at decisions and by the erased
graph's non-choice reachability between decisions. `CyclesWF flow.erase` is
the cycle premise; the function accepts an arbitrary block and environment.
The wrapper calls this function at the checked flow's entry with `[input]`.

Defining the new function by calling `denoteRegionsFuel`, `denoteRegions`,
`regionLoop`, or a runner at a calculated, hidden or arbitrary budget does
**not** satisfy the contract, even if an extensional theorem happens to hold.
Acceptance includes inspecting the recursive body and its dependencies: a
declaration name and an equality alone cannot establish this representation
requirement. Helpers may prove budget adequacy, but fuel and budget computation
must not drive the new denotation's execution.

The body preserves every branch of `denoteRegionsFuel` except its exhausted
fuel branch: missing blocks, failed argument reads and invalid operation
lookups remain stuck; returns remain returns; jumps and successful operations
continue; operation and acquisition failures emit `ScopeName.fail` and retain
the complete ordered failure list. Enter, acquire and successful leave follow
the same target and environment. Both `Option.none` scope answers remain
stuck. A failing leave keeps its first error, remaining errors, and errors
from closing outer scopes in the existing order. A decision consumes exactly
the compatible head; exhaustion is an unanswered frontier and mismatch is a
refusal with the unmatched tape retained. Neither implies scope finalization.

The main equality is at the `Program` level. It must hold for every possible
continuation answer, including scope answers that the standard handler would
not return on its reachable stack. There is no stack well-formedness,
successful-run, total-service, empty-failure, compatible-complete-tape or
region-free restriction. A separate stack invariant is not required here.
The runner corollary composes this equality with the existing
`runRegionsCause_eq_interpret`; it preserves that theorem's lawful-monad
generality and complete result. These are Lean equalities, not host conformance
or a statement about infinite tapes.

## Battery and falsifiers

The new battery reuses the earlier nested resource, clean resource, region-free
and fallible-release fixtures. It adds only fixture data for nested release
failures and a resource-bearing decision cycle. Controls compare the entire
existing denotation and runner records, then pin the expected outcomes:

- Nested body failure with two failing releases retains three failures. A
  first-failure-only candidate is explicitly rejected.
- A failing release after successful body completion remains a failure.
- Both branches of a decision cycle are exercised; true revisits site 7 and
  false leaves. The successful run keeps an unused decision suffix.
- Empty tape, exhausted tape after a loop, initial mismatch and mismatch after
  a loop remain distinct. An open scope on the unanswered frontier has no
  leave, release or completion event.
- A deliberately nonstandard handler answers `none` at acquisition and leave;
  each remains stuck at the relevant block.
- Surplus fuel 37 preserves the full existing observation. A general theorem
  ascription separately requires **every** sufficient fuel, not just this
  sample or exactly `fuelFor`.
- The universal `Program` equality is transported through an arbitrary
  handler, so a proof restricted to the standard scope interpreter fails the
  frozen ascription.

These are finite witnesses for the listed mechanisms. Their success does not
replace the universal theorem or recursive-body inspection. They preserve and
extend the concerns of existing `E4-FLOW-CE-019`, `E4-FLOW-CE-021` and
`E4-TARGET-CE-012`; no new host claim or canonical counterexample is asserted.

## Verification and expected red state

Narrow acceptance commands, run sequentially by the coordinator after build:

```text
lake build Effect4.Semantics.RegionTotal
lake env lean Effect4Test/Semantics/RegionTotalContract.lean
lake env lean Effect4Test/Semantics/RegionTotalAxiomReport.lean
```

The breaker does not run a full package build. Before production exists, the
direct imports fail because `RegionTotal` is missing. That is insufficient
red evidence on its own. An isolated scratch copy replaces only that import
with `RegionDenotation`: it must reach and reject the four missing public
declarations. A second scratch copy removes only the marked `TOTAL-SURFACE`
section and runs all existing-meaning controls successfully. The root import
and explicit known-red list are coordinator-owned.

`RegionTotalAxiomReport.lean` checks the core definition, wrapper and both
theorems. Allowed axiom union is `propext` and `Quot.sound`; no `sorryAx`,
`Classical.choice`, `native_decide` or new axiom. Axiom inspection alone does
not establish the recursive representation requirement.

### Breaker receipt, 2026-09-03

Verified against `2bd2077200a4c189c6bdd08dd5bc6baf1c4ce275`, before the
production file exists. Scratch directory:
`/private/tmp/region-total-breaker.2r18wswk`.

| Command | Observed result |
| --- | --- |
| `lake env lean /private/tmp/region-total-breaker.2r18wswk/Controls.lean` | Exit 0; all 24 concrete guards pass. |
| `lake env lean /private/tmp/region-total-breaker.2r18wswk/FirstFailureMutant.lean` | Exit 1 only at the changed three-failures expectation: retaining just the first failure does not evaluate to true. |
| `lake env lean /private/tmp/region-total-breaker.2r18wswk/Controls.lean` (restored control) | Exit 0 again. |
| `lake env lean /private/tmp/region-total-breaker.2r18wswk/Red.lean` | Exit 1: all four public names are absent; remaining errors are references to those same absent names. No fixture or control error. |
| `lake env lean /private/tmp/region-total-breaker.2r18wswk/AxiomsRed.lean` | Exit 1: precisely the four expected unknown constants. |
| `lake env lean Effect4Test/Semantics/RegionTotalContract.lean` | Exit 1: missing `RegionTotal.olean`, recorded separately from declaration red evidence. |
| `lake env lean Effect4Test/Semantics/RegionTotalAxiomReport.lean` | Exit 1: same missing object file. |

The mutant changes only the positive nested-failure expectation from three
failures to one. The scratch transformations are described above; production
and prior contracts were not edited. No full package build or host test ran.
