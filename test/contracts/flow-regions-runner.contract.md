# Contract: the region runner (P-T7, runner half)

Light ceremony by operator ruling D2. Effects pin: v0.5.0 (`c28833b`, regions).

## Frozen surface (`Effect4/Flow/Region.lean`)

| Name | Shape |
| --- | --- |
| `RegionService alphabet M` | `handle : Op → Val → M (Except Val Val)`, `pure : Op → Bool` (the aborting reading) |
| `tableRegionService` | a table service whose family operations may fail |
| `Frame alphabet` | an open region and its releases, latest first |
| `closeFrame`, `unwind`, `fail` | close one region with an exit; close every open region with a failure; end the run failed |
| `regionLoop`, `runRegions`, `runRegionsDefault` | the fuelled loop over a `CheckedRegionFlow` |
| `RunResult.failed` (`Runs.lean`) | a run that ended in a failure after closing every open region |

## Semantics pinned (each row checked on the host under every mask)

- `enter r` logs `enter r` and pushes a frame; `acquire` performs, logs its
  `op`/`answer`, and registers its release on the innermost frame.
- `leave v` logs `leave r (success v)`, runs the releases latest-first, each
  logging `finalizer r (success v)` before its own rows, and continues at the
  region's `continue_` block with `v`; a release failure becomes the exit of
  everything enclosing and the run ends `failed` with the first release failure.
- A failing operation logs `failed`, closes every open region innermost-first
  with `failure e` (`leave`, then `finalizer` per release with `failure e`),
  and the run ends `failed e`; a release failing during that close does not
  replace `e` (`Exit.mergeFinalizer`: the body's cause comes first).
- The reified Scope agrees: `Scope.closeOrder` is registration order reversed
  and `Scope.closeExits` hands every release the same closing exit
  (`Effect4Test/Flow/RegionRunnerContract.lean`).

Host evidence: `generated/traces/flow/regionNested.empty`, `regionTwoFail.empty`,
`regionBothSucceed.empty` agree under every mask at both yield settings. A
fallible release runs in Lean but has no lowering (`E4-TARGET-CE-012`), so
`regionReleaseFails` is a Lean-only receipt. Rows `E4-FLOW-CE-019`, `E4-FLOW-CE-020`.

Refusals (not modelled): an interrupt cause, a parallel finalizer strategy, a
region closed twice, a finalizer that opens a region (a release is one
operation by construction), a fallible release on the host.

## Acceptance

```text
lake env lean Effect4Test/Flow/RegionRunnerContract.lean
./scripts/check-trace-goldens.sh
./scripts/check-trace-host.sh
```
