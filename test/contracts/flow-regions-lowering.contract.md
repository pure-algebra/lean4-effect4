# Contract: region lowering (P-T7, lowering half)

Light ceremony by operator ruling D2. Ruling R4 holds by construction: the
syntax has no `try` arm. Requires lean4-typescript v0.3.0 (`1f39598`:
`Expr.lambda`, `Expr.method`, `Stmt.scopedGen`).

## Frozen surface (`Effect4/Target/TypeScript/RegionLower.lean`)

| Name | Shape |
| --- | --- |
| `RegionProgram` | name, param, result, `table`, `flow : CheckedRegionFlow (tableAlphabet ⟨0⟩ table)` |
| `regionsRows` | the `Regions` service: `enter(region)`, `leave(region, exit)`, `finalizer(region, exit)` |
| `Region.lowerDispatch`, `Region.lowerCases`, `Region.lowerPlain` | nested dispatch loops, one per region, `block<r>` per loop |
| `Region.ruleSet`, `Region.errorChannel`, `Region.requirementChannel`, `Region.declarationLine` | ledger and type receipt |
| `regionModules?` | plain and region programs in one module; `Decisions`, `Regions` (and `Exit`) when used |
| `Rule.regionEnter`, `regionAcquire`, `regionLeave` (`Lower.lean`) | `region-enter`, `region-acquire`, `region-leave`; nineteen rules in all |

## Shape pinned

- `enter r body args`: the move into `body`, `yield* regions.enter(r)`, then
  `const r<r> = yield* Effect.scoped(Effect.onExit(Effect.gen(function* () { let block<r> = body; while (true) { switch (block<r>) { … } } }), (exit) => regions.leave(r, exit)))`,
  then `b<continue_>p0 = r<r>; block = continue_; continue`.
- `acquire`: `const a<i> = yield* Effect.acquireRelease(cell.op(b<i>p<k>), (a, exit) => regions.finalizer(r, exit).pipe(Effect.andThen(cell.release(a))))`.
- `leave v`: `return b<i>p<v>` from the nested generator.
- A release with an error row has no lowering: `Effect.acquireRelease` types
  its release `Effect<unknown, never, R>` (`E4-TARGET-CE-012`).

## Evidence

`harness/trace/flow-fixture.ts` (drift-checked); type receipts under
`harness/trace/types/flow/region*.receipt`; host receipts under
`harness/trace/receipts/flow/region*.json`; `Effect4Test/Target/TypeScript/RegionLowerContract.lean`.

## Acceptance

```text
lake env lean Effect4Test/Target/TypeScript/RegionLowerContract.lean
./scripts/check-trace-host.sh
./scripts/check-lowering-types.sh
./scripts/check-lowering-coverage.sh
```
