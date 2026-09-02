# Effect 4 source pin

This directory retains exact source bytes from the pinned Effect package. They
are evidence inputs for Effect4 census and assurance gates; Effect4 never
imports or executes them.

- package: `effect@4.0.0-rc.112`
- upstream commit: `2600f62f4532026928454dcea8d1c48557b3f942`
- package integrity: `sha512-wXxwuh1Ywnv4cPRM3Wfa0vDwuOHnZ1TsTgHJkG9XgzND6inhBH9n1vBxhg3iIXOia/OrpmvVmd3lrD4vq6bF3A==`

## Schema census and persisted-field gates

- `src/SchemaRepresentation.ts` SHA-256: `a0a7a1537cfe3a9159a80210e3de92342cc9e98651f0e8273a75ccdcccae69bc`

## Fiber runtime mechanism census

Read by `scripts/generate-effect-runtime-census.sh`; joined to Lean witnesses by
`Effect4Test/Audit/RuntimeCoverage.lean` and gated by
`scripts/check-effect-runtime-census.sh`.

| File | SHA-256 |
| --- | --- |
| `src/internal/effect.ts` | `0e32b42fbc8901ae75419fbd2999bf5c96b40e4bb54cc42c4fc2ec778cc641f0` |
| `src/internal/core.ts` | `233b7a1fb3a53b9f49f63c01f810052cb174cc13742f52ea2e8bd482f302fd11` |
| `src/Scheduler.ts` | `e4c35925d7586a82f93975390f08a67bfff4261d35d8382db7c18c9acc349680` |
| `src/Scope.ts` | `d1f31095954a8348853620ac102ae665acb86afbac54189d99e57c37757ddf18` |
| `src/Exit.ts` | `f9e4baea6718bd6617069563028710cfaee3ba7b432826f87c405e0ca3513818` |
| `src/Cause.ts` | `4b39e7f578b9bceba6712fdf0f53410963006cb335a94f3c5bbd8c49cfe9962b` |
| `src/Array.ts` | `ccc7dfbb44f0a93d4911af0d1db187925cfe7e765804bb3b9bdff2b7e1fc3936` |

The included `LICENSE` is the package license.
