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

## Context and Result (vendored 2026-09-03 for the Context model and the caught-perform reading)

Copied byte for byte from the pinned install whose integrity matches the package hash above
(`docs/research/2026-09-03-lowering-l2-host-tails.md`); read by `workshop/Deep/Context.lean`
and the `Result` arm of the lowering. Not yet a census input.

| File | SHA-256 |
| --- | --- |
| `src/Context.ts` | `dae8fd7aaee4263e4223a415e343542b567d6132da3ad321b30649b24ee1b862` |
| `src/Result.ts` | `2866d8a618682b1d0c32d7578933810f68e353c1615dab4b399239b2b8ca6593` |

## Host structure census (`ref.*`, `deferred.*`, `layer.*`)

Read by the same generator and gate, for the census rows that pin the mutable
cell, the completion store, and layer build and memoization.

| File | SHA-256 |
| --- | --- |
| `src/Ref.ts` | `69dc695dbe042baec090178dcc261f9a171e15a9fe6034d1c479408d6369d8fc` |
| `src/MutableRef.ts` | `0ededd9c6d3f865a9ff804aff3fe7ca7413c22ecd697ae0e7f87d80771ee7a1f` |
| `src/Deferred.ts` | `78b5d3cd2ad37f9e4f8ebaf465c9375bb982a00bd22a9f3d50ed02e0cb65f0e9` |
| `src/Layer.ts` | `55f20d4a18913efc16f8bd5732d477e9455fb2ea1476e47d0a4ed14b12caed58` |
| `src/internal/layer.ts` | `6ad3c8e779bae54dc0b3e57cd99fcd2087354df0c673d6335619d5cd95a74187` |

The included `LICENSE` is the package license.

## Full source tree (vendored 2026-09-04)

The complete `src/` tree of the pinned install (integrity as above; every previously vendored
file was verified byte-identical before the copy) is now in hand for the OCaml avatar lane, so
the port can cite any rc.112 file by line without leaving the repository. Manifest:
`SHA256SUMS` (452 files). The census tables above still name the exact files the gates read;
the rest is reference, never executed or imported.
