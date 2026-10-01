# U-02 evidence: `Scope.close` answers a lone finalizer's value on rc.112

Companion to `../receipt-D4.md` (seat D4, decisions row 151 (a″)) and to row `U-02` of
`docs/UPSTREAM-BACKLOG.md`.

`VendorScopeCloseProbe.ts` runs the pinned rc.112 source end to end with bun 1.4.2;
`vendor-sha256.json` pins the four source files it loads (the `Scope.ts` and
`internal/effect.ts` hashes are the runtime census's `input` lines). `vendor-scope-close.json`
is its output. `Scope.close` (declared `Effect<void>`, `Scope.ts:567`) answers:

| Row | Finalizers when the scope closes | rc.112 answer |
| --- | --- | --- |
| `zero` | none | `undefined` (void) |
| `inline` | one `acquireRelease` release answering `5`, in the inline slot (`internal/effect.ts:3788-3789`) | `5` |
| `mapOne` | the same release, after a child scope was forked and closed, leaving a one-entry map (`:3794-3795`) | `5` |
| `two` | two releases answering `5` and `6` (the walk, `exitAsVoidAll`, `:3826`) | `undefined` (void) |
| `loneDie` | one release that dies | `Failure Cause([Die("boom")])`: the defect passes through |

`Effect3ScopeCloseProbe.ts` is the comparison: rows `zero`, `inline` and `two` (not `mapOne` or
`loneDie`) on Effect 3.21.2, a local install
outside this repository (`/Users/pooks/Dev/effect-jetstream/node_modules/effect`; its
`dist/esm/internal/fiberRuntime.js`, sha256
`d378bdfba82626a2a2599cbad950f2f337669d27684b3b12ead14701fc9b6acc`, closes through
`exitAsVoid` for every finalizer count above zero, `:1885-1904`). Its output,
`effect3-scope-close.json`, answers `undefined` in all three: Effect 3 voids the lone
finalizer's value, Effect 4 dropped that when it added the lone-finalizer fast paths.

The Lean side is `Test/Program/ProtocolPosts.lean`, namespace `CloseScope`: `closeLone` (the
`inline` row as a checked program, typed `⟨unit, never⟩`) answers `unit` on both machines
(`#guard`s on `frameExit` and `termExit`), and the close-scope row's typing of the voided close.

Run from the repository root:

```sh
bun docs/research/2026-10-01-landing/seat-D4/VendorScopeCloseProbe.ts
bun docs/research/2026-10-01-landing/seat-D4/Effect3ScopeCloseProbe.ts
```
