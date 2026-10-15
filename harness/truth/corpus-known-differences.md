# Known disagreements in the corpus results

`scripts/check-corpus.py` (`make check-ts`) fails on a row of
`harness/truth/corpus-results.tsv` that records a disagreement between the Lean machine and
rc.112 (`run` other than agreement, `sync differs`), between Lean's type and the compiler's
(`types mismatch-…`), or between Lean's checker and the compiler on a well-typed program
(`tsc errors`), unless the table below lists that **program, dimension and outcome** with the
design-issue row or the finding that explains it. A listing is a named open question, never
a pass: the row still records the disagreement in full (both exits, both compared schedules,
the compiler's first error), so a difference that changes shape changes the expected file,
and the entry goes when the disagreement does (the check fails on a stale entry too).

The second column is `<dimension> <outcome>` exactly as the results file spells it; a program
listed under one dimension is not excused on another. This table is the list of the
language's known differences from rc.112 over the generated corpus.

| program | dimension outcome | why |
| --- | --- | --- |
| `g81` `g144` `g250` `g289` `g313` | run differ | DI-73: the five rows print one program, `Effect.fiberId`, typed `number` on both faces. The machine answers the root's index `0`; rc.112 answers its process-wide fiber counter (`fiberIdStore`, `vendor/effect-4.0.0-rc.112/src/internal/effect.ts:499`, `vendor/effect-4.0.0-rc.112/src/internal/effect.ts:512`), which starts at `1` and also counts the runner's earlier fibers: `8` on the `runPromiseExit` entry. Renumbering the output cannot repair a value computed from an id: `pIdIsZero` (`Test/Api/ApiContract.lean`) answers `eq(getId, 0)` as `true` on the machine and `false` on rc.112. A named cross-target limitation until DI-81's opaque fiber id lands |
| `g81` `g144` `g250` `g289` `g313` | sync differs | DI-73: the same five on the `runSyncExit` entry, where rc.112's counter answers `7` |
| `g102` | run differ | A layer merge's fork count, not fiber numbering (both faces number fibers by first sight, decisions row 274). The machine forks one fiber per merged layer (`EffThunk.forkLayer`, `src/Effect4/Program/Compile.lean`). rc.112's concurrent `forEach` builds an item that is already an exit inline, with no fork (`vendor/effect-4.0.0-rc.112/src/internal/effect.ts:4820-4821`), and a `Layer.succeed` build is one (`succeedContext`, `vendor/effect-4.0.0-rc.112/src/Layer.ts:1129-1130`). This program's layer build forks four fibers on the machine and one on rc.112, so the answered `forkChild` handle is fiber `5` here and `2` there. A finite probe on rc.112 (bun 1.4.2, 2026-10-12) counts the forks of a build: `Layer.mergeAll(succeed, succeed)` 0, this program's layer 1, `Layer.mergeAll(effect, effect)` 2. The exit kind and the stores agree |
| `g102` | sync differs | The same fork count on the `runSyncExit` entry |
| `g16` `g49` `g55` `g160` `g308` `g363` `g390` | types mismatch-A | DI-77: Lean renders `unit` as `void` and prints the unit value as `undefined`; rc.112 infers `undefined` for `Effect.succeed(undefined)` and `Effect.sync(() => undefined)`, which is assignable to `void` and not the reverse |
| `g309` | tsc errors | tsgo 7 infers `unknown` type arguments from an argument of type `never`: the success branch of `Effect.matchCauseEffect(Effect.fail("hi"), …)` applies `Deferred.await` to the never value, so tsgo widens the answer to `Fiber<unknown, unknown>` and refuses the declared `Fiber<Context<never>, never>`. Lean types the unreachable branch at the never type. The row printed a declaration from `6f32c88cd` (decisions row 349: a context type prints as `Context.Context<R>`); both faces die with `missingService` |
