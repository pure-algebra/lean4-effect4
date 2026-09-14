# Known disagreements in the corpus results

`scripts/check-corpus.py` (`make check-corpus`) fails on a row of
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
| `g81` `g102` `g144` `g250` `g289` `g313` | run differ | DI-73: a fiber id answered as a value (`getId`, a fiber handle from a layer build) is the machine's allocation index on one face and the runtime's counter on the other; `eq(getId, 0)` answers `true` here and `false` there, so renumbering the output cannot repair it — a named cross-target limitation until ruled |
| `g81` `g102` `g144` `g250` `g289` `g313` | sync differs | DI-73: the same six on the `runSyncExit` entry |
| `g38` `g183` `g276` `g352` `g123` `g390` | tsc errors | DI-76 (c): `getContext` prints as `Effect.context()`, whose requirement rc.112 infers as `unknown`, while Lean annotates the answer `Context.Context<unknown>` with requirement `never`: `TS2375`, the shipped annotated module does not compile |
| `g50` `g89` `g290` | types mismatch-R | DI-24: the printed key `Context.Service<number>("k<n>_4")` has no nominal identity on the host, so providing one `number`-shaped key discharges every `number`-shaped requirement at the type level (rc.112 infers `never`; Lean keeps the unprovided key), while the run dies with a missing service on both faces |
| `g16` `g49` `g55` `g160` `g308` `g363` | types mismatch-A | DI-77: Lean renders `unit` as `void` and prints the unit value as `undefined`; rc.112 infers `undefined` for `Effect.succeed(undefined)` and `Effect.sync(() => undefined)`, which is assignable to `void` and not the reverse |
