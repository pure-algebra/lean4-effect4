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
listed under one dimension is not excused on another.

| program | dimension outcome | why |
| --- | --- | --- |
| `g20` `g83` `g122` `g146` `g185` `g189` `g252` `g291` `g334` | run host-load-error | DI-72: `yieldError e` prints as its error term, so the module's `main` is a bare number, not an Effect; the machine runs it as `fail e` |
| `g20` `g83` `g122` `g146` `g185` `g189` `g252` `g291` `g334` | tsc errors | DI-72: the same nine, `TS2322: Type 'number' is not assignable to type 'Effect<never, number, never>'` |
| `g69` `g120` `g145` `g193` `g344` | tsc errors | DI-72: a `yieldError` literal in argument position (`forkChild(17)`, `forkScoped(...)`, a branch arm), `TS2345`/`TS2322` |
| `g120` `g193` | run differ | DI-72: the forked program is a `yieldError` literal inside `Effect.forkScoped(...)`; rc.112 dies with "Not a valid effect" |
| `g120` `g193` | sync differs | DI-72: the same two on the `runSyncExit` entry |
| `g81` `g102` `g144` `g250` `g289` `g313` | run differ | DI-73: a fiber id answered as a value (`getId`, a fiber handle from a layer build) compares allocation numbering, which the two faces assign differently; `eq(getId, 0)` answers `true` on the machine and `false` on rc.112, so renumbering the output cannot repair it |
| `g81` `g102` `g144` `g250` `g289` `g313` | sync differs | DI-73: the same six on the `runSyncExit` entry |
| `g242` `g382` | run differ | DI-74: `die (lit "hi")` and `interrupt (app add [1, 1])` type but evaluate to `badName` on the machine (Lean `die badName`; rc.112 a text defect, an interrupt of fiber 2) |
| `g242` `g382` | sync differs | DI-74: the same two on the `runSyncExit` entry |
| `g53` `g78` `g117` `g121` `g123` `g130` `g145` `g160` `g184` `g223` `g247` `g290` `g353` `g368` `g390` `g396` | run schedule-differs | DI-75: `startImmediately: true` and `daemon: true` forks; the child's `started` precedes the parent's `forked` row on rc.112, and a daemon child's rows after the root's exit are not observed |
| `g38` `g183` `g276` `g352` `g123` `g390` | tsc errors | DI-76: `getContext` prints as `Effect.context()`, whose requirement rc.112 infers as `unknown`, and Lean annotates the answer `Context.Context<unknown>` with requirement `never`: `TS2375`, the shipped annotated module does not compile |
| `g50` `g89` `g290` | types mismatch-R | DI-24: the printed key `Context.Service<number>("k<n>_4")` has no nominal identity on the host, so providing one `number`-shaped key discharges every `number`-shaped requirement at the type level (rc.112 infers `never`; Lean keeps the unprovided key), while the run dies with a missing service on both faces |
| `g16` `g49` `g55` `g160` `g308` `g363` | types mismatch-A | DI-77: Lean renders `unit` as `void` and prints the unit value as `undefined`; rc.112 infers `undefined` for `Effect.succeed(undefined)` and `Effect.sync(() => undefined)`, which is assignable to `void` and not the reverse |
