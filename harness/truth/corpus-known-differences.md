# Known disagreements in the corpus results

`scripts/check-corpus.py` (`make check-corpus`) fails on a row of
`harness/truth/corpus-results.tsv` that records a disagreement between the Lean machine and
rc.112 (`differ`, `schedule-differs`, `host-timeout`, `lean-frontier`, `host-load-error`) or
between Lean's type and the compiler's (`mismatch-…`) unless the program is listed here in
backticks with the design-issue row or the finding that explains it. A listing is a named
open question, never a pass: the row still records the disagreement, and the entry goes
when the disagreement does.

| program | outcome | why |
| --- | --- | --- |
| `g20` `g83` `g122` `g146` `g185` `g189` `g252` `g291` `g334` | run `host-load-error`: the printed module is the bare literal, not an Effect | DI-72: `yieldError e` prints as its error term; the machine runs it as `fail e` |
| `g120` `g193` | run `differ`: rc.112 dies with "Not a valid effect" | DI-72: the forked program is a `yieldError` literal, printed as a bare value inside `Effect.forkScoped(...)` |
| `g81` `g102` `g144` `g250` `g289` `g313` | run `differ`: same kind, the fiber id or handle in the value differs | DI-73: a fiber id answered as a value (`getId`, a fiber handle from a layer build) compares allocation numbering, which the two faces assign differently |
| `g242` `g382` | run `differ`: Lean `badName`, rc.112 a text defect (`g242`) or an interrupt (`g382`) | DI-74: `die (lit "hi")` and `interrupt (app add [1, 1])` type but evaluate to `badName` on the machine; the host accepts the values |
| `g53` `g78` `g117` `g121` `g123` `g130` `g145` `g160` `g184` `g223` `g247` `g290` `g353` `g368` `g390` `g396` | run `schedule-differs`: the exits agree, the reduced schedule does not | DI-75: `startImmediately: true` and `daemon: true` forks, which the hand corpus never draws; the child's `started` precedes the parent's `forked` row on rc.112, and a daemon child's rows after the root's exit are not observed |
