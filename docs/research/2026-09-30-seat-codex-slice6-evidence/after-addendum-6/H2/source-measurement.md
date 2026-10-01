# H2 source measurement at d554cd71

**Nine existing source bodies require repair after the full five-module substitution.** The original eight repairs leave only the new H1 observer adapter. Correcting that adapter passes the fresh five-module harness. Base FitsExit/FitsCause membership and the two base observer embedding helpers remain unchanged.

These are root-run compiler results, independently attributed using each retained harness map. This seat ran no Lean command and made no repository edits.

| Stage | Exit | Diagnostics | Distinct existing bodies |
| --- | --- | --- | --- |
| baseline | 0 | 0 | 0 |
| mechanical | 1 | 15 | 9 |
| eight-only | 1 | 1 | 1 |
| repaired | 1 | 2 | 1 |
| repaired-2 | 0 | 0 | 0 |

The first repaired draft had a Lean layout error in the observer adapter; its original file and log are retained. The corrected branch formatting changes no statement and adds no tenth body. The corrected prepared Scheduler and harness are byte-identical to root’s measured copies.

## Mechanical diagnostics

| Existing body | Harness line(s) | Source module |
| --- | --- | --- |
| `Effect4.Program.Typed.cleanExit_of_never` | 104 | `Effect4.Laws.Program.Typed.Admission` |
| `Effect4.Program.Typed.observer_exitValue_typed` | 1017 | `Effect4.Laws.Program.Typed.Scheduler` |
| `Effect4.Program.Typed.popR_typed` | 680, 698, 710, 795, 805, 828 | `Effect4.Laws.Program.Typed.Stack` |
| `Effect4.Program.Typed.settling_fork` | 475, 475 | `Effect4.Laws.Program.Typed.Residual` |
| `Effect4.Program.Typed.strongExit_bool` | 437 | `Effect4.Laws.Program.Typed.Residual` |
| `Effect4.Program.Typed.strongExit_failure_of_error` | 634 | `Effect4.Laws.Program.Typed.Stack` |
| `Effect4.Program.Typed.strongExit_mono` | 529 | `Effect4.Laws.Program.Typed.Residual` |
| `Effect4.Program.Typed.strongExit_of_clean` | 93 | `Effect4.Laws.Program.Typed.Admission` |
| `Effect4.Program.Typed.strongExit_success` | 82 | `Effect4.Laws.Program.Typed.Admission` |

The 72 strengthened positions include eleven in Scheduler: ten former FitsExit positions and RacePayload.failures, which packages the buffered reasons as a failure exit. The latter field is a statement change and creates no additional source-body failure in this measurement.

Exact commands, hashes, each diagnostic’s source line, and copied results are in `source-measurement.json` and `measurement-evidence/`.

## Tests still to measure

The prepared patch inventories 43 existing test-body adaptations: the original 25 and eighteen from H1, plus seven changed theorem statements. This is a proposed patch inventory, not yet the compiler failure count. Root will first compile the unchanged tests against the strengthened library and preserve their attribution before applying adaptations. Historical H1 claims are expressly restated as former structural clauses instantiated with current H2 admission; the independent ValueMembership historical models are unchanged.
