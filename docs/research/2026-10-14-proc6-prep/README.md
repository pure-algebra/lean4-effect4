# PROC-6 prep: what the coordinator readied before the landing

Status: receipt (history, not authority). From the coordinator, 2026-10-14. The plan is locked
(`docs/research/2026-10-14-proc6-scout.md`, fifth version; decisions row 379). The landing brief is
`landing-prompt.md` beside this file.

## The one thing to know

The base builds, and the behaviour gates the landing will reach pass at the base, except where the
table below says otherwise. So a gate that fails after a slice fails because of that slice.

## The base

- Branch `refactor/phase1-phase3` of `/Users/pooks/Dev/lean4-effect4`, fast-forwarded to Gemini's
  `7c9bb7617`, then the commit that locks the plan (its hash is in the commit log under "PROC-6: lock
  the plan").
- `lake build Effect4 Effect4.Laws`: `Build completed successfully (1111 jobs).`

## The fan-out of the modules the stages edit

Measured by a script over the `import` lines of `src/`, `Test/` and `tools/` (the transitive importers
of each module). The `Effect4.*` column is what a narrow build after an edit recompiles. The `Test.*`
column is what a whole-test build would add.

| Module | Stage | Importers in `Effect4.*` | in `Test.*` |
| --- | --- | --- | --- |
| `Effect4.Program.Compile` | 0a | 404 | 356 |
| `Effect4.Laws.Program.Agreement` | 0a, 4 | 252 | 235 |
| `Effect4.Laws.Program.DenoteR` | 0a | 218 | 230 |
| `Effect4.Laws.Program.Intro.Sequential` | 0a | 193 | 226 |
| `Effect4.Laws.Program.Agreement.Machine` | 1, 4 | 188 | 227 |
| `Effect4.Laws.Program.Agreement.Segment` | 1, 4 | 187 | 227 |
| `Effect4.Laws.Program.Typed.Denotation` | 0a | 88 | 174 |
| `Effect4.Laws.Program.DenoteRowsB` | none (read only) | 14 | 129 |
| `Effect4.Laws.Program.Agreement.Calls` | 4 | 12 | 129 |
| `Effect4.Laws.Program.Agreement.LoopCalls` | 4 | 11 | 129 |
| `Effect4.Laws.Program.Agreement.Hosted` | 1, 4 | 10 | 129 |
| `Effect4.Laws.Api.SessionMeaning` | 1, 4 | 8 | 129 |
| `Effect4.Laws.Effects.Mrec` | 0 (deleted) | 5 | 116 |
| `Effect4.Laws.Program.Block` | 0 (deleted) | 4 | 116 |
| `Effect4.Laws.Program.HostedLoop` | 4 | 3 | 17 |
| `Effect4.Laws.Program.ParamRows` | 0 (deleted) | 2 | 7 |
| `Effect4.Laws.Program.Validated` | 3 (read only) | 2 | 115 |
| `Effect4.Laws.Library.Ref.Cache` | 0 | 1 | 7 |
| `Effect4.Laws.Api.SessionMeaningLoop` | 1, 4 | 1 | 4 |
| `Test.Dogfood.Scenario.Todo.Cached` | 0, 5 | 0 | 2 |
| `ProofGraph.Registry` | P | 2 | 66 |

The `Test.*` column is large for most rows because so many batteries import the `Effect4.Laws` root.
The narrow build reads only the first column.

## The build plan that follows

1. Stage 0a and stage 1's premise swap edit the six modules of highest fan-out. They form slice A,
   built once, with the flag-general lemmas of stage 4 that `Agreement.lean` holds.
2. Stages 0 to 3 go into new leaf modules (the brief's table), appended to the root imports. A proof
   slice rebuilds its own module and the root.
3. Stage 4 edits the hosted spine bottom-up. Each module is built alone as it is edited, and the
   dependents are built once at the end.

## Baseline gates at the base

| Command | Result |
| --- | --- |
| `make check-host-protocol` | PASS. The keyed host: 57 actual rc.112 runs, 52 admitted printed programs. The keyed scenarios: 86 scripts in 295 runs. The to-do's service: 13 scripts on rc.112, each replayed to its journal. The to-do on SQLite: 11 requests from an empty database, each passing Lean's five checks; the Ref cache hit and invalidation as expected; the forgetful and titleless repositories fail `agrees` and `conforming` |
| `make check-ts-reader` | `files 501: matched 416, mismatched 0` |
| `make check-target` | conformance `104 expected, 104 attempted, 104 resolved, 0 mismatching, 0 refused`; assignability PASS (742 pairs: agree 708, cut 6, incomplete 28; the red control caught); rows PASS |
| `make check-compiler` | pending |
| `make check-native` | pending |
| `make check-ocaml` | pending |
| `make check-truth` | pending |
| `make gen-semantics` after row 379 | `generated/semantics.md` unchanged |

Versions: effect 4.0.0-rc.112, bun 1.4.2.

## Not done here

- No source file changed, so no `#axiom_audit` ran in this preparation.
- The placement slice (the registry claim and the planned goals) is the landing seat's first slice,
  so that the seat owns the statements it proves.
