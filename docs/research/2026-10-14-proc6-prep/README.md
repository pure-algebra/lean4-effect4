# PROC-6 prep: what the coordinator readied before the landing

Status: receipt (history, not authority). From the coordinator, 2026-10-14. The plan is locked
(`docs/research/2026-10-14-proc6-scout.md`, fifth version; decisions row 379). The landing brief is
`landing-prompt.md` beside this file.

## The one thing to know

The base builds, and every behaviour gate the landing will reach passes at the base. One of them,
`check-truth`, was broken by an earlier landing and is repaired here: a harness caller that missed a
new argument (`harness/truth/P2b.lean`). So a gate that fails after a slice fails because of that
slice.

## The base

- Branch `refactor/phase1-phase3` of `/Users/pooks/Dev/lean4-effect4`, fast-forwarded to Gemini's
  `7c9bb7617`, then `d6e162caf`, which locks the plan. The landing's base is the commit that records
  this receipt and the `check-truth` repair, one after `d6e162caf`.
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
| `make check-compiler` | `conform compiler: PASS, exit 0` |
| `make check-native` | `conform native: PASS, exit 0` |
| `make check-ocaml` | PASS: the generated fixtures present; `ok` C1, C2 (`ocaml/gen` builds and `@gen/runtest` passes), C3a, C3b, C4; the engine lanes' views equal Lean's |
| `make check-truth` | failed at the base, then fixed here. The differential passed (`81 programs agree on exits, schedules and sync exits; 12 signed divergence(s)`), then `harness/truth/P2b.lean` failed to elaborate. `requirementType` gained its `KeyNames` argument in `8c14ef7cc` (row 378 (22)), and no gate run updated this harness caller. It now passes `[]`, the names of the native signature over an empty table, so its keys print by their runtime text as before. The rerun passes: `PASS P2b: exact consumer columns, retained negative comparisons, and missing-member refusals checked; type-only`; `PASS truth: pinned corpus, bounded differential and the signed U-01, HC-2 and LATEST divergences checked; the regenerated modules type-check` |
| `make gen-semantics` after row 379 | `generated/semantics.md` unchanged |

Versions: effect 4.0.0-rc.112, bun 1.4.2.

## The merge's axiom audit

The fast-forward to Gemini's `7c9bb7617` landed 11 commits that no audit had read. One
`#axiom_audit` over the 23 `Effect4.*` modules and the 9 batteries they changed:

- `Effect4.Codegen.{Admit, CallbackRequirements, Classes, Print, Read, RowServices, Types}`;
- `Effect4.Laws.Api.ModuleReadable`, `Effect4.Laws.Codegen.{Admit, Checked, Classes, Module, ReadPrint}`;
- `Effect4.Laws.Library.Ref.Cache`, `Effect4.Laws.Program.ParamRows`, `Effect4.Laws.Run.CallTree`;
- `Effect4.Program.Authoring` and its `Application`, `ApplicationService`, `Claims` and `Declare`;
  `Effect4.Program.Definitions`;
- `Test.Codegen.{DefinitionsPrint, ServicesPrint, TypeReader}`, `Test.Dogfood.{Application, Bank}`,
  `Test.Dogfood.Scenario.Todo` and its `Cached`, `Test.Program.{AuthoringDeclare, SessionToolControls}`.

```text
#axiom_audit: 4694 declarations within [propext, Quot.sound], 0 of them modulo planned goals; 0 planned goals
```

## Not done here
- The placement slice (the registry claim and the planned goals) is the landing seat's first slice,
  so that the seat owns the statements it proves.
