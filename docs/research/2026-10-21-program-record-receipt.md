# Program record slice

Regenerate the Tool codec after this source commit, before building its consumers.
The strict decoder intentionally refuses the earlier record layout.

The slice derives row spellings from the signature and stores that signature with the program in saved sessions.
Status: source and proof checks pass; affected batteries await the regenerated Tool codec.
Base: `40770f079`.
Branch: `codex/program-record`.

## Proof placement before edits

| Obligation | Concept and property | Claim and consumer | Reach | Exclusions | Requirement |
| --- | --- | --- | --- | --- | --- |
| `namesFrom_eq`, `module_rowNames` | `translation-simulation`, authoring elaboration | Helpers of the existing author-build static facts; `Author.build_retains`, `build_table` | Every row declaration list and module; the names are the signature projection | No execution observation or host behavior | R10 |
| `finishBuild_retains`, `build_retains` | `translation-simulation`, authoring elaboration | Existing static facts; `Workers.releases_once`, `QueueWorkers.releases_once`, `Run.CallTree.bound_in_tree` | Successful admission; same program, application and derived names | No progress or finalization claim | R10, R11 |
| `rebuild_spec`, `rebuild_admitted`, `rebuild_self` | `residual-program-typing`, admission | Helpers of `rebuild-admission`; checked edited programs | Same application; admission of the exact candidate | No equality of behavior or result type | R1 |
| `ofProgram_of_admitted` | `host-session-protocol`, `typed-replay-session` | Helper of `built-admission-exact`; object opening and `LiveRecord.restore_save` | Every supplied admission certificate | No host execution or progress | R6, R13 |
| `restore_save`, `restore_unsupportedVersion` | `host-session-protocol`, `typed-replay-session` | Existing `live-session-persists` contract; tool restore and record query | Every live session; exact recorded run, journal and derived row names | No external resource restoration or effect repetition guarantee | R6, R13 |

The shared object and its opening laws belong to the coordinator.
`LiveRecord.currentVersion` remains `1`; the generated decoder rejects the earlier field layout.
The changed layout replaces `app`, `program` and `rowNames` with `object`.

## Verification

The source uses dependencies `30e263cbb`, `e45087eeb` and `578c63e9c` from the coordinator.
The local cherry-picks are `38add1726`, `985ee185c` and `d56f6a7bf`.

The narrow build passes:

```sh
LEAN_NUM_THREADS=3 lake build Effect4.Api.Built Effect4.Api.Author Effect4.Laws.Api.Built Effect4.Laws.Api.AuthorBuild Effect4.Laws.Program.Author Effect4.Run.LiveRecord Effect4.Laws.Api.LiveRecord
```

The build reports `Build completed successfully (651 jobs).`
A repeat after the generated dependency update passes with `ProofGraph.AxiomAudit` added.
It reports `Build completed successfully (658 jobs).`

The audit imports those seven modules and `ProofGraph.AxiomAudit`.
Its command names those seven modules:

```sh
LEAN_NUM_THREADS=3 lake env lean /private/tmp/program-record-audit.lean
```

```text
#axiom_audit: 294 declarations within [propext, Quot.sound], 0 of them modulo planned goals; 0 planned goals
```

`git diff --check` passes.
The public conclusions of `build_retains`, `build_table`, `rebuild_spec` and `restore_save` remain unchanged.
`finishBuild_retains` identifies names derived from the application; `finishBuild` no longer accepts arbitrary names.

## Pending verification

The affected batteries await the coordinator's regenerated Tool codec.
The saved-record controls check malformed admission, unknown versions, restoration and the earlier field layout's refusal.
The coordinator owns the generated files and outside implementation gates.
This slice claims no outside implementation agreement or external resource restoration.

## Changed source files

- `src/Effect4/Api/Built.lean`
- `src/Effect4/Api/Author.lean`
- `src/Effect4/Laws/Api/Built.lean`
- `src/Effect4/Laws/Api/AuthorBuild.lean`
- `src/Effect4/Laws/Program/Author.lean`
- `src/Effect4/Run/LiveRecord.lean`
- `src/Effect4/Laws/Api/LiveRecord.lean`

