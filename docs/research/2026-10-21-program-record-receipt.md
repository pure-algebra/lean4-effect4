# Program record slice

`LiveRecord.currentVersion` stays `1`, and the strict decoder intentionally refuses the earlier record layout.
The coordinator regenerated the Tool codec in `7001dd8e`; its local cherry-pick is `be60ad5c9`.

The slice derives row spellings from the language signature and stores that signature with the program in saved sessions.
Status: the narrow builds, affected controls and declaration audits pass.
Base: `40770f079`.
Branch: `codex/program-record`.
Source head: `9f7eabf65`.
The caller changes and this updated receipt form the follow-up commit.

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

## Caller and saved-record checks

An intermediate caller build reaches the earlier Tool codec and fails on its old constructor layout.
The regenerated codec resolves that failure.
All thirteen affected test modules pass, together with the existing restoration-law and run-origin readers:

```sh
LEAN_NUM_THREADS=3 lake build Test.Api.HostList Test.Api.SessionMeaning Test.Api.TargetSupport Test.Counterexamples.Machine.Runtime.HostInstancePrefix Test.Counterexamples.Machine.Runtime.HostRefPrefix Test.Dogfood.Bank Test.Program.DenoteRowsContract Test.Program.LiveRecordControls Test.Program.NativeBoundaryControls Test.Program.PreviewControls Test.Program.RunAdmissionControls Test.Program.TableReference Test.Run.RunContract Test.Run.LiveContract Test.Program.RunOriginControls
```

The build reports `Build completed successfully (1339 jobs).`
The earlier record layout's control runs `Canonical.decode` on encoded eight-field record bytes.
The decoder refuses those bytes.
A final narrow build of `Test.Program.RunAdmissionControls` passes with `1176 jobs`.
The other controls cover object byte round trips, malformed admission, unknown versions, derived row names and session restoration.

The audit imports the thirteen changed test modules and `ProofGraph.AxiomAudit`.
It names those thirteen modules in its `#axiom_audit` command.

```sh
LEAN_NUM_THREADS=3 lake env lean /private/tmp/program-record-tests-audit.lean
```

```text
#axiom_audit: 981 declarations within [propext, Quot.sound], 0 of them modulo planned goals; 0 planned goals
```

No assigned proof obligation remains open.
These test controls are finite evaluations, not outside implementation agreement.
The coordinator owns the generated files and outside implementation gates.
This slice claims no external resource restoration.

The receipt's language check and `git diff --check` pass:

```sh
python3 scripts/check-language.py --strict docs/research/2026-10-21-program-record-receipt.md
git diff --check
```


## Changed source files

- `src/Effect4/Api/Built.lean`
- `src/Effect4/Api/Author.lean`
- `src/Effect4/Laws/Api/Built.lean`
- `src/Effect4/Laws/Api/AuthorBuild.lean`
- `src/Effect4/Laws/Program/Author.lean`
- `src/Effect4/Run/LiveRecord.lean`
- `src/Effect4/Laws/Api/LiveRecord.lean`


## Changed caller files

- `Test/Api/HostList.lean`
- `Test/Api/SessionMeaning.lean`
- `Test/Api/TargetSupport.lean`
- `Test/Counterexamples/Machine/Runtime/HostInstancePrefix.lean`
- `Test/Counterexamples/Machine/Runtime/HostRefPrefix.lean`
- `Test/Dogfood/Bank.lean`
- `Test/Program/DenoteRowsContract.lean`
- `Test/Program/LiveRecordControls.lean`
- `Test/Program/NativeBoundaryControls.lean`
- `Test/Program/PreviewControls.lean`
- `Test/Program/RunAdmissionControls.lean`
- `Test/Program/TableReference.lean`
- `Test/Run/RunContract.lean`
