# Timeout source flow receipt

The original three timeout goals remain open.
This landing connects successful reply application to the actual source return path.
It does not prove that every reachable machine follows that path with those source slots.

Base: `447ef7869`. Branch: `codex/host-planned-goals`.

## Placement

| Declaration | Concept | Claim and consumer | Reach | Limit |
| --- | --- | --- | --- | --- |
| `application_body`, `Test/Dogfood/Proofs/HostPayloads.lean` | host-session-protocol, R6 | source step of `stale_never_applies` | every reached run and successful application | no source-slot correlation |
| `success_cases`, `Test/Dogfood/Proofs/HostTimeoutSource.lean` | host-session-protocol, R6 | source case split for the machine invariant | every source lookup in the actual elaborated fetch | no machine preservation |
| `applied_body_through_source`, same module | host-session-protocol, R6 | source step of `stale_never_applies` | arbitrary body, cells, fuel, prior error and completed-fiber view | matching race and source points remain premises |
| `retry_reads_returned`, same module | translation-simulation, R10 | source test step of amended `retries_declared` | arbitrary singleton typed failure and lexical cells | no attempt bound or history relation |

`appliedBodies` excludes submitted replies without an application.
`appliedBodies_step` retains earlier applied bodies after every recorded command.
The generated fold lists all 38 effect nodes.
The generated success collection supplies five cases for every successful source lookup.
The equations use `interpAt`, including its actual completed-fiber view.
The model extraction preserves the scenario declaration names and statements.

## Verification

| Command | Result |
| --- | --- |
| `LEAN_NUM_THREADS=3 lake build Test.Dogfood.Proofs.HostTimeoutSource Test.Dogfood.Scenario.Timeout Test.Dogfood.Proofs.TimeoutCounterexample Test.Dogfood.Proofs.HostJournal` | passed, 1063 jobs |
| `LEAN_NUM_THREADS=3 lake env lean docs/research/2026-10-10-goals-packet/codex/TimeoutSourceAudit.lean` | passed: 348 declarations within `[propext, Quot.sound]`, no planned goal or dependence |

Changed files: `HostPayloads.lean`, `HostTimeoutSource.lean`, `Timeout.lean`, and `Timeout/Model.lean` under `Test/Dogfood`.
The audit reader and this receipt also change.
The coordinator already owns the identical unused-argument repair in `RaceFirst.lean`.
This commit excludes that local repair and the earlier untracked `KernelRfl.lean` helper.

## Remaining closure

The command invariant must correlate each source location with its lexical environment.
It must cover all current code, saved continuations, pending resumes and forced yields.
It must retain successful-body membership in race acceptance and cleanup publication.
The full command and decision lifts must establish those facts from the actual native load.
The root reader must then connect its returned body to the call's applied receipt.
The retry and cleanup observations additionally need count-cell and completion-log preservation.
These are universal obligations over admitted histories, rather than bounded evaluations.
The coordinator runs the reached behavior gates and owns imports and register placement.
No push occurs.
