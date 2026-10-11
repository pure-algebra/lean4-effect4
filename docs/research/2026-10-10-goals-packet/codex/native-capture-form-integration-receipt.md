# Native captures and completed timeout forms

The original Workers history and both Timeout numeric goals remain open.
These integrations check their local producers against the existing consumers.

Base: `8e7b70f65`.
Integrated commits: `62210135f` and `afe972270`.
The landing commit records the exact changed paths.

Timeout retains the actual completed form result through native finalizer selection.
Its retry handler consumes the published singleton declared failure.
This follows the settled owner ruling and retains the four-attempt bound.
No original scenario statement changes.

Workers retains actual acquisition captures through scope registration and close selection.
`ScopeFields` shares the scope census with `NativeScopeStore`, whose existing theorem statements remain unchanged.
The Workers current-code and history premises remain explicit.

With `LEAN_NUM_THREADS=3`, `lake build` checks these targets:

- `Test.Dogfood.Proofs.HostTimeoutNumberFormFamily`
- `Test.Dogfood.Scenario.Timeout`
- `Effect4.Laws.Program.NativeReplies`
- `Effect4.Laws.Program.ReleaseCustody.Execution`

The build succeeds with 1196 jobs.
The first invocation names a nonexistent proof target; the corrected invocation above succeeds.
`NativeCaptureFormIntegrationBuild.log` retains the corrected output.

`lake env lean` independently builds `MachineWorkersNativeSlots.lean` and `MachineWorkersCapturedSlots.lean` from this directory.
The commands use this directory as `--root` and write their modules under `.lake/build/lib/lean`.
`WorkerNativeSlotsIntegration.log` and `WorkerCapturedSlotsIntegration.log` retain their successful, empty outputs.

`lake env lean` checks `TimeoutNumberFormFamilyAudit.lean` and `MachineWorkersNativeSlotsAudit.lean`.
The Workers audit uses this directory as `--root`.
The audit outputs report 168 and 217 declarations, respectively, within `[propext, Quot.sound]`.
Both report zero planned goals and zero dependencies on planned goals.
The adjacent `.out` files retain those outputs.

`Test/All.lean` imports the new Timeout family reader.
No executable behavior changes, and no additional behavior gate is reached.
The evidence establishes conditional symbolic laws, not complete histories or outside-runtime agreement.
