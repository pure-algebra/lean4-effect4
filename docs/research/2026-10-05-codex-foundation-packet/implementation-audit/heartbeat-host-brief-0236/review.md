# HOST brief: observation connector

Snapshot: `eb29f4a997551e5fdffa800e8886e5bc99ed2ce4`.
Evidence: bounded source review. No build, runtime, generator or UI action occurred.

## One clarification before dispatch

The brief's acceptance asks for the whole scenario observation on the host.
Its concrete comparison procedure currently specifies less.
Assignment item 3 compares a Lean replay observation with the scripted Lean observation, then compares the host exit with Lean's exit.
That does not independently measure the rest of the host observation.
This is a missing design obligation, not an implementation defect in an unfinished seat.

### Exact missing fields

`Workers.observe` reads assignment and cleanup logs from private Ref cells 2 and 1.
It also reads the full `Run.Work`, including runnable fibers, armed owners and timers.
The existing keyed recorder observes external calls, reply receipts and applications.
It associates runtime fibers when they make an external call.
It does not expose those private Ref values or every runtime fiber and scheduler field.

`Timeout.observe` additionally reads the attempt counter, cleanup log and per-fiber timers.
`Atomic.observe` reads full Window and Account records, each request's exit and the cleanup log.
The clock boundary can control time but currently exports no timer observation with a semantic fiber mapping.
Those fields cannot be filled from Lean replay and then described as host measurements.

`run-keyed.ts` writes actual host exit, call associations and external-resource snapshots.
`check-keyed.ts` compares that host exit and the recording's application sequence against Lean's replay.
Its pending and outstanding checks inspect the replay result.
The proposed scenario observations contain additional host facts beyond that existing comparison.

### Smallest revision

Add one required table to the design note before selecting the first script.
For each field, name its independent host measurement, serialization, identity mapping and observation checkpoint.
Use the same Observation type and keep each source of evidence explicit.
A field read only from Lean replay is replay evidence, not host evidence.
If a field has no permitted host reader, mark that scenario's whole-observation comparison waiting.
Do not silently substitute exit equality or a projected observation for acceptance.

Reuse the keyed recorder for calls, receipts and applications.
Extend its existing observer or binding surface only where that actually exposes a scenario field.
Do not add a second runner or change the scenario program solely to manufacture observable values.
If private-state access needs instrumentation beyond the brief's fence, ask the coordinator to settle that narrow instrumentation contract first.

### Discriminating control

Use a host-only fault that drops one assignment or cleanup update while preserving the root exit.
The full observation check must fail at that field.
A changed Lean expected observation does not test that connector.
A moved recording tests replay validation, which is a different boundary.
This is a proposed acceptance control; it was not executed here.

## Reuse and scope

Placement: the scenario's existing claim, `host-session-protocol` R6 and `translation-simulation` R8.
Consumer: the keyed scenario comparator and its finite host-run receipt.
Reach: one printed module, one supported script and one recorded schedule on the pinned release.
It establishes no general host adequacy, scheduler liveness or equality beyond the measured observation.
Routing is the appropriate first cut because its observation uses the root exit, repository calls and session refusals.
Its refusal outcome still needs an explicit host-versus-replay evidence label.
Workers requires the additional private-state and work observation mapping before whole-observation acceptance.

The recorder's current `finish` also rejects live calls or stored replies and appends a terminated flush.
A live-prefix scenario needs a named snapshot/export path, or an explicit unsupported-script entry in the design note.
It must not be completed artificially merely to obtain a recording.

## Completion

Only the brief and named observation/recorder sources were reviewed.
No source was changed. The source hashes are in `receipt.json`.
The prior Queue premise advisory is separately marked resolved by its new active source.
