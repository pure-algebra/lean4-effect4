# Worker initializer integration

The actual initializer and its live-owner reader compile together on the coordinator branch.
The original log-writer history remains open.

The agent's `06571638e` lands as `6dd60c882`, following shared callback commit `ca7d9000d`.
`MachineWorkersInitializerReceipt.md` records the source placement and exact conditional scope.

The following commands use `LEAN_NUM_THREADS=3` and exit zero:

- `lake env lean --root=docs/research/2026-10-10-goals-packet/codex -o .lake/build/lib/lean/MachineWorkersSlots.olean docs/research/2026-10-10-goals-packet/codex/MachineWorkersSlots.lean`.
- `lake env lean --root=docs/research/2026-10-10-goals-packet/codex -o .lake/build/lib/lean/MachineWorkersExclusivity.olean docs/research/2026-10-10-goals-packet/codex/MachineWorkersExclusivity.lean`.
- `lake env lean --root=docs/research/2026-10-10-goals-packet/codex docs/research/2026-10-10-goals-packet/codex/MachineWorkersExclusivityAudit.lean`.

Audit: 167 declarations within `[propext, Quot.sound]`, zero modulo planned goals, zero planned goals.
`WorkersInitializerIntegration.log` and `WorkersInitializerIntegrationAudit.out` retain the outputs.
These conditional symbolic proofs establish no completed scenario or outside-host observation.
