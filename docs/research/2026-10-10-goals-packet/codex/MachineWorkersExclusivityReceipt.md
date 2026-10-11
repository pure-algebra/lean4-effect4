# Initial worker exclusivity

The current frame contracts imply one live initializer before the gate exists.
The history producer must still establish those contracts at each command boundary.

Base: `7a5623443`.
The slice adds `MachineWorkersExclusivity.lean` and its audit in this directory.
It attaches `Effect4.Laws.Machine.AnswerFlow` to `src/Effect4/Laws.lean`.

Placement: store-typing R4 and scope-lifetime-finalization R11.
Question: the helpers serve `Workers.Assertions.logs_step` in `Test/Dogfood/Scenario/Workers/Assertions.lean`.
Reach: actual live stored frames, their current store, and distinct stored fiber identities.
Consumer: native allocation transport excludes another live initializer from changing the initial store lengths.
Limit: no source-history closure, cleanup count, progress, or outside-runtime agreement follows.

`frame_phase` projects the phase from the actual current code inside `AnswerFlow.FrameAt`.
`initial_owner` excludes the stable phase while the deferred store remains empty.
`live_owner` applies that fact to a stored live fiber.
`unique_live` uses the existing fiber lookup law to identify any two live stored fibers.
`other_exited` applies the actual root allocation stage to every differently named stored fiber.
Finished fibers need no current-code contract.

## Verification

Run with `LEAN_NUM_THREADS=3`:

```sh
lake build Effect4.Laws.Machine.AnswerFlow
lake env lean --root=docs/research/2026-10-10-goals-packet/codex -o .lake/build/lib/lean/MachineAnswerFlow.olean docs/research/2026-10-10-goals-packet/codex/MachineAnswerFlow.lean
lake env lean --root=docs/research/2026-10-10-goals-packet/codex -o .lake/build/lib/lean/MachineWorkersWriters.olean docs/research/2026-10-10-goals-packet/codex/MachineWorkersWriters.lean
lake env lean --root=docs/research/2026-10-10-goals-packet/codex -o .lake/build/lib/lean/MachineWorkersSlots.olean docs/research/2026-10-10-goals-packet/codex/MachineWorkersSlots.lean
lake env lean --root=docs/research/2026-10-10-goals-packet/codex -o .lake/build/lib/lean/MachineWorkersExclusivity.olean docs/research/2026-10-10-goals-packet/codex/MachineWorkersExclusivity.lean
lake env lean docs/research/2026-10-10-goals-packet/codex/MachineWorkersExclusivityAudit.lean
```

Every command passes.
The narrow library build reports 174 jobs.
The audit covers the shared library law, the actual worker allocation consumers, and the exclusivity helper.
It reports 135 declarations within `[propext, Quot.sound]`, zero modulo planned goals, and zero planned goals.
These are symbolic conditional proofs, not finite execution checks.
The original `logs_step` remains open.
No runtime or generated target changes.
