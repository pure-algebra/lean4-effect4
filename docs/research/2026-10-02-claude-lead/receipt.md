# Lead implementation, Claude (2026-10-02, after the owner's hand-back)

Base `53caad0f98447c21cce952520ae97b0c1efb8cd2` (main and `codex/proofs-lead`, clean). Branch
`claude/proofs`, fast-forwarded from `247d7487` after checking status and ancestry. No push. The
owner ratified the three contract repairs "as recommended" (2026-10-02): the weak enrollment
bound (row 134 (e)), callback-only typing for the scope-exit marker, and the race-correlated
alternative for a yield-wrapped registration marker. Compiler lane: one `lake` at a time,
`LEAN_NUM_THREADS=1`, runner and logs in the session scratchpad (`run.py`, `logs/<label>.{log,json}`).

## Slice 1 — queued enrollment bound (`E4-TYPED-CE-032`, row 134 (e))

**First:** `ConfigTyped` is strengthened. `EnrollRaceOk` requires `child.value < m.nextId` beside
its unchanged conditional compatibility; a missing old child stays admitted and inert. No machine,
world-order or `StepPreserves` change; no presence requirement.

Placement. Concept 4 (reactive scheduling, the configuration invariant `I`); question
`M6Ledger.step_launch`, whose current statement the checked witness refutes; the bound is the
clause the launch producer keeps (its enrollment names the child it just allocated at the old
counter). Consumers: `QueueOk.enroll`, `enrollRace_preserves` (projects the compatibility
conjunct), the queue transports. Not established: `launch_preserves`, which still owes the
producer's incremented counter, lookup agreement below the old bound for retained bookkeeping,
and the world extension at the new child; a global `ObsView` is false across allocation.

Changes (Codex's staged patch, applied unchanged after its five source hashes matched):
`Typed/Scheduler.lean` (`EnrollRaceOk`), `Commands/Bookkeeping.lean` (`enrollRaceOk_view`,
`queueOk_transport` take `ids : m.nextId ≤ m'.nextId`; world/updateRace transports keep the
bound), `Commands/Observe.lean` (`enrollRaceOk_except`), `Commands/Race.lean`
(`enrollRace_preserves` projects `.2`), `Commands/Registration.lean` (`enrollRaceOk_off`,
`queueOk_transport_off`). Controls: new `Test/Program/EnrollmentBound.lean` (imported after
`RegistrationColumn` in `Test/All.lean`). Codex's control draft reused fixture proofs across a
changed machine; the structure clauses that mention the machine are rebuilt field by field
(`{ old with }`, the observer clause by hand, the queue as in the fixture). Records:
`REGISTER.md` `E4-TYPED-CE-032`; decisions row 134 status ("Clarified 2026-10-02").
Historical witness pinned unchanged: `witnesses/LaunchQueuedFuture.lean` (sha256 `2136e238…`,
log beside it; checked by Codex at `53caad0f`).

Commands and results (cwd `/Users/pooks/Dev/lean4-effect4-claude`):

- `lake build Effect4.Laws.Program.Typed.Commands.Observe Effect4.Laws.Program.Typed.Edits` —
  exit 0, 28.5 s; rebuilt Scheduler, Assembly, Bookkeeping, Finish, Race, Registration, Observe,
  Edits under `warningAsError`.
- `lake build Test.Program.RegistrationColumn` — exit 0 (the CE-028 battery is unchanged by the bound).
- `lake env lean -j1 -M6144 -DwarningAsError=true Test/Program/EnrollmentBound.lean` — exit 0;
  all 15 reports `[propext, Quot.sound]`.

The pinned witnesses of the other two checked refutations (`LoopMarkerYield.lean` sha256
`22085f4b…`, `RawScopeExit.lean` sha256 `2340ea64…`) are recorded with slice 2.
