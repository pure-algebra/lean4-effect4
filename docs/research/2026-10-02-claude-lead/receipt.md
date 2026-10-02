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

## Slice 2a — the scope-exit callback at its run position (`E4-TYPED-CE-034`, row 188 (a))

**First:** `TypedProg`'s general `scopeExit` constructor is gone. The scope's exit callback is typed
only at the run position of the `onExit false` guard the `scoped` arm installs
(`TypedProg.scopedGuard`) and of the slot that guard saves (`FrameAccepts.scopedResume`). Typed code
that contained a raw marker anywhere else is no longer typed; the producer's own code now is
(the old constructor demanded its `pure` continuation at every answer, so it never was).

Placement. Concept 4 (the configuration invariant `I`); questions `M6Ledger.step_deliver` and
`M6Ledger.step_loop` (both run the evaluator core on current code). Reach: `TypedProg`,
`FrameAccepts`, `FrameProtocols` (new field `scopeExit`, instantiated as `ScopeLive ∧ ServicesFit`
of the restored context), the walk's outcome `WalkTyped` (new `CallbackSaved`). Consumers: the
`scoped` arm and the post-walk glue (`prepareScopedExitR`) of the two evaluator goals; the
positive helper `scopedGuardBind_typed` is the `scoped` arm's code typing. Not established:
either goal; `prepareScopedExitR`'s typing (the scope close and the finalizer program) is the
next obligation of the walk's callback outcome, and the `interpRAt`/`interpR` hook connection
(`deliver-review.md` G2) stays a missing proof.

Changes: `Typed/Contracts.lean` (`scopeExitCallback?`, `scopeExitCallback?_bind`,
`FrameProtocols.scopeExit`, `FrameAccepts.scopedResume`, `frameAccepts_mono`), `Typed/Residual.lean`
(`TypedProg.scopedGuard` replacing `scopeExit`; `fiber_inv`; `guard_inv` now two-way, with
`guard_inv_of_ne` and `guard_inv_ordinary`; `frameProtocols`; `guard_frame`; `typedProg_mono`;
`typedProg_rows_append`), `Typed/Seq.lean` (`close_typed`, `typedProg_widen`, new
`scopedGuardBind_typed`), `Typed/Stack.lean` (`CallbackSaved`, `WalkTyped`, `walk_saved`,
`popR_typed`'s `scopedResume` arm), `Typed/Assembly.lean` (docstrings). Tests adjusted to the
two-way inversion and the new frame arm without weakening a statement: `AsyncHookContract`,
`AwaitLoad` (its red fixture's expected message unchanged), `FitsOrder`, `ProtocolPosts`,
`TypedControl`, `TypedDenotation` (`guardBind_body` takes either arm's body), `ValueMembership` and
`FramesNotKripke` (historical hooks get `scopeExit := False`, so their judgments are unchanged;
`frameAccepts_now`/`stackAccepts_now` take the absence of a `scoped` slot, which the one-world
judgment never had), `M6Capstone` (`callback_typed` flipped to `callback_untyped`; `callback_refused`
and `input_refused` now follow from it). New controls `Test/Program/ScopeExitCallback.lean`.
Witness pinned unchanged: `witnesses/RawScopeExit.lean` (sha256 `2340ea64…`); the review
`deliver-review.md` is the source review written before the check.

Commands and results:

- `lake build Effect4.Laws` — exit 0 (39.3 s after the last production edit; every `Typed`
  dependent of `Contracts` rebuilt: Denotation, Scheduler, Assembly, the five command modules,
  Edits, LayerArm, the root).
- `lake build` of the 18 test modules that read the changed judgments (AsyncHookContract,
  AwaitLoad, FitsOrder, M6Capstone, ScopePresence, StaleCode, ValueMembership, FramesNotKripke,
  H2PartOne, LoadedAdmission, ProtocolPosts, RegistrationColumn, TypedControl, TypedDenotation,
  TypedProgBindRed, TypedProgRows, TypedResidual, TypedStack) — exit 0.
- `lake env lean -j1 -M6144 -DwarningAsError=true Test/Program/ScopeExitCallback.lean` — exit 0;
  `live` axiom-free, the other five `[propext, Quot.sound]`.
