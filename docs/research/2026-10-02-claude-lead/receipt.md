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

### Slice 2a follow-ups (Codex's scope-callback review, applied with 2b)

`Test/Program/ScopeExitCallback.lean` gains `absent_scope_refused`: the producer's well-shaped code
is not typed where scope 0 is absent, so presence is still tested at the run position now that the
raw marker is refused independently of presence. `FramesNotKripke`'s projection prose is narrowed to
stacks with no `onExit false` resume slot (its premise). The `scopedResume` and `TypedProg`
docstrings no longer say the callback "delivers the same exit": a finalizer's failure may combine
with it when the scope closes; the frame types the carried exit. Codex's reuse points for typing
`prepareScopedExitR` (`closeScopeUnsafeR`'s three cases with `FinalizerTyped`/`lone_of_snapshot` and
`closeWalk_typed`, the cleanup bind through outer guard associativity ending at `finishFinalizer`)
are recorded for the evaluator proof; none is implemented here.

## Slice 2b — registration callbacks as correlated arrows (`E4-TYPED-CE-033`, row 188 (b))

**First:** a host's saved stack is now a typed path, `HostStack` (`Typed/Scheduler.lean`), with
ordinary frame arrows and correlated registration arrows (every success answer returns race `r`'s
marker; `r` exists with this host; a failure skips into the rest at the token's declared type).
Every consumer reads it: `CodeOk` (in `LiveCode`/`ReadCode`), `ActiveDelivery`, and `StackReply`
(so the reply consumers `afterInterrupt`, `raceCancel`, `closeParAwait` and the registration's
delivery carry it). The generated position clause reads the machine-free shape, `PositionStack`.
`ConfigTyped` admits more stacks (the injected callbacks); no `StepPreserves` premise, no machine
change.

The design went through two checked-by-review corrections before landing, both from Codex:
1. a disjunction placed only in the code clauses (`CodeOk`) left the reply consumers on plain
   stacks: typed code above a stored callback (`interruptAll []`) queues `afterInterrupt`, whose
   reply would have to cross the callback (consumer-check);
2. a single distinguished callback is not closed under a second injection over a stored one
   (closure review); the inductive path composes any number.
Both cases are positive controls now. The generated position clause could not be left on plain
`StackAccepts` either: typed code above a callback can force the callback's input type inhabited, so
the position clause gets its own machine-free registration arrow; its one code-building consumer
(the applied interrupt in `Bookkeeping`) now takes its stack from the fiber's correlated clauses
(`code`, or the registration's reply stack).

Placement. Concept 4 (the configuration invariant `I`); question `M6Ledger.step_loop` (the
injection) and, through the reply consumers, every command that installs a reply over a host stack.
Consumers: the walk's success arm installs the marker over the arrow's rest (`RegistrationState`
reads that rest through `StackReply`), its failure arm continues at the token type. Not
established: `step_loop` or `step_deliver`; the walk's typing over `HostStack` (an extension of
`popR_typed`) is the evaluator proof's next obligation.

Changes: `Typed/Scheduler.lean` (`HostStack`, `CodeOk`, `PositionStack`, `RacesKept`, the transports,
`hostStack_push`, `StackReply` over `HostStack` with the machine, `stackReply_races`,
`commandDelivery_races`), `Typed/Assembly.lean` (`SavedPosition` over `PositionStack`,
`ActiveDelivery`/`LiveCode`/`ReadCode` over the new clauses, `activeDelivery_races`,
`registrationState_races`, `readCode_races`), `Commands/Bookkeeping.lean` (`FiberTyped.delivery`/`code`/
`registration`, `delivery_races`/`code_races`, `configTyped_rupdate_code` beside
`configTyped_rupdate_gen`, the transports carrying `RacesKept`, the applied interrupt),
`Commands/Finish.lean`, `Commands/Race.lean` (`configTyped_cons_loop` and `configTyped_rupdate_owner`
take `CodeOk`; `afterInterrupt`, `closeParAwait` over `HostStack`), `Commands/Registration.lean`
(`hostStack_raceFinalizer`; both branches over `HostStack`), `Commands/Observe.lean`. Tests adjusted
without weakening a statement: `FitsOrder`, `M6Capstone`, `StaleCode`, `EnrollmentBound`,
`FramesNotKripke`, `RegistrationColumn`, `WaiterColumn`, `TimerColumn`. New controls
`Test/Program/RegistrationYield.lean`. Witness pinned unchanged: `witnesses/LoopMarkerYield.lean`
(sha256 `22085f4b…`).

Commands and results:

- `lake build Effect4.Laws` — exit 0 after the last production edit (`race-tests-07`).
- `lake build` of the 38 test modules reading the changed clauses (the 18 of slice 2a and the 20
  that read `ConfigTyped`/`MachineTyped`/`TypedState`/`StackReply`) — exit 0 (`race-tests-07`,
  `race-tests-08`).
- `lake env lean -j1 -M6144 -DwarningAsError=true Test/Program/ScopeExitCallback.lean` — exit 0;
  `live` axiom-free, six reports `[propext, Quot.sound]`.
- `lake env lean -j1 -M6144 -DwarningAsError=true Test/Program/RegistrationYield.lean` — exit 0;
  all 15 reports `[propext, Quot.sound]`.

No whole battery (`lake build Test`), trust gate or generator was run.
