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

## Documentation checkpoint (after slice 2b)

`docs/STATE.md`'s lead paragraph names Claude as the lead implementation seat with Codex reviewing
and supporting (Codex's request), and lists the three contract repairs. `docs/core/semantics.md`:
Concept 2's account of the scope-exit marker (row 188 (a)); Concept 4 §5 on the two administrative
markers and the typed-path host stack (row 188 (b)). Regenerated, not hand-edited:
`generated/semantics.{md,json}` (inherited theorems 1138 → 1157) and
`docs/core/architecture-map.html`.

- `lake build Effect4.Laws Test.Program.TypedProgBindRed Test.Program.ProtocolPosts
  Test.Audit.SemanticsCensus Drivers.Semantics Drivers.SemanticsControls Tools.ProofMapFixture
  Tools.Architecture` — exit 0 (39 s).
- `python3 scripts/check-semantics.py --generate generated` — exit 0 (92.7 s).
- `lake env lean -j1 -M6144 -DwarningAsError=true --run tools/Tools/Architecture.lean` — exit 0;
  then `--check` — exit 0 ("current", 658 Lean files).
- `python3 scripts/check-semantics.py` — exit 0 (253.7 s), after the `semantics.md` edit.

## Slice 3 — queued observe sources below `nextId` (`E4-TYPED-CE-035`, decisions row 189)

**First:** `ConfigTyped` is strengthened by a new proposed rule, decisions row 189, separate from
row 134 (e)'s ratified enrollment bound though of the same kind: a queued `observe`'s source is
below `nextId` (`QueueOk.observer`, `HeadOk.observer`, beside the unchanged `ObserverCommandOk`).
Proposed by the lead coordinator; the owner ratified it ("ratified as recommended", 2026-10-02),
after which it landed on main. Codex's command-polarity review independently found the same single
negative read (`finish`/`observe` on Γ, `resume` on Θ; only `observe`'s source unbounded).

Found while placing `launch_preserves`: allocation extends the fiber table, and every queued
command's typed reading was checked for an antitone read at a future fiber id. Exactly one exists:
`RCmdOk`'s `observe` arm (`∀ ty, Γ source = some ty → ExitOk ty exit`). The checked falsifier
`witnesses/LaunchQueuedObserve.lean` (the registration fixture with one unlaunched entrant and a
queued `observe ⟨1⟩ (success "x") (untrackChild root)` at `nextId = 1`) refutes the unchanged
`M6Ledger.step_launch` at `96415122` (`config_typed`, `launch_false`, both `[propext, Quot.sound]`;
log `observe-falsifier-03`). The other readings are positive (`FiberColumnsBelow`, `StackReply`,
`AfterInterruptReply`), bounded (`EnrollRaceOk`, countdown targets, live sets), or read Θ, which
allocation does not extend.

Placement. Concept 4 (`I`); question `M6Ledger.step_launch` (and every allocating evaluator arm).
Consumers: `queueOk_transport`/`_world`/`_emit`/`_off`, the `except` and `updateRace` queue
constructions, `observe_preserves` and the countdown walk (`.2`), `configTyped_observes`
(producer: `finish` queues its observers at its own id, `FiberTyped.below`). Not established:
`launch_preserves`, which still owes the allocation transports.

Changes: `Typed/Assembly.lean` (`QueueOk.observer`, `queueOk_emit`), `Commands/Bookkeeping.lean`
(`HeadOk.observer`, the queue transports), `Commands/Finish.lean` (`configTyped_observes`,
caller), `Commands/Registration.lean`, `Commands/Observe.lean`; tests `M6Capstone` (`.2` at two
refusals), `EnrollmentBound` (`ObserveSource` controls; imports `Commands.Observe`).

- `lake build Effect4.Laws` — exit 0 (`observe-build-06`).
- `lake build` of the 16 affected test modules — exit 0 (`observe-tests-01`).
- `lake env lean -j1 -M6144 -DwarningAsError=true Test/Program/EnrollmentBound.lean` — exit 0;
  18 reports `[propext, Quot.sound]` (`observe-controls-02`).

## Slice 4 — one frame path for the saved-stack judgments

**First:** no judgment changes meaning. The owner asked for reuse of the algebra abstractions to cut
drift and verbosity; Codex's reuse review agreed on the factoring. `Contracts.FramePath Edge` is the
free-category path over an edge relation (decisions row 48: existential middle types), with `map`,
`append`, `split` proved once and `StackAccepts` shown equivalent to its instance
(`framePath_of_stackAccepts`, `stackAccepts_of_framePath`). `HostStack` and `PositionStack` are now
instances (`HostEdge` = ordinary frame or `RegistrationArrow`; `PositionEdge` = ordinary frame or
`PositionArrow`), and their transports and conversions are edge maps through `FramePath.map`
(`hostStack_mono`, `hostStack_races`, `hostStack_of_stackAccepts`, `positionStack_of_host`, …).
The edge maps carry the semantic proofs (`registrationArrow_mono`, `registrationArrow_races`,
`positionArrow_of_registration`, one-way). `StackAccepts` itself is unchanged.

Placement: Concept 4 (row 188 (b)'s judgments), also Concept 7's composition account; consumers
`step_loop`/`step_deliver` (the walk over `HostStack`) and every command already proved. No new
theorem about programs. `#frame_rules` (Codex's pointer) rebuilds a state record with one field
changed at a fixed world; allocation changes the fiber table, the counter and the world together,
so it will serve only the untouched record clauses there.

Changes: `Typed/Contracts.lean` (`FramePath` and its laws), `Typed/Scheduler.lean` (the row 188 (b)
block rewritten over it); tests `RegistrationYield` (arrows written as `.cons (.inr (.mk …))`),
`M6Capstone` (`input_refused` cases on the edge).

- `lake build Effect4.Laws` — exit 0 (`path-build-01`); every Typed module rebuilt unchanged.
- `lake build` of the 18 test modules reading the stack judgments — exit 0 (`path-tests-01`);
  `RegistrationYield`'s 15 reports `[propext, Quot.sound]`, no `sorryAx` in the log.

## Slice 5 — `launch` keeps `I` (`M6Ledger.step_launch`), and the read-site transports made general

**First:** `M6Ledger.step_launch` is proved (`launch_preserves`, `Typed/Commands/Launch.lean`); the
ledger stands at 4 open of 20 (`loop`, `deliver`, decision preservation, reachable typing), and
`Commands/Observe.lean`'s report runs at ceiling 4. No judgment changed meaning. Two transports in
`Scheduler.lean`/`Bookkeeping.lean` that enumerated all twenty commands (`commandDelivery_races`,
`commandDelivery_world`) are replaced by one monotonicity lemma, `commandDelivery_mono`; their
callers (`queueOk_emit`, `queueOk_world`) moved.

The step (`Machine/Fibers.lean:1879-1896`, rc.112 `:1520-1528`): on the allocating arm the entrant
is appended at the old `nextId` (`allocR`, `spawn`'s record update, `:948-966`) and the world declares
it (`World.addFiber`) at the race's result type: the program is typed at a type whose columns are
below it (`RacePayload.programs`), widened there (`typedProg_widen`), and the type is closed because
the race token's declaration is (`WorldValid.tokenClosed`). The race loses that program
(`configTyped_updateRace`), and the entrant's evaluation and enrollment join the queue ahead of the
next launch (`configTyped_cons_evaluate`, `configTyped_cons_enroll`, with the new child's columns at
its own declaration and the race's registration completion still queued). Every other arm drops the
head (`configTyped_tail`).

The allocation transport (`configTyped_alloc`) is assembled from the per-fiber and machine-wide split
(`machineTyped_of`): `machineWide_alloc`; `fiberTyped_alloc` for each old fiber (its own reads at its
id, below `nextId`; observers by `storedObserverOk_alloc`; stacks by `hostStack_mono`/`_races`);
`fiberTyped_child` (idle, unparked, no record, an empty stack, its code at its declaration);
`readCode_alloc`; `queueOk_alloc`. Each negative read of the fiber table is at an id below `nextId`:
the clause's own fiber, live sets and countdown targets (row 134 (e)), queued enrollments (row
134 (e)), queued observe sources (row 189), a queued `finish`'s active owner. Positive reads are kept
by the extension.

General lemmas, at the owner's direction during this slice ("if we can do something general and not
do a bunch of pattern matching … we're obviously going to want to do that"). A transport is stated
once as monotonicity in what the predicate observes, and each edit is an instance:

- `commandDelivery_mono` (`Scheduler.lean`): delivery reads the world only positively, the machine
  only at the command's owner (`Guard.commandOwner`), and races only through host and token; it moves
  along any world extension to a machine that agrees at the owner and keeps the races. Instances: the
  trace edit (`queueOk_emit`), a fixed fiber table (`queueOk_world`), the allocation
  (`commandDelivery_alloc`). Helpers `fiberListColumns_mono`, `afterInterruptReply_mono`,
  `stackReply_mono`.
- `commandAuthority_mono`: authority is monotone in the fiber table (old lookups found unchanged,
  races kept). Instance: `commandAuthority_alloc`, a one-line term.
- `commandOwner_found`: a queued command's owner exists (active, or the host of the race it
  completes). It gives the allocation's owner agreement.
- The remaining case splits list only the constructors that read and close the rest with one
  catch-all alternative (`| _ => trivial`), as the 2026-09-18 owner rule asks of proofs.

The theory behind it is the store-typing weakening lemma of the references chapter of TAPL (and
Software Foundations' store weakening, per Codex's `theorem-reuse-scout/map-literature.md`; citation
not checked here against a vendored copy). A judgment consults the store typing only at locations
the term names. Every such location is allocated, so typing survives any extension. Here
the positive reads are Kripke-monotone outright, and a negative read (`∀ ty, Γ id = some ty → …`) is
stable exactly where `id` is already declared. Codex's packet states the same thing as observational
congruence: a predicate that factors through equal observations transfers, absent lookups included.

A possible consolidation, recorded for the owner and not proposed for landing: one queue clause,
"every fiber id a queued command names literally is below `nextId`", in place of the per-command
bounds of rows 134 (e) (enrollment) and 189 (observe source). Codex's follow-up review
(`transport-consolidation-review/review.md`) corrects my first statement of it. It would be a new
admission policy, not a consequence of `launch`. It would not by itself make `QueueOk` monotone across
world or record changes: `resume` reads Θ negatively, and race- and host-derived dependencies are not
literal ids (`EnrollRaceOk`'s live set). The ratified missing-old behaviour (an absent old source stays
admitted and inert) must be kept. The existing view and stack-edit transports still serve edits that
change a fiber record, so they are not redundant. Codex also notes a small simplification for the next
touch: the Γ-extension premise of the new monotonicity lemmas is already inside `w.leHost w'`.

Placement (the five, for `launch_preserves` and its helpers):
1. Concept 4 (the configuration invariant `I`), property: step preservation for `launch`.
2. Question: ledger goal `M6Ledger.step_launch`. The helpers are steps of it. `configTyped_alloc`
   and its parts also serve every allocating evaluator arm (`fork`, `forkIn`, `forkScoped`, the
   parallel close) under `step_loop`/`step_deliver`. `commandDelivery_mono` and
   `commandAuthority_mono` serve every queue transport.
3. Reach: `StepPreserves root rootTy (.launch raceId)` for every input satisfying `ConfigTyped`, at
   the reference runner's evaluator (`termEvaluatorFor`). Bounded by decisions rows 134 (e), 188 (b)
   and 189, and register lines CE-032 and CE-035.
4. Not established: progress; that the entrant's evaluation keeps `I` (that is `evaluate`, `loop`
   and the evaluator goals); reachability of the inputs; the host boundary (no host answer is in
   scope, row 95).
5. Unlocks: one of the five open M6 command goals on the M5 → M6 → M7 spine. The allocation transport
   is the piece `step_loop`'s fork arms need.

Control: `Test/Program/LaunchEntrant.lean`. It takes RegistrationColumn's typed configuration with
one unlaunched entrant moved onto its race by the general race edit, and the two commands
`registerRace` queues. The actual step allocates (`allocates`, by `rfl`: the queue is
`[evaluate ⟨1⟩, enrollRace 0 ⟨1⟩, launch 0, registrationDone 0 false]`, `nextId = 2`, two fibers,
the race's programs empty), and `launch_preserves` types the result (`result_typed`). The original
witnesses stay refused (`EnrollmentBound`: `Future.config_refused`, `ObserveSource`).

Changes: new `src/Effect4/Laws/Program/Typed/Commands/Launch.lean`. Edited: `Typed/Scheduler.lean`
(the general lemmas; `commandDelivery_races` removed), `Typed/Assembly.lean` (`queueOk_emit` caller;
`step_launch` docstring; its `#proof_wanted` removed), `Commands/Bookkeeping.lean`
(`commandDelivery_world` removed; `queueOk_world` caller), `Commands/Observe.lean` (imports `Launch`;
ceiling 4), `src/Effect4/Laws.lean` (imports `Launch` after `Registration`), `Test/All.lean`
(`LaunchEntrant` after `RegistrationYield`). New `Test/Program/LaunchEntrant.lean`. Records:
`Test/Counterexamples/REGISTER.md` (CE-032, CE-035), `docs/STATE.md`.

- `lake env lean -j1 -M6144 -DwarningAsError=true src/Effect4/Laws/Program/Typed/Commands/Launch.lean`
  — exit 0 (`launch-18`).
- `lake build Effect4.Laws.Program.Typed.Commands.Observe Test.Program.RegistrationColumn` — exit 0
  (`launch-19`); the M6 report passes at ceiling 4.
- `lake build Effect4.Laws Test.Program.LaunchEntrant Test.Program.EnrollmentBound
  Test.Program.RegistrationYield` — the four built; the fifth target was named at a wrong path
  (`launch-22`). It was rebuilt at its real path with the other 15 test modules importing the
  changed modules: exit 0 (`launch-23`).
- Axioms (`launch-axioms`): `launch_preserves`, `commandDelivery_mono`, `configTyped_alloc`
  `[propext, Quot.sound]`; `commandAuthority_mono`, `commandOwner_found` `[propext]`.

Open after this slice: the walk's typing over `HostStack` tails (`CallbackSaved`/`WalkTyped`, Codex's
note), `prepareScopedExitR`, the G2 hook-law gap (`interpRAt` against `interpR`), then `step_loop` and
`step_deliver`. Codex's theorem-reuse packet (`/private/tmp/codex-lead-2026-10-02/theorem-reuse-scout/`)
proposes a `popR` prefix/suffix factoring for the walk and a `PointTyped`/`completed_mono` route for
G2. It is evidence to check at those steps, not kernel-checked. The generated reports
(`generated/semantics.*`, the architecture page) lag the ledger by this goal until the next docs
checkpoint.

## Slice 6 — the walk over a host stack

**First:** no judgment changes meaning. `HookLaws` is now the conjunction over worlds of a one-world
interface, `HookLawsAt` (the same three fields at a fixed world). `popR_typed` is `popR_typedAt` at
each world, and `hookLaws_interpR` is unchanged in content. The walk reads the hook laws only at its
own world; the resumed tails' later-world closure is the protocols' own. This is the interface G2
needs: the machine's interpreter (`interpRAt root m.completedExits`) can only have hook laws at the
world where its completed view is typed.

The walk over a host stack (`Typed/HostWalk.lean`):
- `popR_cons` (Codex's `theorem-reuse-scout/path-review.md` §3, at the singleton prefix): a walk over
  `slot :: rest` is the walk over `[slot]`, then either `rest` appended below the frame it stopped
  in, or the walk over `rest` with the returned exit from the returned frame. Proved for every
  interpreter, by cases on the slot (`[propext]`).
- `popR_stack`/`popR_mk` (the walk ignores the stack field it is handed) and `popR_interrupts` (it
  never changes the recorded interrupt or the deferred flag; by `fun_induction popR`).
- `popR_hostTyped`: delivering a typed exit to a `HostStack` installs typed code (`CodeOk`), a scope's
  exit callback (`HostCallback`, `CallbackSaved` with a host tail) or a race registration marker
  (`HostMarker`, the correlation `RegistrationState` reads) over a typed remaining host stack, or
  completes typed at the final type. Ordinary frames reuse `popR_typedAt` on the singleton stack
  (the 200-line frame analysis is not repeated) and `FramePath.append` the host tail. A registration
  arrow installs its marker on a success and passes a failure by `RegistrationArrow.skip`.
- `deliverR_hostTyped` and `deliverR_shape`: the delivery to a fiber (the deferred-interrupt branch
  installs the pending cause as typed code; otherwise the walk), which changes only the frame and
  ends `continue_` or `finished`.

Placement:
1. Concept 4, property: preservation by `loop` and `deliver` (`semantics.md`'s step-loop and
   step-deliver properties); the walk serves their evaluator arms that deliver an exit (a bare exit,
   `unguard`, `finishFinalizer`).
2. Questions: `M6Ledger.step_loop` and `.step_deliver`. The equations and `popR_interrupts` are
   steps of `popR_hostTyped`, whose consumer is `deliverR_hostTyped`, whose consumers are those
   arms.
3. Reach: every interpreter with `HookLawsAt` at the walk's world; a `HostStack`, an exit typed at
   its input type, recorded-interrupt provenance. Rows 48, 135, 188 (a) and (b).
4. Not established: `HookLawsAt` for the machine's interpreter (G2, next); the typing of the scoped
   exit's cleanup that consumes `HostCallback` (`prepareScopedExitR`); the rest of the evaluation
   step and `settle`; progress.
5. Unlocks: the walk arm of `step_loop`/`step_deliver` over the stacks rows 188 (a)/(b) admit.

Controls: `Test/Program/HostWalk.lean`, two stacks from RegistrationYield delivered a success under
the reference hook laws. Two arrows: the first installs its marker over the second. An answer slot
above an arrow: the slot completes and the arrow installs its marker. Both reach `HostMarker`, the
other outcomes refuted there (`[propext, Quot.sound]`).

Changes: `Typed/Stack.lean` (`HookLawsAt`, `HookLaws` as its conjunction, `popR_typedAt`); new
`Typed/HostWalk.lean`; `src/Effect4/Laws.lean` (imports it after `Typed.Assembly`);
`Test/Program/FramesNotKripke.lean` (`hookLawsX_refused` reads `(laws world).iterator`); new
`Test/Program/HostWalk.lean`; `Test/All.lean` (after `LaunchEntrant`).

- `lake env lean -j1 -M6144 -DwarningAsError=true src/Effect4/Laws/Program/Typed/HostWalk.lean` —
  exit 0 (`walk-12`); axioms `popR_hostTyped`, `deliverR_hostTyped`, `popR_interrupts`
  `[propext, Quot.sound]`, `popR_cons`, `deliverR_shape` `[propext]`.
- `lake env lean … Test/Program/HostWalk.lean` — exit 0 (`walk-14`).
- `lake build Effect4.Laws Test.Program.FramesNotKripke Test.Program.TypedStack Test.Program.H2PartOne
  Test.Program.HostWalk Test.Program.LaunchEntrant` — exit 0 (`walk-15`; `walk-09`, `walk-13` rebuilt
  the chain through `Scheduler` and `RegistrationYield` first).

## Slice 7 — G2 and the loop/generator hook contract (controls; repair proposed, not landed)

**First:** the loop/generator part of the frame contract has three kernel-checked gaps, and their
repair is a contract change for the owner (decisions row 190, proposed). The walk (slice 6) is
unaffected. Nothing in `src/` changed in this slice.

Codex's hook-view-support packet (priority note, `protocol-review.md`, `producer-review.md`) was
read before any design. It proposed the first two controls from source reading and asked that they
be kernel-checked, with a finishing-loop positive control, before choosing a producer. Checked at
`ed83ea23`, `docs/research/2026-10-02-claude-lead/witnesses/LoopProtocols.lean` (log `g2-04`, every
report `[propext, Quot.sound]`):

| Control | Result |
| --- | --- |
| `Endless` (CE-036) | The checker admits `iterate (some unit) unit true unit unit (succeed unit)` at `pure unit` from the root (`decide +kernel`). Entry and every resume answer `continue unit (pure (success unit))` under the same loop name (`rfl`). `no_protocol`: no `LoopProtocol` at an input type admitting `unit`, by `LoopProtocol.rec` with both motives (the continue's body is typed at the tail's input type, so the tail admits `unit` again). `no_code_after_entry`: the frame the entry leaves (`entry_eq`) has no `CodeOk` at any world. |
| `Finishing` | The same loop with a false test has a protocol (positive control). |
| `Cursor` (CE-037) | A checked Boolean-cursor loop entered with `unit` meets `fiberPre`'s loop arm (`pre_admits`, it reads only `PointTyped`); its entry installs `badShapeExit` (`entry_current`), typed at no type (`bad_untyped`). |
| `View` (CE-038) | A loop whose point's own view holds a fiber's failure has a protocol at every world (`protocol`: the inline failure typed at `never`'s answer, the tail vacuous). Under the machine's interpreter at the empty view the body is `await` of that fiber (`empty_view`); at a world not declaring it, `HookLawsAt` fails (`no_hookLaws`) and the ordinary walk's premises hold while its conclusion fails (`walk_untyped`). |

The generator analogue of `View` was run by `#eval` only (`walkR` is defined by well-founded
recursion and does not reduce by `rfl`); it is not part of the evidence.

Against the existing goals:
- `M4Stack.popR_typed` and `M5Hooks.hookLaws_interpR`: unaffected (conditional, and the bare
  interpreter respectively).
- `M6Ledger.step_loop`: unprovable over the current contract. The evaluator's `loop` entry on the
  endless loop leaves a running fiber whose code clause (`ReadCode`, through the `loop` that `settle`
  queues) can hold at no world; on the Boolean-cursor loop entered with `unit` it installs
  `badShapeExit`. A full `StepPreserves` falsifier needs a `ConfigTyped` input fixture, not built.
- `M6Ledger.step_deliver` (and `step_loop`'s walk arm): the walk route needs `HookLawsAt` for the
  machine's interpreter, which the current protocols do not give (CE-038). A full falsifier would
  likewise need an input fixture.

Proposed (row 190):
- (a) The protocols in their postfixed (greatest-fixed-point) form: an invariant containing the
  frame and closed under one hook step. The old inductive protocol embeds one way; the endless loop
  is admitted, and an ill-typed body is still refused. This is Codex's priority-note candidate. The
  theory is the coinduction principle for postfixed sets, which Leroy and Grall's coinductive
  big-step semantics, §2, applies to inference rules; I have not reread the paper, and the citation
  is Codex's.
- (c) The step obligation over every completed view typed at the step's world, which gives
  `HookLawsAt` for `interpRAt root C` from the construction post's clause on `C`.
- (b) `fiberPre`'s loop arm adds the cursor's fit.
- The producers supply source-derived invariants.

Placement of the proposed work:
1. Concepts 2 (residual typing) and 4; property: admitted loop and generator continuations, and
   preservation by `loop`/`deliver`.
2. Questions: `M6Ledger.step_loop`/`.step_deliver`. A protocol-producer claim would be registered
   with the corrected contract; `M5Hooks.hookLaws_interpR` kept as history beside a goal for the
   machine's interpreter.
3. Reach: the unchanged checker and machine; rows 117, 135, 175.
4. Not established by any of it: termination, progress, fairness, a host result.
5. Unlocks: a non-vacuous generator/loop producer for M5 → M6, before decision preservation and
   reachable typing.

Changes: witness `docs/research/2026-10-02-claude-lead/witnesses/LoopProtocols.lean`;
`Test/Counterexamples/REGISTER.md` (CE-036, CE-037, CE-038, SEEDED); `docs/core/decisions.md` (row
190, proposed).

## Slice 8a — decisions row 190 (a) and (c): the protocols as greatest invariants over typed views

**First:** the frame contract for saved `iter`/`loop` slots changed meaning, as ruled. The inductive
protocols, the global `HookLaws` and `hookLaws_interpR` are deleted, per the owner's instruction at
the ruling: "This is all greenfield". Two ledger goals were restated:
- `M4Stack.popR_typed` takes `HookLawsAt` at the walk's world;
- `M5Hooks.hookLaws_interpR` is replaced by `M5Hooks.hookLawsAt_interpRAt`: the machine's
  interpreter has its hook laws wherever its completed view is typed.

The coalgebraic structure (`Typed/Contracts.lean`, `Greatest`). A step on predicates over states,
an invariant `I ⊆ F I` (a coalgebra of `F` in the order of predicates), and the greatest one,
`Greatest F`, the union of all of them (Knaster–Tarski). It is the dual of the free objects' folds:
`Eff` is the initial algebra with its fold, the protocols are the greatest invariant of the
interpreter's hook, itself a coalgebra on hook names (`iterNext`: name → value → done | halt |
resume code name'). Laws proved once:
- `coind` (an invariant lies below the greatest one);
- `unfold`/`fold`/`iff` (for a monotone step it is a fixed point);
- `coind_upto` (coinduction up to the greatest invariant: an invariant may close its tails in any
  known protocol, the shape a generator that ends in a close walk needs);
- `weaken` (a larger step, a larger invariant);
- `transport` (closure under any relation the unfolding respects).

`IteratorProtocol`/`LoopProtocol` (`Typed/Residual.lean`) are `Greatest (IteratorStep root)` and
`Greatest (LoopStep root)` over `IterState`/`LoopState`. Each step answers every fitting value at
every later world under every completed view typed there (`ViewTyped`, the construction post's
clause). It keeps the error-column equality and the requirement-row condition (rows 117 and 135),
with one intermediate type per resumed tail.

The aesop bank `Effect4.Coind` (`Laws/Auto/RuleSets.lean`) holds only finite-search rules:
- protocols move to later worlds (`iteratorProtocol_mono`, `loopProtocol_mono`, safe forward);
- the steps are monotone (safe apply);
- the frame hooks project to the protocols (norm simp).

It never folds or unfolds a protocol, since a greatest fixed point has no bottom; coinduction takes
its invariant from the call. Its theorems are `frameAccepts_iter`/`frameAccepts_loop` (a frame
accepted by a protocol at the current world, one `aesop (rule_sets := [Effect4.Coind])` each). The
red control is in `Test/Program/LoopProtocols.lean`.

Controls: `Test/Program/LoopProtocols.lean`.
- `Endless.protocol`: the always-true loop has a protocol, by `Greatest.coind` on the one state it
  revisits.
- `Endless.entry_saved`: the frame its entry leaves is typed.
- `Finishing.protocol`: the finishing loop's protocol, folded once.
- `View.refused`: the view-dependent frame is refused at input `unit` where the awaited fiber is
  undeclared.
- The bank's red control: `frameAccepts_iter`'s premise without `Effect4.Coind` fails under
  `#guard_msgs (error)`.

Ported: `TypedStack` (the walk at the machine's interpreter at an empty view), `H2PartOne` (the
row-117 controls by `unfold`/`fold`), `ProtocolPosts` (`closeSeq_protocol` by `fold`; the history
step over the deleted inductive protocol removed, register CE-017 updated), `FramesNotKripke`
(`hookLawsX_refused` over `HookLawsAt`), `HostWalk`. Register: CE-036, CE-038 REPAIRED; CE-037
waits for (b).

Placement:
1. Concepts 2 and 4; property: admitted loop and generator continuations, the walk's hook premise.
2. Questions: `M5Hooks.hookLawsAt_interpRAt` (proved), `M4Stack.popR_typed` (restated, proved);
   consumers `popR_hostTyped`, then `step_loop`/`step_deliver`.
3. Reach: every interpreter and protocol as stated; rows 117, 135, 175, 190.
4. Not established: the cursor's fit (b); the producers (8c); whole-step preservation.
5. Unlocks: protocols that safe nonterminating loops and the machine's own interpreter can meet.

Changes: `Laws/Auto/RuleSets.lean` (`Effect4.Coind`), `Typed/Contracts.lean` (`StepMono`, `Greatest`
and its laws), `Typed/Residual.lean` (protocols, steps, bank rules, `frameAccepts_iter`/`_loop`),
`Typed/Stack.lean`, `Typed/HostWalk.lean`; tests above, new `Test/Program/LoopProtocols.lean`,
`Test/All.lean`; `docs/core/decisions.md` (row 190 ruled and its landing).

- `lake build Effect4.Laws.Program.Typed.Stack` — exit 0 (`p8-05`, 545 s, the bank declaration
  rebuilds the law graph).
- `lake build Effect4.Laws Test.Program.LoopProtocols Test.Program.HostWalk Test.Program.TypedStack
  Test.Program.H2PartOne Test.Program.ProtocolPosts Test.Program.FramesNotKripke` — exit 0 (`p8-06`).
- `lake env lean … Test/Program/LoopProtocols.lean` — exit 0 (`p8-08`). Axioms
  (`p8-ax`): `hookLawsAt_interpRAt`, `popR_typed`, `frameAccepts_iter`/`_loop`, the four controls
  `[propext, Quot.sound]`; `Greatest.coind_upto`, `Greatest.transport` none.

## Slice S1 — a host answer decoded by its Schema, admitted at its token

**First:** the Schema JSON decoder yields the shape check (`Val.hasTy`), not membership (`Fits`).
Codex's `hook-view-support/schema-bridge-review.md` found the same thing independently. They agree
on a new classifier column. Exits are outside it: the Exit codec is total and represents internal
defects too (the owner: "generic schema for exit so we can always represent exits"). Their membership
also asks a shape-free cause (row 152), a decidable check the bridge keeps visible as a premise. No
codec or contract changed.

- `TyClasses.ClassRow.shapeDecides` (one column of the one classifier table): true for the data
  constructors, false for handles, fibers, cells, deferreds, `unknown` and exits.
- `shapeDecides t := cata_ty (TyTable.allHeads tyClasses ClassRow.shapeDecides) t`, and
  `fits_of_hasTy_shapeDecides` (`Typed/Membership.lean`): on that fragment the shape check is
  membership at every world and allocation table, the converse of `fits_hasTy` there. When the
  approved data constructors land (W4), each is one row of this table.
- `Typed/AnswerSchema.lean`:
  - `hasTy_of_decode` (`Schema.hasTy_decode` at the raw type);
  - `fits_of_decode`;
  - `exitOk_of_hasTy`/`exitOk_of_decode` (a decoded exit at shape-decided columns with a shape-free
    cause is `ExitOk`);
  - `answerOk_of_decode` (with the token's declaration, `AnswerOk`);
  - `decodedAnswer_keeps` (`edit_answer` with it, the consumer).

Placement:
1. Concept 5 (exact codecs) meeting Concept 1's membership.
2. Question: the `DecisionKeeps` premise of `M6Ledger.decision_preserves`, consumed by
   `edit_answer` (`M6Edits.answer`).
3. Reach: shape-decided answer and error columns, a declared token; rows 95, 96, 122, 152.
4. Not established: the session's correlation of a reply to its parked row and token (host
   boundary); world-reading answer types; nested exits; agreement with the target library's decoder
   (row 5's separate host gate).
5. Unlocks: a real `AnswerOk` premise for the proved answer edit, and the place the W4 constructors
   slot into.

Controls: `Test/Program/AnswerSchema.lean`:
- a string-error failure and a unit success, encoded and decoded, admitted at a declared token;
- a `badName` die exit decoded from its own encoding (representable) and refused by `ExitOk` at
  every world;
- an exit type is not shape-decided.

Changes: `src/Effect4/Program/TyClasses.lean` (column), `Typed/Membership.lean` (`shapeDecides`, the
theorem), new `Typed/AnswerSchema.lean`, `src/Effect4/Laws.lean` (imports it after `Typed.Edits`),
new `Test/Program/AnswerSchema.lean`, `Test/All.lean`.

- `lake build Effect4.Laws.Program.Typed.AnswerSchema` — exit 0 (`s1-01`; the core column rebuilds
  the typing cone); `M6Edits` 13 of 13.
- `lake env lean … Test/Program/AnswerSchema.lean` — exit 0 (`s1-03`).
- `lake build Effect4 Effect4.Laws Test.Program.AnswerSchema Test.Program.TyTables
  Test.Program.ConfigContract Test.Program.AdmissionColumns` — exit 0 (`s1-06`). `s1-05` first
  failed: `Test/Program/TyTables.lean`'s missing-row control writes one-field rows; it was updated to
  two columns, with the same expected refusal (`Fields missing: unknown`).
- Axioms: `fits_of_hasTy_shapeDecides`, `hasTy_of_decode`, `exitOk_of_decode`,
  `answerOk_of_decode`, `decodedAnswer_keeps` and the four controls `[propext, Quot.sound]`.

## Slice W4a — the `Val` append: the nesting images (data wave commit 3; decisions rows 121, 162)

**First:** one value, one image (the owner's ruling, "Nesting images"): a non-negative integer is
its `nat` image, the signed frame holds the negative integers only, and the binary64 frame holds
every double that is not stored as an integer — negative zero, the infinities and every NaN bit
pattern included. So the leaf edges `nat ⊑ int ⊑ number` the `Ty` append declares are membership
inclusions (probe P's `generated_int_image_breaks_tower` is why). No arithmetic; JSON keeps refusing
`-0`/NaN/∞ and keeps the safe-integer bound.

- `Store.Val` gains `negInt (n : Nat)` (the integer `-(n+1)`, store tag 13, the minimal digits of
  `n`) and `float (bits : UInt64)` (tag 14, eight big-endian bytes), appended. `floatFrame` is the
  canonicity predicate on the bits (exponent 2047: every infinity and NaN; exponent 0: every
  subnormal and `-0`, not `+0`; exponents 1–1022: fractions; 1023–1074: integral exactly when the
  low `1075 − e` fraction bits are zero; 1075 and up: integral). `Val.WF` requires it, so
  `decode_encode` (on well-formed values) and `decode_exact` cover both frames; the decoder refuses
  a leading zero digit in the signed frame and a binary64 payload of the wrong width or an integral
  pattern.
- `Store/Domain/Shape.lean`'s `printIn`: the two diagnostic arms (`{"int": "-n-1"}`,
  `{"float64": "<16 hex digits>"}`); a diagnostic printer, not a codec.
- Regenerated by `python3 scripts/generate.py --only derived` (exit 0, 684.8 s): only
  `Store/Carrier/Fold.lean` (the two algebra fields and equations) and
  `Store/Domain/Derived/Value.lean` (the two shape rows and codec arms) changed.
- Three proofs that enumerate `Store.Val.ind`'s arms gain the two: `ConfigValue.ofStore_exact`
  and `StoresLaws.Val.validIn_eq_handles` (named by the root build `w4-03`, compiled in `w4-06`),
  and `Handles.Val.keys_eq_handles` (named by `w4-06`; the same two `rfl` arms; its rebuild `w4-07`
  was stopped at the owner's word before `Handles` finished, so it first compiles in the `Ty`
  append's build). A grep for `using Store.Val.ind with` finds no fourth.
- **Deviation from the brief, deliberate:** `Canonical Int` and `Canonical Float64` are not re-pointed
  at the frames here. The promotion is W5's, where the JSON number arms consume it (Codex's
  `canonical-route.md`: `Canonical.guarded_toVal`/`guarded_exact` and the writer-image left inverse;
  the Float64 seed removed from the generator manifest so regeneration cannot revert it). So no
  stored byte moves in this commit and C1 lists none.

Controls (`Val.lean`'s guards; Codex's `numeric-review.md` boundary set, added): `-0`, `0.5`, `+∞`
in the frame, `3.0` and `+0` out; `2^51 + 0.5` in, `2^51 + 1`, `2^52`, `-1` out; the smallest and
largest subnormal and the smallest normal round-trip; signalling, quiet and signed NaN payloads and
`-∞` round-trip and stay distinct; payloads of seven and nine bytes refused; a nested integral
double refused by `encode?`; `-1` is the empty digit string, `-256`/`-257` round-trip.

Placement:
1. Concept 5 (exact codecs) under Concept 1's membership: the store carrier's exact embedding
   extended to two frames; required property: one value, one image (the leaf edges' inclusions).
2. Question: the `Val` codec's laws (`decode_encode`, `decode_exact`) at the new frames, consumed
   by the `Ty` append's `int`/`number` membership arms (W4b) and W5's JSON number arms.
3. Reach: the store byte codec on well-formed values; rows 109, 121, 162.
4. Not established: the Canonical Int/Float64 promotion (W5); arithmetic (FloatLib, deferred);
   any JSON number codec.
5. Unlocks: `nat ⊑ int ⊑ number` as membership inclusions in W4b; R3.

Commands: `lake build Effect4 Effect4.Laws` — `w4-03` named the first two matches; `w4-06` built the
core root clean and every Laws module but `Handles` (its one error, the third match); `w4-07`
(stopped). Lesson recorded: a root build is the seat's end check, not a per-fix check (the owner:
"we shouldn't be running 10 min gates every 2 mins"); the matches are found by grep. Conservativity
(`scripts/check-conservativity.sh 695bc714` on the generated tree): C1 295 goldens unchanged, C2
pass, C3 862 verdict rows, C4 pass. Axioms: `Val.decode_encode`, `Val.decode_exact` at
`[propext, Quot.sound]` (the module's guards and receipts).
