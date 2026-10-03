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

## Slice W4b — the `Ty` append: eight forms with their order, normalization and membership (data wave commit 4; decisions rows 119, 125, 157–162, 165, 166, 177, 178)

**First:** `Ty` gains `record`, `map`, `tuple`, `app`, `null`, `undefined`, `number` and `bytes`,
appended, with the subtype order, normalization, membership (`Val.hasTy`, `Fits`), inhabitance and
the classifier columns at every one; the Schema bridge, the JSON codec and codegen refuse each by
name (row 162) until W5. Two deliberate changes beyond the brief, both for a consumer:

1. `Ty.valueVarsAlg` (Laws/Program/TypeAlgebra): a record, a map and a tuple are value formers like
   `prod`, so a parameter under them is allowed when their children allow it, and a reference's
   arguments are unread by membership, so they always allow it. The first cut (children closed)
   made `valueVars_of_noInternalHandle` false — `record [("a", required, var 0)]` passes the
   internal-handle scan — and that theorem feeds `hostRow_valueVars`, M5's host-row arm. The
   widening also makes `tuple [a, b]` agree with `prod a b`, which it normalizes to.
2. `Bridge.unlowered` writes a non-null payload (Codex's unlowered-boundary review): the marker
   used to be the same declaration as `schema (.handle "effect4/unlowered/<head>")`, so `ofSchema`
   read it back as that handle. Every declaration arm of `ofSchema` demands `.null`, so the marker
   now refuses at the reader while a handle of the same name keeps its image (controls in
   `Test/Program/TyWave.lean`). A raw exporter still writes the marker; no publication gate is
   claimed.

### What landed

- Core: `Program/TyCore.lean` (the inductive), `Program/Ty.lean` (rendering, the leaf table
  `leafEdges` with `lit < string`, `nat < int < number`, `undefined < unit`, `sub` with its record,
  map, tuple and variance-read reference arms, `normalize` with `normTuple`/`normApp` and the field
  canonicalization `Ty.canon`, `mapKeyOk`), `Data/FieldOrder.lean` (`Field.canonBy`, first wins on a
  repeated name), `Program/Typed.lean` (`Val.hasTy` mutual with `fieldCheckers`/`itemCheckers`;
  `namedHasTy`, `itemsHasTy`, `entriesHasTy`, `intImage`, `numberImage`), `Program/Admission.lean`
  (inhabitance: a record reads its canonical fields, optional-or-inhabited; `findInt` through the
  new children), `TyClasses` (eight rows), `Schema/TyFaces`, `Schema/Bridge`, `Schema/Codec`,
  `Codegen/Types` (the refusals), `Eff.lean`.
- Generated (`generate.py --only variances` and `--only derived`, the TyEq group first):
  `Program/TyEq.lean`, `Program/TyVariance.lean`, `Program/Fold.lean`, `Program/TyFoldExtras.lean`,
  `Store/Domain/Derived/Program.lean` (wire tags 20–27), `Laws/Program/TyView.lean` (the leaf laws,
  `AdmitsSub` with an invariant child read both ways, `AdmitsMono`, `AdmitsExtend`).
- Laws: `Admits` (membership respects the order and allocation growth at every form),
  `TypeAlgebra` (transitivity through the leaf table, antisymmetry on normal forms with canonical
  heads, normalization's laws, the widened `valueVarsAlg`), `Template` (widening by `AdmitsMono`),
  `Signature`, `Decision` (an `int` member under a tag hit), `Typed/Membership`.
- Membership (`Typed/Membership.lean`, 14 s alone): `Fits` mutual with `fitters`/`itemFitters`;
  `NamedFit`/`ItemsFit`/`EntriesFit`; every law ported — `fits_hasTy`, liveness, world growth,
  `fits_sub`, `fits_normalize`, `fits_members`, the instantiation laws (parameters under the value
  formers now), and inhabitance from probe P6 on the tree's world (`namedFit_fresh`/`itemsFit_fresh`
  thread one world; `namedFit_world_free`/`itemsFit_world_free` for the data fragment;
  `inhabited_of_fits` is now `inhabited_of_hasTy ∘ fits_hasTy`, one induction fewer). Helpers checked
  first in a scratch file in seconds: `allHeads_record`/`allHeads_tuple` (the classifier through
  `cata_ofLayer_view`), `inhabited_record`/`inhabited_tuple`, `namedFit_of_namedHasTy`,
  `itemsFit_of_itemsHasTy`, `namedFit_witness`, `itemsFit_witness`, `namedFit_map`, `itemsFit_map`,
  `namedFit_skip`, `namedFit_cons_eq`, `canon_instantiate`, `valueVarsAlg_record/tuple/app`.
- Tests: `Test/Program/TyWave.lean` (probe P's order and formation controls, the reader controls
  for the unlowered marker at all eight heads, P6's inhabitance controls), `TyTables` (the full
  table; the missing-field control on `bigint`), `Store/Templates` (the `negInt`/`float` arms),
  the historical `Fits` copies in `FitsOrder`/`ValueMembership` (a catch-all: the historical
  relation predates the appended forms).

### Commands and results

Builds (`scratchpad/run.py`, logs `logs/<id>.log`; `LEAN_NUM_THREADS=1` through w4b-33, `3` from
w4b-34 at the owner's word):

| Run | Target | Exit | Seconds | What it showed |
| --- | --- | --- | --- | --- |
| w4b-26 | Membership | 1 | 1240 | `Handles` alone 703 s (its W4a edit had not been rebuilt in this worktree); Membership 103 errors, all in unported arms |
| w4b-27 | TypeAlgebra | 0 | 35 | the widened `valueVarsAlg` |
| w4b-28 | Membership | 1 | 44 | one error (a closed `decide` over a free variable) |
| w4b-29 | Membership | 0 | 15 | Membership green |
| w4b-30 | `Effect4.Laws` | 1 | 1036 | every module but `Decision` (an `int` member under a tag hit) |
| w4b-31 | `Effect4.Laws` | 1 | 1043 | `LayerArm`'s ledger: `denoteR_typed.checked` and `typedState_load.checked` reach `Classical.choice` |
| w4b-32, -33 | Membership | 0 | 36, 33 | the source: `valueVars_normalize` (an `omega` closing an existential goal by `Classical.byContradiction`); a scan of the touched modules finds no reacher after the fix |
| w4b-34 | `Effect4.Laws` and 18 batteries | 1 | 251 | the ledger green; two stale pins (`ApiContract`'s `null` handle, `TyViewContract`'s `litRule`) |
| w4b-35 | the two batteries | 0 | 4 | green |

The batteries built in w4b-34/35: `TyWave`, `TyTables`, `Store.Templates`, `FitsOrder`,
`ValueMembership`, `SchemaGenerationContract`, `TermFits`, `AdmissionColumns`, `TypeAlgebraContract`,
`DecisionContract`, `CatchIfContract`, `ExprContract`, `ReadContract`, `ApiContract`, `TyViewContract`,
`LayerSharingContract`, `AuthorContract`, `AuthoringContract`. `ApiContract`'s `nullable` pins move to
the new images (`none`, `unit`) with a control that the retired `"null"` handle no longer fits.

Producers (`python3 scripts/generate.py --only <family>`; each first run named the next fix):

- `cas` and `readme` regenerated unchanged on the first run.
- `eff`, `wire`, `ts`: the hand-written `Ty` traversals of the producers gain the eight arms, each a
  mutual fold over the field and item lists — `OCaml5/Eff/Emit.lean` (`tyO`, OCaml literals; a
  record's fields are `(string * (bool * ty)) list`), `OCaml5/Eff/Goldens.lean` (`tyV`),
  `tools/Tools/ProfileJson.lean` (`tyJson`; a product is the generated codec's two-element array,
  fields named by their Lean binders), and `OCaml5/Eff/Metadata.lean` gains one fixture per new
  constructor (its coverage check refused the run). The conformance encoders
  `tools/Conform/Effect4/{LcnfMl,LcnfSemantics}.lean` gain the same arms and read the renamed
  `Field.ltKey`.
- `lcnf`: W4a's debt — `Api.run`'s closure reaches `UInt64.decEq` and `UInt64.toNat` through the
  `float` frame. `OCaml5/Lcnf/Translate.lean` maps both (equality and the identity, `UInt64` being
  `int` like `UInt8`); a `UInt64` literal above `max_int` is now a fatal hole. See point 4 below.
- `variances` and `derived` reproduce byte for byte (hashes taken before the run).
- OCaml (`opam exec --switch=effect4 -- dune build`, `dune test`, both exit 0 after): the
  hand-written mirrors gain the forms and frames — `engine/e4_engine.{ml,mli}` (`Val_negInt`,
  `Val_float`, their rendering), `engine/e4_program.ml` (`of_ty`'s eight arms, the alphabet count
  28), `eff/eff_frame.ml` (`tag_int = 13`, `tag_float = 14`, named only: a program's wire carries
  neither frame) and `test_lean_wire.ml`'s tag list. `test_eff` 451, `test_val_frames` 26,
  `test_lean_wire` 117, all passing.

The default build (`make corpus`, which builds `Effect4`, `Effect4.Laws` and `Test` first; 63 s at
three jobs once warm) is green with `Test.All`'s axiom gate and module-closure gate: the gate first
refused `Test/Program/TyWave.lean` as unreachable (added to `Test/All`), and two stale pins of the
value append — `StoreContract`'s "tag 13 is unused" (13 is the signed frame; the empty payload is
-1; the next unused tag is 15) and `TypedContract`'s `nat 1 : int = false` — moved. The latter is
`E4-TYPED-CE-002`'s witness: the register row is `RETIRED` 2026-10-02 (decisions row 121), its
attacked statement — `nat` in `int` because both print as `number` — gone with the refusal it
attacked; `nat` is in `int` now by the image inclusion. `generated/corpus-index.tsv` unchanged.

Conservativity (`scripts/check-conservativity.sh 41cafcfd`): C1 295 goldens unchanged, C2 8
constructors appended to `Ty` and nothing reordered, C3 862 verdict rows unchanged, C4 pass after
the eight are named in `Test/fixtures/baseline/66ee4657-supplement-v1.policy.json`'s
`constructor_additions`, C5 the record. PASS, 4 of 4.

`make check-cases`: PASS after the case policy is re-seeded from the measured scan
(`Audit.lean --seed-policy`, notes kept; decisions row 173's route). The diff is the `Ty` family
only: `Ty.beq`/`Ty.repr` (the generated `TyEq`) replace the derived `instDecidableEqTy`/`instReprTy`;
`findRepeatedField`, `leafHead`, `tyArgs`, `tyCtor` and `Ty.sub`'s three new sites are named; and
the existing default arms gain the forms they absorb. Reviewed site by site: every default arm
absorbing a record, map, tuple or reference is a shape query (tags, payloads, `exitOf?`,
`listOf?`, members, factors), the JSON codec's refusal until W5, the verified order's dispatch, or
`Ty.infer`, which binds no parameter under a composite head — a completeness gap for templates, not
an unsound default. The scans that must look inside (`findInt`, `internalHandleScan`,
`valueVarsAlg`, `varsOf`) are folds over the new children and absorb nothing.

### Placement

1. Concept 1 (typing and membership) with Concept 5 (exact codecs) at the refusal boundary; required
   properties: membership respects the order (`AdmitsSub`, `fits_sub`), normalization does not
   change membership (`fits_normalize`), inhabitance agrees with membership (`inhabited_iff_fits`).
2. Questions: the existing ledger goals and registry claims at the appended forms — `hasTy_sub`,
   `fits_sub`, `fits_normalize`, `inhabited-iff-fits`, `of-schema-exact` (unchanged statements).
3. Reach: closed and template types; records first-wins canonical, closed width, exact flags (row
   178 (a)); maps with `string` keys (row 125); tuples at exact arity; references at declared
   variances (row 158).
4. Not established: the OCaml engine's `UInt64` carrier is not exact (Codex's lowering review):
   `UInt64` lowers to the 63-bit `int`, so a float bit pattern at `2 ^ 62` or above (negative zero,
   the infinities, every NaN) has no carrier there. The generated closure only compares and
   converts float bits and constructs none, so none reaches it today; a `UInt64` literal above
   `max_int` is now a fatal generation hole, not a clamp. The repair, an exact 64-bit carrier
   (`Int64` or eight bytes) with its byte connector, is owed before a float producer reaches the
   engine; the values goal keeps every binary64. Schema/JSON lowering of the eight forms (W5); terms over them (W6); `int` stays
   refused by admission's `findInt` (DB-15); no width subtyping on unchanged values; `{a?: never}`
   and `{}` have equal membership but stay apart in the order (Codex's record/tuple note).
5. Unlocks: W5 (codecs replace the refusals), W6 (record terms with P7's required-field lookup),
   M5's host-row arm at tables using the new forms.

## Slice T1 — the default battery's slow lane and two dead batteries (owner, 2026-10-02)

**First:** `lake build` (and so `make check`) no longer builds the five slowest batteries; they are
built at a sweep by `make check-slow`, through `Test/Slow.lean`, which imports `Test.All` and them
and runs the axiom gate over everything. The owner's choice ("cut + slow lane") after the measured
inventory: 211 test files, 46,836 lines, about 48 minutes single-threaded over the 169 with build
times on record, five of them 44%.

- Deleted: `Test/Machine/Fuzz.lean` (347 s; 160,384 machine runs by `#guard`, untouched since
  2026-09-12; the M6 theorems state what it enumerated) and `Test/Data/DataContract.lean` (it guarded
  Lean's own `Option`/`Bool`/`List` functions and nothing of the tree; its import leaves
  `TypeAlgebraContract`).
- The slow lane (`slowLane` in `Test/Audit/AxiomGate.lean`, imported by `Test/Slow.lean`):
  `Test/Program/LayerSharingCertificate.lean` (the kernel-checked run certificate, 414 s, split from
  `LayerSharingContract`, whose fixtures stay in the default battery for the authoring contracts),
  `Test/Audit/TraversalCensus.lean` with its two fixtures (260 s; a printed report, also
  `make traversal-census`), `Test/Api/TraceOrigin.lean` with its importers `SupervisionContract` and
  `StepInvRulesRed` (137 + 10 + 12 s), `Test/Program/ExitTypeLane.lean` (109 s; delete when M6's
  typed-state proof lands). Paths unchanged, so no library docstring moved.
- The module-closure gate admits the slow files unreachable only when it runs from `Test.All`;
  from `Test/Slow.lean` they must be reached like every other source (Codex's review: a dropped
  slow import would otherwise escape the sweep). `check-slow` is an explicit phony target, not a
  stamped `CHECKS` entry (Codex: the stamp rule gave it a prerequisite with no rule; `make -n
  check-slow` now prints `lake build Test.Slow`). `AGENTS.md`'s closure rule names the exception.
- Kept, after reading the 60 batteries untouched since before 2026-09-20: the frozen contract
  packets and the seeded counterexample models (register entries; most build in seconds).

Commands: the default build through `make corpus` (`Test.All`'s gate green with the slow files
outside it, 63 s warm); `make -n check-slow`. Not run: `make check-slow` itself (the sweep).

## Slice M6-E — the evaluation step through operation clauses; row 170's premise carried in J

**First:** `MachineTyped` (J) has a fifth field, `sourceWF : root.program.layerRefsWF = true`
(owner, 2026-10-02: "carry it in J"). This makes the invariant's contract stronger: every
`StepPreserves`, decision and reachability statement now asks a post-state for it too. The root
never changes, so each step keeps it by the frame. No runtime definition changed, and no
ledger goal's text changed.

Base `7e087c20`; heads `58cccb7a` (the clause interface), then this slice's two commits.

### Row 170's premise in J

- Why: M5's `DenotesTyped` takes `layerRefsWF` (decisions row 170, `E4-TYPED-CE-020` repaired at
  `aabb1b5e`). An M6 or M7 consumer that reads a layer reference at a reachable state needs it, and
  J did not hold it.
- `Typed/Assembly.lean`:
  - the field, with its docstring citing row 170 and CE-020;
  - `typedState_of_load`: the `TypedState` half of the load, with no premise;
  - `machineTyped_load closed sourceWF noMarker code`, built from it;
  - `typedState_load_of_code` goes through `typedState_of_load` and no longer takes the premise;
  - `loadsTyped_of_denotesTyped` passes `DenotesTyped`'s own `wf`;
  - the congruence lemma threads the field.
- `Commands/Bookkeeping.lean`:
  - `MachineWide.sourceWF`;
  - `MachineTyped.wide`, `machineTyped_of` and the three `MachineWide` constructions thread it.
- `Commands/Launch.lean`: `machineWide_alloc` threads it.
- Tests:
  - The eight concrete J witnesses close the field by `rfl` at their roots: StaleCode, M6Capstone
    (two), RegistrationColumn, RegistrationYield (two), TimerColumn and WaiterColumn.
  - So do the admitted loads in AwaitLoad and FitsOrder.
  - New control, `TypedDenotation.chain_untyped`: CE-020's root (`chainSrc`; `chain_not_wf` by
    `decide +kernel`) has no J at any `rootTy`, world or state.
- What CE-020 does and does not show here:
  - CE-020's checked refutation is of `DenotesTyped`, the denotation (M5).
  - The machine-side falsifier would be a J without the premise that admits a state whose step
    reaches the `.ref` arm's `badShapeExit`. It is not compiled.
  - `chain_untyped` shows that the strengthened J refuses CE-020's root. It does not show that the
    old J was false there.

### The clauses (`Typed/Commands/Evaluate.lean`)

- Accessors on `Evaluating`: `look`, `code`, `declared`, `view`, `settle_continue`,
  `settle_answered` and `answer_typed`. `answer_typed` handles a fiber operation whose answer is
  typed at the operation's post: a value `v` with `fiberPost` gives the continuation's typed code at
  the same world.
- Six `FiberClauseKeeps` instances:
  - `clause_suspend`, `clause_foreignRelease` and `clause_closeWalk` answer `unit` inline;
  - `clause_frontier` leaves the frame as it is;
  - `clause_construction` is `prepareR` glue at the completed view;
  - `clause_sync` delivers an answered value.

### Placement (`deliver_preserves_of_clauses` and the clauses)

1. Concept: Reactive Scheduling & Machine Invariants (`reactive-scheduling`). The required
   property served is `step-deliver-preserves`, and through the same clauses
   `step-loop-preserves`.
2. Question: the `ProofGraph` ledger goals `M6Ledger.step_deliver` and `M6Ledger.step_loop`.
   - `deliver_preserves_of_clauses` is the step from the clauses to `StepPreserves` for `deliver`.
   - Each clause is one premise of it.
   - `sourceWF` serves the M7 consumers' reads of layer references, and the `mask` and `scoped`
     clauses through `denotesTyped`.
3. Reach:
   - the judgment is `ConfigTyped root rootTy w` (I);
   - the observation is the next configuration of `driveStep` at the `deliver` head, at the same
     world;
   - the fragment is a non-halted machine whose evaluating fiber is `Evaluating` (typed, stale exit,
     running, live);
   - hypotheses: one `FiberClauseKeeps` per fiber operation, `StoreClauseKeeps` per sync operation,
     and `WalkKeeps`.
4. Not established:
   - The theorem is conditional. Its open premises are:
     - the frame-pushing clauses: `guard_`, `mask`, `scoped` and the sequential `closeIter`;
     - `gen` and `loop`, which wait on row 190 (b), the cursor fit and the 8c producers;
     - `scopeExit` and `refuse`;
     - `raceRegister`;
     - the `FiberAction` arms;
     - `StoreClauseKeeps` and `WalkKeeps`.
   - It is an invariant, not progress (row 139). It is safety only; `fair-scheduling` (R12) is
     separate.
   - The host boundary stays where `host-boundary.md` puts it.
5. Unlocks: `step_deliver`, then `step_loop` (the same clauses plus the runloop prefix lemma), then
   `typedState_reachable`, then M7's four goals. `exitHandles_valid` also needs
   `HandlesRegistered`.

Commands:
- `lake build Effect4.Laws` (green);
- `lake build` of the twelve batteries that construct J or `MachineWide` (green; the slowest,
  M6Capstone, took 22 s);
- the axiom scan over every declaration of `Evaluate`, `Assembly`, `Bookkeeping` and `Launch`:
  1,037 declarations, none outside `[propext, Quot.sound]`.

Not run: `lake build Test`, the trust gate and `make check`, which are owed at the sweep. All
evidence is kernel-checked; none is bounded or host-only.

## Slice M6-F — the body bridge, `BodyTyped` at what its programs need, and the frame-pushing clauses `guard_` and `mask`; two Codex ports adopted

**First:** `BodyTyped` (`Typed/Admission.lean`), the pre of `mask` and `fork`, changed in four of its
six arms so that an admitted body's program is typed (`bodyTyped_typed`, the new
`Typed/Body.lean`). The old `fin` arm admitted a finalizer body at any type its exit fits while the
step installs the finalizer's own program: a refutation of the bridge at every source and world
(`E4-TYPED-CE-039`, the witness compiled at `f4d8be8f` and kept under `witnesses/`). The three
producers of the strengthened arms already had the facts and discharge them; no runtime definition
changed; no ledger goal's text changed. Two additive Codex ports ride the same rebuild.

Base `f4d8be8f`.

### The judgment

| Arm | Before | After | Why the program needs it |
| --- | --- | --- | --- |
| `fin name ex` | any `ty` with `ExitOk w ty ex` | `FinalizerAdmitted src w name`, `ex` fits `Exit<unknown, unknown>`; type `⟨unknown, never⟩` | `bodyR … (.fin name ex) = denoteFin name ex`, typed by `finalizerTyped_of_admitted` and nothing else |
| `acquireIn p ctx` | `PointTyped` | + the node is an `acquireRelease`, + `ServicesFit w ctx.services` | `acquireInR` registers `p.capture a ctx`, whose pre `CaptureTyped` reads both |
| `release p prev` | `PointTyped` | + `ServicesFit w prev.services` | the finalizer restores `prev` (`setContext`'s pre) |
| `layerBuild p m scope` | `LayerPointTyped`, `LayerBuildTy lt ty` | `LayerPointTyped`, `ScopeLive w scope`; type `buildTy lt` | `layerBuild_typed` reads the scope's presence; the one producer builds at `buildTy` |

`LayerBuildTy` is deleted (its one user was this arm). `FinalizerAdmitted` moved from
`Typed/Residual.lean` to `Typed/Admission.lean` unchanged, so `BodyTyped.fin` can read it; the
pre still cannot mention `TypedProg`. The transports (`bodyTyped_mono`, `bodyTyped_rows_append`,
with the new `finalizerAdmitted_rows_append`; `finalizerAdmitted_mono` and
`captureTyped_rows_append` moved earlier in the file) carry the new fields.

The producers:
- `acquireRelease_arm` (`Typed/Denotation.lean`) takes the node fact its dispatcher already held and
  keeps the services fit `fits_context_inv` returns;
- the foreign arm of `finalizerTyped_of_admitted` (`Typed/Assembly.lean`) keeps the previous
  context's services fit from the same inversion, transported to the release's world;
- `forkLayer_typed` (`Typed/LayerArm.lean`) takes the forked scope's presence; its three call sites
  had it from `fits_scope_inv` and discarded it.

### The bridge (`Typed/Body.lean`, after `LayerArm`)

`denoteAt_typed` (M5 through the interpreter's body hook), `acquireIn_typed`, `release_typed`,
`layerBuildR_typed`, and `bodyTyped_typed` over `bodyR (interpRAt root.program completed)`, by cases
on the admission. `acquireIn_typed` is the one with content: the `Scope` read, the acquire at the
point's child 0 at the node's own columns (`Checker.inv_acquireRelease`), the registration as a
store step whose answer is typed at `unit | Exit<unknown, unknown>` (the two posts of `scopeAdd`),
and the closed branch's release now, typed by the registration pre's bridge at the exit read back
(`exitOfVal_of_fits`, `fitsExit_of_exitOfVal`).

### The clauses (`Typed/Commands/Evaluate.lean`)

- `clause_guard_`: the resume frame `guard_frame` types, pushed on the host stack.
- `maskFrame` and `evaluateFiberR_mask` (by `rfl`): the frame the `mask` arm installs, named once.
- `clause_mask`: the body's program typed at the certificate by the bridge from `J.sourceWF` and
  `J.services` (this is what row 170's premise in J is for), or the recorded interrupt delivered
  (`pendingCause_clean`, `pendingCause_noShapeDefect` from `InterruptProvenance`); the answer
  frame carries the certificate; the restore frame is the identity arrow.

Eight of the fiber clauses are now proved: `suspend`, `foreignRelease`, `closeWalk`, `frontier`,
`construction`, `sync`, `guard_`, `mask`.

### `E4-TYPED-CE-039` (register row added; first written as `CE-036`, an id row 190 holds)

`docs/research/2026-10-02-claude-lead/witnesses/FinBody.lean` (log beside it): at every source,
world and view, `BodyTyped root w (.fin (.interruptFiber ⟨0⟩ true) (.success (.str "x"))) ⟨string, never⟩`
held (`admitted`) and the installed program was not `TypedProg` there (`body_untyped`, the finalizer
answers `unit`). What it does not show: a `ConfigTyped` state with this code current was not built;
the bridge's refutation is the exact statement, and it is what the `mask` clause needs. `Body.fin`
has no producer in the tree (the close walk passes `denoteFin` programs directly).

### The Codex ports (additive; `git apply --check` together, then applied)

- `Effect4.Program.RawHandles` (`Laws/Program/Handles/Term.lean`, ten declarations): a successful
  `nativeAtom`/`evalTerm`/`evalTerms` evaluation's raw handle frames (`Store.Val.handles`) are a
  subset of its inputs'; `evalTerm_registered` gives the existing `HandlesRegistered` conclusion
  from registered inputs. One producer leaf of `M7.exitHandles_valid`; not the reachable-exit
  connector. Fixture `Test/Program/RawHandleTerms.lean` (eighteen evaluator controls; byte 6
  unregistered copied, byte 7 kept; the overstrong claim refuted).
- `Effect4.Program.Typed.CompletionDue` (`Typed/Commands/Bookkeeping.lean`, four declarations):
  `complete_due_origin`, `complete_due`, `completion_due_typed`, `completion_due_typed_later` — a
  Deferred's completion keeps `PromiseTableOk.due` from `MachineWide` and `CompletionStrong`,
  transported to a later world with the token table unchanged. The due-field conjunct of the
  completing-store clause; not the store or frame invariants. Fixture
  `Test/Program/CompletionDueControls.lean` (the coarse completion is insufficient; the due
  typing is not monotone in the world alone).
- Both fixtures imported in `Test/All.lean` after `Test.Program.ProtocolPosts`.

### Placement

1. Concept 2 (`residual-program-typing`) for the bridge and the judgment; concept 4
   (`reactive-scheduling`), properties `step-deliver-preserves` and `step-loop-preserves`, for the
   clauses.
2. `M6Ledger.step_deliver` and `M6Ledger.step_loop`: `bodyTyped_typed` is a step of the `mask`
   clause and of the fork clauses to come; each clause is a premise of
   `deliver_preserves_of_clauses`.
3. Reach: `TypedProg root w ty` at a world whose service table is the source's, at a source whose
   layer references are well formed (rows 112, 170); the clauses on the `Evaluating` fragment at the
   same world (no world extension: `guard_` and `mask` allocate nothing).
4. Not established: the clauses listed open (`scoped`, `gen`, `loop`, `raceRegister`, the fiber
   actions, `scopeExit`, `refuse`, `closeIter`, the store rows, the walk); `loop`'s prefix; progress;
   the host boundary unchanged. The ports: no reachability, no handle existence, no whole store step.
5. Unlocks: the fork clauses (`fork`, `forkIn`, `forkScoped`, `scoped`, `raceAll`) read the same
   bridge; `step_deliver`; the M7 exit-handle route's term leaf.

### Proposed decisions rows (coordinator's register)

- `Body.fin` has no producer; cut it (`Sched.Body`, `denoteBody`, `bodyR`, `body_means`,
  `BodyTyped.fin`, `SchedContract`'s guard, the contract packet's two words). A representation cut,
  so proposed, not landed.
- `BodyTyped` is "what the program needs": an admission arm is stated from its program's typing
  derivation, and a producer that lacks a fact the program needs is the finding, not a weaker arm.


Commands and results:
- `lake env lean docs/research/2026-10-02-claude-lead/witnesses/FinBody.lean` at `f4d8be8f`, before
  the change: `admitted`, `body_untyped`, `bridge_refuted` at `[propext, Quot.sound]`
  (`FinBody.log`).
- `lake build Effect4.Laws Test.Program.RawHandleTerms Test.Program.CompletionDueControls`: green
  in three runs (a shadowed section binder in `Residual.lean`; then an implicit `fin` and an unused
  binder in `Body.lean`). The rebuilt cone: Residual 34 s, Denotation 18 s, Assembly 8.3 s,
  LayerArm 8.7 s, Bookkeeping 7.6 s, Body 11 s, Evaluate 3.1 s, RawHandleTerms 4.4 s,
  CompletionDueControls 3.1 s. The ledger report is unchanged (`M6Ledger: 4 open, 16 proved, 20
  total`): the clauses are premises of `step_deliver`, not yet all of them.
- The axiom scan over every declaration of Evaluate, Body, Admission, Residual, Denotation,
  Assembly, LayerArm, Handles/Term and Bookkeeping: 2,352 declarations, none outside
  `[propext, Quot.sound]`.

Not run: `lake build Test`, the trust gate, `make check` (owed at the sweep). All evidence is
kernel-checked; none is bounded or host-only.

## Finding F-WF — the store well-formedness clause of `J` is not re-establishable from membership (2026-10-02, with Codex's checked seam)

**First:** `WorldValid.wf : m.state.WF` (`Laws/Machine/StoresLaws.lean:223`) asks every stored value
and every scope's closing exit to be `validIn` the store (`Val.validIn`, `Laws/Machine/StoresLaws.lean:83`,
through `Stores.handleValid`, `:70`: every handle frame has a registered kind byte and names a present
cell, promise, scope, memo map or external; a fiber frame is accepted; an unregistered byte is refused). Membership at `unknown` is
`Live` (`Typed/Membership.lean:52,203`), which reads only `Val.keys`: the registered cell, promise
and fiber frames. So a typed program may carry `.handle 255 7` at `unknown` — into `refMake` (Codex's
checked seam, `/private/tmp/codex-lead-2026-10-02/m6-close-stores/checked-seam.md`, at `f409507f`:
any ordinary non-marker `Evaluating` witness frame-edited to that allocation stays `ConfigTyped`, and
no later world has the result `WF`), or out of a `scoped` region as the body's exit (the walk's
callback outcome: `prepareScopedExitR` writes it as the scope's closing exit). No fact of `J` gives
`validIn` there. Source reachability is not established by the witness (terms mint no frames, `RawHandles`; host
answers are decoded; store reads return `WF` values — none of which is a reachability proof), but the
clause interface (`Evaluating`) admits it, so the universal clause `StoreClauseKeeps (refMake …)` is
false as stated (`E4-TYPED-CE-040`: Codex's hypothesis-free `refMake_clause_false`, copied to
`witnesses/RefMakeClause.lean`); the walk's callback outcome is not established from `J` (no compiled
refutation of `WalkKeeps`).

What this does and does not show: the refutations are at the clause interface over `ConfigTyped`;
they are not a reachable-source counterexample and not a refutation of M6's reachable statement.

Owner's constraints (2026-10-02): do not weaken `WF`; do not assume output preservation; supply the
actual capability-validity relation at the interface, or a justified narrower interface.

Proposal (a decisions row for the coordinator): **membership at `unknown` is validity.** Strengthen
`Live w v` to every handle frame of `v` (`Store.Val.handles`), each with a registered kind byte and
present in its table: cells and promises in the world's tables (as now), fibers in the world's ids,
scopes live at `w.state`, memo maps present (`mapAt`), externals allocated. Then
`fits_validIn : StoreTyped root w → Fits w v ty → v.validIn w.state` holds for every form (the handle
forms by their declarations read through the store's forward bounds, `StoreTyped.heap`/`promises` —
Codex's `ValidityBoundaryControls.lean` shows the coverage predicates `HeapTable`/`PromiseTable`
alone leave a declared, absent cell that fits but is invalid; the data forms by their parts; `unknown`
directly), the store family and the scope close re-establish `WF` from the pre, and
`refMake (.handle 255 7)` is no longer typed. Codex's `RawLiveBridge.lean`
(`/private/tmp/codex-lead-2026-10-02/m6-adoption-next/`, `validity-and-closedness-receipt.md`) is the
proposal's leaf: `rawLive_validIn` from `StoreTyped`, raw liveness kept under `World.le`, transported
through `evalTerm` by `RawHandles.evalTerm_handles`; its review lists what `live_of_keys_nil`,
`fits_map`/`Grows` and fresh memo allocation still need, and row 187 is not to be amended silently. `HandleFits`'s memo arm gains presence (row 187 revisited: memo maps are never removed,
`Stores.le`). Producers of `Fits … unknown` today: closed values (`live_of_keys_nil`), decoded host
answers, store reads (already `WF`). Cost: one Membership change with its `fits_live`/`fits_subN`
arms re-proved (the full Typed rebuild), and the register row for the seam. Rejected alternative:
dropping `wf` from `J` — it is the runtime's store invariant and its memo clause is consumed
(`Typed/Assembly.lean:402`).

Until the ruling: the walk lands with its callback outcome isolated as the one named premise
(`ScopedExitKeeps`), the three other outcomes proved; the clauses that touch no stored value
(`scoped`'s make, the inline answers, the forks) continue.

## Slice M6-H — the walk under one named premise; the loop prefix and four store clauses adopted

**First:** every outcome of the saved-stack walk settles typed except the scoped-exit callback's
close, isolated as `ScopedExitKeeps` (finding F-WF above): `walkKeeps_of_scopedExit`,
`clause_unguard` and `clause_finishFinalizer` take it as their one premise. With Codex's loop prefix
adopted (`loop_preserves_of_clauses`, `53ea8fad`) both heads of M6 now reduce to the clause family;
Codex's four read-only store clauses are adopted too (`clockNow`, `refGet`, `deferredIsDone`,
`deferredPoll`; the fixture `Test/Program/ReadOnlyStoreClauses.lean`).

- `fiberTyped_frame` generalized (one lemma, no second copy): a race registration marker current
  carries its registration facts (row 188 (b)); the no-marker callers discharge it vacuously.
- `configTyped_frame_edit` factored out of `configTyped_frame_step`; beside it
  `configTyped_frame_marker` (the marker outcome, `loop` queued) and `configTyped_frame_finish`
  (the delivered exit, `finish` queued over the empty stack, row 134 (c), through
  `configTyped_cons_plain`).
- `popR_done` (a completed walk leaves the stack empty and the current code as handed),
  `raceRegistrationR_shape`; `Evaluating.settle_marker`, `.settle_finished`, `.deliver_keeps` (the
  four outcomes of `popR_hostTyped` at the typed view's hook laws, `hookLawsAt_interpRAt`, and the
  deferred-interrupt branch).
- Fiber clauses proved: ten unconditional (`suspend`, `foreignRelease`, `closeWalk`, `frontier`,
  `construction`, `sync`, `guard_`, `mask`, `scopeExit`, `refuse`), two under `ScopedExitKeeps`
  (`unguard`, `finishFinalizer`); the walk under it.

Placement: concept 4, `step-deliver-preserves` and `step-loop-preserves`; helpers of
`M6Ledger.step_deliver` and `step_loop`. Reach: the `Evaluating` fragment at the same world (the walk
allocates nothing). Not established: `ScopedExitKeeps` (the owner's ruling on F-WF), the clauses
still open (`scoped`, `gen`, `loop`, `raceRegister`, the fiber actions, `closeIter`, the store
family), progress.

Commands: `lake env lean -DwarningAsError=true …/Evaluate.lean` (27 s, no warnings);
`lake build Effect4.Laws` (below); `witnesses/RefMakeClause.lean` compiled here at this head
(seventeen declarations, every printed footprint at `[propext, Quot.sound]`, `RefMakeClause.log`). The register ids: my `.fin`
row was first written as `CE-036`, an id row 190 already held; it is `CE-039`, and the seam is
`CE-040`.

## Slice M6-I — the context clauses and `scoped`; finding F-CLOSED

**First:** fourteen fiber clauses are unconditional (`suspend`, `foreignRelease`, `closeWalk`,
`frontier`, `construction`, `sync`, `guard_`, `mask`, `scopeExit`, `refuse`, `setContext`, `getId`,
`ambientScope`, `scoped`), two and the walk are under `ScopedExitKeeps`. The fork family waits on a
second interface fact, closedness (below).

- `Evaluating.recontext`: a running fiber's context moves to one whose services fit, with its cached
  budget, through `configTyped_rupdate_code` (one lemma; `setContext` and `scoped` use it).
  `Evaluating.emit` for a trace event. `SettlesTyped.mono` for a settlement from a later world.
- `clause_setContext` (the pre's services; `unit` answered), `clause_getId`, `clause_ambientScope`
  (`ambientScope_live`, row 156; the `missingService` defect is admitted at every type).
- `clause_scoped`: the store edit is the `scopeMake` row's step (`syncOpStep_scopeMake`), so its order,
  well-formedness and generated typing are the row's through `configTyped_restate` (the new entry is
  empty); the context gains the scope (`servicesFit_addV`, the scope present); the body under the
  `onExit` guard bound to the scope's exit callback (`scopedGuardBind_typed`, row 188 (a)). The
  world grows by the store.

**Finding F-CLOSED** (the fork family: `fork`, `forkIn`, `forkScoped`, `raceAll`). `WorldValid.fiberClosed`
declares every fiber at a closed type (`ClosedEff`: no `Ty.var`); an allocation re-establishes it
from `closed : ClosedEff ty` (`machineWide_alloc`, `configTyped_alloc`; `launch` has it from the race
token, `tokenClosed`). A fork declares its child at its certificate, and
`fiberPre (.fork body) cert = BodyTyped root w body cert` says nothing about closedness, so the fork
clauses cannot re-establish the clause. The closed clauses are read (`Ty.closed_normalize`,
`rowTy_closed_some`, `Typed/Denotation.lean:2514`), so they are not dead. A `check_closed` route is refuted: Codex's
`ForkClosednessLocal.candidate.lean` (same folder) has `PointTyped`/`BodyTyped`/`fiberPre` accept
`succeed(var0)` over a captured empty list at `list(var0)`, whose certificate is not `ClosedEff`
(`list(nat)` is the passing control): the checker does mint open certificates. So the fork pre cannot
simply gain `ClosedEff cert` (M5's `fork_arm`/`settling_fork` could not discharge it;
`fork-closedness-review.md`). The options for the owner: declare a forked fiber at a closed widening
of its certificate (the type variables instantiated at `unknown`, the fiber's `Fits` facts kept by
widening), or narrow `fiberClosed` to where closedness is read. `configTyped_alloc` keeps its
explicit `closed` premise either way. Until the ruling the fork clauses are not attempted.

Still open and their blockers: `closeScope` and the walk's callback (F-WF: the closing exit's
`validIn`); `fork`/`forkIn`/`forkScoped`/`raceAll` (F-CLOSED); `gen`/`loop`/`closeIter .sequential`
(decisions row 190 (b), the owner's); `snapshotChildren` (no children clause in `J`: a fiber's
`children` are not known declared — a third gap, small: `FiberTyped` gains `childrenBelow`/declared,
discharged at `trackChild`); `getContext` (needs `Live w (Val.context ctx)` from `ServicesFit`, a
lemma over the encoded services); the parking and interrupting actions (`yieldNow`, `async`, `await`,
`awaitAll*`, `awaitNewChildren`, `interrupt*`, `runIn`, `cancelRace`, `dropObservers`,
`closeIter .parallel`, `raceRegister`), each a composition of existing edit lemmas.

Commands: `lake env lean -DwarningAsError=true …/Evaluate.lean` after each clause (10–27 s, no
warnings); `lake build Effect4.Laws` before each commit (`b553ce8d`, `77a9f813`).

**Finding F-PRE** (the interrupt family: `interrupt`, `interruptScoped`, `interruptAll`). The pre of an
operation that installs code or queues a command must contain what that code's or command's own
contract demands at the install: `interrupt target` (pre `True`) installs
`fiberValR (.interruptAs target self)` (`interruptAsCode`, `Laws/Program/InterpR.lean:339`), whose
pre is `(w.Γ target).isSome` (row 139's halting arm), so the installed code is not `TypedProg` from
the clause's hypotheses; `interruptScoped target` (pre `True`) installs `fiberValR (.interrupt target)`;
`interruptAll targets _` (pre `True`) queues `afterInterrupt self y (.awaitAll targets)`, whose
delivery clause asks `FiberListColumns w targets …` (`AfterInterruptReply`, `Typed/Scheduler.lean:467`).
`interruptAs` already carries its pre and its `afterInterrupt (.join …)` reply reads it. Proposal (a
decisions row): `fiberPre (.interrupt target) := (w.Γ target).isSome`,
`fiberPre (.interruptScoped target) := (w.Γ target).isSome`,
`fiberPre (.interruptAll targets _) := ∀ t ∈ targets, (w.Γ t).isSome`; the producers discharge them
from the fiber values' membership (`Fits … (.fiberOf …)` is `FiberDeclared`; `interrupt_arm`,
`interruptScoped_arm`, `interruptAll_arm`, `Typed/Denotation.lean:1799-1879`), and the
`interruptFiber` finalizer's admission (`FinalizerAdmitted`, today `True`) becomes the fiber's
declaration, discharged where `link` registers it (the forked child is declared). `Γ` is monotone, so
the pres are stable. Same kind as `sourceWF` and `BodyTyped`: the admission arm states what the
program's typing derivation needs. Not landed: it changes `fiberPre` (a Residual rebuild) and three
producers; the owner's call on ordering against F-WF and F-CLOSED.

**Finding F-LIVE** (`cancelRace`, and every queuing of `raceCancel`). The `raceCancel` command's
delivery clause (`CommandDeliveryOk`, `Typed/Scheduler.lean:477`) asks `FiberListColumns w live …`,
each live entrant *declared* with columns below the race's result (`FiberColumnsBelow` is
existential). `J` holds only `liveBelow` (each live entrant's id below `nextId`) and
`RacePayload.live`, the conditional form (`∀ childTy, w.Γ id = some childTy → …`). So the
`cancelRace` clause cannot queue `raceCancel` from `J` alone (`FiberAction.cancelRace` on a known
race). Proposal (a decisions row): `RacePayload.live` becomes the existential form
(`∀ id ∈ race.state.live, FiberColumnsBelow w id resultTy.answer resultTy.error`); `enrollRace`
discharges it (`EnrollRaceOk` already carries `cols : FiberColumnsBelow w c.id …`), the race
transports keep it (`Γ` is monotone, `fiberColumnsBelow_ext`). The `unknown race` branch of
`cancelRace` (an inline `unit`) is fine. Same kind as F-PRE.

**Finding F-CTX** (`getContext`). The answer `Val.context f.context` must fit `.handle contextTarget`,
whose arm asks `Live w (Val.context ctx)` beside `ServicesFit`. `ServicesFit` constrains only the
keys the static table types (`w.serviceTy key = some sty → FlatFits …`); a bound key outside the
table is unconstrained, so a context's handle keys are not known declared. Adequacy's
`getContext_answers` (`Typed/Adequacy.lean:1258`) already takes `Live w (Val.context ctx)` as a
premise. Proposal: `ServicesFit` (or `J`'s per-fiber services clause) states that every bound key has
a static type (shape A, row 112: the table fixes the keys a context may bind), after which
`Live` follows from the entries (`Ctx.keys_eq_handleKeys`, `keysNodup`, `FlatFits`'s handle arm).

Landed meanwhile: `clause_interruptScoped` (self: `unit`; another fiber: the public interrupt
program, typed at `unit` over the saved answer frame — `Evaluating.unitAnswerFrame`, the arrow from
`⟨unit, never⟩` to the code's type through `seqR next`). Fifteen fiber clauses unconditional.

## Slice C — J's closedness clauses cut (owner's ruling, 2026-10-02: "cut them")

**First:** `WorldValid`/`MachineWide` lose `fiberClosed`, `heapClosed`, `promiseClosed` and
`tokenClosed`. Nothing but their own re-establishment read them; they blocked every clause that
declares a fiber or token at an operation certificate, and the checker does mint open certificates
(Codex's `ForkClosednessLocal.candidate.lean`: `list(var0)`). With them go `ClosedEff` itself, the
`closed` premises of `initial_world_valid(_at)`, `typedState_of_load`, `machineTyped_load`,
`typedState_load_of_code`, `machineWide_alloc` and `configTyped_alloc`, the `cert.closed` conjuncts of
`storePre`'s `refMake` and `deferredMake` rows (`deferredMake`'s pre is now `True`), and the
`ClosedEff rootTy` premise of `LoadsTyped`, `ReachableTyped`, `ExitHandlesValid` and `M7Fragment`.
Each dropped premise strengthens its goal; no statement weakens. `Fits` at a type variable is still
`False`, so an open certificate admits nothing at its variables.

Tests: the J witnesses lose the four fields; the historical batteries' refutations drop the premise
(`¬ (A → ClosedEff → B)` becomes `¬ (A → B)`, still proved by the same witness). FramesNotKripke's two
`MachineTyped` witnesses also gain `sourceWF` (`rfl`): that battery was not in the `f681d65e` rebuild
and had been red since.

Commands: `lake build Effect4.Laws` (green after six rounds: Residual, Denotation, Adequacy, Assembly,
Finish and Edits each held a destructuring of the dropped premise); `lake build` of the twenty-one
batteries reading the changed statements (green after one round of four fixes).

## Slice F-WF — membership at `unknown` is validity (owner's ruling, 2026-10-02: "unknown means valid")

**First:** `Live` (`Typed/Membership.lean`), what `Fits … unknown` is and what every handle arm
implies, now reads every raw handle frame (`Store.Val.handles`, unregistered bytes included): each
frame's kind byte is registered and its column holds it (`KindLive`: cells, deferreds and fibers in
the declaration tables; scopes, memo maps and externals in the store). With the store's forward
bounds this is the store's validity: `live_validIn`, and `fits_validIn` (`Typed/Adequacy.lean`) at a
typed store. So the store family and the scope close can re-establish `Stores.WF` from their pres,
and `E4-TYPED-CE-040`'s input is refused (`raw_byte_refused`). `WF` was not weakened; no output
preservation was assumed.

Decisions row 187 amended (memo maps): a memo map handle fits only where the map is present
(`MemoLive`, `World.lean`, beside `ScopeLive`; monotone, `memoLive_mono`, since memo maps are never
removed). Its consequences, threaded exactly as `ScopeLive` already was:
- `memoFork`'s post gives the fresh map's presence (`memoFork_implements`, `mapAt_append_self`); a
  `memoGet` hit's post gives the owner's (`memoGet_implements`: the owner holds the entry, and the
  store's order keeps it);
- `BodyTyped.layerBuild` carries the memo map's presence; the build quantifier (`BuildsTyped`)
  takes it after `ScopeLive`; `forkLayer_typed`, `mergeFork_typed`, `mergeTwo_typed`,
  `mergeAllFork_typed`, `buildWithMemoMap_typed`, `addCurrentMemoMap_typed`, `layerBuild_typed`,
  `layerBuildR_typed` take it; `forkBuild_typed`'s build is quantified over present maps and gets
  the fork's from the post; `provideLayer_arm` passes it;
- `fits_handle_fresh` (row 127's inhabitance) allocates a real memo map (`World.allocMemo`, as
  `memoFork none` does) instead of the unchecked index 0; `inhabited_iff_fits` keeps its statement.

The transport section (`kindLive_map`, `live_map`, `handleFits_map`, `servicesFit_map`, `fits_map`,
`Grows`) takes the store's order (`w1.state.le w2.state`) in place of its scope-only premise; every
caller had a world order and passes `ord.1.1.2`. The context lemmas gained raw-frame twins in
`Handles/Layer.lean` (`Env.Context.rawHandles`, `Val.handles_context`, `Val.handles_builtContext`,
`Val.context?_handles`, `rawHandles_addV`/`_merge`/`_mergeAll`, `contextsOfList_handles`; Codex's
`RawContextHandles.candidate.lean` placed); `LayerArm`'s context proofs read them. The key-based
helpers `live_of_keys_nil`, `keys_of_cause`, `intImage_keys`, `numberImage_keys`,
`live_of_keys_subset`/`_append` are replaced by their raw-frame forms.

Tests: the new battery `Test/Program/CapabilityMembership.lean` (red: the raw byte fits no type;
`refMake (.handle 255 7)` is admitted at no certificate; an absent memo map fits nowhere; green:
scalars, a present memo map, its validity). Historical batteries: ValueMembership's
`live_iff_handlesLive` deleted (its converse is false under the ruling: raw bytes and presence);
TypedDenotation's CE-020 walk gives its world memo map 0 for the fork's post; TypedResidual,
ProtocolPosts and MemoTable read the raw frames and the new posts.

Placement: concept 1 (value/capability membership) serving concept 4's store and walk clauses
(`step-deliver-preserves`, `step-loop-preserves`). Not established: the store-family clauses and
`ScopedExitKeeps` themselves (they can now be proved; not yet done); source reachability.

Commands: `lake build Effect4.Laws` (green; Membership 26 s alone); the twenty-five batteries reading
`Live`, `HandleFits`, the memo posts or the transport signatures (green); the axiom scan over every
declaration of the sixteen touched modules: 4,388, none outside `[propext, Quot.sound]`.

## Slice F-LIVE — a race's live entrants are declared (owner's ruling, 2026-10-02)

**First:** `RacePayload.live` (`Typed/Scheduler.lean`) is now existential: every live entrant is
declared, with columns below the race's result (`FiberColumnsBelow`). This is what `raceCancel`'s
reply reads (`CommandDeliveryOk`'s `FiberListColumns` over the live set), so the `cancelRace` clause
can queue it from `J`. `enrollRace` supplies it (its `EnrollRaceOk` already carried the columns);
the world and allocation transports carry it forward along `Γ` (`racePayload_world`,
`racePayload_alloc`, whose freshness argument is gone: a forward transport needs none).

Tests: the two `emptyPayload` helpers (RegistrationColumn, RegistrationYield) take the existential
form; H2PartOne's `new_admitted` proves it (its `OldRacePayload` keeps the old form). EnrollmentBound's
`MachineTyped` witness gains `sourceWF` (`rfl`): red since `f681d65e`, not in that rebuild.

Commands: `lake build Effect4.Laws` (green); the twelve batteries that build `J` or a `RacePayload`
(green).

## Slice F-CLOSE — a scope closes with an exit that fits `Exit<unknown, unknown>` (2026-10-02)

**First, for the coordinator:** this is a pre strengthening landed under the principle of the four
approved small pres (the admission states what the program needs), not on its own ruling. The
`closeScope` row's fiber pre (`Typed/Residual.lean`) now reads
`ScopeLive w scope ∧ FitsExit w ⟨unknown, unknown, empty⟩ ex`. The closing exit becomes the scope's
(`scopeCloseSnapshot`), which the scope store types at `Exit<unknown, unknown>` (`ScopeExitOk`, DI-94)
and `Stores.WF` asks to be valid; with presence alone, typed code could write `closed badClose` and no
later world typed the store (seat D4's open finding from landing row 151 (a″), the old
`closeScope_pre_admits_unfit_exit`). `closeScope_installs` already took the same fit as its one
premise beside the store's typing. The coordinator should propose this as a decisions row or reject
it; the clause `closeScope` and `ScopedExitKeeps` are proved against it.

Producers, each now supplying the fit:
- the `closeScope` arm of the fundamental property (`closeScope_arm`, `Typed/Denotation.lean`): the
  exit term's checked type `Exit<a, e>` widened to `Exit<unknown, unknown>`;
- the synthetic finalizers that close (`finalizerTyped_of_admitted`, `Typed/Assembly.lean`):
  `closeChildScope` and `closeChildOnFailure` take the finalizer's closing exit, which
  `FinalizerTyped` already types at `Exit<unknown, unknown>`; `memoEntry`'s last-observer close
  takes it forward (`fitsExit_mono`);
- `fromBuild`'s finalizer (`closeChildOnFailure_typed`, `Typed/LayerArm.lean`) and `provideLayer`'s
  scope close, from the body's `ExitOk` through the new `fitsExit_unknown` (`Typed/Membership.lean`:
  every fitting exit fits `Exit<unknown, unknown>`).

Tests: ProtocolPosts' red control becomes `closeScope_pre_refuses_unfit_exit` (the pre refuses
`badClose` at every world, as the closed-scope clause does) with a green twin
(`closeScope_fitting_exit_typed`); `close_code_typed` and `close_code_refused_absent` read the
conjunction (`failed_fits` moved before them); ScopePresence's `close_live` and
`old_makeThenClose_refused` likewise.

Placement: concept 4 (`step-deliver-preserves`), the store's validity under the scope close; it
serves `clause_closeScope` and the walk's `ScopedExitKeeps` (`M6Ledger.step_deliver`). Not
established: those clauses themselves (next).

Commands: `lake build Effect4.Laws` (green); `lake build Test.Program.ProtocolPosts`,
`Test.Counterexamples.Machine.Semantics.{AsyncHookContract, M6Capstone, ScopePresence, StaleCode,
ValueMembership}`, `Test.Program.TypedProgRows`, `Test.Audit.RuntimeCoverage` (green); the touched
controls print `[propext, Quot.sound]`.

## Slice M6-J — the scope close and the walk, unconditional (2026-10-02)

**First:** the walk's one premise is gone. `ScopedExitKeeps` is deleted: the scoped exit's close is
proved (`Evaluating.settle_callback`), so `walkKeeps root rootTy`, `clause_unguard` and
`clause_finishFinalizer` hold with no premise, and `clause_closeScope` is proved. All four rest on
F-CLOSE's pre (slice above).

Landed (`Typed/Commands/Evaluate.lean` unless named):
- `configTyped_closeState`: closing a present scope with an exit that fits `Exit<unknown, unknown>`
  keeps `I` at the world over the closed store. Growth is `scopeCloseSnapshot_keys`;
  well-formedness is the closing exit's validity (`fits_validIn` through
  `storeTyped_of_typedState`) plus the memo entries' scopes staying present; the scope column is
  `scopeStoreOk_closeState` (`Commands/Bookkeeping.lean`, beside the `addUnsafe`/`removeFinalizer`
  columns). The heap, cells, externals, due list and timers are untouched. Shared by both closes.
- `clause_closeScope`: presence and the fit from the pre; the program installed (void, the lone
  finalizer voided, the walk) is `closeScope_installs` at `J`'s finalizer typing
  (`finalizers_of_typedState`), over the saved answer frame at the post `ExitOk ⟨unit, never⟩`.
- `Evaluating.settle_callback` (replaces `ScopedExitKeeps`): `prepareScopedExitR` restores the
  previous context (its services fit: the slot's protocol, so `Evaluating.recontext`, moved up),
  closes the present scope with the callback's exit (`fitsExit_unknown` of its `ExitOk`), and
  installs either `finishFinalizer ex` or the close's program under the finalizer boundary, bound to
  the callback's continuation.
  - The second case needed `finalizerBind_typed` (`Typed/Seq.lean`): a finalizer's boundary bound to
    any continuation is typed. The success arm ends at `finishFinalizer`, which reads no
    continuation; every other exit skips the bind (`seqGuard_typed`).
  - `finalizer_typed` is now its corollary at `Program.pure`.
  - The close's optional program is typed at `⟨unknown, never⟩` by `closeScopeUnsafe_installs`
    (`Typed/Adequacy.lean`, beside `closeScope_installs`).
- `settle_frame_ready` / `Evaluating.settle_ready`: a continue iteration whose glue already ran
  settles typed (the tail of `settle_frame_continue`, which now calls it).
- `scopeExitCallback?_some`: the callback recognizer's inversion.

Placement: concept 4 (`step-deliver-preserves`, `step-loop-preserves`), clauses of
`M6Ledger.step_deliver` through `evaluate_keeps`; `finalizerBind_typed` and
`closeScopeUnsafe_installs` are concept 2 (`residual-program-typing`) steps with this consumer. Not
established: the remaining fiber clauses (fork family, race registration, async/await family,
interrupt family behind children/F-PRE, getContext behind F-CTX, dropObservers, yieldNow, runIn,
closeIter, gen/loop behind row 190), the store family (Codex), and so `step_deliver`/`step_loop`
themselves.

Commands: `lake build Effect4.Laws` (green; M6Ledger 4 open of 20, unchanged until the clauses
close); `lake env lean` axiom print of the twelve new or restated theorems: `[propext, Quot.sound]`
each.
