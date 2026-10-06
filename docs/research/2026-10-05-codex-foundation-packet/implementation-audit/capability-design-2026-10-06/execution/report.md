# Run, continuation and clock capabilities

## Review boundary

This is a design study, not an implementation or an acceptance receipt.
Main is frozen at `4b57609c03ad0a38fd81cfc2c09ea5731dfe7ff0`.
The initial working tree is clean.
LIFT's separately committed source is frozen at `b88ff25d61316040734e4be83622087c24a393d3`.
No project program, compiler, generator, host runtime or Lean command ran.

The finishing criteria are source-grounded interfaces, exact proof premises, clock distinctions, named consumers, retained source hashes and checked finite controls.
The source manifest identifies all 48 frozen inputs and their original paths.

## Recommendation

Build one inspection and command surface around the existing `Run` and `HostSession`.
Reuse their commands, observations, pending replies, retirement records, budgets and journals.
Add views and checked selectors before adding another executor or scheduler.

Treat execution history, source locations, continuation types and clock readings as separate data.
A source tree does not identify each runtime visit.
A journal records an execution order, not every causal dependency.
A typed continuation does not grant permission to resume an expired registration.
A clock reading does not identify an event.

The clock's first useful extension is an explicit plan over existing commands and a precise clock profile.
It is not a rewrite of the timers or an in-program `TestClock.adjust` construct.
The nanosecond compatibility slice is already ratified and remains open.
Keep its existing owner and registry placement.

## Current authority and ownership

- `docs/STATE.md` names LIFT, SEMW and CHECK as active seats at this snapshot.
- SEMW's `waitRetryAt` and `protectedBy` are committed, followed by six public Semaphore operations.
- Earlier STATE sentences saying these slices have not compiled lag those commits.
- `foundation-contracts.md`, lane K, assigns clock compatibility to a separate seat before timed APIs.
- The frozen active-seat list names no staffed clock seat.
- Decisions row 83 leaves custom clocks and Random open.
- Row 231 chooses exact nanoseconds internally, with explicit preservation of every old millisecond input.
- Row 231 explicitly says the conversion has not landed.
- Row 226 leaves embedded-budget adequacy and full driver suspension open.
- Rows 275–276 require shared waiting and protected acquisition without changing Queue's existing trees.

`ClockPlan` is not a declaration in the frozen tracked source and authority paths searched.
Use that name below as a proposed protocol record, not a landed API.

LIFT's `Program.compiled_mask_chain_runs` and `Api.replay_maskRuns` now cover the native evaluator.
They require no typing, table-admission or decision-admission premise.
They preserve the chain for live fibers, with an extending table of initial flags.
They do not prove a completed region's bracket, cleanup multiplicity, delivery, sufficient fuel or target agreement.
Their own module explicitly excludes `runSync` and the journal.
The journal connector is already anticipated coordinator work, not a new discovery here.
This study inspected committed propositions and proofs; it did not rerun LIFT's acceptance.

## One run surface, several precise capabilities

These are suggested interface shapes, not Lean declarations.
Existing names retain their meaning.
New names describe small wrappers over the named source owners.

| Capability | Proposed request and result | Existing owner and exact limit |
| --- | --- | --- |
| Observe | `observe(run)` returns `Run.Observation`, `Run.Work`, both budgets and a snapshot reference. | `Run.observe`, `Run.work`, `Api.inspect`. Empty work categories prove neither completion nor retained driver ownership. |
| Explain | `explain(snapshot, selection)` returns source facts, protocol reasons, pending work and relevant proof references. | `Point`, `PointTyped`, frontier readers, HostSession phases. Distinguish derived facts from an unavailable witness. |
| Inspect a completed prefix | `atPrefix(run, journalIndex)` reconstructs the exact `Run` at that command boundary. | `Run.play`, `Run.journal_replays`. A separate CUTS result identifies the prefix whose decisions raw replay consumes. |
| Inspect a machine position | `atDecision(run, positionIndex)` returns the completed command prefix and its machine projection. | `Scenario.tapeFrom_position_prefix` and `tapeFrom_position_replays`. A decision index is not a journal index. |
| Branch for analysis | `branch(prefix, suffix)` plays alternative commands in an offline branch. | `Run.play_append`, exact prefix reconstruction. It does not repeat physical host actions or transfer their ownership. |
| Select a continuation | `continuation(snapshot, fiber, registration)` returns captured data and typed endpoint diagnostics. | `PointTyped`, `CodeOk`, `FramePath`, current world and exact guard. A source point alone is insufficient. |
| Propose one control | `plan(snapshot, policy)` returns an existing command with a reason and a stale-snapshot guard. | `Run.nextControl_spec`; clock changes and reply applications remain explicit caller choices. Selection proves no progress. |
| Apply a reply | Existing `submit`, then selected `apply key`, reports its phase and new observation. | `HostSession.preflight`, `submit`, `applyReply`. Receipt and application remain distinct. |

### Data every inspectable snapshot needs

Keep `Run` as the semantic owner.
A boundary record should contain references or exact encodings of the following data.
Do not create a second mutable copy of the session.

1. Program, row table, row names, admitted signature and the artifact revision used to interpret them.
2. Session version, semantic session identifier and named profile.
3. Command fuel and compile fuel, separately.
4. Journal boundary, recorded phases and the first unread command, when applicable.
5. Existing observation, work lists, pending and retired replies, and consumed call identifiers.
6. The logical clock profile, exact current reading, pending deadlines and any active advance target.
7. The observation's declared exclusions and the proof references supporting its projections.

`Api.Built` currently certifies `⟨table, []⟩` and stores row names.
A built program with declared services remains its documented follow-on.
Do not label an API's serialized certificate as covering arbitrary service declarations today.

`Run.Observation` deliberately omits the machine and its stores.
`Run.Work` separately reports runnable fibers, armed dispatcher owners, host waits, pending replies and timers.
A new inspector may select stores, but it must name that stronger observation.
The existing engine `MachineView` does not recover the session ledger.

### Source locations and runtime occurrences

`Program.Point` stores a root, child path, captured environment, compile fuel, Boolean tape and completed-fiber view.
Its path locates source content.
`loopResumeAt` revisits the same point with a new cursor and body answer.
A loop's body can execute repeatedly inside one driver decision.
Consequently, `(fiber, sourcePath, journalIndex)` need not uniquely identify an activation.

Begin with honest identities:

- Source reference: artifact revision, root and child path.
- Journal position: run lineage, command index and recorded phase.
- Recorded runtime event: journal position plus an event offset, only when the retained trace supports that mapping.
- Registration identity: the existing fiber and guard token, with its current session binding.
- Dynamic activation: a distinct occurrence identifier only after instrumentation and its projection law exist.

Do not invent a precise activation from a missing trace.
Show an unknown activation rather than presenting a source location as a unique runtime occurrence.
A source edit also changes the meaning of a path.
Start a fresh admitted program after edits unless a checked rebase relates the old and new addresses and environments.

### Typed continuations compose today

`Contracts.FramePath Edge tin tout frames` is already the shared composition object.
Its `append` requires the same middle `EffTy` at the join.
Its `split` returns the existential middle type.
Its `map` requires a proof preserving every edge's endpoints and frame.

`HostStack` instantiates that path with ordinary frame arrows and machine-correlated registration arrows.
A registration arrow carries the actual race, its host, its declared token type, and its success-marker and failure laws.
`PositionStack` keeps less information.
The map from `HostStack` to `PositionStack` is one-way.
Matching displayed input and output types cannot reconstruct the forgotten race or token ownership.

`CodeOk` combines typed current code, a `HostStack` and interrupt provenance.
`PointTyped` also requires the located checked node, fitting captured values and typed completed exits.
`hostStack_mono` uses world extension; `hostStack_races` separately requires preserved race host/token facts.

The public explanation should therefore display answer, error and requirements, not only a result type.
It should distinguish captured values, dynamic service context and completed-view captures.
Never serialize proof-side host functions as canonical program content.
A wire view contains first-order data and a named certificate reference.

An agent may request a continuation splice for research.
Execution still requires compatible endpoints, typed captures, a current world and current ownership at the exact registration.
`FramePath.append` alone authorizes none of those effects.

## Prefixes, branches and cuts

`Run.play_append` gives exact Run equality for playing command lists in parts.
`Run.journal_replays` reconstructs a reachable Run from its original opening and recorded commands.
It includes the session ledger, not only the machine.

CUTS adds a different, narrower connection.
`Scenario.tapeFrom` maps progressed controls and applied replies to decisions.
It skips machine-inert rows and stops before a frontier row or an insufficient decision.
`tapeFrom_cut_replays` equates the machine after the completed prefix with raw replay.
`tapeFrom_position_prefix` also identifies the exact Run at a selected completed position.
The stopped row can change the machine before reporting its frontier.
It is outside that completed prefix.

The inspector should show both:

- “last completed replay prefix”, with its prefix length and machine relation;
- “observed state after the stopped command”, with that command's frontier phase.

Calling the latter a resumable checkpoint would overstate the current representation.
`TimerStore.target` alone does not retain commands, drained tasks or the enclosing clock/flush phase.

An offline branch may preserve the original semantic session identifier and add a separate branch identifier.
Physical host execution stays unavailable in that branch.
Changing `Run.id` while copying old replies fails their session check.
A new semantic session requires explicit envelope renaming and its own correspondence law.
Likewise, replaying a recorded completion does not reacquire or clone its external resource.
These distinctions belong in the interface before an agent receives a “branch” button.

## Straight code and loops share inspection, not every execution theorem

`DenoteB` contains the straight fragment and loop-bearing synchronous code.
`meaningB_straight` connects it to the unbudgeted straight meaning.
`loopAgreement_of_straight` reuses the straight theorem.
`Agreement.loopAgreement` covers the full admitted `Looped` fragment.

`LoopAgreement e` says: if a budgeted meaning finishes with an exit and stores, some machine-fuel bound eventually reproduces them.
It starts with empty stores and one fresh program.
It supplies an existential bound, not a computable planner for arbitrary loops.
An unfinished meaning keeps its stores and does not assert termination.

Both `Straight` and `Looped` exclude asynchronous sleep and waiting operations.
A source-level loop containing a wait uses the scheduled machine/run relations.
The same observation and journal API can serve both fragments while reporting different evidence.
Do not force users to choose different session engines merely because their program contains `iterate`.
Do not label a clock-driven loop as covered by the synchronous loop theorem.

`straight_sufficient` similarly covers a fresh standalone load.
It is not the embedded budget for waiting, cleanup, receiver reentry or a transaction.
The existing `Guarded J I O tasks` captures commands and drained tasks outside the machine.
`FoldLift` already owns the repeated dispatcher/clock induction.
Reuse these when the separately owned suspension work begins.

## The clock contract has four layers

### 1. Current logical model

`ClockMillis` is exact, nonnegative milliseconds.
Its decimal codec rejects noncanonical representations.
The model's native `sleep` takes a natural number.
`asyncRoute` makes zero sleep yield and positive sleep register a cancellable deadline.
`clockNow` returns the logical clock through the existing natural-number row.

`TimerStore` holds `now`, pending sleeps and an optional advance target.
`dueMin` selects deadline order, then registration order.
`clockStep` keeps the original target through intermediate wakes.
`advanceState` runs the woken work and flushes before looking for the next due sleep.
A newly registered sleep due before the target can fire within the same advance.

The timer module names its profile differences explicitly.
Cancellation removes an entry, following the live clock; stock TestClock retains it.
The model has no backwards `setTime`.
The model's immediate owed wake is not the stock TestClock's posted latch wake.
The postponed Latch connection remains separate from deadline-order facts.

### 2. Effect's retained live clocks

The rc.112 and 4.0.1 `Clock.ts` files are byte-identical.
Their retained `ClockImpl` and time-source block are byte-identical too.
This is a local source comparison, not a statement about a newer release.

The live clock exposes wall milliseconds, wall nanoseconds and monotonic nanoseconds.
`Date.now()` supplies wall milliseconds.
The nanosecond wall clock projects from a monotonic origin and reanchors when skew exceeds its threshold.
The monotonic source uses `hrtime.bigint`, then `performance.now`, then a nondecreasing Date fallback.
Its origin is not a portable wall timestamp.

Sleep converts Duration to milliseconds, chunks large timers, and cancels through `clearTimeout`.
A nonpositive live sleep yields; a nonfinite live sleep waits forever.
A nanosecond-valued read therefore does not establish nanosecond timer wake precision.

### 3. Effect's retained TestClock

Both `testing/TestClock.ts` files are byte-identical.
They keep separate wall-nanosecond and monotonic-nanosecond readings beside the numeric timestamp.
`adjust` runs due sleeps in order and yields between wakes.
A semaphore serializes adjustments.
`setTime` can move the wall timestamp backwards while the monotonic reading does not decrease.
The test clock also retains the original live clock for its live bridge and warnings.

Its nonpositive sleep returns directly, unlike the live clock's yield.
Its cancellation and posted wake differ from the logical timer profile above.
Thus “uses TestClock” must name the selected observation and admitted domain.
It cannot mean arbitrary trace equality with either the live clock or the model.

### 4. Current keyed host boundary

`harness/truth/session/clock.ts` provides a restricted Clock service and keeps adjustment outside the program.
`Rc112ClockBoundary` accepts canonical decimal milliseconds and rejects unsafe numeric conversion.
A nanosecond Duration is admitted only when divisible by one million.
It validates the whole end timestamp before advancing.
The exposed service has no adjustment or `setTime` method.

A profile failure is retained outside program failure handling.
The driver checks it after receiver work as well as before adjustment.
The optional sleep notes do not grant the model's full timer or causal observation.
The retained `clock.test.ts` exercises these boundaries; this study did not rerun it.

## Proposed clock capabilities

Separate the program capability from the test-driver capability.

| Capability | Data and action | Initial scope |
| --- | --- | --- |
| Read wall moment | Clock profile, origin interpretation, unit and exact value | Existing logical milliseconds today; live readings require their own recorded-input contract. |
| Read monotonic moment | Clock identity, execution/origin identity, unit and exact value | Compare only within a compatible origin. No implicit cast to wall time. |
| Sleep for a duration | Duration unit and accepted numeric domain | Existing millisecond row stays unchanged. A Duration is not a moment. |
| Inspect time | Current logical value, exact deadlines, timer guard tokens and active advance target | Read-only projection of current owners. |
| Advance virtual time | Explicit `.advance delta` command, original snapshot and named policy | External driver action. Serial command execution, not an unrecorded service mutation. |
| Flush | Existing `.flush` command | Runs queued work. It does not itself advance the logical clock. |
| Use live clock | An explicitly named provider/profile and recorded nondeterministic observations | Not supplied by a test-clock seed or initial timestamp alone. |
| Resume an interrupted advance | Full driver suspension plus remaining budgets and phase | Unsupported until row226's connector and ownership representation land. |

`ClockPlan` can initially be an immutable explanation of selected existing commands.
It needs a snapshot reference, clock profile, unit, chosen delta, reason, budget and intended observation.
Applying a stale plan refuses or requires replanning.
It must not hide a reply application or choose a host reply from arrival order.

A policy may first use `Run.nextControl`, then propose the earliest deadline when the program is waiting.
Name that scheduling policy explicitly.
A fixed number of successful control steps is not proof of quiescence or fairness.
Even one advance can run a loop or a receiver which registers more work.
Its result must expose its actual phase and current work rather than promising “all tasks ran”.

The existing `sleepDeadlines` is a syntax fold.
It visits a loop body once and also visits syntactic branches that a run may not execute.
Keep it useful as a source summary.
Do not present it as an execution-count or universal schedule synthesis API.
`fastForward` and `dilateTime` are program transformations, not general timing-preserving simulations.
They can change clock readings, scheduling boundaries and timeout races.

The finite independent model retains the linear positive case and three contrary shapes.
Three visits to one `sleep(5)` need wakes at 5, 10 and 15.
The syntax list contains only one 5.
A single explicit advance to 15 can include all three dynamically registered sleeps.
Another retained case finishes its root at 150 while the final clock reaches 1000.
These are bounded Python models, not Lean execution or Effect runtime evidence.

## Small next obligations and acceptance sketches

### A. A completed-prefix inspection boundary

**Status:** proposed API wrapper over proved source connections, not a newly missing replay theorem.

**Concept and placement:** `translation-simulation`, existing `journal-position-replay`, R13; the machine projection also serves R8.

**Consumer:** an agent or debugger selecting a journal position before branching.

**Property:** a successful selection names an exact command prefix and returns the same Run as playing that prefix.
Its machine equals raw replay at the selected completed decision position.
A stopped command is returned separately and never folded into that equality.

**Inputs and hypotheses:** the original Built, opening, row table, both budgets, commands and selected position.
Use `Run.Reached` only for reconstruction from an existing Run's own journal.
The CUTS position law itself accepts arbitrary starting Runs and its exact successful lookup premise.

**Reuse:** `Run.play_append`, `journal_replays`, `tapeFrom_position_prefix`, `tapeFrom_position_replays` and `tapeFrom_cut_replays`.
Do not duplicate CUTS's reply induction.
If a library consumer needs these Test-owned declarations, move the owner with a narrow compatibility connector.
Do not import Test into the core or silently promote a separate implementation.

**Positive control:** a prefix containing bind, receipt, apply and control has different command and decision indices but the same reconstructed session.

**Red controls:** select past a frontier; change compile fuel; erase a receipt while retaining its application; replay old envelopes under a new session identifier.

**Exclusions:** physical host replay, resource cloning, interrupted-command resumption, source-edit rebase and full engine-session agreement.

**Prerequisite:** choose the actual UI/API consumer and serialized snapshot identity.
The corresponding laws already exist; do not delay useful read-only inspection for a new general framework.

### B. Clock-unit compatibility, then an honest planner view

**Status:** existing accepted clock slice and proposed claims, not new authority.

**Concept and placement:** `translation-simulation`, `clock-unit-compatibility`, R13; numeric embeddings serve `exact-codecs`, R8 and R13.
The scheduled connector serves `reactive-scheduling`, R12, and reaches R10 when used inside owned operations.

**First property:** explicit embedding of an old millisecond duration into exact nanoseconds preserves zero, addition and deadline order.
The old wire value `sleep(1)` still means one millisecond.
Its clock-read boundary converts back under the old profile.
It never silently reinterprets the old integer as one nanosecond.

**Next property:** timer selection and the observable results of each completed old-profile advance correspond under that embedding.
Keep fiber/token identities, registration order, pending target and the exact observation in the relation.
Separate local store correspondence from scheduled delivery and host-clock agreement.

**Inputs and hypotheses:** nonnegative exact durations, fixed legacy wire version, explicit conversions and the chosen numeric target domain.
Any host-number conversion keeps the present safe-integer boundary.
New public nanosecond readings require the bigint image chosen by row231.

**Reuse:** `ClockMillis.toNat_add`, its exact decimal codec, `ClockCanonical`, `dueMin_first`, `dueMin_min`, `clockStep_finish` and `clockStep_wf`.
Reuse `FoldLift` for the later scheduled loop and `Run.runClock_eq_run` for progressed controls.
The latter proves machine equality at fixed table and budgets, not target agreement or a new budget bound.

**Positive controls:** zero and one millisecond; large exact internal durations; equal-deadline FIFO; a loop registering another due sleep during an advance.

**Red controls:** unchanged numeric reinterpretation; a fractional nanosecond Duration admitted through the millisecond-only host profile; a backwards wall reset claimed monotonic.
Also retain a cancelled timer under each named profile and an advance cut between wake and receiver work.

**Exclusions:** arbitrary custom Clock services, wall-clock realism, clock precision guarantees, fairness and a retained driver continuation.

**Prerequisite:** coordinator allocation of the already planned compatibility lane and its wire/profile boundary.
Before that slice, the proposed plan view emits only current millisecond commands.

## What should not expand

Do not add a second Eff representation or a second session engine.
Do not invent a new path algebra: `FramePath` already owns composition.
Do not turn every source node into a runtime activation identifier.
Do not infer causal independence from a total journal order or equal timestamps.
Do not make a mutable `Clock` object canonical program syntax.
Do not broaden the natural-number target policy to make nanoseconds convenient.
Do not expose `setTime` through the current logical profile without its own contract.
Do not equate a machine snapshot with the complete driver suspension.
Do not claim all straight and looped programs share a termination or budget theorem.

## Primary sources and read scope

The following notes are applicability arguments, not transferred theorems about this repository.
Each summary derives fewer than 200 words from its source.

- [W3C High Resolution Time, 1 September 2026 Working Draft](https://www.w3.org/TR/2026/WD-hr-time-3-20260901/), sections 2.1–2.2 and the introduction, read directly. It distinguishes adjustable wall time from monotonic time. Moments belong to clocks; duration subtraction requires compatible clocks. It also distinguishes timestamp resolution from timer throttling. This supports origin-aware protocol fields and separate duration/moment meanings. It does not establish Effect's timer order, model agreement or operating-system precision. This is a Working Draft, not a final Recommendation.
- [Lamport, Time, Clocks, and the Ordering of Events in a Distributed System](https://lamport.azurewebsites.net/pubs/time-clocks.pdf), printed pages 559–561, happened-before definition, clock condition and total-order construction, read directly. Program order and matching communication induce a partial order. A clock's increasing labels respect that order without determining its converse. A total order adds choices. This supports separate causal-edge and journal-order views. An Effect fiber's event granularity, shared-store edges and reentrant callbacks still need an explicit local definition. The paper does not prove the current trace complete or justify reordering independent-looking journal commands.

The two retained Effect versions are primary implementation sources.
Their exact files and clock-block comparison hashes are retained in this packet.
No newest-release claim or upstream-bug claim is made.
