# rc.112's stateful APIs, and a review of the stores map (2026-09-19)

Two tasks from one brief: an adversarial review of `docs/research/2026-09-19-stores-and-event-log-map.md`
(the map note), and a catalogue of rc.112's remaining stateful modules with a verdict on the
owner's hypothesis that nearly all of them are library code over the primitives the tree has.

Read at `72698899`. The only commit since the map note's `23e668b0` adds two research notes, so
every source line cited here is the line the map note read. Nothing was built or run. Every claim
about the tree cites `path:line`, every claim about the host library cites
`vendor/effect-4.0.0-rc.112/src/<file>:<line>`, and a claim I reached by reasoning or by a
search rather than by reading the line is marked *inferred*. No claim in this note is proved,
reproduced, tested or stamped by me; where a theorem is named, the proof is the tree's.

## 0. The answer

The owner's hypothesis holds, with one primitive and one language feature doing the work, once
"composed" is pinned to a level of fidelity. There are three levels:

- **Values** (the answers, exits and final stores a program produces, up to renaming of handles).
  All nineteen modules are library code over Ref, Deferred, Scope, the fork family, race, sleep
  and `iterate`. None needs a new machine store. What they need is language, not machine:
  polymorphic `Ref` and `Deferred` rows, read-modify-write rows that take a binder term, atoms
  for association maps, and typing of handles inside values. Six of them (Cache, ScopedCache,
  RcMap, RcRef, Pool, RequestResolver) also keep a behaviour inside the object and run it later,
  possibly on another fiber; composing those needs a *program value* (a program position with
  its captured values, which is exactly what a registered release already is, `Capture`,
  `src/Effect4/Machine/Stores.lean:134-142`), or an API restated to take the behaviour at each use.
- **Schedule** (which host callback runs which fiber, in what order). rc.112 builds five things
  on raw `scheduleTask` calls: Latch, Semaphore, Queue, Pool's wake and the STM commit wake.
  Composed over Deferred, their waiters wake inline instead of on a dispatcher, which changes
  interleavings. One new store family, **Latch**, placed on the tree's existing and currently
  unused scheduled-wake machinery, restores the schedule for all of them except Queue, whose
  rc.112 wake runs on the dispatcher of the fiber that made the queue.
- **Trace** (the same fibers, events and allocations). Composition cannot match rc.112 here:
  it adds cells and, for some modules, fibers. Trace fidelity would need dedicated stores for
  the five scheduled-wake families.

The tree's own plan already states the bar that decides between them: "Concurrency inherits
decision-relative claims, not deterministic scheduling"
(`docs/research/2026-09-16-foundational-language-implementation-plan.md:767`). At that bar the
answer is: compose everything, add Latch, design a program value. The map note's §8 and
`docs/core/language-cut.md:75` claim a store per waiting family; that is more than rc.112's own
structure requires, and it contradicts the ruled DI-11 (`docs/DESIGN-ISSUES.md:85`: "Queues,
Mailboxes, and PubSub are composite `Eff` programs over `Ref` + `Deferred` + `WakeList` …, never
new machine stores").

On the map note: its store facts are mostly right, and F1 and R1 are sound. Its errors are
local (§1.2), but four of them matter: R1 touches about twenty files, not six; R2 deletes a
field that two green census witnesses read; R3's new fields have a one-lemma alternative for the
consumer it names and must move 501 lines of supervision laws; and F4 and R4 describe as missing
an OCaml interface, list twins and property tests that already exist.

## 1. Review of the map note

### 1.1 Confirmed

Each item was read at the cited line.

- The record `RunMachine` and its ten fields (`src/Effect4/Machine/Fibers.lean:415-433`); the
  decision alphabet of eight decisions (`src/Effect4/Machine/Fibers.lean:436-461`); the event
  alphabet of twenty-one constructors (`src/Effect4/Machine/Fibers.lean:360-384`); `emit` as an
  append with the empty-list guard (`src/Effect4/Machine/Fibers.lean:614-616`).
- The reference machine's state `RState` over the same `Stores`, with frame events erased to
  `Unit` (`src/Effect4/Laws/Program/InterpR.lean:94`).
- `Stores` (`src/Effect4/Machine/Stores.lean:1719-1733`) and the Deferred store
  (`src/Effect4/Machine/Stores.lean:1079-1177`), which transcribes rc.112's two optional fields
  (`vendor/effect-4.0.0-rc.112/src/Deferred.ts:58-61`) and `doneUnsafe`
  (`vendor/effect-4.0.0-rc.112/src/Deferred.ts:1648-1662`).
- **F1.** Every writer of a completion stores the image of a `Completion`. The only function
  that writes `DeferredCell.completion` is `DeferredStore.complete`
  (`src/Effect4/Machine/Stores.lean:1142-1152`), and its only callers are `deferredCompleteWith`
  (`src/Effect4/Machine/Stores.lean:1946-1948`, through `completionPrim`,
  `src/Effect4/Machine/Stores.lean:1813-1815`), `deferredInterruptWith`
  (`src/Effect4/Machine/Stores.lean:1949-1953`) and `memoComplete`
  (`src/Effect4/Machine/Stores.lean:2019`). `register`, `cancel` and `wakeBatch` only copy what
  is already stored (`src/Effect4/Machine/Stores.lean:1120-1175`). I found no path that stores a
  non-completion program in a cell (search over `src`, *inferred* complete). Through programs the
  only completions ever stored are exits (`src/Effect4/Program/Native.lean:248-251`,
  `src/Effect4/Machine/Stores.lean:2048-2055`); `ofRefGet` reaches the machine only from the
  host (`src/Effect4/Program/Admit.lean:69`).
- The proof invariants F1 names, `CompletionShaped` and `DeferredOk`
  (`src/Effect4/Laws/Program/Simulation/Hooks.lean:27-35`), and the partial decoder
  `denoteStored` with its `pending .unsupported` fall-through
  (`src/Effect4/Laws/Program/InterpR.lean:133-137`). The total `denoteCompletion` R1 wants
  already exists, with the bridge `denoteStored_completion`
  (`src/Effect4/Laws/Program/InterpR.lean:127-143`).
- **F2.** `MemoEntry.effect` is written at `memoBuild` and `memoComplete`
  (`src/Effect4/Machine/Stores.lean:2007`, `:2021`) and never read by a machine step; the hit
  path answers the entry's promise (`src/Effect4/Machine/Stores.lean:1996-2002`). rc.112's hit
  path runs the field (`vendor/effect-4.0.0-rc.112/src/Layer.ts:241-250`).
- **F3.** The API tells the root from a detached daemon only through the trace's `forked`
  events (`src/Effect4/Api/Supervision.lean:168-172`, `:196-197`, `:235-244`), and the
  holder-facing `Run.Observation` carries those statuses
  (`src/Effect4/Run.lean:220-238`, `:253`). `Obs` omits the trace
  (`src/Effect4/Laws/Machine/Behaviour.lean:10-17`, `:29-32`, `:47-49`).
- **F4's** container swaps (`ocaml/engine/externs.txt:53-71`) and its measurements: `Point.path`
  and `env` at 98.5 % of retained memory and 58 % of time (`ocaml/engine/externs.txt:33-39`),
  `completedExits` at 62.7 % at fan-out 512 (`ocaml/engine/externs.txt:40-47`); the translator
  maps `Array` to lists (`src/OCaml5/Lcnf/Translate.lean:239-255`).
- **F5.** `FiberId`, `RefKey`, `DeferredKey` and `MemoMapId` are one-field structures
  (`src/Effect4/Machine/Fiber.lean:12`, `src/Effect4/Machine/Completion.lean:21`,
  `src/Effect4/Machine/Wake.lean:49-51`, `src/Effect4/Machine/Alphabets.lean:83`); scope keys,
  finalizer keys, tokens and race ids are bare `Nat`.
- The typing sources the note quotes (`src/Effect4/Laws/Program/Typed/Sources.lean:31`, `:51`,
  `:53-58`), `HeapNat` (`src/Effect4/Laws/Program/Progress.lean:72`), and
  `drive_resume_wrong_token` (`src/Effect4/Laws/Machine/Clauses.lean:452`).
- §8's clock facts: the machine refuses `setTime` (`Test/Counterexamples/REGISTER.md:114`);
  with whole-millisecond advances from zero, rc.112's wall and monotonic nanos both equal the
  millisecond clock times 1,000,000 (`vendor/effect-4.0.0-rc.112/src/testing/TestClock.ts:258-259`,
  `:348-375`, *inferred* from the arithmetic); `timeoutOrElse` is `raceFirst(self,
  flatMap(sleep(d), orElse))` (`vendor/effect-4.0.0-rc.112/src/internal/effect.ts:3677-3704`);
  `ClockRef` is a `Context.Reference` (`vendor/effect-4.0.0-rc.112/src/internal/effect.ts:6033-6035`).

### 1.2 Wrong or imprecise

1. **"Seventeen fields transcribe rc.112's `FiberImpl`" (§1.2).** `RunFiber` declares fifteen
   (`src/Effect4/Machine/Fibers.lean:232-246`); the number is copied from a stale docstring
   (`src/Effect4/Machine/Fibers.lean:223`). rc.112's `FiberImpl` declares twenty-two
   (`vendor/effect-4.0.0-rc.112/src/internal/effect.ts:528-552`), of which the scheduler, tracer,
   log-level, stack-frame and metrics fields have no counterpart.
2. **"Four interpreter hooks: `registerAsync`, `dueResumes`, `wakeList` and `answerCode`" (§0).**
   Most promise operations go through `syncState` (`src/Effect4/Machine/Fibers.lean:490`, used at
   `:1121`): make, isDone, poll, completion, interruption, the await cleanup and the three memo
   rows. `answerCode` never touches the store; its type is `Completion → κ`
   (`src/Effect4/Machine/Fibers.lean:495`). `prepareAnswer` does touch it
   (`src/Effect4/Machine/Fibers.lean:592-593`).
3. **"A promise cell holds compiled-machine code even when the reference machine runs" (§1),
   "a store type that depends on the compiled machine's code type" (F1).** The cell holds the
   stores module's own name alphabet, `Program := Prim Name Thunk …`
   (`src/Effect4/Machine/Stores.lean:538`). The compiled machine runs a different alphabet,
   `NCode := Prim EffName EffThunk …` (`src/Effect4/Program/Compile.lean:345`), and embeds the
   stored code (`embed`, `src/Effect4/Program/Compile.lean:358`, applied at `:1466`, `:1469`,
   `:1487`, `:1491`); the reference machine decodes it (`denoteStored`). F1's substance stands:
   the store depends on *a* code type. The instance table also misses the fourth instance, the
   stores module's own interpreter `stores`, which runs that alphabet natively
   (`src/Effect4/Machine/Stores.lean:2167-2272`).
4. **The §2 table's writer columns are incomplete.** `deferreds.cells` is also written by
   `register` (`src/Effect4/Machine/Stores.lean:1127`), `cancel` (`:1136`) and `wakeBatch`
   (`:1169-1175`). `nextName` is also advanced by `scopeAdd` (`:1975-1976`) and `memoFork`
   (`:1994`). `externals` is written by the external rows' registration and by
   `prepareExternalAnswer` (`src/Effect4/Program/Compile.lean:1382`, `:1472-1483`), not by
   admission. The `refs` row's "now the kernel table `refStepOf`" should say that the machine
   still runs `refStep` (`src/Effect4/Machine/Stores.lean:880-917`) and that `refStepOf` is the
   proof-side table proved equal to it (`src/Effect4/Laws/Machine/RefKernel.lean:7-10`).
5. **F2, "only `Laws/Machine/Handles.lean` and the `StoresLaws` bookkeeping read it".** The two
   `StoresLaws` theorems that write the field, `syncOpStep_memoBuild` and
   `syncOpStep_memoComplete_some` (`src/Effect4/Laws/Machine/StoresLaws.lean:691-717`), are green
   witnesses of the census row `layer.memo-build-once`
   (`Test/Audit/RuntimeCoverage.lean:1007-1015`), whose summary ends "and on exit replaces the
   entry effect with the exit". That clause is exactly the write at
   `src/Effect4/Machine/Stores.lean:2021`. Deleting the field turns the row partial unless the
   clause is restated against the cell. The other reader is `MemoEntry`'s key set
   (`src/Effect4/Laws/Machine/Handles.lean:747`).
6. **F4, "no statement relating them to the Lean definitions, only the differential lanes".**
   The engine is a functor over seven carrier signatures (`ocaml/engine/api_engine.ml:10-121`);
   a reference instance runs the same generated bodies over list twins that reproduce the Lean
   operations "operation for operation" (`ocaml/engine/api_engine_ref.ml:1-30`); and per-carrier
   property tests compare each law with "the LEAN LIST OPERATION, written out … from
   Stores.lean" (`ocaml/engine/test/prop_store.ml:1-9`, `ocaml/engine/test/prop_table.ml:1-11`).
   What is true is narrower: those laws and twins are hand-written OCaml, stated nowhere in
   Lean, and the twins are not generated from LCNF. F4's list also omits the dispatcher swap
   (`ocaml/engine/externs.txt:10-14`, `:50`) and the `Capture` rows (`:64-66`).
7. **§8.2, "Cache, ScopedCache, RcMap and Pool … each needs its own keyed store".** rc.112 keeps
   those entries in ordinary maps inside library objects and fires expiry lazily on read
   (`vendor/effect-4.0.0-rc.112/src/Cache.ts:674-679`,
   `vendor/effect-4.0.0-rc.112/src/ScopedCache.ts:389-394`), through an ordinary `sleep` loop on a
   forked fiber (`vendor/effect-4.0.0-rc.112/src/RcMap.ts:758-773`,
   `vendor/effect-4.0.0-rc.112/src/internal/rcRef.ts:160-173`), or through `Effect.delay` over a
   Queue (`vendor/effect-4.0.0-rc.112/src/Pool.ts:941-1011`). They need map-valued Refs, not
   stores (§2).
8. **§8.3, "Random is also a context reference, and the machine has none".** The machine has
   context references: `Context.Reference`, a key with a default
   (`src/Effect4/Machine/ContextMap.lean:264-276`), with `maxOpsRef` and `preventYieldRef`
   (`:673-676`) among four reserved keys (`:779-790`). It has no *Random* reference.
9. **§8.4, "each is a new store, its rows, and a wake policy".** This contradicts DI-11
   (`docs/DESIGN-ISSUES.md:85`). And PubSub has no waiter list of its own in rc.112: it is
   library code over Deferred, Latch, Scope and MutableRef
   (`vendor/effect-4.0.0-rc.112/src/PubSub.ts:278-292`, `:1439-1461`, `:2714-2804`).
10. **§8.5, STM "would add a new kind of state".** In rc.112 the journal is an ordinary `Map`
    inside a context service, provided per transaction
    (`vendor/effect-4.0.0-rc.112/src/Effect.ts:24211-24223`, `:24273-24311`); versions are fields
    of the TxRef object (`vendor/effect-4.0.0-rc.112/src/TxRef.ts:61-67`); the commit writes
    values and posts one `scheduleTask` per pending waiter
    (`vendor/effect-4.0.0-rc.112/src/Effect.ts:24343-24354`). It composes over one Ref holding
    every TxRef (so that a commit is one atomic `modify`), a context service and a Latch per
    retrying transaction (§2, notes).
11. **§2.1, "(the `PendingOk` custom row)".** The typed-state `PendingOk` types a fiber's pending
    list (`src/Effect4/Laws/Program/Typed/State.lean:34`), and the book's `PendingOk` says no park
    resumes through a named continuation (`src/Effect4/Laws/Machine/Book.lean:231-232`). The
    waiter-to-guard relation §2.1 wants is what `ResumeOk`
    (`src/Effect4/Laws/Program/Typed/State.lean:36`) and the composed graph's parked-fiber clause
    (`docs/research/2026-09-18-typed-state-composed-graph.md:88-92`) need. The recommendation
    stands; the named row is the wrong one.
12. **Omissions in two lists.** §1.3's `Prim` list leaves out `yieldableError`, `onSuccessConst`,
    `onSuccessAndFailure` and `whileLoop` (`src/Effect4/Machine/Frames.lean:112`, `:120`, `:124`,
    `:133`). §3.2's event classification leaves out `finalizerProgram` and `scopeClosedOnLink`
    (`src/Effect4/Machine/Fibers.lean:375`, `:377`).
13. **R3, "`emit`'s O(n) append stops mattering".** In the OCaml engine the trace is already a
    carrier with its own `emit` (`ocaml/engine/externs.txt:54`, `:74`), so the append does not
    matter there today.

### 1.3 Missed

**State the map does not list.**

- **The fiber's context.** `Ctx` is the service map plus two cached budget fields
  (`src/Effect4/Machine/Stores.lean:82-89`), held per fiber
  (`src/Effect4/Machine/Fibers.lean:246`). Services hold values, including handles: the ambient
  scope handle under the reserved key (`src/Effect4/Machine/Stores.lean:113`) and a
  `Ref` handle under service code 7 (`src/Effect4/Program/Native.lean:277-279`). So the context
  is part of the handle graph and has its own typed-state row
  (`src/Effect4/Laws/Program/Typed/Sources.lean:27`, `:44`). The map's §2 table covers only the
  stores, and §1.2 names `context` without saying what it holds.
- **Captures.** A registered release is stored as a program position with its captured values
  and context: `Capture` (`src/Effect4/Machine/Stores.lean:134-142`), held inside a scope's
  finalizer name (`FinName.foreign`, `src/Effect4/Machine/Stores.lean:168`) and inside a thunk
  (`src/Effect4/Machine/Stores.lean:534`), with two typed-state rows
  (`src/Effect4/Laws/Program/Typed/Sources.lean:28`, `:57`). This is the tree's one existing
  defunctionalised closure, and §2 of this note leans on it.
- **Races.** `Race` holds the not-yet-forked entrants as code (`programs`), the host's park
  token, the frozen bookkeeping and a registration flag
  (`src/Effect4/Machine/Fibers.lean:398-410`), with its own typed-state rows
  (`src/Effect4/Laws/Program/Typed/Sources.lean:29`, `:50`).
- **Dispatchers.** A resume task carries code (`Task.resume`,
  `src/Effect4/Machine/Fibers.lean:115-120`), typed by its own row
  (`src/Effect4/Laws/Program/Typed/Sources.lean:43`). R1's slogan should therefore be "the
  service state holds data", not "the machine holds data": after R1 the machine still holds code
  in frames, dispatcher tasks and race entrants, as a defunctionalised machine must.
- **A machine-state snapshot inside code.** `Point.completed` is the completed-exit view taken
  when code was constructed (`src/Effect4/Program/Compile.lean:66-69`); it is what the OCaml
  fiber table maintains (`ocaml/engine/externs.txt:40-47`). `Point.tape` and `Capture.tape` are
  carried and copied (`src/Effect4/Program/Compile.lean:64-65`, `:85`, `:91`) and, by search,
  read by nothing (*inferred*): an inert second decision input beside the tape of §3.1.
- **Counters beyond F5's four.** `nextName` also mints memo-map ids
  (`src/Effect4/Machine/Stores.lean:1994`); allocation indices are list lengths for refs and
  promises (`src/Effect4/Machine/Stores.lean:881`, `:1100`) and the allocated-target list length
  for external handles (`src/Effect4/Program/Compile.lean:1357-1358`); each waiter list has its
  own phase counter (`src/Effect4/Machine/Wake.lean:119-123`); the host session mints call ids
  and counts applications (`src/Effect4/Api/HostSession.lean:84-93`), and a session key is a
  fiber with a park token (`src/Effect4/Api/HostSession.lean:56`), so the park token is shared
  by the parks, the store waiters and the host protocol.

**Logs the map does not count.** §3 says there are three. There are five. The fourth is the
host session's ledger: bound calls, received replies, consumed call ids and retired calls
(`src/Effect4/Api/HostSession.lean:84-93`). The fifth is the run's own journal of played rows
with their verdicts (`src/Effect4/Run.lean:57-59`), from which a fresh run replays
(`src/Effect4/Laws/Run.lean:164`). That fifth log matters for F3's argument: at the run layer
the tree has already chosen "the input journal is the truth and the state is a fold over it",
which is the event-sourced shape F3 says the machine did not choose. The machine's own trace is
the derived, diagnostic one — both halves are true, at different layers.

**R1's real blast radius.** The map lists six places. A search finds a second invariant of the
same kind that R1 also deletes — `StoredCodeNoRace` and `DeferredCodes`
(`src/Effect4/Laws/Program/Guard/RaceSites.lean:473-477`,
`src/Effect4/Laws/Program/Guard/Core.lean:1669-1750`), used in
`src/Effect4/Laws/Program/Guard/{FrameOwned,NativeState,Settle}.lean` — plus the key law stated
with `programKeys` (`src/Effect4/Laws/Machine/Handles.lean:5364-5366`), the `DeferredOk` users in
`src/Effect4/Laws/Program/Simulation/{Evaluate,Deliver,Actions,Drive}.lean`, the compiled
interpreter's four hook sites (`src/Effect4/Program/Compile.lean:1466`, `:1469`, `:1487`,
`:1491`), and the witnesses of twelve `deferred.*` census rows, which re-spell at `Completion`
(for instance `deferredStore_complete_stores_argument`,
`src/Effect4/Machine/Stores.lean:1272-1281`, witness of `deferred.complete-with-stores-effect`,
`Test/Audit/RuntimeCoverage.lean:968-971`). About twenty files, most of it deletion, but not a
narrow slice.

**The scheduled-wake machinery is dormant.** `WakeMode.scheduled`, `Task.wake`, `Cmd.wake`,
`RunInterp.wakeList`, and the policies `schedule`, `runBatch`, `delay`, `sweep`, `wakeTake` and
`wakeOne` (`src/Effect4/Machine/Wake.lean:62-65`, `:136-225`;
`src/Effect4/Machine/Fibers.lean:119`, `:749`, `:503`) have no producer in the tree: the register
says so (`Test/Counterexamples/REGISTER.md:113`, `SCHED-FB-PRODUCER`), and a search finds no
consumer of `schedule`, `delay`, `sweep`, `wakeTake` or `wakeOne` outside
`src/Effect4/Machine/Wake.lean` (*inferred* complete). The map treats the waiter protocol as
live infrastructure for the families to come without saying that today nothing produces a
scheduled wake. That is the fork in the road of §3: either a family lands that produces one, or
the machinery is dead code to cut.

**Two rulings the map's §8 does not cite.** DI-11 (`docs/DESIGN-ISSUES.md:85`) already ruled
Queue, Mailbox and PubSub composite programs and "never new machine stores"; DI-89
(`docs/DESIGN-ISSUES.md:163`) already ruled the route by which a module enters the language
(constructors, generated rows, or `Forms` templates with a typing lemma and one behaviour law),
and names `Schedule` as data over `iterate` in that route. `docs/core/language-cut.md:75` says
the opposite of DI-11. One of the three has to move.

**An adjacent error in the tree, not in the map.** The timer's header and one of its lemma
docstrings say that rc.112 posts the sleeper's resume on a dispatcher
(`src/Effect4/Machine/Timer.lean:21-27`, `:240-241`; also
`src/Effect4/Machine/Fibers.lean:2006-2012`). rc.112's `TestClock` fires a sleep with
`latch.openUnsafe()` (`vendor/effect-4.0.0-rc.112/src/testing/TestClock.ts:365`), and
`openUnsafe` flushes its waiters inline
(`vendor/effect-4.0.0-rc.112/src/internal/effect.ts:5600-5623`). The machine's `WakeMode.now`
is therefore the faithful transcription and nothing is owed there; the docstrings are wrong.

### 1.4 The five findings and the five changes

- **F1: sound.** See §1.1. The one correction is which code alphabet the cell depends on (§1.2,
  item 3).
- **R1: sound, and better prepared than the note says** — `denoteCompletion` and the bridge
  theorem already exist (`src/Effect4/Laws/Program/InterpR.lean:127-143`). Two things to add to
  its packet: the twelve `deferred.*` witnesses re-spell at `Completion`, and the narrowing
  lets `deferredPoll` answer the stored exit instead of a Boolean, which would shrink the
  signed exception DI-97 (`docs/DESIGN-ISSUES.md:171`) rather than leave it (*inferred*: the
  answer would be an option of a reified exit, which is a value `Ty` can write, while rc.112's
  own answer is an option of an effect, which it cannot).
- **F2: sound; R2 has a cost the note misses.** Deleting `MemoEntry.effect` removes the object
  of a green census clause (§1.2, item 5). R2 should either restate that clause against the
  cell or take the row to partial deliberately. R2 should also record what the machine already
  does differently from rc.112: on a hit after the build has finished, rc.112 runs the stored
  exit (`vendor/effect-4.0.0-rc.112/src/Layer.ts:241-250`), while the machine awaits the cell
  (`src/Effect4/Machine/Stores.lean:1996-2002`), which is one asynchronous registration more
  (*inferred*; the values agree because a completed cell resumes at registration,
  `src/Effect4/Machine/Stores.lean:1120-1127`).
- **F3: sound. R3's fields are not the cheapest fix for the consumer it names.** rc.112's
  `FiberImpl` has no parent pointer and no daemon flag either
  (`vendor/effect-4.0.0-rc.112/src/internal/effect.ts:528-552`; a parent tracks children,
  `:5279-5282`), so the two fields are machine bookkeeping, not transcription — which is fine,
  but should be said. For `statusOf` the trace is avoidable without them: `Api.load` always makes
  fiber 0 the root (`src/Effect4/Api.lean:251-260`), every other fiber record is created by
  `spawn`, which always emits `forked` (`src/Effect4/Machine/Fibers.lean:922-923`), and the two
  other creators are unused by the API (`src/Effect4/Machine/Fibers.lean:2162`, `:2173`; search
  finds no API caller, *inferred*). So "is this the root" is `f.id = Api.root` plus one lemma.
  What does need state, or the observable alphabet, is the other consumer: `Inspection.forked`
  (`src/Effect4/Api/Supervision.lean:285`) and the 501 lines of supervision laws stated over
  `forkedOf` (`src/Effect4/Laws/Api/Supervision.lean:1-37`). R3's packet must carry that move.
- **F4 and R4: the gap is narrower than stated, and the seam is wider.** The interface, the list
  twins, the reference instance and the property tests exist in OCaml (§1.2, item 6). What is
  missing is the Lean half: the carrier laws are stated only in OCaml, the twins are hand
  transcriptions rather than LCNF output, and nothing relates the hand prelude rows to the Lean
  definitions. R4 should be re-scoped as "lift the existing seven signatures and their laws into
  Lean, generate the list twins from LCNF, and keep the fast carriers property-tested against
  them", and it must cover the fiber table, the trace and the dispatcher, not only the stores
  (`ocaml/engine/api_engine.ml:10-121`, `ocaml/engine/externs.txt:50`).
- **F5 and R5: sound.** The concrete hazard is visible in one constructor: a finalizer name
  carries a parent scope key and a finalizer key side by side
  (`src/Effect4/Machine/Stores.lean:156`), as does the observer that drops it
  (`src/Effect4/Machine/Fibers.lean:102`). The scope state machine is already generic in its key
  type (`src/Effect4/Machine/Stores.lean:1299`), so the change is signatures, and the trivial
  structure erasure the OCaml table relies on keeps the carrier integer-keyed
  (`ocaml/engine/externs.txt:68-71`).

### 1.5 rc.112's event log as prior art for R3

`unstable/eventlog` is an application-level event store, not a runtime trace, but three of its
choices bear on R3.

1. **Entries are schema'd, stable-tagged, encoded data with a derived key**
   (`vendor/effect-4.0.0-rc.112/src/unstable/eventlog/Event.ts:1-12`,
   `vendor/effect-4.0.0-rc.112/src/unstable/eventlog/EventJournal.ts:281-290`). R3's observable
   alphabet should be exactly that: a generated codec type with append-only tags, which is what
   the estate already asks of every boundary value (D12) and what the wire tags already do.
2. **An entry is committed only after its handler succeeds**
   (`vendor/effect-4.0.0-rc.112/src/unstable/eventlog/EventLog.ts:3-8`,
   `vendor/effect-4.0.0-rc.112/src/unstable/eventlog/EventJournal.ts:395-416`): the log records
   accepted facts, not attempts. The machine's analogue is already in the session: a reply is
   *received* into `pending` and only counted when applied and consumed
   (`src/Effect4/Api/HostSession.lean:84-93`). So the observable record R3 wants is largely the
   session's ledger plus the fiber exits, not a second projection of the machine trace — that is
   the sharpest thing to take from the prior art.
3. **Idempotence by entry id and per-remote cursors**
   (`vendor/effect-4.0.0-rc.112/src/unstable/eventlog/EventJournal.ts:384-391`, `:418-467`): a
   consumer can resume from a position and a repeated entry is a no-op. The session's call ids
   give the same property for replies (`src/Effect4/Api/HostSession.lean:84-93`), and the run's
   journal already replays (`src/Effect4/Laws/Run.lean:164`). Conflict detection and compaction
   are replication features with no counterpart here; they should not be imported.

## 2. The catalogue

Classification: **(a)** composed, a first-order program over primitives this tree has or will
have; **(b)** a new store with a waiter-list policy or a keyed table; **(c)** a new kind of
machine state. Every classification is at the value level unless the row says otherwise, and
the schedule-level caveats are in the notes. Paths in the second column are under
`vendor/effect-4.0.0-rc.112/src/`.

| module | rc.112 state, and what it is built from | class | what it needs here |
| --- | --- | --- | --- |
| `Latch.ts` | `_isOpen`, a waiter array of resumes, and a pending batch (`internal/effect.ts:5569-5575`); `callback` await with splice-out from either list (`:5624-5640`); `open`/`release` post one coalesced `scheduleTask(flushScheduled, 0)` on the caller's dispatcher (`:5577-5599`, `:5612-5617`); `openUnsafe` flushes inline (`:5600-5623`) | (b) recommended; (a) possible at the value level | a cell holding an open flag and a broadcast waiter list, on the existing `schedule`/`runBatch` (`src/Effect4/Machine/Wake.lean:210-225`), six rows, one handle kind, no typing column |
| `Semaphore.ts` | `waiters: Set<observer>`, `taken`, `permits` (`Semaphore.ts:225-236`); `callback` whose observer re-checks `free` (`:207-223`); a raw `scheduleTask` sweep on the releaser's dispatcher that stops when no permit is free (`:257-268`); take re-polls (`:238-247`) | (a) over Ref and Latch | binder-term modify, a shared latch, re-poll loop; the sweep's decision moves from task time to release time (note 2) |
| `PartitionedSemaphore.ts` | closure variables `totalPermits`, `waitingPermits`, a map of partitions to waiter sets, and a live iterator over the map (`PartitionedSemaphore.ts:133-142`); permits handed out one at a time round-robin with inline resumes (`:144-176`); `callback` take (`:178-233`) | (a) | map atoms, a cursor key standing for the live iterator, Deferred (its inline wake is already the machine's `now` mode) |
| `Queue.ts` | the maker's dispatcher, capacity, strategy, a message list, a coalescing flag, and `Open`/`Closing`/`Done` with takers, offers and awaiters (`Queue.ts:343-386`, `:448-468`); `callback` for each waiter kind (`:1625-1637`, `:2002-2035`, `:2071-2082`); a coalesced `scheduleTask(releaseTakers)` on the stored dispatcher (`:1955-1975`); inline resumes in capacity release, finalize and shutdown (`:2037-2069`, `:2100-2114`, `:1191-1210`) | (a) by DI-11 | Ref with a record and lists, Latch for takers, Deferred for offerers; two named deviations (note 3); the buffer costs a list copy per offer |
| `PubSub.ts` | a ring-buffer backing with per-slot subscriber counts (four variants), a map from subscription to poller lists, a Scope, a shutdown Latch, a shutdown flag, a strategy (`PubSub.ts:278-292`, `:1859-1876`, `:2405-2420`, `:2637-2668`), optional replay buffer (`:3043-3088`); pollers are Deferreds completed inline in the strategy loops (`:1439-1461`, `:2994-3021`); back-pressured publishers park on Deferreds (`:2729-2747`); subscriptions are child scopes (`:1304-1315`) | (a) | Latch (shutdown), records and lists in a Ref, an allocated subscription id, `Scope.fork`; cost is a buffer copy per publish (note 4) |
| `Pool.ts` | scope, shutting-down flag, usage counter, a resize Semaphore, an item set, an intrusive available list, an invalidated set and a waiter set (`Pool.ts:117-127`), items with refcount and finalizer (`:150-159`), stored `acquire` and strategy (`:374-375`) | (a) with a program value | Scope per item, Semaphore, Latch for the count wake (`:700-714`), fork, sleep, Queue for the time-to-live strategies (`:941-1011`), raw `setContext` (`:883`) as an ordinary context action |
| `Cache.ts` | a map from key to entry (`Cache.ts:111-117`, `:212`), entry with expiry, awaiter count and the lookup fiber (`:138-143`, `:648-672`), stored `lookup` and `timeToLive` (`:115-116`); immediate daemon fork of the lookup (`:657`); a raw exit observer that edits the map (`:625-639`); join with awaiter counting and interrupt of the last leaver (`:662-671`); clock reads for expiry (`:635`, `:674-679`); insertion-order eviction (`:681-690`) | (a) with a program value | map atoms, handles in values, fork and join, clock read, the exit observer as an `onExit` wrapper or a watcher fiber (note 5) |
| `ScopedCache.ts` | `Open` with a map or `Closed` (`ScopedCache.ts:78-83`), entry with expiry, a Deferred and a Scope (`:104-108`), stored `lookup` (`:151-155`); Scope and Deferred per miss (`:319-320`); the lookup under `Scope.provide` (`:375`); completion in `onExit` (`:376-383`); eviction closes scopes on forked daemons and awaits them (`:396-413`) | (a) with a program value | as Cache, plus polymorphic `Deferred.done` of an exit and a scope-provision form |
| `RcMap.ts` | `Open` with a map or `Closed` (`RcMap.ts:99-142`), entry with a Deferred, a Scope, a finalizer, an idle time-to-live, an idle fiber, an expiry and a refcount (`:156-165`), stored `lookup` and a captured context (`:75-80`); the lookup runs as a root fiber under a merged context, bound to the entry scope, completing the Deferred from a raw observer (`:564-572`); release drops the refcount and starts an idle-expiry sleep loop (`:736-775`) | (a) with a program value | detached immediate fork with an explicit context, `runIn` (`src/Effect4/Program/Eff.lean:361`), sleep, map atoms, clock read |
| `RcRef.ts` | `Empty`, `Acquired` with value, scope, idle fiber, refcount and an invalidated flag, or `Closed` (`internal/rcRef.ts:14-33`), a Semaphore of one (`:51`), stored `acquire` (`:52`); acquisition under the permit with the scope provided (`:110-134`); idle expiry by a sleep fiber bound to the owner scope (`:160-173`) | (a) with a program value | Ref, Semaphore, Scope, sleep, fork, `runIn` |
| `FiberHandle.ts` | `Open` with an optional fiber or `Closed`, plus a Deferred (`FiberHandle.ts:59-60`); `acquireRelease` (`:146-160`); a root fork under the parent's context (`:819`); a raw exit observer (`:410`); interruption with the reserved id −1 (`:396-405`); a process-global interrupted fiber (`:665`) | (a) | Ref, Deferred, detached fork, a watcher fiber for the observer, the structure's own record of what it interrupted in place of the reserved id (note 6) |
| `FiberSet.ts` | the same with a set of fibers (`FiberSet.ts:56-67`, `:154-167`, `:402-426`, `:687-701`, `:920-925`) | (a) | as FiberHandle, plus list removal by equality |
| `FiberMap.ts` | the same with a keyed map and an "only if missing" option (`FiberMap.ts:60-71`, `:162-179`, `:436-481`, `:1366-1384`) | (a) | as FiberSet, plus map atoms |
| `SubscriptionRef.ts` | a value, a Semaphore of one and an unbounded PubSub with replay one (`SubscriptionRef.ts:37-41`, `:111-119`); every set publishes (`:296-299`); effectful updates hold the permit across the effect (`:462-472`) | (a) | Ref, Semaphore, PubSub; `changes` is a stream and belongs to the DI-11 stream route |
| `SynchronizedRef.ts` | a backing Ref and a Semaphore of one (`SynchronizedRef.ts:37-41`, `:65-70`); effectful updates hold the permit (`:295-305`) | (a) | Ref, Semaphore, binder-term modify for the pure variants |
| `Random.ts` | a context reference whose default draws from the host (`internal/random.ts:10-21`, `Random.ts:52-58`); `withSeed` provides a generator object with 256 words of state (`Random.ts:290-368`, `:381`) | (a) | a reference whose value is a Ref handle to generator state, one pure step atom, and a seed decided at load (note 7) |
| `References.ts` | keys with defaults for log level, annotations, spans, stack frame, tracer flags and loggers (`References.ts:185-635`, `internal/references.ts:10-68`), two of them cached on the fiber (`internal/references.ts:49-57`) | (a) | the existing reference mechanism (`src/Effect4/Machine/ContextMap.lean:264-276`), one reserved key and carrier each; their consumers are observations, not state |
| `ClockRef` | a context reference whose default is the live clock (`internal/effect.ts:6033-6066`); `sleep` and the time reads go through it per fiber (`:6110-6121`); `TestClock` is itself library code over a sorted sleep array of Latches and two Semaphores (`testing/TestClock.ts:249-381`) | (a) for the clocks rc.112 ships; refusal for user-written clocks | a first-order clock descriptor in the context that `sleep` dispatches on; the machine clock as the default; in-program advance is the S7 packet (`src/Effect4/Api/TestClock.lean:23-25`) |
| `Request.ts`, `RequestResolver.ts` | a process-global map from resolver identity to batches and an object pool (`internal/request.ts:81-82`), a batch with its entries, delay and run effects and its fiber (`:70-79`); a resolver is a record of functions (`RequestResolver.ts:80-105`); each request is a `callback` (`internal/request.ts:41-49`); a root fiber waits the delay, default a yield (`RequestResolver.ts:236-244`), then runs the batch (`internal/request.ts:130-164`), interrupted early when collection stops (`:169-172`) | (a) with a program value | Ref holding the batch map, Deferred per entry, detached fork, yield or sleep, interrupt; resolver identity becomes an allocation, and the object pool is dropped (note 8) |
| `Schedule.ts` | a schedule is an effect producing a step function with private mutable state (`Schedule.ts:250-260`, `:262-273`, `:1090-1195`); repeat and retry read the clock, call the step, sleep the delay and loop (`:377-406`, `internal/schedule.ts:13-80`) | (a), already ruled | a schedule descriptor as data with a pure step, expanded at the use site by DI-89's `Forms` route; `timeout` needs a first-exit race (note 9) |

Notes on the rows that are not obvious.

1. **Latch is the only row I would make a store.** Everything it does is expressible over a Ref
   holding an open flag and a gate Deferred, so at the value level it is composed; what is not
   expressible is *when* its waiters run. rc.112 wakes them from a task on the opener's
   dispatcher, coalesced (`vendor/effect-4.0.0-rc.112/src/internal/effect.ts:5577-5599`), so the
   opener keeps running and the waiters run in a later host callback. A Deferred wakes them
   inline inside the completing step (`src/Effect4/Machine/Stores.lean:1142-1152`, drained by
   `src/Effect4/Machine/Fibers.lean:1780-1789`), so the waiter observes the opener's later writes
   differently. The machine already has the whole scheduled-wake protocol and no producer for it
   (§1.3); Latch is the producer, and it is the primitive rc.112 itself builds PubSub, the test
   clock and the time-to-live cache on
   (`vendor/effect-4.0.0-rc.112/src/PubSub.ts:289`,
   `vendor/effect-4.0.0-rc.112/src/testing/TestClock.ts:331`,
   `vendor/effect-4.0.0-rc.112/src/internal/effect.ts:4244`).
2. **Semaphore composed over a latch keeps the winners and loses the silence.** rc.112 decides
   *at task time* which waiters to wake and leaves the rest untouched, in place
   (`vendor/effect-4.0.0-rc.112/src/Semaphore.ts:257-268`, where an observer whose permits are
   not free returns without removing itself, `:214-218`). A shared latch wakes every waiter, and
   those that cannot take re-park. The permits granted, and their order, agree (*inferred*, by
   reading both loops); the trace does not, and waiters that re-park take new tokens. Semaphore
   is the hub: SynchronizedRef, SubscriptionRef, RcRef, Pool and the event journal all use one of
   permit one as a mutex (`vendor/effect-4.0.0-rc.112/src/SynchronizedRef.ts:67`,
   `SubscriptionRef.ts:114`, `internal/rcRef.ts:51`, `Pool.ts:365`,
   `unstable/eventlog/EventJournal.ts:378`).
3. **Queue's two deviations.** rc.112 posts the taker release on the dispatcher *stored at make*
   (`vendor/effect-4.0.0-rc.112/src/Queue.ts:456`, `:1974`); composed code can only post on the
   dispatcher of the fiber doing the offer, because nothing in the language addresses another
   fiber's dispatcher. And `releaseTakers` wakes takers one at a time while messages remain
   (`:1955-1967`), where a latch wakes the batch and the losers re-poll. Both are named refusals,
   or Queue becomes a store, where `WakeMode.scheduled owner` and the re-poll reply already exist
   (`src/Effect4/Machine/Wake.lean:62-65`, `:136-143`).
4. **PubSub is composed in rc.112 already**, which is the strongest single piece of evidence for
   the owner's hypothesis: its waiters are Deferreds, its shutdown is a Latch, its subscriptions
   are scopes, and only its buffer is a hand-written array. The buffer is also the cost: as a
   value list, publishing copies the buffer, so a high-throughput subscription is quadratic
   until Val lists get a carrier of their own, which is the container work of R4.
5. **A raw exit observer becomes a watcher fiber.** rc.112 attaches a callback to another fiber
   (`vendor/effect-4.0.0-rc.112/src/Cache.ts:625`,
   `vendor/effect-4.0.0-rc.112/src/FiberSet.ts:410`). The first-order replacement is a daemon
   that awaits the target and then does the bookkeeping: its observer is added at the same point,
   observers fire in order, and a resume evaluates the waiter inline before the next observer runs
   (`src/Effect4/Machine/Fibers.lean:1614-1615`, `:1746-1749`), so the bookkeeping lands where
   rc.112's callback lands (*inferred* from those two clauses). The costs are one extra fiber per
   watched fiber and one more entry in every fiber listing; pin the watcher to the structure's
   scope so it is not reported as a loose daemon (`src/Effect4/Api/Supervision.lean:235-244`).
6. **The reserved interruptor.** rc.112 marks its own interruptions with fiber id −1
   (`vendor/effect-4.0.0-rc.112/src/FiberSet.ts:262-266`), which the machine's identity type
   cannot hold. The composed structure can record which members it interrupted in its own state
   instead; the two differ only when a member is interrupted by the structure and from outside at
   once (*inferred*).
7. **Randomness.** The seeded generator is a pure function of its state, so it composes over a Ref
   and one step atom; matching rc.112's `withSeed` sequences means implementing its generator as
   that atom. The unseeded default reads the host
   (`vendor/effect-4.0.0-rc.112/src/internal/random.ts:13-18`), which is nondeterministic, so any
   deterministic choice the machine makes is one of rc.112's admitted behaviours; the seed
   belongs in the run's load, beside the answers.
8. **Batching's identity.** rc.112 keys its batches on the resolver *object*
   (`vendor/effect-4.0.0-rc.112/src/internal/request.ts:82`), which a first-order value cannot
   have. Either the resolver is allocated (its batch map is a Ref minted when the resolver is
   made) or it is a declared subterm whose identity is its path, the way a layer's is
   (`src/Effect4/Program/Eff.lean:401-406`). The object pool (`internal/request.ts:81`) is a
   memory optimisation with no semantics and should be dropped.
9. **`timeout` and the first-exit race.** rc.112 builds `timeout` on `raceFirst`
   (`vendor/effect-4.0.0-rc.112/src/internal/effect.ts:3677-3704`), which is `raceAllFirst`
   (`:1535-1580`, `:1623-1660`): the same fork-and-observe loop as `raceAll` (`:1477-1533`) with
   acceptance at the first *exit* rather than the first success. Spelling it as `raceAll` over
   exit-wrapped entrants is plausibly exact up to the extra exit frames (*inferred*; it should be
   checked against the truth harness before either a row or a form is written).
10. **STM, which the map note raised.** rc.112's transaction state is a journal map inside a
    context service, provided per transaction, with versions on the TxRef objects and a scheduled
    wake per retrying waiter (`vendor/effect-4.0.0-rc.112/src/Effect.ts:24211-24223`, `:24273-24354`;
    `vendor/effect-4.0.0-rc.112/src/TxRef.ts:61-67`). Composed: one Ref holding every transactional
    cell so that a commit is one atomic modify, a journal Ref provided as a service, and a latch
    per retry. It is (a), not a new kind of state; what it needs beyond the basis is nothing.
11. **The memo world is the same shape as RcMap.** rc.112's layer memo map is library code over
    Deferred, Scope and a map (`vendor/effect-4.0.0-rc.112/src/Layer.ts:390-458`), and the tree
    made it a store (`src/Effect4/Machine/Stores.lean:551-572`) keyed by the layer's path. Entry
    for entry it is RcMap without a time-to-live. I would not unwind it — its census rows are
    green — but when RcMap lands, the two should be read side by side, and the store is the
    precedent for "a behaviour found by declaration path" that note 8 and §3 item 5 rely on.

## 3. The minimal primitive basis

Six items. The first four are language work already on the plan, the fifth is a door the
profile has deliberately kept shut, and the sixth is the one machine addition I would make.

1. **Polymorphic `Ref<A>` and `Deferred<A, E>` rows.** The types exist
   (`src/Effect4/Program/Ty.lean:61`, `:64`); the rows still spell both at `number`
   (`src/Effect4/Program/Native.lean:90-99`). This is decisions row 42 with the template-table
   work. Cost: the checker's rows become schematic, the printer must emit explicit type
   arguments where the handle's parameters are not determined by the call
   (`src/Effect4/Program/Native.lean:92-97`), and nothing in the machine changes, because the
   heap is already a list of values (`src/Effect4/Machine/Stores.lean:843`). The typed-state
   invariant is designed for it: the world already carries per-cell tables rather than a constant
   column (`docs/research/2026-09-18-typed-state-composed-graph.md:206-258`).
2. **Read-modify-write rows that take a binder term.** Every composed structure needs one atomic
   step that reads its record, computes the next one and answers something, with no scheduling
   point in between; today the function is one of five names
   (`src/Effect4/Machine/Stores.lean:61-72`), which cannot express "take one permit if there are
   at least `n`". The fix is already written down: the row carries a term evaluated at the
   environment extended by the current value, as `iterate` does
   (`docs/core/language-cut.md:25`), and `FnName` retires. Cost: the operation alphabet carries a
   term and its captured values, the kernel table generalises
   (`src/Effect4/Laws/Machine/RefKernel.lean:7-10`), and the restatement of `refSet`'s answer
   rides along (`docs/DESIGN-ISSUES.md:172`).
3. **Atoms for association maps, and list removal.** The carrier already holds a map: a list of
   pairs, in insertion order, which is also the order rc.112's maps iterate in
   (`src/Effect4/Store/Val.lean:150-167`). What is missing is the first-order operations over it
   — lookup, insert or replace, remove, keys, size — and removal of a list element by equality.
   Cost is the atom-table pattern, one row, one evaluation arm, one typing scheme and one
   prelude line each (`src/Effect4/Machine/Term.lean:146-165`); the last slice added thirteen
   atoms this way. Records (decisions row 2) would make the entry types readable; nested pairs
   work without them.
4. **Handles inside values, typed.** Every structure holds handles — deferreds in a waiter list,
   fibers in a set, scopes in a cache entry — so the world must say what a handle in a value
   stands for while `Val.hasTy` stays coarse
   (`src/Effect4/Machine/Value.lean:41-45`). That is the `HandlesFit` ruling already owed on the
   milestone (`docs/research/2026-09-18-typed-state-composed-graph.md:277-283`).
5. **A program value.** Six modules keep a behaviour and run it later, on a fiber that does not
   know it: the cache's lookup, the scoped cache's lookup, the reference-counted map's lookup,
   the reference-counted ref's acquire, the pool's acquire, the resolver's batch program. The
   data this needs already exists as machine state: a program position with its captured values
   and context (`src/Effect4/Machine/Stores.lean:134-142`), run through the point the compiler
   already resolves (`src/Effect4/Program/Compile.lean:84-85`, `:311-312`) and typed by a
   predicate the milestone already generates
   (`src/Effect4/Laws/Program/Typed/State.lean:41`, `:67-69`). Promoting it to a value means one
   value shape, one type former, one row that runs it, a printed form (an arrow function) and a
   read form. This is the profile's closed door
   (`docs/core/language-cut.md:27`: "no functions as values … the basis's own direction is
   content-addressed programs … Not designed"), and it is an owner decision (§5). A defunctionalised
   closure is not a host closure, so the basis's exclusion (`docs/DESIGN-BASIS.md:761-767`) does
   not by itself refuse it. The narrower alternatives are to restate those six APIs so the
   behaviour is supplied at each use, or to allow only closed behaviours found by declaration
   path, as a layer's build is (`src/Effect4/Program/Eff.lean:401-406`).
6. **A `Latch` store family.** A cell holding an open flag and a broadcast waiter list, on the
   protocol the tree already has: register, cancel with the owed-wake clause, `schedule` with its
   coalescing guard, `runBatch` for the posted task, and the inline `wakeAll` for the unsafe open
   (`src/Effect4/Machine/Wake.lean:129-225`). Six rows (make, open, release, close, await, is
   open), one handle kind byte (`src/Effect4/Machine/Value.lean:56-67`; byte 6 is reserved for
   Queue, so a latch takes the next one), one arm in the wake hook
   (`src/Effect4/Machine/Stores.lean:2156-2159`), and one arm each in the operation and answer
   typing. No typing column: waiters carry unit payloads and resume with void, as the timer's do,
   so the position census should ask for no new source row (*inferred*: the timer store has none
   in `src/Effect4/Laws/Program/Typed/Sources.lean:20-72`). It is also
   the first producer of a scheduled wake, which flips a named refusal
   (`Test/Counterexamples/REGISTER.md:113`). Census rows come from one span,
   `vendor/effect-4.0.0-rc.112/src/internal/effect.ts:5568-5657`, and need a row kind the
   coverage document does not yet list (`docs/RUNTIME-COVERAGE.md:29-32`).

Deliberately **not** in the basis: stores for Semaphore, Queue, Pool or PubSub (notes 2 to 4);
a primitive that attaches a hook to another fiber's exit (note 5 replaces it with a watcher
fiber); and a primitive that posts work on another fiber's dispatcher, which only Queue's wake
would use (note 3).

**The trade-off, honestly.** Library code over a Ref is cheap to add and expensive to run and to
prove. Each operation is one read-modify-write over a whole record, so a structure with a buffer
costs a copy of the buffer per operation in both back ends, since a value list is an OCaml list
(`src/OCaml5/Lcnf/Translate.lean:239-255`); a queue or a publish-subscribe buffer becomes
quadratic in the buffer length, where a dedicated store can hold the carrier the OCaml engine
already knows how to swap (`ocaml/engine/externs.txt:53-57`). The proof cost runs the other way
from what a first reading suggests. A store's laws are equations about a pure function, proved
once, the way the promise store's are (`src/Effect4/Machine/Stores.lean:1183-1291`), and its
waiter behaviour inherits the protocol's proved clauses
(`src/Effect4/Machine/Wake.lean:255-322`). Library code has no such statement: its correctness
is a property of a *program* under every interleaving the tape admits, and this tree has no
program logic for that — the typed-state invariant gives types, not mutual exclusion. So a
composed module's evidence is a typing lemma and a behaviour law per form (the route DI-89
already fixed, `docs/DESIGN-ISSUES.md:163`) plus differential runs, while a store's evidence can
be green census rows. Against that, a store costs alphabet: rows in the operation and answer
typing, a typing column if it holds values, an OCaml carrier, and a position for the census —
which is why the recommendation is one store, not five.

## 4. Landing order

Nothing here starts before the typed-state milestone is finished; the milestone's own order
stands (`docs/research/2026-09-18-typed-state-composed-graph.md:289-300`). Two of the map note's
changes and four of §3's items are prerequisites that already have owners on the plan, so the
first thing this order does is name which ones this catalogue is waiting on.

**Prerequisites (other people's slices).** The milestone; the open Tier 3 items; then the
language series with decisions row 42 (§3 item 1), the binder-term rows (§3 item 2), and the
record types of row 2 if the owner wants readable entry types. `HandlesFit` (§3 item 4) is a
ruling owed on the milestone, not a slice.

**Slice 1 — promise cells hold data.** The map note's R1 and R2, corrected by §1.4: narrow the
cell and the owed resume to `Completion`, delete the memo copy, delete `CompletionShaped`,
`DeferredOk`, `StoredCodeNoRace` and `DeferredCodes`, re-spell the twelve `deferred.*` witnesses
at `Completion`, and restate or re-mark the `layer.memo-build-once` clause. Add the promise rows
the composed modules need at polymorphic types: completion from an exit, interruption, and the
poll that answers the stored exit (which shrinks DI-97). Acceptance: the census rows named above
stay green or are marked deliberately, and the source table is re-pinned in the same commit.
Why first: every module in §2 stores exits in promises, and the invariant deletions make the
later slices smaller.

**Slice 2 — the data layer, and the modules that need nothing else.** The association-map and
list-removal atoms (§3 item 3). Then the composed modules that need no new primitive: the
schedule descriptors with repeat and retry (DI-89's route), `timeout` once the first-exit race
is checked (note 9), the partitioned semaphore (its wake is already inline), and the fiber
handle, set and map with watcher fibers (note 5). Each lands as a form with a typing lemma and
one behaviour law, plus census rows citing the rc.112 lines in §2's table.

**Slice 3 — the latch.** §3 item 6, as a store family. Acceptance: the refusal row for "no
producer of a scheduled wake" flips (`Test/Counterexamples/REGISTER.md:113`), the new census
rows are green against `vendor/effect-4.0.0-rc.112/src/internal/effect.ts:5568-5657`, and the
truth harness runs a program that opens a latch with waiters on it. This is the slice that
decides the question in §5 item 5: if it is refused, the scheduled-wake machinery should be
deleted in the same breath.

**Slice 4 — the mutex family.** Semaphore composed over a Ref and the latch, with its refusal
row for the sweep's decision point (note 2); then the synchronised ref, which is a Ref and a
permit. Both are small, and both unlock later slices.

**Slice 5 — the buffers.** Queue over a Ref, the latch and deferreds, with the two named
deviations (note 3); then the publish-subscribe structure and the subscription ref (its change
feed waits for the stream route). Measure here, not before: if the buffer copy is the cost §3
predicts, this is the slice that justifies the container work of R4 for value lists.

**Slice 6 — the behaviour-holding modules.** First the owner's decision on §3 item 5. Then, in
this order because each reuses the last: the reference-counted ref, the reference-counted map,
the scoped cache, the cache, the pool, and request batching. Read the memo world beside the
reference-counted map when it lands (note 11).

**Slice 7 — the environment.** Randomness as a reference over a Ref and a step atom with the
seed in the load (note 7); the remaining context references as data; the clock descriptor with
the in-program advance of the S7 packet, and a refusal row for user-written clocks.

Independent of this order: the map note's R3 and R5 can run beside slices 2 and 3 (R3's
observable alphabet should be read against §1.5 first), and its R4 before slice 5 if the
measurement asks for it. After slice 5, the waiter-list policies that no family uses — the
re-poll reply (`src/Effect4/Machine/Wake.lean:142-143`), the single wake (`:163-166`), the
counted wake (`:169-172`) and the sweep (`:188-208`) — are dead and should be deleted with a
line in the register saying which family would have used each.

## 5. Open questions for the owner

1. **What fidelity does a composed module owe rc.112?** Values, schedule, or trace (§0).
   *Recommendation: values, with claims stated relative to the decision tape — the plan's own
   words (`docs/research/2026-09-16-foundational-language-implementation-plan.md:767`) — and a
   named refusal row for each schedule deviation. Promote a module to a store only when a
   differential failure that matters shows up, not before.*
2. **DI-11 or `docs/core/language-cut.md`?** They contradict each other on whether Queue,
   PubSub, Semaphore and Latch are composite programs or store families
   (`docs/DESIGN-ISSUES.md:85` against `docs/core/language-cut.md:75`), and the map note's §8
   takes the second side. *Recommendation: keep DI-11, amend it to name the one primitive it
   left vague — the waiter list becomes program-visible as `Latch`, not as a general waiter-list
   row — and fix the language-cut line in the same commit.*
3. **What does a composed module print?** Its expansion, or a call to rc.112's module? If it
   prints the expansion, rc.112's Queue is never exercised by the truth harness and interop with
   host-owned queues goes through external rows, which is what DI-11 already says; if it prints
   the call, the machine must transcribe that module, which is the store route.
   *Recommendation: print the expansion; keep external rows for host-owned instances.*
4. **Is the program value in or out?** Six modules need it (§3 item 5), and so do user-written
   schedules and, later, stream operators. *Recommendation: open the door in its narrow form — a
   program position with its captured values, one type former, one row that runs it, no function
   types beyond it — because the alternative (restated APIs, or closed behaviours found by
   declaration path) fails exactly the case Effect code writes every day, a lookup that captures
   a variable from its creation site. If the owner prefers to keep it shut, slice 6 shrinks to
   the declaration-path form and the six modules keep an API that is not rc.112's.*
5. **Latch, or delete the scheduled-wake machinery?** Today nothing produces a scheduled wake
   (§1.3). *Recommendation: land the latch. It is rc.112's own building block for the
   publish-subscribe structure, the test clock and the time-to-live cache; it gives the protocol
   its first producer; and without it every composed structure wakes its waiters inline, which is
   the one place where composed code stops feeling like Effect. If the answer is no, delete the
   protocol's unused half in the same slice rather than leaving fixture-only code.*
6. **When do R1 and R2 land?** The map note asks for before the ledger pins its count; this
   brief asks for after the milestone. *Recommendation: after, with one deliberate re-pin. The
   blast radius crosses the guard and simulation families (§1.3), which is where the milestone's
   own work is, and the promise column's obligation is the same shape before and after. The one
   argument for landing early is that the column's proof is simpler over data than over code; if
   that proof has not been written when the milestone reaches it, take R1 then.*
7. **Where does randomness come from?** *Recommendation: a seeded generator whose state lives in
   an ordinary Ref behind the reference, with the seed supplied at load beside the host answers.
   Unseeded rc.112 is host nondeterminism, so a fixed seed is a refinement of it, and replay
   needs nothing new.*
8. **Can a program provide its own clock?** *Recommendation: no, for now. The machine clock is
   the default and matches the test clock's shape; a first-order clock descriptor that `sleep`
   dispatches on is a later slice, and user-written clock objects are refused by name, because
   they are code in the context. Register the refusal now, as the map note also recommends.*

---

Reading receipt. Everything above was read at `72698899` from the files cited; nothing was
built, run, proved or stamped. The statements I marked *inferred* are: that no path stores a
non-completion program in a promise cell; that `Point.tape` and `Capture.tape` are read by
nothing; that the scheduled-wake policies have no consumer outside their own module; that the
API never creates a fiber except through `load` and `spawn`; that a watcher fiber lands its
bookkeeping where rc.112's exit observer lands; that permits granted and their order agree
between rc.112's sweep and a latch-plus-repoll semaphore; that a first-exit race is `raceAll`
over exit-wrapped entrants; that the machine's memo hit costs one asynchronous registration more
than rc.112's; and that a latch needs no typing column. Each is a search or a reading of two
definitions, not a proof, and each would be settled by the slice that lands it.

