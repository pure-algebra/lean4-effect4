# The machine's stores, its logs, and the promise store: a full map (2026-09-19)

The owner asked where the promise store comes from, and for a full map of the stores and the
event log. These semantics are the machine's architecture, and the lowered form should be one
we can build verified implementations of. Codex is implementing Tier 3 (the typed-state
ledger) while this note is written, so it changes no code. It maps what is there, names five
findings, and gives an order that does not collide with that work.

Everything below was read at `23e668b0` (3.5 landed).

**Reviewed the same day** by `docs/research/2026-09-19-stateful-api-catalogue.md` §1. Its
corrections are applied below. Two things it adds are not repeated here and should be read
there: §1.3 lists state this map does not cover (the fiber's context and the services in it,
captures, races, the code inside dispatcher tasks, `Point.completed` and the inert
`Point.tape`), and it measures R1's blast radius at about twenty files rather than the six
named in §7.

## 0. The short answer

**Where the promise store comes from.** It transcribes rc.112's `Deferred`
(`Deferred.ts:58-61`: an optional stored `effect` and an optional `resumes` array). It lives
in `Stores.deferreds` (`Machine/Stores.lean:1079-1177`). It has two populations of cells:

- **user promises**: `Deferred.make/succeed/fail/await`, spelled at `number` in this cut;
- **memoised layer builds**: `memoBuild` allocates a cell from the same store, and
  `memoComplete` completes it with the build's exit (rc.112 `Layer.ts:396-416`).

The scheduler never touches the store directly. It goes through interpreter hooks:
`syncState` (`Machine/Fibers.lean:490`), which carries most promise operations, `registerAsync`,
`dueResumes`, `wakeList` (`:491-503`) and `prepareAnswer` (`:592-593`). `answerCode` (`:495`)
turns a completion into code and never touches the store. That layering is right.

**What is wrong with it**, in one line each (details in §4):

1. The cell is typed as *code* (`completion : Option Program`), while only three data
   shapes are ever stored. An invariant and a partial decoder make up the difference.
2. The memo entry keeps a second copy (`MemoEntry.effect`) that no machine step reads.
3. The event log (`RunMachine.trace`) is excluded from the observation the theorems compare,
   yet the API reads fork parentage back out of it.
4. The OCaml engine swaps every store's representation by hand (lists to tables), and none of
   those swaps is proved.
5. Four identity spaces (scope keys, finalizer keys, park tokens, race ids) are bare `Nat`,
   and the first two share one counter.

**The lowered form I recommend** (§6): stores hold data, never code; state is the truth and
the log is write-only; containers sit behind a small interface with laws, proved once in Lean
and implemented once in OCaml. The first two findings should land **before** the ledger pins
its obligation count, because they change positions the ledger walks (§7).

## 1. The whole state, top down

The machine is one record, `RunMachine` (`Machine/Fibers.lean:415-433`), parametric in the
code type `κ`, the saved-fiber type `φ`, the frame-event type `η` and the store type `St`.
Three instances run it:

| instance | code `κ` | saved fiber `φ` | frame events `η` | stores `St` | where |
| --- | --- | --- | --- | --- | --- |
| compiled machine | `Prim` (frames) | `FrameFiber` | `FrameEvent` | `Stores` | `Api.run` |
| reference machine | `RProgram` (free-monad tree over `RSig`) | `RSaved` | `Unit` | `Stores` | `InterpR.lean:94` (`RState`) |
| OCaml engine | generated `prim` | generated `frame_fiber` | generated `frame_event` | generated `stores`, containers swapped | `ocaml/engine/api_engine.ml` |

There is a fourth instance: the stores module's own interpreter (`Machine/Stores.lean:2167-2272`),
which runs the stores' own name alphabet natively.

The reference machine and the compiled machine share the record *and the stores*. The code a
promise cell holds is the stores module's own alphabet, `Program := Prim Name Thunk …`
(`Machine/Stores.lean:538`). The compiled machine runs a different alphabet and embeds the
stored code (`embed`, `src/Effect4/Program/Compile.lean:358`); the reference machine decodes it.
So the store depends on *a* code type, which is what F1 is about.

### 1.1 `RunMachine` (the process)

| field | type | what it is | rc.112 |
| --- | --- | --- | --- |
| `fibers` | `List RunFiber` | every fiber ever spawned, exited ones included | the live `FiberImpl`s |
| `races` | `List Race` | `raceAll` bookkeeping in flight | `:1493-1531` |
| `nextId`, `nextToken`, `nextRace` | `Nat` | fresh fiber ids, park-guard tokens, race ids | object identity |
| `middlewareInstalled` | `Bool` | the `interruptChildren` latch | `:6656-6658` |
| `armed` | `List FiberId` | host callbacks scheduled, in arming order | `Scheduler.ts:207-212` |
| `state` | `St` = `Stores` | the service state (§2) | |
| `trace` | `List RunEvent` | the event log (§3.2) | none: diagnostic |
| `stuck` | `Option Stuck` | a state rc.112 cannot reach, made visible | none |

### 1.2 `RunFiber` (one fiber; `Fibers.lean:229-247`)

Fifteen fields (`:232-246`) transcribe the modelled part of rc.112's `FiberImpl`, which declares
twenty-two (`vendor/effect-4.0.0-rc.112/src/internal/effect.ts:528-552`; the scheduler, tracer,
log-level, stack-frame and metrics fields have no counterpart). The docstring at `:223` says
seventeen and is stale:

- `id`
- `frame`: the saved execution state. For the compiled machine this is `FrameFiber`
  (`Frames.lean:307-318`): `current`, `stack`, `interruptible`, `interruptedCause` and
  `deferredInterrupt`, which is the C and K of a CEK machine.
- `running`
- `parked`: `notParked`, or `withGuard token`.
- `pending`: outstanding parks with their token, what they wait on, and the exits collected.
- `finalizing` and `exit`.
- the yield budget: `currentOpCount`, `maxOpsBeforeYield`, `preventYield`, `yieldOverride`.
- `observers` and `children`.
- `dispatcher`: priority buckets of `Task`s.
- `context`.

### 1.3 The code and its continuations

`Prim` (`Frames.lean:100-160`) is rc.112's op set:
- `success`/`failure`/`sync`/`suspend`/`withFiber`/`yieldableError`;
- the continuation frames `onSuccess`/`onSuccessConst`/`onFailure`/`onSuccessAndFailure`/
  `onExit`/`exitFrame`/`setInterruptible`/`iterator`/`whileLoop` (the frame alphabet keeps
  `whileLoop` although `Eff` retired it);
- `yieldNowWith`, `async` and `asyncFinalizer`.

Continuations are *names* (`ν`) with a total interpretation (`PrimInterp`), never closures
(DB-02). This is defunctionalisation in Reynolds' sense, and it is why every piece of state
here is first-order data.

## 2. The stores (`Stores`, `Machine/Stores.lean:1719-1733`)

| store | type | rc.112 origin | key space | written by | read back by | typing source (typed-state) | OCaml engine |
| --- | --- | --- | --- | --- | --- | --- | --- |
| `refs` | `List Val` | `Ref.ts` | `RefKey` = allocation index | `refMake`, `refSet`, the update/modify rows (`refStep`, now the kernel table `refStepOf`) | `refGet`, every read-modify-write | `HeapNat` (`Progress.lean`) | `val_ M.t` (externs E3) |
| `deferreds.cells` | `List DeferredCell` | `Deferred.ts:58-61, 140-185, 1648-1662` | `DeferredKey` = allocation index | `deferredMake`, `deferredCompleteWith`, `deferredInterruptWith`, `memoBuild`, `memoComplete` | `registerAsync` (resume at once when done), `isDone`, `poll`, `wakeBatch` | `PromiseTable` column (`Typed/Sources.lean:53`) | `deferred_cell M.t` (E4) |
| `deferreds.due` | `List (Owed Program)` | `Deferred.ts:1655-1659` (`resumes` cleared, then called) | none | `complete`, `wakeBatch` | `dueResumes` (drained by the machine) | `PromiseTable` (`Owed.code`) | generated list |
| `scopes` | `List ScopeEntry` (key + `Scope` state machine: `empty`/`openEmpty`/`openInline`/`openMap`/`closed exit`) | `Scope.ts`, `internal/effect.ts:3833-3922` | scope key from `nextName` (sparse) | `scopeMake`, `scopeFork`, `scopeAdd`, `scopeRemove`, close | `scopeIsClosed`, `scopeStatus`, `closeScope`, `scopeAdd` on a closed scope | `closed.exit` refused until the release DI (Sources:57) | `scope_entry M.t` (E5) |
| `memo` | `List MemoMap`, each `entries : List (LayerId × MemoEntry)` | `Layer.ts:230-250, 396-442` | memo-map id from `nextName` | `memoFork`, `memoGet`, `memoBuild`, `memoComplete`, `memoRelease` | `memoGet` (answers the entry's **promise**), `memoRelease` | `PromiseTable` for `effect` (Sources:55) | `L.t` (E6) |
| `timers` | `TimerStore` = `now`, `wake : WakeList Nat`, `target` | `TestClock.ts:249-381`, live clock `:6052-6066` | none (waiters keyed by fiber + token) | `registerAsync` (`registerSleep`), `sleepCancel`, `clockStep` | `clockNow`, `clockStep` | `unit` by inspection | generated record |
| `nextName` | `Nat` | object identity (`{}`) | mints scope keys, finalizer keys, memo-map ids | `scopeMake`, `scopeFork`, `memoBuild`, the scope links | freshness only | `ScopeKeysFresh` | `int` |
| `externals` | `answers : List Completion`, `allocated`, `rejected` | the host | encounter order | `load` (the answers), admission | the table-aware answer path | refused (DI-57) | generated record |

Three shared pieces sit under the stores:

- **`WakeList π`** (`Machine/Wake.lean:89-122`): waiters `(fiber, token, phase, payload)`, a
  coalescing `batch` and a `phase` counter. It is one protocol for every waiting family.
  Deferred is its first instance (broadcast, inline), the timer its second. Latch, Queue,
  Semaphore, Pool and PubSub are named as future consumers.
- **`Owed κ`** (`:97-101`): a resume the store owes: waiter, token, code, and delivery mode
  (`now`, or `scheduled` on a dispatcher).
- **`Completion`** (`Machine/Completion.lean`): `ofExit exit | ofRefGet cell`. It is the
  alphabet of what can complete a promise and of what the host can answer. `ofRefGet` is
  deliberately data: a ref read performed when the receiver resumes, not when the answer is
  written.

### 2.1 The park handshake (two sides, one token)

A fiber waiting on a promise is recorded twice: in the store, as a waiter `(fiber, token)` on
the cell's `WakeList`; and on the fiber, as `parked = withGuard token` plus a `Pending` entry.
Completion moves every waiter into `due`, and the machine drains `due` into `Cmd.resume fiber
token code`. The resume is **inert unless the fiber is still parked on that token**
(`drive_resume_wrong_token`). This is the generation-index pattern (stale handles cannot
fire) and it is correct. What is not stated anywhere is the relation between the two sides:
every store waiter `(f, t)` either matches `f.parked = withGuard t` or is provably inert. The
typed-state invariant will need it (as `ResumeOk`, `Laws/Program/Typed/State.lean:36`, and the
composed graph's parked-fiber clause; not `PendingOk`, which types a fiber's pending list). I
recommend stating it once,
as its own named invariant, instead of discovering it inside S2.

## 3. The logs

The machine has three logs with three different roles. Two more sit above it, in the API layer,
and the review note found them: the host session's ledger of bound calls, received replies,
consumed call ids and retired calls (`src/Effect4/Api/HostSession.lean:84-93`), and the run's own
journal of played rows with their verdicts (`src/Effect4/Run.lean:57-59`), from which a fresh run
replays. That fifth log qualifies F3 below: at the run layer this tree has already chosen "the
journal is the truth and the state is a fold over it", and the machine's trace is the derived,
diagnostic one. Both are true, at different layers.

### 3.1 Inputs: the decision tape and the host's answers

**The decision tape.** `RunDecision` (`Fibers.lean:436-461`) is every choice rc.112 leaves to
the host:

- `fire owner` and `flush`: the event loop;
- `evaluate`;
- `yieldVerdict`: the `shouldYield` override;
- `answerAsync fiber token completion`: an external answer;
- `interruptFrom`;
- `installMiddleware`;
- `advance millis`: the clock.

The machine is deterministic given the tape. Tape exhaustion and fuel exhaustion are live
frontiers (DB-04). This is the **oracle** in CakeML's sense: all nondeterminism enters here
and nowhere else.

**The host's answers.** `Stores.externals.answers` is a queue of `Completion`s supplied at
load, consumed in encounter order by external rows. It is a second input channel next to the
tape's `answerAsync`. On the reference machine, external rows park forever, and their answers
belong to the table-aware slice (DI-57).

### 3.2 Output: the event log

`RunMachine.trace : List RunEvent` (`Fibers.lean:360-384`) has twenty-one constructors, of
three kinds:

- **host-visible**: `exited`, `callback`, `forked`, `started`;
- **scheduling**: `scheduledTask`, `ranTask`, `yieldInjected`, `parkedOn`, `resumedWith`, the
  interrupt events, `observerFired`, the race events, `scopeLinked`, `scopeClosedOnLink`,
  `finalizerProgram`, `contextSet`;
- **frame-level**: `frame fiber (η)`, which wraps `FrameEvent` (`Frames.lean:334-350`):
  `popped`, `pushed`, `ranContAll`, `ranFinalizer`, `substituted`, `deferred`, `yielded`.

`emit` appends (`m.trace ++ events`, `:614-616`). The reference machine instantiates
`η := Unit`, so frame events are already erased there.

### 3.3 What the theorems compare

`Obs` (`Laws/Machine/Behaviour.lean:29-50`) is every fiber's exit plus the stores, **without
the trace** (`E4-DEN-CE-003`). The trace is ruled not to be semantics:
`BEH-FB-TRACE-ORDER` shows identical traces can accompany different stores. The holder-facing
reading, `Run.Observation` (`Run.lean:220`), carries the protocol state, the outcome, the root
exit, the awaits, pending and retired keys, the applied count, the frontier reasons and the
fiber statuses.

## 4. Findings

**F1. The promise cell holds code where only data is ever stored.** `DeferredCell.completion
: Option Program`. Every writer stores the image of a `Completion`:

- `deferredCompleteWith` stores `completionPrim completion` (`Stores.lean:1946-1948`);
- `deferredInterruptWith` stores `Prim.ofExit (failure (interrupt …))`;
- `memoComplete` stores `Prim.ofExit exit` (`:2015-2022`).

`completionPrim` has two arms: `ofExit` and `ofRefGet ↦ Prim.sync (refGet)` (`:1813-1815`).
To recover the data, the proofs carry `CompletionShaped` / `DeferredOk`
(`Simulation/Hooks.lean:27-45`). The reference machine reads a cell back through
`denoteStored` (`InterpR.lean:133`), a partial decoder whose fall-through is
`pending .unsupported`. It is unreachable only because of the invariant.

In rc.112 a Deferred can hold *any* Effect (`completeWith`), but this machine's alphabet
already restricts completions to `Completion`, so narrowing the type loses nothing. The cost
of not narrowing is real:

- a store invariant with no content except "this is really data";
- a partial function on the reference path;
- a store type that depends on the compiled machine's code type, although the reference
  machine uses the same store;
- a `PromiseTable` column that must type code rather than an exit.

**F2. `MemoEntry.effect` is a copy nothing reads.** It transcribes rc.112's `effect` field
(`Layer.ts:237`), which rc.112's hit path runs (`memoMapReuse`, `:241-250`). This machine's
hit path answers the entry's **promise** instead (`memoGet`, `Stores.lean:1996-2002`), and
`memoizeR` awaits it. Awaiting a completed cell answers the stored exit, and awaiting a
pending one parks. So `effect` (either "await the cell" or "the exit") carries nothing the
cell does not.

In the tree, only `Laws/Machine/Handles.lean:747` (the key set) and the `StoresLaws`
bookkeeping read it, and the typed-state source table gives it a `PromiseTable` row
(`Typed/Sources.lean:55`). It is write-only state that costs proof work.

One caveat the review adds: the two `StoresLaws` theorems that write the field
(`syncOpStep_memoBuild` and `syncOpStep_memoComplete_some`) are the green witnesses of the
census row `layer.memo-build-once`, whose summary ends "and on exit replaces the entry effect
with the exit". Deleting the field makes that row partial unless the clause is restated against
the cell, which is the honest restatement since the cell is what the machine reads.

**F3. The log is read back as if it were state.** The API's fiber statuses
(`Api/Supervision.lean:168-196`) need to tell the run's root from a detached daemon, and the
module says so outright: "The `forked` events of the trace separate them, and only they
can." `RunFiber` has `children` but no `parent` and no daemon flag. So the fork topology lives
only in the log, while `Obs` excludes the log. One consumer's semantics therefore depends on
something the correctness theorems do not cover.

Event-sourced systems pick one source of truth: either the log, with state as a fold over it,
or the state, with the log derived. This machine chose state; the log must then be write-only.

**F4. The lowered representation is chosen by hand, and unproved.** `ocaml/engine/externs.txt`
swaps containers by type-directed rows:

- `RunMachine.fibers` becomes `F.t`, a table that also maintains the completed view;
- `trace` becomes `T.t`;
- `refs` and `DeferredStore.cells` become `M.t`;
- `MemoMap.entries` becomes `L.t`;
- `ScopeEntry` lists become `M.t`;
- `Point.path` and `env` become `P.t` and `E.t`.

About twenty store operations are re-implemented in the hand prelude (`sh_ref_step`,
`sh_deferred_make`, `sh_deferred_set_cell`, `sh_scope_*`, `sh_memo_*`, `sh_machine_*`,
`sh_spawn`, …).

The swaps were forced by measurement (`externs.txt` D7, D8). `Point.path` and `env` were
98.5 % of retained memory and 58 % of time. `completedExits` was 62.7 % of time at fan-out
512. So the need is real. The review note corrects the sharpness of the complaint: the engine is
a functor over seven carrier signatures, a reference instance runs the same generated bodies
over list twins written to reproduce the Lean operations one for one
(`ocaml/engine/api_engine_ref.ml:1-30`), and per-carrier property tests compare each law against
the Lean list operation (`ocaml/engine/test/prop_store.ml:1-9`). What is true is narrower, and
still the problem: those twins and laws are hand-written OCaml, stated nowhere in Lean, and not
generated from LCNF. The list above also omits the dispatcher swap (`externs.txt:10-14`, `:50`)
and the `Capture` rows (`:64-66`).

Lowering Lean `Array` does not rescue this today: the translator maps `Array` to OCaml lists
(`OCaml5/Lcnf/Translate.lean:239-255`).

**F5. Four identity spaces share one type.** Fiber ids, ref keys, deferred keys and memo-map
ids have their own types (`FiberId`, `RefKey`, `DeferredKey`, `MemoMapId`). Scope keys,
finalizer keys, park tokens and race ids are bare `Nat`. One counter, `nextName`, mints scope
keys, finalizer keys and memo-map ids, which is the deliberate ruling (one counter, identity
only). The shared counter is fine; the shared *type* is not. It lets a finalizer key be passed
where a scope key is wanted without a type error. Lean erases a one-field structure to its field (the trivial
structure rule `externs.txt` already relies on for `ScopeStore`), so distinct types cost
nothing at run time.

## 5. What verified compilers and abstract machines do here

- **The CESK machine and defunctionalisation** (Reynolds 1972; Danvy's functional
  correspondence; Van Horn and Might, "Abstracting Abstract Machines", 2010). The C, E, S and
  K registers correspond to `current`, the point's environment and captures, `Stores`, and
  `stack`. The store is a map from allocated addresses to *values*. Continuations are data.
  This machine already has that shape; F1 is the one place a store slot holds code.
- **CompCert** (Leroy). The semantics are labelled transitions whose labels are *observable
  events*. A behaviour is a trace plus how it ends, internal steps are silent, and compiler
  correctness means the target's behaviours refine the source's. Here, `Obs` plays the role
  of the final state, and the trace is not yet split into observable and silent labels (F3).
- **CakeML**. The FFI oracle is an input, the I/O event list is the output, and the
  correctness theorem is stated over both. Here that is the decision tape plus the answers
  (input), and the host-visible events (output).
- **Data refinement** (Hoare 1972; the Isabelle Refinement Framework and Autoref, Lammich;
  seL4's abstract, executable and C specification layers). Write the algorithm over abstract
  containers, prove each concrete operation commutes with an abstraction function once, and
  get the fast implementation without re-proving the algorithm. F4 is exactly the missing
  proof.
- **Lean's own runtime** (Ullrich and de Moura, "Counting Immutable Beans", 2019; Perceus,
  2021). `Array` updates happen in place when the array is unshared. This is a property of
  Lean's native backend only. The OCaml backend has no reference counts, so the OCaml side
  needs a persistent structure or a uniqueness argument.

## 6. The lowered form, as five changes

**R1. Stores hold data, never code.** Change the promise store's types:
`DeferredCell.completion : Option Completion` and `DeferredStore.due : List (Owed Completion)`.
The code is minted at the consumer through the interpreter hook that already exists
(`answerCode`: `completionPrim` for the compiled machine, `denoteCompletion` for the
reference). Then:

- `CompletionShaped` and `DeferredOk`'s first conjunct are deleted;
- `denoteStored` becomes `denoteCompletion`, a total function;
- `Stores` stops depending on the compiled code type, so both machines share it honestly;
- the promise table `Π` types an exit per cell, which is the column the composed graph (§9)
  asked for.

The timer's owed resume can use the same carrier (`ofExit (success unit)`).

**R2. Delete `MemoEntry.effect`.** The memo world keeps `observers`, `layerScope`,
`deferred` and `finalizer`. The rc.112 field is noted in the docstring as "derived from the
cell" rather than stored.

**R3. State is the truth, and the log is write-only.** Add `parent : Option FiberId` and
`daemon : Bool` to `RunFiber` (set at `spawn`), and read supervision from them.
`forkedOf` becomes a test that the log agrees with the state, not a source. Then split the
event alphabet the way CompCert does:

- a small **observable** alphabet: the calls issued to the host, the answers consumed, the
  fiber exits and the callbacks, which theorems and the holder may read;
- a **diagnostic** alphabet (everything else), emitted through a sink parameter.

The reference machine already instantiates the frame part with `Unit`. The lowered engine can
instantiate the whole diagnostic sink with `Unit` and pay nothing. (The append cost is not the
argument: in the OCaml engine the trace is already its own carrier with its own `emit`,
`externs.txt:54`, `:74`.)

**R4. One container interface with laws, proved in Lean and implemented once in OCaml.** The
fiber machine is already parametric in `St` through `RunInterp`. What is missing is a single
container abstraction for the allocation-indexed stores (`refs`, `deferreds.cells`, the fiber
table) and the keyed ones (scopes, memo maps):

- a structure of operations (`alloc`, `get?`, `set`, `find?`, `toList`) with a list model and
  five or six laws;
- the machine written against it;
- the list model as the proof instance.

The OCaml engine then implements *that interface* once (the `M`/`F` tables it already has),
and the twenty hand prelude rows shrink to its few primitives. Those primitives can be
property-tested against the Lean list model law by law, which is far cheaper and sharper than
whole-machine differential runs. `Point.path` and `env` (D7) are the same move for the point.

This is data refinement with a small trusted base, and it is how "OCaml only from LCNF" can
hold for the stores. It is the largest of the five changes; it belongs after the typed-state
milestone, not inside it.

**R5. Give every identity space a type.** `ScopeKey`, `FinKey`, `Token` and `RaceId` as
one-field structures, beside the existing `MemoMapId`. The one counter `nextName` still mints
scope keys, finalizer keys and memo-map ids. There is no run-time cost.

## 7. Order, and what it means for Codex's slice

The ledger Codex is building (3.3 and 3.4) walks the positions in `Typed/Sources.lean` and will
pin a count of open obligations. R1 changes the type at `DeferredCell.completion` and
`Owed.code`, and R2 deletes the `MemoEntry.effect` position. Landing them after the pin moves
the pin and invalidates the frame and obligation rows for those positions.

1. **R1 and R2 first**, before the ledger pins its count. The review note measures the real
   radius at about twenty files, most of it deletion (it also finds two further invariants R1
   deletes, `StoredCodeNoRace` and `DeferredCodes`, and twelve `deferred.*` census witnesses
   that re-spell at `Completion`), so this is not the small slice the list below suggests:
   - `Machine/Stores.lean` (the cell, `due`, three writers, `memoBuild`/`memoComplete`);
   - `InterpR.lean` (`denoteStored`);
   - `Simulation/Hooks.lean` (`DeferredOk`);
   - `Laws/Machine/{StoresLaws,Handles}.lean`;
   - the source table;
   - the generated OCaml, by regeneration.

   The totality gate forces the source-table edit, so nothing can be missed silently. If the
   ledger lands first, re-pin once, deliberately, in the R1 commit.
2. **The park-handshake invariant (§2.1)**, stated as its own definition before S2 needs it.
3. **R3 and R5**, alongside or after S2: small, independent, and they make the observable
   alphabet explicit before any cross-backend statement is written.
4. **R4** after the milestone. It is the lowered form's real foundation and should not
   compete with S1–S3 for attention.

## 8. Is this enough for the clock, and for everything else?

The owner asked whether this infrastructure is enough to store the clocks and everything else.
The answer is yes for the clock, and not yet for the rest of rc.112's stateful surface.
Nothing listed below needs a new machine architecture, except STM.

**The clock is covered.** `TimerStore` (`now`, the pending sleeps on a `WakeList` ordered by
deadline then registration, an advance in progress) plus the tape's `advance millis` is
rc.112's `TestClock` shape. Time moves only by a tape decision, so the tape is the complete
record of time and replay is exact. What is not a row yet is still derivable with no new
state:

- **`currentTimeNanos` and `monotonicTimeNanos`**: `TestClock` keeps them as separate state
  because `setTime` can move the wall clock backwards (`testing/TestClock.ts:258-259`).
  This machine refuses `setTime` (`TIMER-FB-SET-TIME`) and advances in whole milliseconds,
  so both are `now × 1_000_000`. That is two sync rows.
- **`timeout`**: rc.112 defines it as `raceFirst(self, flatMap(sleep(d), orElse))`
  (`internal/effect.ts:3677-3704`), a program over a race and a sleep. The alphabet has
  `raceAll` (first *success*), not `raceFirst` (first *exit*). `raceFirst` either becomes a
  row or is spelled as `raceAll` over exit-wrapped entrants; checking that against rc.112
  comes before either.
- **`Schedule`** (retry and repeat): programs over `sleep`, `clockNow` and `iterate`.

**What has no home yet:**

1. **The clock as a service.** rc.112 reads the clock per fiber from the context
   (`ClockRef`, a `Context.Reference`, `internal/effect.ts:6033`), so a program can provide
   its own `Clock`. Here there is one global logical clock and no refusal row names the
   difference. Register the refusal now, and revisit with the service carriers (L7).
2. **Things that expire.** `Cache`, `ScopedCache`, `RcMap` and `Pool` all read the clock for
   their time-to-live. This first said each needs its own keyed store; the review shows
   otherwise. rc.112 keeps those entries in ordinary maps inside library objects and expires
   them lazily on read, or through a `sleep` loop on a forked fiber. They need map-valued refs
   and a way to hold a behaviour, not stores.
3. **Randomness.** The machine does have context references (`Machine/ContextMap.lean:264-276`,
   with the two budget references among the reserved keys); what it has is no *Random*
   reference. For replay the values must come from somewhere deterministic: a seeded generator
   in the stores (as rc.112's test random does), or a tape decision. A seed is the
   recommendation, since randomness is not a host scheduling choice.
4. **The other waiting primitives.** Semaphore, Queue, PubSub and Latch are not in the
   alphabet. This first said each is a new store; that contradicts a ruling. DI-11
   (`docs/DESIGN-ISSUES.md`, ruled 2026-09-10) says queues, mailboxes and publish-subscribe are
   composite programs over `Ref`, `Deferred` and the wake protocol, "never new machine stores",
   and rc.112 itself composes publish-subscribe that way. The review's finding is that only the
   *schedule* is lost by composing, and that one store family, a latch, restores it for four of
   the five affected modules. Note that `docs/core/language-cut.md:75` states the opposite of
   DI-11: one of those has to move.
5. **STM** looked like the exception when this was written, on the assumption that it needs a
   per-transaction journal with version checks. The STM scout
   (`docs/research/2026-09-19-stm-scout.md`) shows otherwise: rc.112's journal and versions
   exist only because its run loop can let another fiber commit inside a transaction body, and
   this machine can close that window with the `PreventSchedulerYield` it already models plus a
   fold admitting only bodies that cannot park, fork or resume another fiber. What STM then
   needs is a store family on the wake protocol (a value and a waiter list per cell) and one
   short-lived record for the open transaction, which is what Queue or Semaphore needs. What is
   new about STM is control, not state: a body whose writes are thrown away and run again.
6. **Tracing spans and metric timestamps** read the clock too, but they are observations,
   not state. They belong to the diagnostic sink of R3.

Rulings this asks of the owner:
- R1 and R2 before the ledger's pin (recommended);
- whether the observable event alphabet of R3 is the four kinds listed there, or also
  includes the scheduling events a holder may want (recommended: the four, with scheduling
  kept diagnostic);
- where randomness comes from when it is added: a seeded generator in the stores, or a tape
  decision (recommended: the seed, §8);
- a refusal row now for the provided-`Clock` difference, revisited with L7 (recommended).
