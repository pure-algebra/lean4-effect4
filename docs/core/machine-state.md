# The machine's state, its logs, and the route to the rest of Effect

The authority for what state the reified machine holds, what its logs are for, how transactions
would work, and how the surveyed Effect stateful modules can land. Written 2026-09-19 at `23e668b0`
as the language's last major design push; reviewed against the completed scouts at `5d6c70da`.
The approved typed-world model is recorded in decisions rows 44–45. The new representation,
observation and control choices remain proposals in rows 78–83; §6 points to that one register.

The current proposed sequence and whole-core semantic workstreams are in
`docs/research/history/post-phase-c-synthesis.md`; the earlier contracts are retained in
`docs/research/2026-09-19-state-refinement-plan.md`. That earlier plan includes a finite rc.112 control
showing that changing wake timing can change a returned value. It does not establish general
agreement for a composed API or a lowered backend.

The evidence is three notes, each cited by section below:

- `docs/research/2026-09-19-stores-and-event-log-map.md` — the full map, field by field.
- `docs/research/2026-09-19-stm-scout.md` — rc.112's transactions as rules, and the smaller design.
- `docs/research/2026-09-19-stateful-api-catalogue.md` — the surveyed API families, and a review of the map.

## 1. What the machine holds

One record, `RunMachine` (`src/Effect4/Machine/Fibers.lean`), parametric in the code
type, the saved-fiber type, the frame-event type and the store type. It holds every fiber, the
races in flight, three fresh-name counters, the armed host callbacks, the service state, the
event log and a stuck marker. Four instances run it: the compiled machine, the reference machine
(which erases frame events), the stores module's own interpreter, and the generated OCaml engine.

A fiber has sixteen fields transcribing the modelled part of rc.112's fiber object and
its source provenance:
its saved execution state (the current code, the continuation stack, the interrupt flags), its
parking state and outstanding parks, its exit, the yield budget, its observers and children, its
dispatcher, its context, and its origin. Origin is either the root or a fork's parent, daemon
flag and source path; supervision reads this state even when diagnostic events are erased.
The current tracking parent remains a separate relation. The compiled runtime uses first-order code and continuation names.
The reference proof instance instead has function-valued RProgram/ScopeFrame continuations;
they are semantic carriers, not stored program syntax or serializable runtime snapshots.

The service state, `Stores` (`src/Effect4/Machine/Stores.lean`), holds seven things:
the ref heap, the promise store, the scopes, the layer memo world, the timer, one fresh-name
counter and the host's answers. Each transcribes a named part of rc.112, and the map note's §2
gives the origin, the writers, the readers, the typing source and the OCaml representation of
every one.

State the map does not cover, listed in the catalogue's §1.3, belongs here too: the fiber's
context and the services in it, captured releases, race entrants, the code inside dispatcher
tasks, and the completed-exit view carried inside code.

## 2. The promise store

It transcribes rc.112's `Deferred`: a cell is an optional stored completion and a waiter list.
It has two populations — user promises, and memoised layer builds, which allocate cells from the
same store. A fiber waiting on a cell is recorded twice, as a waiter in the store and as a guard
token on the fiber, and a resume for a fiber no longer parked on that token is inert. That
handshake is the machine's protection against stale wakeups and should be stated as its own
invariant before the typed-state proofs need it.

The runtime payload is `Completion`; consumers interpret it when it is delivered. The store
and cell accept a defaulted payload parameter so the Laws graph can relate this representation
to the former program payload without copying the store's operations. The runtime no longer
needs a stored-program shape check or partial decoder.

The logical timer uses exact nonnegative `ClockMillis` values for its current time, advances
and deadlines. Its generated OCaml carrier uses arbitrary precision arithmetic; decimal text
transports large advances. The public `clockNow` result remains a number, and the target
refuses observations outside its exact number range. The stock rc.112 clock adapter also
refuses an overflowing advance or deadline before changing its numeric timer state. DB-14
owns this target-profile decision.

## 3. The logs, and what they are for

Three logs in the machine, two above it:

1. **The decision tape** (`Fibers.lean:436-461`): the modeled scheduler and host choices.
   Together with admitted host answers, these are explicit external inputs to replay.
2. **The host's answers**: a queue of completions consumed in encounter order.
3. **The event trace**: twenty-one kinds, from host-visible exits down to frame pushes and pops.
4. **The host session's ledger** (`src/Effect4/Api/HostSession.lean:84-93`).
5. **The run's journal of played rows** (`src/Effect4/Run.lean:57-59`), from which a fresh run
   replays.

What the correctness theorems compare is every fiber's exit plus the stores
(`src/Effect4/Laws/Machine/Behaviour.lean:29-50`), deliberately without the trace. At the run
layer, though, the journal is the truth and the state is a fold over it. Both are consistent as
long as each layer says which it is: in the machine, state is the truth and the trace is
derived.

## 4. Representation changes and migration conditions

| area | current cost or gap | proposed change and condition |
| --- | --- | --- |
| promise cells | storage now holds Completion data; the shape invariant and partial decoder are removed | retain deferred Ref reads and do not claim arbitrary Deferred.completeWith support; the mapping/representation connector landed through Phase C |
| memo entries | the unused effect field is removed and census witnesses inspect the cell | cell-based witnesses and the connector landed through Phase C; identity-write deletion remains conditional on unique map IDs below the allocation supply and its reachable-state connector |
| supervision and events | the holder now reads the fiber's origin instead of the event trace | retain separate semantic, holder/replay and diagnostic observations; prove the source-path and observation statements in the Laws graph |
| optimized containers | OCaml already has interfaces, list twins and property tests, but no Lean refinement certificate for the swaps | use separate lawful interfaces for dense arenas, keyed tables, ordered work, append sequences and persistent paths; prove a relation to the reference |
| identities | scope/finalizer/token/race spaces share Nat | distinguish their types while retaining the shared allocation policy; target overflow/freshness obligations remain |

The completion and memo changes affect positions walked by the typed-state ledger. The proposed
order is to settle their contract, migrate with a connector, then pin the semantic obligation
count. Their landed radius includes runtime, simulation and census witnesses; measure the remaining
cleanup against the current tree rather than reusing the early six- or twenty-file estimates. The fast-container implementation can follow the milestone;
its interface and observation contract should be fixed now.

Current Obs contains the full concrete Stores value. Book/BMeans relates machines with the same
store type and equal stores. Neither currently licenses sorted/deduplicated maps, hidden private
cells, or a new transaction buffer. Keep those statements intact and add a named projection or
representation relation, then a connector for the new observation. Helper fibers and handles
introduced by a composed program also need an explicit visibility and identity relation.

## 5. Primitive basis and proof boundaries

**Transactions.** The STM scout proposes an admitted atomic profile on the existing evaluator.
It remains conditional: disabling automatic yields alone does not stop inline completion,
observer delivery, protected-context changes or a later stored-program call from executing
another fiber. A compositional admission judgment and single-owner invariant must exclude
those routes, including across fuel frontiers, before versions can be erased.

Specify ordered dynamic accesses, own-write reads, flat nesting, selective rollback, retry
registration/cancellation and cleanup-before-resume first. rc.112 schedules wakes for every
accessed cell, including unchanged cells; that is not a coalesced Latch batch. Allocation and
any admitted ordinary Ref writes are not automatically rolled back. The observation and
execution assumptions determine where an active transaction record belongs. A future concurrent
backend may require locking or validation even if the cooperative implementation does not.

Fuel ownership needs a continuation contract. driveState returns unfinished Cmd data, but the
public decision/session boundary does not retain the complete command and outer-driver remainder.
A fresh command with more fuel is not resumption of that remainder. Choose either replay from
the original state with more fuel, or a retained driver suspension, before relying on ownership
across budgets. The checked witness and proposed control law are in
`docs/research/2026-09-19-critique-response.md` §5; no STM implementation exists yet.

**Composed APIs.** The catalogue has 20 API-family rows, not an exhaustive export census.
DI-11 already chooses composite programs for Queue, Mailbox and PubSub. The proposed basis
adds generic Ref/Deferred operations, binder-term atomic updates, map/list atoms with a named key
policy, nested-handle typing, and typed first-order references to stored behaviors. Such
references must resolve into the existing Eff owner; promoting the whole Capture record would
accidentally freeze execution details into the value language.

Code resolution must establish the entry signature and capture layout; a digest alone does not.
Invocation context is selected by the module contract: existing registered finalizers restore
captured services. First-order capability handles can be captured with type/lifetime conditions;
reusable behavior content and a paused invocation's control state remain different sorts.

A Latch is a candidate scheduled-wake primitive. It does not by itself prove Semaphore, Pool,
Queue or transaction agreement: they differ in selection timing, wake count, live traversal,
coalescing, cancellation and dispatcher ownership. The retained rc.112 probe demonstrates that
scheduled and inline wakes can return different values. Each composed module therefore needs
its own behavior law on a named profile, as DI-89 requires; typing is not enough. Printing an
expansion exercises that expansion, not the native rc.112 module API.

**Deferred modules.** Reserve a public signature and contract for known future needs; derived
modules are Eff programs using the shared primitives. Prove reusable consequences over explicit
implementation and law parameters, then instantiate them when the implementation arrives.
Existing wanted declarations record missing definitions or proofs without supplying them.
They are planning dependencies, never executable defaults or extra Eff constructors. Stream
and Channel can follow this pattern; logging remains optional until an application needs it.
The priority is composing existing representations and laws, with tooling serving those
interfaces rather than introducing a new framework or gate for each module.

Container laws fix their hidden parameters once: code root/resolver for cached paths, projection
for cached views, equality/order/duplicate policy for maps, and immutable payloads or explicit
heap ownership for retained snapshots. Scalar relations cover intermediate arithmetic and fresh
allocation; saturation does not implement mathematical Nat or preserve fresh identities.

**Lowering.** Keep four obligations distinct: program meaning to machine behavior; concrete
storage to logical storage; LCNF/IR to target syntax; target compiler/runtime/host execution.
The existing OCaml interfaces and tests are useful inputs to the second. Structural rule
summaries and layout checks are not lowering proofs. Native C, direct LLVM, OCaml and Wasm
have separate scalar, memory, runtime and ABI contracts; the presence of an emitter does not
establish a verified backend. The plan's first refinement consumer is the dense Ref arena,
not a rewrite of every store.

## 6. Decisions and sequence

`docs/core/decisions.md` owns the decisions: rows 44–45 are the approved typed world;
78–83 hold completion/memo ordering, observations/agreement profiles, transaction control,
scheduled waking, stored behaviors, and Clock/Random profiles. DI-11 remains the existing
composition ruling; correcting a contradictory summary does not require ruling it again.

**Ruled 2026-10-05 (rows 219 to 234).** The owner ruled the first profiles of this section:

- the Queue's contract (rows 219 to 222): strict order, consumption at the taker's step, a posted
  signal, and a cancellation that withdraws only when it wins before consumption;
- the shared waiting wrapper, with a checked body profile (row 221);
- the atomic body and its alternatives (rows 223 and 224), and its work limits (row 226);
- posted work as an `Eff` body with task metadata (row 225);
- the mask that restores (row 227);
- the public behaviour that a module's profile defines (row 230);
- the clock's unit (row 231), the release audit (row 232) and the reserved contract of a
  retained behaviour (row 234).

Row 233 orders the slices. §5's conditions on a transaction still hold. Rows 223 and 226 select
how the first profile meets them, and the relation to the source's behaviour stays open (row 80).

`docs/research/history/post-phase-c-synthesis.md` now owns the proposed staged sequence and acceptance;
`docs/research/2026-09-19-state-refinement-plan.md` is its historical contract basis:
contracts and observations, completion/memo migration, generic-cell/world tooling and the
concrete ledger, typed-state proofs, one storage refinement, then the additional primitive
families and target profiles. The data and placement slices of the owner's skeleton-first redirect are landed. Next are
the checked statement amendments, relational predicate shape, protocol/validity contracts and
their proof graph. The broader families use those same foundations; no new gate framework is
a prerequisite for designing or proving the next real semantic slice.

## 7. Storage interfaces, creation ledgers, derived declarations (2026-09-30)

From the external runtime contract's §7
(`docs/research/2026-09-30-external-runtime-contract.md`), row 101. Six operational interfaces,
each with a small lawful model before a real consumer moves onto it. None is a universal container
that hides order or allocation policy.

| Interface | Laws each backing implementation owes |
| --- | --- |
| Dense arena | empty, extent, lookup, replace, allocate; a fresh key is the old extent; old keys stay stable; a stated policy for updating an absent key; earlier snapshots persist |
| Keyed table | equality and hash agree; stated duplicate and missing policies; stated iteration order; sparse ids distinct from the count and the allocation supply |
| Ordered work | selection; priority or FIFO where specified; cancellation; snapshot versus live drain; reentrancy; no loss and no duplication |
| Append sequence | ordered append, index and projection; prefixes retained; an authoritative journal never becomes a lossy ring |
| Persistent path and environment | resolution against the owning program; captures and layout agree; scope and lifetime; aliases kept |
| Derived view | the cache equals one fixed projection of the owner's state after every operation |

**The families and their owners.**

| Family | Source | Interface | Invariants kept |
| --- | --- | --- | --- |
| Fibers | `Machine/Fibers.lean` | keyed table | unique ids below the supply, children, ordered observers, exited fibers retained |
| Fork records | row 91 | append sequence | written only by `spawn`; one record per forked fiber |
| Saved frames | `Machine/Frames.lean` | persistent path | typed intermediate continuation, masking, catches, finalizers, loops, context, interruption |
| Race, iterator and driver work | `Machine/Fibers.lean` | ordered work | entrants, results, sites and tokens correlate; launch and cancel order |
| Dispatchers and armed callbacks | `Machine/Fibers.lean` | ordered work | snapshot drain, reentrant enqueue, arming order |
| Ref heap | `Machine/Stores.lean` | dense arena (`Laws/Machine/Arena.lean`, `RefKernel.lean`) | atomic answer and state, aliases, absent-update policy |
| Deferreds, due work, wakes | `Machine/Stores.lean`, `Machine/Wake.lean` | ordered work over a keyed table | first completion wins, stored `Completion`, registration-order broadcast, delayed reads, active-token receiver typing, stale-token inertness |
| Scopes and releases | `Machine/Scope.lean` | keyed table | sparse ids, closing marked before cleanup, sequential or parallel strategy, failure accumulation |
| Layer memo world | `Machine/Stores.lean` | keyed table | unique map ids below the shared supply (`Stores.MemoIdsOk`), parent lookup, correspondences, sharing and release |
| Clock and timers | `Machine/Timer.lean` | ordered work | exact clock, monotone, deadline and tie order, staged advance |
| Context and captures | `Machine/Stores.lean`, `Program/Compile.lean` | persistent path | service identity, override, inheritance, static types, capture lifetime |
| External allocations and replies | `Machine/Stores.lean`, `Program/Admit.lean` | dense arena plus a keyed host table | prepared-value relation, target extension, no allocation on a refused reply |
| Session and capability ledgers | `Api/HostSession.lean` | append sequence and keyed table | call ids distinct from tokens, exact active, pending, consumed and retired sets |
| Journal and diagnostics | `Run.lean`, `Api/Runner.lean`, the trace | append sequence | authoritative command replay; semantic, holder and diagnostic projections kept apart |

**Two patterns.**

- **Creation facts live in append-only records.** A fact fixed when something is created, and
  needed later, is kept where ordinary updates of the working record cannot reach it. The fork
  record of row 91 is the first case.
- **Declarations are derived views.** A handle's declared type is computed from its creation
  record and the checker (`host-boundary.md` §4.3), never stored in a value.

**What is proved today.**
- The arena and list laws, and the `refStepOfA` connection.
- `Projects` composition, and `Refines` induced by a projection, for the same operation and
  answer carriers with exactly corresponding steps.

Initialization, whole-machine store replacement, id renaming, different event encodings and
stuttering simulation are not provided automatically. The behavior observation includes the whole
concrete `Stores`, so a named logical projection and its connector come before any layout is
replaced or private state is hidden.
