# The machine's state, its logs, and the route to the rest of Effect

The authority for what state the reified machine holds, what its logs are for, how transactions
would work, and how the surveyed Effect stateful modules can land. Written 2026-09-19 at `23e668b0`
as the language's last major design push; reviewed against the completed scouts at `5d6c70da`.
The approved typed-world model is recorded in decisions rows 44–45. The new representation,
observation and control choices remain proposals in rows 78–83; §6 points to that one register.

The implementation sequence and proof contracts are in
`docs/research/2026-09-19-state-refinement-plan.md`. That plan includes a finite rc.112 control
showing that changing wake timing can change a returned value. It does not establish general
agreement for a composed API or a lowered backend.

The evidence is three notes, each cited by section below:

- `docs/research/2026-09-19-stores-and-event-log-map.md` — the full map, field by field.
- `docs/research/2026-09-19-stm-scout.md` — rc.112's transactions as rules, and the smaller design.
- `docs/research/2026-09-19-stateful-api-catalogue.md` — the surveyed API families, and a review of the map.

## 1. What the machine holds

One record, `RunMachine` (`src/Effect4/Machine/Fibers.lean:415-433`), parametric in the code
type, the saved-fiber type, the frame-event type and the store type. It holds every fiber, the
races in flight, three fresh-name counters, the armed host callbacks, the service state, the
event log and a stuck marker. Four instances run it: the compiled machine, the reference machine
(which erases frame events), the stores module's own interpreter, and the generated OCaml engine.

A fiber (`:229-247`) is fifteen fields transcribing the modelled part of rc.112's fiber object:
its saved execution state (the current code, the continuation stack, the interrupt flags), its
parking state and outstanding parks, its exit, the yield budget, its observers and children, its
dispatcher and its context. The compiled runtime uses first-order code and continuation names.
The reference proof instance instead has function-valued RProgram/ScopeFrame continuations;
they are semantic carriers, not stored program syntax or serializable runtime snapshots.

The service state, `Stores` (`src/Effect4/Machine/Stores.lean:1719-1733`), holds seven things:
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

## 4. Representation changes under review

| area | current cost or gap | proposed change and condition |
| --- | --- | --- |
| promise cells | code-shaped storage requires a shape invariant and partial decoder | use admitted Completion data and interpret it at the consumer; retain deferred Ref reads and do not claim arbitrary Deferred.completeWith support |
| memo entries | the duplicated effect is not read by machine execution, but census witnesses inspect it | delete it only with cell-based replacement witnesses and the representation connector |
| supervision and events | the holder's supervision depends on a trace excluded by Obs | define semantic, holder/replay and diagnostic observations; make needed topology available without relying on erased diagnostics; a parent/daemon field is one candidate |
| optimized containers | OCaml already has interfaces, list twins and property tests, but no Lean refinement certificate for the swaps | use separate lawful interfaces for dense arenas, keyed tables, ordered work, append sequences and persistent paths; prove a relation to the reference |
| identities | scope/finalizer/token/race spaces share Nat | distinguish their types while retaining the shared allocation policy; target overflow/freshness obligations remain |

The completion and memo changes affect positions walked by the typed-state ledger. The proposed
order is to settle their contract, migrate with a connector, then pin the semantic obligation
count. Their actual radius is about twenty files, including simulation/census witnesses. They
are not a six-file mechanical edit. The fast-container implementation can follow the milestone;
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

`docs/research/2026-09-19-state-refinement-plan.md` owns the staged work and acceptance:
contracts and observations, completion/memo migration, generic-cell/world tooling and the
concrete ledger, typed-state proofs, one storage refinement, then the additional primitive
families and target profiles. Runtime implementation stays paused for this design review.
