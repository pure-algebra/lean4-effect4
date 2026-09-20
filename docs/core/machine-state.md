# The machine's state, its logs, and the route to the rest of Effect

The authority for what state the reified machine holds, what its logs are for, how transactions
would work, and how the rest of Effect's stateful modules land. Written 2026-09-19 at `23e668b0`
as the language's last major design push. Nothing here is ruled yet: §6 is the list of decisions
this document asks the owner for, and a ruling counts only once it is written into
`docs/core/decisions.md`.

The evidence is three notes, each cited by section below:

- `docs/research/2026-09-19-stores-and-event-log-map.md` — the full map, field by field.
- `docs/research/2026-09-19-stm-scout.md` — rc.112's transactions as rules, and the smaller design.
- `docs/research/2026-09-19-stateful-api-catalogue.md` — the nineteen modules, and a review of the map.

## 1. What the machine holds

One record, `RunMachine` (`src/Effect4/Machine/Fibers.lean:415-433`), parametric in the code
type, the saved-fiber type, the frame-event type and the store type. It holds every fiber, the
races in flight, three fresh-name counters, the armed host callbacks, the service state, the
event log and a stuck marker. Four instances run it: the compiled machine, the reference machine
(which erases frame events), the stores module's own interpreter, and the generated OCaml engine.

A fiber (`:229-247`) is fifteen fields transcribing the modelled part of rc.112's fiber object:
its saved execution state (the current code, the continuation stack, the interrupt flags), its
parking state and outstanding parks, its exit, the yield budget, its observers and children, its
dispatcher and its context. Continuations are names with a total interpretation, never closures,
which is what makes every piece of this state first-order data.

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

1. **The decision tape** (`Fibers.lean:436-461`): every choice rc.112 leaves to the host. All
   nondeterminism enters here, which is what makes replay exact.
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

## 4. The five defects, and the five changes

From the map note's §4 and §6, as corrected by the catalogue's §1:

| # | defect | change |
| --- | --- | --- |
| 1 | a promise cell is typed as code, though only three data shapes are ever stored; an invariant and a partial decoder make up the difference | stores hold data, never code: the cell and the owed resume carry a completion, and each machine mints its own code when it reads one |
| 2 | a memo entry keeps a copy of its result that no machine step reads | delete it, and restate the one census clause that reads it against the cell |
| 3 | fork parentage lives only in the event log, while the theorems exclude the log | put the parent and the daemon flag on the fiber; split the events into a small observable alphabet and a diagnostic sink |
| 4 | the OCaml engine's container swaps are hand-written and stated nowhere in Lean | one container interface with laws, proved in Lean against the list model and implemented once in OCaml |
| 5 | scope keys, finalizer keys, park tokens and race ids are all bare numbers | give each its own type; Lean erases a one-field structure, so it is free |

Changes 1 and 2 touch positions that the typed-state obligation ledger walks and pins, so they
come before that pin, or the pin is taken again deliberately in the same commit. The catalogue
measures their real radius at about twenty files, most of it deletion. Change 4 comes after the
typed-state milestone.

## 5. Transactions, and the rest of Effect

**Transactions.** rc.112's STM is one section of `Effect.ts` plus the `TxRef` cell; its other ten
transactional modules are library code over that cell. Its journal and per-cell versions exist
only because its run loop can let another fiber commit inside a transaction body. This machine
can close that window with the prevent-yield reference it already models and a fold admitting
only bodies that cannot park, fork or resume another fiber. Then versions carry no information,
and what is left is one store family (a value and a waiter list per cell), one short-lived record
for the open transaction, a handful of rows and a scoped `tx` constructor. So STM is not a new
kind of machine state; what is new about it is control — a body whose writes are discarded and
run again.

**The rest.** All nineteen of rc.112's remaining stateful modules are library code over ref,
promise, scope, fork, race, sleep and the loop, with no new machine store. That is what DI-11
already ruled. What composition loses is the schedule: for the five things rc.112 builds on raw
task scheduling (latch, semaphore, queue, the pool's wake, the transaction commit wake), waiters
would wake inline rather than on a dispatcher. One store family, a latch, placed on the machine's
existing but currently unused scheduled-wake machinery, restores four of the five.

What that route needs first is language, not machine: polymorphic ref and promise rows,
read-modify-write rows that take a binder term, atoms for association maps, typing for handles
inside values, and a program value for the six modules that store a behaviour and run it later.
The catalogue's §4 sequences it as seven slices, none of which starts before the typed-state
milestone is done.

## 6. What the owner has to decide

1. Whether changes 1 and 2 of §4 land before the obligation ledger pins its count (recommended).
2. Whether the observable event alphabet is the four host-visible kinds, with scheduling events
   kept diagnostic (recommended).
3. Whether transactions are atomic, with the deviation from rc.112 registered, rather than
   preemptible (recommended). The STM note's §5 has eight further transaction questions, each
   with a recommendation.
4. Whether the waiting primitives compose, with one latch store, rather than each getting a store
   (recommended, and it is what DI-11 ruled).
5. Whether randomness, when it arrives, comes from a seed in the stores rather than the tape
   (recommended).
6. Two conflicts to settle either way: `docs/core/language-cut.md` states the opposite of DI-11
   about queues and publish-subscribe, and the timer's docstrings say rc.112 posts a sleeper's
   resume on a dispatcher where in fact it opens a latch inline
   (`src/Effect4/Machine/Timer.lean`).
7. Whether the scheduled-wake machinery gets its first producer (the latch) or is deleted: today
   nothing in the tree produces a scheduled wake.
