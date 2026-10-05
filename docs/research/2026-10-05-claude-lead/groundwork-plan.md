# 2026-10-05 groundwork for the composed modules: the base abstractions first

Status: research note (history, not authority). Base: `50700443` (`refactor/phase1-phase3`).

**Ruled 2026-10-05.** The owner ruled on these proposals: decisions rows 221 and 225 to 234 are
the authority, and `docs/research/2026-10-05-claude-lead/foundation-contracts.md` holds the
obligations and the order. Item 7's "any body" is withdrawn: row 221 asks for a checked body
profile.

**The one thing to know first.** The owner's direction of 2026-10-05 is to lay the groundwork
before any module. No module should send the work back for an atom, a table or a language
feature. This note lists every base abstraction that Effect's stateful modules need from this
tree. It says where each stands, and which questions to resolve before development starts. Nine
are missing. The three largest are a list fold in terms, a mask that restores the caller's
interruptibility, and the kit for a module's law. Nothing here is a ruling: Codex reviews it,
and the owner rules.

The note was amended on 2026-10-05 after Codex's review of the queues review. Proposal 1 no
longer signs one schedule difference for every module, and F4 carries Codex's list for the fold.

It was amended again the same day, after Codex's third review and the transactions note
(`docs/research/2026-10-05-claude-lead/transactions-and-clock.md`). Item 7 now serves any body,
item 10 is open again, and items 17 and 18 are new. F5 gives the reasons.

## Question

Which base abstractions do the stateful modules need, and which exist? In which order do the
missing ones land, so that no module adds a language feature later?

## What was read or run

| Item | How |
| --- | --- |
| The stateful-API catalogue, §2 and §3 (`docs/research/2026-09-19-stateful-api-catalogue.md`): 20 module families and a basis of six items | read; its rc.112 line citations were not checked again |
| The queues review of today (`docs/research/2026-10-05-claude-lead/queues-review.md`) and its probes | read; tested |
| The term language and its atoms (`src/Effect4/Machine/Term.lean`); the program syntax (`src/Effect4/Program/Eff.lean`) | read |
| `uninterruptibleMask` in `vendor/effect-4.0.0-rc.112/src/`, by file | tested (a search) |
| A cell that holds a list of handles, searched in `Test/` and `src/Effect4/Laws/` | tested (a search): none found |
| Decisions rows 43, 79, 81, 82 and 109; DI-11; the state plan (`docs/research/2026-10-04-claude-lead/state-any-type-plan.md`) | read |
| The transactions note of today and its probes (`docs/research/2026-10-05-claude-lead/tx-probes/`) | read; tested |
| Any design of an item below | not written |

## Findings

### F1. The base abstractions and where each stands

| # | Abstraction | State today | Recommended form | Question to resolve |
| --- | --- | --- | --- | --- |
| 1 | A cell and a deferred at any type | Landed (seat T3a) | — | — |
| 2 | An atomic update that takes a binder term | In flight: seat T3b has four of six slices on its branch | As seat T3b's approved design | Resume now, or after the questions below |
| 3 | A list fold in terms | Missing. A term has no loop and no binder | One term constructor: a list, a start value, and a body that binds the accumulator and the element. Total. Prints as `reduce` | The binder convention; whether a counted loop is also needed |
| 4 | Bulk list atoms | Missing. The list atoms are `listNil`, `listCons`, `listGet`, `listLength`, `listAppend` | `listTake` and `listDrop`, each total. Every other list function is a builder over the fold | Which builders ship with the fold |
| 5 | The identity of a handle inside a term | Missing. `eq` compares numbers and strings only | Equality of two handles of one kind. Never deep equality of messages | Extend `eq`, or give each registration a number |
| 6 | Handles inside a cell's value, typed | Believed landed with T3a. No test holds a list of handles in a cell | A finite probe: a cell with a list of `Deferred`s builds, types and runs | — |
| 7 | The wrapper for an operation that waits | Missing | One derived form over `Deferred`, `onExit` and `uninterruptible`: install the cleanup, run the body, resolve its signals, await, run the body again (the queues review, F6). The body is any body that answers a value, a wait or a failure; the queue's step is one instance (F5) | Who owns the signals that a body answers (the queues review, F10); the delivery of a signal (item 10) |
| 8 | A mask that restores the caller's interruptibility | Missing. The owner's ruling of 2026-10-05 on question 5 of the derived forms plan defers it; the register does not hold that ruling yet | A mask construct and a `restore` construct that names its mask | The first-order form of `restore`; whether that ruling's timing changes |
| 9 | The kit for a module's law | Missing. `Profile` and `Agrees` are text only (row 79, R79.5) | Abstract operations for the client, their expansion, the profile as data, the simulation with stutter steps, the quiet-state lemma | The client's alphabet: an operation type beside the native one, or rows of an application signature |
| 10 | A posted wake for programs | In the machine (`WakeMode.scheduled`, `src/Effect4/Machine/Wake.lean`); no program-visible row | Open again (F5). One design under row 81 for every site that posts; each module names its delivery in its profile (row 79) | Its form: a posted resolution of a `Deferred`, a forked helper, or the machine's batch wake |
| 11 | Retained behaviour: a program kept in a value and run later | Missing. R7 and row 82 are open | A separate design | Design it now, or after the first modules |
| 12 | A watcher fiber for another fiber's exit | Composed from fork and await | A detached fork pinned to the structure's scope | A finite probe that it lands where rc.112's observer lands |
| 13 | The race that takes the first exit | Missing | A derived form over `raceAll` | Check it against the truth harness first |
| 14 | Numbers | Open (row 109) | As row 109 rules | — |
| 15 | The faces of terms: binder terms, the fold, type arguments | Slice T5 of the state plan | Extend T5 to the fold | — |
| 16 | The pin | rc.112; npm's latest is 4.0.1 | An audit of what changed in the proved runtime, then a decision | Audit now or later |
| 17 | A region in which no other fiber runs | The machine honours `PreventSchedulerYield`; no rule admits a body, and four more routes let another fiber run (`docs/core/machine-state.md` §5) | One admission rule over a body, with its single-owner invariant (row 80) | Which bodies it admits; whether a signal inside it may wake its waiter |
| 18 | The clock's unit | Milliseconds (`ClockMillis`, `src/Effect4/Data/ClockMillis.lean`); the type is exact and has no bound | Nanoseconds, Effect's finest unit (the transactions note, F7) | The two nanosecond readings need a `bigint` type (rows 109 and 121) |

### F2. Which module needs which abstraction

The table reads the catalogue's §2. A dot means the module needs the item.

| Module | 2 term update | 3 fold | 5 identity | 7 wrapper | 8 mask | 11 retained behaviour | Other |
| --- | --- | --- | --- | --- | --- | --- | --- |
| `Queue` | • | • | • | • | `into` only | | |
| `Latch` | • | | • | • | | | Posts its wake in rc.112 |
| `Semaphore` | • | • | • | • | • | | Posts its sweep in rc.112 |
| `PartitionedSemaphore` | • | • | • | • | • | | Map atoms |
| `PubSub` | • | • | • | • | | | Map atoms; a scope per subscription; a Latch |
| `SynchronizedRef` | • | | | | • | | `Semaphore` |
| `SubscriptionRef` | • | | | | • | | `Semaphore`, `PubSub` |
| `FiberHandle`, `FiberSet`, `FiberMap` | • | • | • | | • | | Item 12; map atoms |
| `Pool` | • | • | • | • | • | • | Scopes, `Semaphore`, sleep |
| `Cache`, `ScopedCache` | • | • | | | • | • | Map atoms; the clock; item 12 |
| `RcMap`, `RcRef` | • | | | | • | • | Scopes; sleep; a fork with a context |
| `Request`, `RequestResolver` | • | • | | • | | • | A detached fork |
| `Schedule` | | | | | | | Items 13 and 14; a pure step as data |
| Streams | • | • | • | • | • | | `Queue`; row 205 |

- **The mask is not rare.** 14 source files of rc.112 use `uninterruptibleMask` (a search). They
  include `Semaphore.ts`, whose `withPermits` restores the caller's state around the wait and
  around the body (reading).
- **The fold covers each scan the catalogue names.** Each of these is one pass over a list with
  a running value:
  - `Semaphore`'s sweep, and `Pool`'s wake of `n` waiters;
  - the queue's acceptance of pending offers;
  - `PubSub`'s loop over subscribers;
  - the cache's eviction, and a removal by identity.
- **Retained behaviour splits the modules in two.** Six need a program kept in a value. The
  waiting modules and the fiber collections do not.

### F3. The order

The diagram shows what each item waits on. It shows the plan's order and proves nothing.

```mermaid
flowchart TD
  T3b["2. term update (seat T3b)"] --> FOLD["3. list fold, 4. bulk atoms, 5. handle identity"]
  FOLD --> WRAP["7. wrapper for waiting"]
  T3b --> PROBE["6. probe: handles in a cell"]
  KIT["9. law kit"] --> Q["Queue"]
  WRAP --> Q
  MASK["8. mask with restore"] --> SEM["Semaphore"]
  WRAP --> SEM
  Q --> STR["streams (row 205)"]
  SEM --> SR["SynchronizedRef, SubscriptionRef"]
  WRAP --> PS["PubSub, Latch, fiber collections"]
  RB["11. retained behaviour"] --> T2["Cache, RcMap, RcRef, Pool, RequestResolver"]
  SEM --> T2
  T5["15. faces of terms"] --> PRINT["printing every module above"]
  FOLD --> T5
```

- Items 3, 4, 5 and 8 change the language. Each starts as its own design note (`AGENTS.md`,
  "Working").
- Item 9 is proof infrastructure only. It can be designed beside the fold.
- The pure queue of the queues review needs none of them. It is a Lean model with its laws.

### F4. What the fold's design must show

The fold's first named consumer is the queue's service pass over its pending requests (Codex's
review). The fold's design note is accepted when it writes each step below as one term and
evaluates it:

1. the queue serves the takers that wait, after a batch offer;
2. the queue accepts pending offers, after a batch take;
3. `Semaphore` grants permits to waiters in order while permits remain;
4. `PubSub` hands one message to every subscriber;
5. a removal of one waiter by its handle's identity;
6. the oldest `k` entries leave a cache.

The same note states the typing rule, the scope rule, weakening and evaluation. It also states
the laws on handles, the wire entry (DI-47), and the printed and read forms. From Codex's review
it also fixes:

- the order of the two binders, and how the body captures outer variables;
- an element and an accumulator at any types, nested handles included;
- the answer on an empty list, and the order of evaluation;
- that the fold is pure, so `Ref.modify` stays one atomic step that answers `B` and stores `A`;
- that a bulk atom is added only where a named consumer needs it.

### F5. What the transactions note and Codex's third review changed

- **Item 10 is open again.** The queues review said that the queue needs no posted wake. Its
  reason was wrong: no turn policy removes the time of a retry from the answers (Codex's third
  review). Probes P5 to P7 show the answers that the delivery decides.
- **Posting is common.** Six sites of the pin post a task at priority 0: the queue, the
  semaphore, the pool, the Latch, a transaction's commit and the fork. Every build posts a
  transaction's wake, Effect 3 included (the transactions note, F2 and F4).
- **Item 7 serves any body.** A finite model has one wrapper for a queue's take and for a
  transaction over two queues. Its law holds for every body at once (the transactions note, F5).
- **Item 17 is new.** A transaction needs a region in which no other fiber runs. The queue's
  step and its signals want the same region (the queues review, proposal 10).
- **Item 18 is new.** The clock's unit shows at two rows today. `Schedule`, the caches and
  `timed` would each fix the millisecond.
- **Transactions themselves are not groundwork.** They land after `Queue` and `Semaphore`, from
  their own design note. Items 7, 10 and 17 are what they need from this list.

Items 7, 10 and 17 belong in one design note. It covers the wrapper, the delivery of its
signals, and the region that makes a body and its signals one step.

## Proposals (not rulings): the questions to resolve before development

1. **The stance on schedules.** Each derived module names its own profile (row 79). No common
   entry signs one schedule difference for every module (Codex's review). The posted wake is
   designed once, under row 81, for every site that posts (F5). Whether the queue uses it is
   proposal 10 of the queues review.
2. **The fold.** One constructor, with `listTake` and `listDrop` as atoms and every other list
   function as a builder. Confirm, or ask for a counted loop too.
3. **Identity.** Extend `eq` to two handles of one kind. The alternative is a registration
   number in each module's state.
4. **The mask with restore.** Design it now as groundwork. This changes the timing of the
   owner's ruling on question 5 of the derived forms plan, not its content.
5. **The law kit's client alphabet** (item 9).
6. **Retained behaviour.** Design it after the first waiting modules, because none of them
   needs it. Confirm, or pull it forward.
7. **The pin.** Audit the changes between rc.112 and 4.0.1 in the files the proofs transcribe.
   `Ref.ts` and `Semaphore.ts` did not change; `internal/effect.ts` did.
8. **Seat T3b.** Its remaining slices do not depend on questions 1 to 7. Resume it on the
   owner's word.
9. **The queue's own questions** are in the queues review's proposals 2 to 6 and 10.
10. **The atomic region** (item 17). Design it with the wrapper and the delivery, in one note.
    Decide row 80's profile against the release's transaction rules, not the pin's.
11. **The clock's unit** (item 18). Move it to nanoseconds now, as an amendment under row 83.
    The two nanosecond readings follow the numbers decision.

## What this does not establish

- F2 rests on the catalogue of 2026-09-19 (reading). Its rc.112 citations were not checked again,
  and the changes of 4.0.0 and 4.0.1 were read for `Queue.ts` only.
- No item has a design. Each count of modules is a reading of the catalogue's table.
- That the fold covers every module's pure step is a reading of six cases. F4 makes it a test.
- Item 6 is believed landed. The probe is not written.
- F5 rests on the transactions note: finite runs and a finite model. Items 17 and 18 have no
  design, and the form of item 10 is not chosen.
