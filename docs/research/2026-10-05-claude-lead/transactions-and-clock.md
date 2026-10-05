# 2026-10-05 transactions, the wait wrapper and the clock

Status: research note (history, not authority). Base: `9b372555` (`refactor/phase1-phase3`).

**The one thing to know first.** The owner asked how the queue design bears on transactions,
whether to prepare for them now, and whether the clock should be finer. Six results:

1. A queue operation that waits and a transaction that retries are one pattern. A pure body runs
   on a snapshot in one atomic attempt, and it commits or registers a wait. A finite model has
   one wrapper for both (F5).
2. The groundwork owes transactions three designs and no transaction code. They are the wait
   wrapper for any body, an atomic region, and a signal with two deliveries (F4, F8).
3. The buffer, the versions and the locks of an implementation belong to the lowering to OCaml
   (the LCNF route). The reference meaning is one atomic step (F8).
4. The pin's transactions have two defects that the scout of 2026-09-19 inferred by reading. Runs
   on the pin now show both, and the released 4.0.0 repairs both (F2).
5. Effect 4 posts a queue's wake. Effect 3's runs show the message handed over inside the offer.
   A sliding queue of Effect 4 discards a message while a taker waits (the queues review, P5 to
   P7).
6. The clock should count nanoseconds. That is Effect's finest unit, and the tree's clock type is
   already exact. The pin's test clock is not exact below a microsecond (F7).

Nothing here is a ruling. No file of the tree changed.

## Question

The owner asked on 2026-10-05:

1. How does the queue design bear on software transactional memory? How would this tree
   implement it, and how does Effect?
2. Is that work for now, or does it come with lowering? The same for transactions in general.
3. Should a base abstraction for it land now?
4. Could such a semantics be "just another program", so that queues and transactions compose
   across programs?
5. Should the clock be finer than milliseconds?

## What was read or run

| Item | How |
| --- | --- |
| The STM scout (`docs/research/2026-09-19-stm-scout.md`); `docs/core/machine-state.md` §5; decisions rows 79, 80, 81 and 83 | read |
| The transaction section of `vendor/effect-4.0.0-rc.112/src/Effect.ts` (`tx`, `awaitPendingTransaction`, `commitTransaction`, `txRetry`); `TxRef.ts` | read |
| The same two files in the released 4.0.0 and 4.0.1, against the pin | tested (a diff of the code lines); 4.0.0 and 4.0.1 are equal there |
| `docs/research/2026-10-05-claude-lead/tx-probes/tx-probes.ts` on rc.112, 4.0.0, 4.0.1 and Effect 3.22.2, with bun 1.4.2; each output sits beside it | tested |
| The exports of Effect 3.22.2's `STM` module, and its `T` modules | tested (a search); its source was not read |
| Every `scheduleTask` call of the pin's source | tested (a search), then read at the six sites of F4 |
| `makeWithTransaction` in `vendor/effect-4.0.0-rc.112/src/unstable/sql/SqlClient.ts` | read |
| `docs/research/2026-10-05-claude-lead/tx-probes/TxModel.lean`, a pure model of one wrapper | tested: every control holds; the bounded exploration passes; the red control fails as it must |
| `ClockImpl` and `timed` in `vendor/effect-4.0.0-rc.112/src/internal/effect.ts`; `testing/TestClock.ts`; `Duration.ts`; `Clock.ts` | read; `Clock.ts`, `TestClock.ts` and `ClockImpl` equal 4.0.1's by code lines (tested) |
| `docs/research/2026-10-05-claude-lead/tx-probes/clock-probes.ts` on rc.112 and 4.0.1 | tested |
| `src/Effect4/Data/ClockMillis.lean`; `src/Effect4/Machine/Timer.lean`; the rows `sleep` and `clockNow` of `src/Effect4/Program/Native.lean`; `duration` in `src/Effect4/Codegen/Styles.lean`; `ocaml/clock/e4_clock.ml` | read |
| The uses of `ClockMillis` in `src`, `Test` and `tools` | tested (a count): 197 in 42 files |
| Any Lean file of the tree, any proof | not written |

## Findings

### F1. How Effect implements a transaction

| Part | Effect 3.22.2 | rc.112, the pin | 4.0.0 and 4.0.1 |
| --- | --- | --- | --- |
| The body | A value of the `STM` type: transactional operations and pure code | Any effect, under `Effect.tx` | The same as the pin |
| An alternative | `orElse`, `orTry`, `check` | None | None |
| A cell | `TRef` | `TxRef`: a value, a version, and a map of waiting callbacks | The same |
| The attempt's record | not read | A journal: one entry for each cell that the body read or wrote | The same; each entry also says whether the body wrote it |
| Other fibers during the body | By its type the body holds no effect; not read further | They run at each yield or wait of the body | The same as the pin |
| The check before a commit | not read | Each journal entry's version equals its cell's version | The same |
| A retry | `STM.retry` | `txRetry` sets a flag and fails the body with an interrupt | The same |
| The wait | not read | Registers on every journal cell, with no check | Checks the versions and registers in one synchronous step |
| The wake | A commit that only read a cell wakes its waiters (TX2) | The same (TX2) | Only a cell that the commit wrote |
| The delivery of the wake | Posted (TX5) | Posted: one task for each waiter, on the committing fiber's dispatcher | The same |
| The modules over it | 12 `T` modules, `TRef` included | 11 `Tx` modules, `TxRef` included | 11 |

- The pin's column is a reading of `tx`, `awaitPendingTransaction` and `commitTransaction`. The
  scout gives the pin's rules in full.
- Effect 3's column rests on the runs of F2 and on its export list.
- **The journal exists because another fiber can commit during the body.** The scout said so (its
  §2.4). TX4 shows the result in every Effect 4 build.

### F2. The probes: transactions

Each row is one finite run with bun 1.4.2. The probe file states each schedule.

| Probe | Effect 3.22.2 | rc.112 | 4.0.0 and 4.0.1 |
| --- | --- | --- | --- |
| TX1. A body reads a cell, yields, and retries on the value that it read. Another fiber commits a new value during the yield. Nothing writes the cell afterwards | no such body: the type excludes the yield | **the transaction waits for ever** | it runs again and answers the new value |
| TX2. A transaction waits for a cell to change. Another fiber reads the cell three times | three more runs of the body | three more runs of the body | no run |
| TX2, continued. The other fiber writes the value that the cell already holds | one more run | one more run | one more run |
| TX4. Two cells keep a sum of zero. A body reads one, yields, and reads the other. Another fiber moves both during the yield | no such body | the first attempt sees the pair `(0, -1)` | the same |
| TX5. A transaction waits for a cell to leave zero. One fiber commits `1`, then `2`, with no yield between | answers `2` | answers `2` | answers `2` |
| TX5, with a yield between the two commits | answers `1` | answers `1` | answers `1` |

- **TX1 is the lost wake that the scout inferred** (its rule T6, part d). The pin registers its
  wait after the other commit has woken the waiters. The release checks the versions as it
  registers.
- **TX2 is the scout's rule T7.** The pin wakes on any commit that touched the cell. The release
  wakes on a write. Effect 3 behaves as the pin here.
- **TX4 is no defect by Effect 4's rules.** A body may hold any effect, and an attempt with stale
  reads runs again. But the attempt's own effects have happened, on a pair that no commit made.
- **TX5: every build posts a transaction's wake.** The answer depends on a yield of the
  committing fiber, in Effect 3 too. The queue differs: only Effect 4 posts its wake.
- So the release repairs five known defects of the pin: P2, P3 and P4 of the queues review, TX1
  and TX2.

### F3. What the queue design and a transaction share

- **The smallest transaction is in the tree.** An atomic update of one cell by a pure function is
  a transaction over one cell (`Ref.modify`; seat T3b gives it binder terms).
- **The queue's request is a retry.** It runs a step. If the step cannot answer, the request
  registers, waits for a signal, and runs the step again (the queues review, F6).
- **The queue's first rule is the rule that TX1 breaks.** "The check and the registration must be
  one step" (the queues review, F5.4). The pin's transactions make them two.

A transaction differs in four ways:

- it touches several cells;
- its wait set is the set of cells that this attempt read;
- its commit names every request that waits on a written cell;
- its body is a program, not one term.

### F4. What a transaction needs from the groundwork

| Need | State in the tree | Groundwork item |
| --- | --- | --- |
| Cells at any type; binder terms; the list fold; handles in a cell; the identity of a handle | As the groundwork plan's items 1 to 6 | shared with the queue |
| The wrapper for an operation that waits | Missing | item 7, restated for any body (proposal 1) |
| A region in which no other fiber runs | The machine honours `PreventSchedulerYield` (`preventYieldRef`, `src/Effect4/Machine/ContextMap.lean`; `injectYield_prevented`, `src/Effect4/Laws/Machine/Clauses.lean`). Four more routes let another fiber run (`docs/core/machine-state.md` §5). No rule admits a body | new item 17: the atomic region (proposal 2); row 80 |
| To drop the writes of a body that fails or retries | The reference machine's store is a value, so the old store is still there. A lowered engine needs a buffer or an undo log | lowering (F8) |
| A posted wake | `WakeMode.scheduled` and `Task.wake` exist; no row of a program reaches them | item 10, reopened (proposal 3); row 81 |
| A mask that restores | Missing | item 8: `tx` restores the caller's state around its body and its wait |
| The `tx` construct, `txRetry`, the cell rows | Missing | later, after its own design note (row 80) |

A posted wake has more consumers than transactions. Each site below posts one task at priority 0
(the search, then reading).

| Site in rc.112 | The task |
| --- | --- |
| `Queue.ts`, `scheduleReleaseTaker` | wakes takers in order while messages remain; one task at a time; on the dispatcher stored at `make` |
| `Semaphore.ts`, `releaseUnsafe` | wakes waiters in order while a permit is free; it reads the permits when the task runs |
| `Pool.ts`, `wakeWaiters` | wakes the first `count` waiters |
| The `Latch` class, `scheduleUnsafe` | wakes the batch of waiters; later waiters join a batch that is pending |
| `Effect.ts`, `commitTransaction` | one task for each waiter of each cell |
| `internal/effect.ts`, the fork | the child's first run |

- **A fork is a posted program.** The machine has the same form (`Task.start`,
  `src/Effect4/Machine/Fibers.lean`).
- So row 81's question is wider than Latch. The sites differ in three controls: which waiters,
  and when they are chosen; one task or one for each waiter; whose dispatcher.

### F5. One wrapper: the model

`TxModel.lean` has one wrapper, `attempt`, and no step that is written for a queue.

- A body is a pure function of a snapshot of the store. It answers a value, `retry` or `fail`.
- One attempt runs the body. A success commits its writes and names each request that waits on a
  written cell. A `retry` registers the request on the cells that it read.
- A queue is one cell and two small bodies, `take` and `offer`.

| Control | What it shows |
| --- | --- |
| `queueTrace` | A take waits on an empty queue; an offer names it; its second attempt answers the message |
| `transferTrace` | `take` and `offer` compose into one body. When the target is full, the source keeps its message: no part of the move shows |
| `eitherTrace` | An alternative of two takes answers from the queue that holds a message. It waits on both queues when both are empty |
| `ticketTrace` | The turn check is state: a cell of tickets. A new request cannot pass the oldest (P1). The offer names the oldest request only, because the others did not read the buffer |
| `broadcastTrace` | Without tickets, one message names both waiting takes. The second runs again for nothing, and no answer changes |
| `lostWakeWhenSplit` | The red control. When the decision and the registration are two steps, a commit between them leaves the request waiting beside a message: TX1 |
| `explore` | Seven bodies over two queues; every sequence of at most six attempts; 137,257 runs. In every state, each waiting request would still retry. With a wrong wake rule the exploration fails |

- **The wrapper's law covers every body at once.** A body is a function of the cells that it
  read. A commit names every request that waits on a cell that it wrote. So no waiting request is
  left behind. The queues review's quiet-state law is one instance.
- **A module's own wake rule is a saving, and it needs that module's proof.** `ticketTrace` shows
  the cost of the generic rule: each new ticket names every waiting request. The queue's own step
  names one.
- The model has no fibers, no interruption and no delivery. It proves nothing about the tree.

### F6. Patterns that the formal view shows

The owner asked whether such a semantics can be "just another program". Five patterns follow.
Each is a candidate with its test, and none is a plan.

1. **A waiting operation is a body and the one wrapper.** The body is data. The wrapper, its
   cleanup and its law are written once (F5).
2. **Operations compose into one atomic body.** Effect keeps two families, `Queue` beside
   `TxQueue`, because a plain queue's operations do not compose. The pin has 11 `Tx` modules for
   that. Here one definition could serve both uses. The test: one queue whose `take` is the same
   body alone and inside a transaction.
3. **Posted work is a program.** A wake pass can be a program that a forked fiber runs (F4).
   TypeScript posts a closure, which nothing can inspect. The cost: the helper fiber's identity
   shows (`docs/core/machine-state.md` §4).
4. **A transaction is an atomic region with a release that reads the exit.** The release commits
   on success and undoes on failure. The pin's SQL client has this form over a host
   (`makeWithTransaction`: reading). It masks, sends `BEGIN` or a savepoint, runs the body, and
   sends `COMMIT` or `ROLLBACK` by the exit. A memory transaction undoes exactly, because no
   other fiber saw the middle. A host transaction is the host's to undo.
5. **A second reading of one program is a fold.** A program is data (`Eff`, `cata_eff`). The
   meaning of a body under a buffer is one more algebra. That is the scout's design C.
   TypeScript needs a second type or a run-time journal for it.

Alternatives are the clearest gain. Effect 3 had `orElse`. Effect 4 has none, because its bodies
hold effects that cannot be dropped. A body on a snapshot drops the left branch at no cost
(`eitherTrace`).

### F7. The clock

What the tree has:

- `ClockMillis` is an exact natural number with no bound (`src/Effect4/Data/ClockMillis.lean`).
  Its OCaml image is a Zarith integer (`ocaml/clock/e4_clock.ml`).
- The timer keeps `now` and each deadline in it (`TimerStore`, `src/Effect4/Machine/Timer.lean`).
- `sleep` takes a count of milliseconds, and `clockNow` prints as `Effect.currentTimeMillis`
  (`src/Effect4/Program/Native.lean`).
- The unit shows at those two rows, in the printer's `duration` and in the session's clock
  command (`Run.clock`, `src/Effect4/Run.lean`). The timer's arithmetic never reads it.

What Effect offers:

- **The nanosecond is its finest unit.** A `Duration` is a whole count of milliseconds, a whole
  count of nanoseconds, or an infinity. A fraction of a millisecond is rounded to a nanosecond
  (`make`, `vendor/effect-4.0.0-rc.112/src/Duration.ts`; C1).
- The `Clock` service has three readings: `currentTimeMillis`, `currentTimeNanos` and
  `monotonicTimeNanos` (`vendor/effect-4.0.0-rc.112/src/Clock.ts`).
- The pin's own runtime calls a nanosecond reading in 7 files outside the clock modules (a
  search). `timed` measures with the monotonic reading, and spans carry nanosecond stamps
  (reading).
- The live clock sleeps through the host's timer. A sleep of 100 microseconds took at least 1.15
  milliseconds in each of ten runs (C3). The monotonic reading stepped by 41 nanoseconds at
  least on this machine (C2).

| Probe | Result (rc.112 and 4.0.1 agree) |
| --- | --- |
| C1. `Duration.millis(0.5)` and `Duration.millis(1 / 3)`, in nanoseconds | `500000` and `333333` |
| C4. The test clock at time 0. A fiber sleeps 300 000 ns; the clock is adjusted by 1 ms | at its wake: `0.3` ms, wall `300000` ns, monotonic `300000` ns |
| C4. The same at time 1 700 000 000 000 ms | at its wake: wall `…300048` ns, monotonic `…300049` ns |
| C5. The test clock at time 0. Two fibers sleep 100 ns and 200 ns; the clock is adjusted by 150 ns | the first wakes, and the second still sleeps |
| C5. The same at time 1 700 000 000 000 ms | **the 100 ns sleep returns with no adjustment; the 200 ns sleeper wakes after 150 ns** |

- **The pin's test clock keeps each deadline as a floating-point count of milliseconds** (`make`,
  `vendor/effect-4.0.0-rc.112/src/testing/TestClock.ts`: reading). At a realistic time its step is
  about 244 nanoseconds. Below that a sleep returns at once or wakes early. At a wake the wall
  register and the monotonic register differ by a nanosecond.
- The same module keeps exact nanosecond registers for the two nanosecond readings. So only the
  deadlines lose precision.
- **Neither the queue nor a transaction reads the clock.** Their answers depend on the order of
  steps alone. A timeout composes from a sleep and a race.

The proposal: the clock counts nanoseconds.

- The meaning needs no new arithmetic, because the type is exact and has no bound.
- `currentTimeMillis` answers the count divided by one million, rounded down. That is a whole
  number, as the live clock's answer is.
- A sleep takes a count of nanoseconds. The printer picks the largest unit that divides it.
- Two more readings become rows: `currentTimeNanos` and `monotonicTimeNanos`. Each answers a
  `bigint` in TypeScript, and the type language has none. They wait for the numbers decision
  (rows 109 and 121).
- One register serves all three readings, because the tree refuses `setTime`
  (`TIMER-FB-SET-TIME`).
- The test clock agrees with this clock when every duration is a whole count of milliseconds.
  Below that, this clock is exact and the test clock is not. The clock's profile signs that
  difference (row 83).

### F8. Now, or with lowering

| Decision | When | Why |
| --- | --- | --- |
| The wait wrapper's contract: any body; the decision and the registration in one step; the cleanup; the delivery | Now | It is groundwork item 7, and the queue is its first instance. A wrapper for one cell only would be written twice |
| The atomic region: which bodies it admits | Design now; land with its first consumer | The queue's step and its signals want it too (the queues review, proposal 10). Row 80 asks for the rule before any version is erased |
| The signal's two deliveries | Design now, once (row 81) | Six sites of the pin post a task. Transactions post in every build |
| `tx`, `txRetry`, the cell rows, the `Tx` modules | After `Queue` and `Semaphore` | Nothing in the groundwork blocks them, and no module of the next wave needs them |
| The buffer or the undo log; versions; locks for an engine with parallel fibers | Lowering | The reference meaning is one atomic step. An engine owes a refinement to it (`docs/core/machine-state.md` §5) |
| A host transaction, such as SQL's | No machine feature | It composes from the mask that restores, a release that reads the exit, and a service. The host owns its atomicity (`docs/core/host-boundary.md`) |
| The clock's unit | Now | Two rows and the timer read the unit today. `Schedule`, the caches and `timed` come next, and each would fix the millisecond |

So the work splits in two. What a transaction means is language work, and its three shared
designs are due with the groundwork. How an engine stores an open transaction is lowering.

## Proposals (not rulings)

1. **Restate groundwork item 7.** The wrapper takes any body that answers a value, a wait or a
   failure. It registers in the step that decides to wait. The queue instantiates it with one
   cell.
2. **Add the atomic region to the groundwork** (item 17). It is one admission rule over a body,
   with the single-owner invariant that `docs/core/machine-state.md` §5 asks for. Decide row 80's
   profile against the release's rules, not the pin's: the release wakes on a write, and it
   checks as it registers.
3. **Design the signal's delivery once** (row 81), with F4's table as its consumers. Each module
   then names its delivery in its profile (row 79).
4. **The queue's delivery** is proposal 10 of the queues review.
5. **Transactions wait for their own design note**, after `Queue` and `Semaphore`. The scout's
   design B stays the candidate.
6. **One bounded probe of pattern 2** before any `Tx` module is planned: one queue definition,
   used alone and inside a transaction.
7. **The clock counts nanoseconds** (item 18), as an amendment under row 83. Its slices:
   1. the type and the timer;
   2. the two rows and the printer;
   3. the session's clock command;
   4. the two nanosecond readings, after the numbers decision.
8. **Upstream candidates**, for the owner to decide: P6 and P7 of the queues review, and the test
   clock's deadlines (C5). TX1 and TX2 are repaired upstream; the pin audit records them.
9. **The pin audit gains a reason.** The release repairs five defects of the pin (F2).

## What this does not establish

- Each probe is one finite run on one schedule with bun 1.4.2. None is a proof, and none says
  what the maintainers intend.
- Effect 3's source was not read. Its column of F1 rests on runs and on an export list.
- `TxModel.lean` is a finite model outside the tree. It has no fibers, no interruption and no
  delivery of a signal. Its exploration is bounded at six attempts over seven bodies.
- That a module's own wake rule loses no request is that module's proof. The model checks the
  generic rule only.
- The atomic region is not designed. That `PreventSchedulerYield` and an admission rule are
  enough is the scout's inference. `docs/core/machine-state.md` §5 lists what the rule must
  still exclude.
- Pattern 2 is a candidate. No queue was written that serves both uses. The cost of the generic
  wake on a busy queue is not measured.
- The clock's slices are not sized beyond the count of 197 uses. The change to the session
  protocol and to the stored outputs was not measured.
- No file of the tree changed, and no proof was written.
