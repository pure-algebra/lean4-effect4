# Task, masking, and cancellation contracts from primary sources

Adopt three separate contracts: cancellation restoration, ownership of scheduled work, and notification followed by retry.
Reuse `Eff` for their bodies. None of these sources requires another program representation.

Evidence: fresh primary-source reading, downloaded references, and source inspection.
Status: design recommendations and proposed obligations. No Lean proof, build, or new runtime experiment ran.
Scope: groundwork items 7, 8, 10, and 17 in `docs/research/2026-10-05-claude-lead/groundwork-plan.md`.
The sources inform those contracts. They do not prescribe Effect's scheduler.

## Reference set

`vendor/refs/MANIFEST.tsv` contains no matching masking, condition-variable, or structured-concurrency reference.
The downloaded artifacts and SHA-256 hashes are in `resources/manifest.json` and `resources/index.md` beside this note.

### A. Masking and resource cleanup

Marlow, Peyton Jones, Moran, and Reppy, *Asynchronous Exceptions in Haskell*, PLDI 2001, pages 274–285.
[Author bibliography](https://simonmar.github.io/bib/async01_abstract.html) and [author PDF](https://simonmar.github.io/bib/papers/async.pdf).
The relevant original sections are §5.1 “Safe Locking”, §5.2 “Blocking exceptions”, and §5.3 “Interruptible Operations”.
I inspected PDF pages 3–4 visually because its text extraction is corrupt.

The paper identifies the gap between acquiring state and installing cleanup.
Its scoped operations restore control state on ordinary and exceptional exits.
Its `unblock` explicitly enables interrupts, regardless of an enclosing blocked scope.
Its blocking `takeMVar` accepts interruption before acquisition, but not after acquisition while enclosed by `block`.
**Limit:** this is the paper's calculus, not the modern `mask` API or Effect's interruption semantics.

Modern reference: GHC 9.12.2, base 4.21.0.0, [Control.Exception](https://downloads.haskell.org/ghc/9.12.2/docs/libraries/base-4.21.0.0-8bb5/Control-Exception.html#v:mask).
Relevant declarations are `mask`, `uninterruptibleMask`, `MaskingState`, `bracket`, and “Applying mask to an exception handler”.
`restore` reinstates the incoming masking state; it does not always enable interrupts.
GHC distinguishes unmasked, interruptible masking, and uninterruptible masking.
Its [bracket implementation](https://downloads.haskell.org/ghc/9.12.2/docs/libraries/ghc-internal-9.1202.0-a87f/src/GHC.Internal.Control.Exception.Base.html#bracket) masks acquisition and cleanup, restoring only the body.
**Limit:** import the restoration and ownership pattern, not GHC's three-state representation or blocking exception policy without an Effect-specific decision.

### B. Child ownership and queued callbacks

Reference implementation: Trio v0.30.0, commit `c49507856005763d9391c7044a7e0a7a5bd1548f`.
The release identity comes from the saved GitHub tag response.
Its [core reference](https://trio.readthedocs.io/en/v0.30.0/reference-core.html#child-tasks-and-cancellation) defines nursery ownership.
Children inherit the nursery's cancellation scopes, rather than the spawning caller's currently active scopes.
A nursery waits for its children at exit.
`Runner.spawn_impl` records nursery membership and cancellation status before scheduling the new task.
The source is [the pinned `_run.py`](https://github.com/python-trio/trio/blob/c49507856005763d9391c7044a7e0a7a5bd1548f/src/trio/_core/_run.py).
**Limit:** Trio's normal nursery exit waits. Effect's ordinary child supervision has its own exit policy.

Queued callbacks have a separate reference implementation: [the pinned `_entry_queue.py`](https://github.com/python-trio/trio/blob/c49507856005763d9391c7044a7e0a7a5bd1548f/src/trio/_core/_entry_queue.py).
`EntryQueue.task` runs callbacks through a system task.
`run_all_bounded` fixes the ordinary queue's count before each pass and snapshots the idempotent queue.
Later submissions remain queued for another pass.
`run_sync_soon` rejects submissions after shutdown begins; accepted residual work drains during shutdown.
Idempotent submissions use a separate keyed queue. This is an explicit caller option, not an inferred equal-observation relation between programs.
**Limit:** these are Trio's runtime-lifetime and queue policies. They do not select Effect's owner, priority, or coalescing rules.

### C. Cancellation and completion arbitration

Trio's [low-level reference](https://trio.readthedocs.io/en/v0.30.0/reference-lowlevel.html#trio.lowlevel.wait_task_rescheduled) specifies `wait_task_rescheduled`, `reschedule`, and the abort result.
`Abort.SUCCEEDED` requires cleanup that prevents a later resume.
`Abort.FAILED` leaves responsibility for eventual resumption with the operation.
The runtime attempts abort at most once per wait.
The protocol requires one reschedule per wait, counting successful abort as that reschedule.
The implementation is `Task._attempt_abort` in the pinned `_run.py`.

The same reference's [checkpoint section](https://trio.readthedocs.io/en/v0.30.0/reference-lowlevel.html#trio.lowlevel.cancel_shielded_checkpoint) separates scheduling from cancellation.
Its successful-operation path schedules under cancellation protection before returning the result.
That implements its chosen guarantee: cancellation means the operation did not happen.
**Limit:** Effect need not adopt that guarantee. It must choose its own outcome at the operation's commit-to-return boundary.

The [pinned `_parking_lot.py`](https://github.com/python-trio/trio/blob/c49507856005763d9391c7044a7e0a7a5bd1548f/src/trio/_core/_parking_lot.py) supplies a concrete queue protocol.
`ParkingLot.park` installs the wait entry and supplies deletion as its abort action.
`unpark` removes a selected list before rescheduling its tasks.
**Limit:** this snapshot selection does not reproduce Effect's live Semaphore or Queue callback traversal automatically.

### D. Notification, retry, and cancellation under a lock

Standard: The Open Group Base Specifications Issue 8, IEEE Std 1003.1-2024.
The saved pages identify that edition explicitly.
[Condition wait](https://pubs.opengroup.org/onlinepubs/9799919799/functions/pthread_cond_clockwait.html), DESCRIPTION and RATIONALE “Condition Wait Semantics” and “Cancellation and Condition Wait”.
Releasing the mutex and beginning the wait form one operation relative to another thread's mutex-and-signal access.
A returned wait does not establish its predicate; the caller checks again.
Cancellation reacquires the mutex before cleanup.
A canceled waiter must not consume a concurrent condition signal when other threads are waiting.
**Limit:** Effect has fibers and explicit stores, not POSIX mutexes. This supplies a comparison contract, not a claimed conformance requirement.

[Condition signal/broadcast](https://pubs.opengroup.org/onlinepubs/9799919799/functions/pthread_cond_signal.html), DESCRIPTION.
Issue 8 atomically selects currently blocked threads and unblocks one or all, respectively.
Scheduling policy governs selection and subsequent lock contention. An empty wait set retains no signal.
**Limit:** this does not specify FIFO service, reservation transfer, helper identity, or Effect's delayed callback selection.

Paper: Lampson and Redell, *Experience with Processes and Monitors in Mesa*, CACM 23(2), February 1980, pages 105–117.
[Author's hosted CACM copy](https://www.microsoft.com/en-us/research/wp-content/uploads/1980/01/Lampson-and-Redell-Experience-with-Processes-and-Monitors-in-Mesa-CACM-version.pdf), §4, §4.1, §4.2.
I read those sections through the web PDF reader. Direct file download returned HTTP 403, so no local PDF hash is claimed.
Mesa notification allows later execution and intervening entrants; the waiter repeats its predicate test.
The paper separates resource scheduling from the monitor's mutual exclusion.
Its naked-notify discussion identifies the check-before-wait lost notification race.
**Limit:** this explains signal-and-continue. It does not prove no starvation or prescribe Effect wake timing.

## Recommended decisions for Claude

### 1. Give mask and restore one dynamic meaning

Choose restoration of the associated mask's incoming interruption state.
A first-order lexical reference identifies the mask binder; its runtime activation stores the saved state.
Repeated calls of the same program syntax must resolve the correct activation, including nested calls.
Restore temporarily selects that state and restores its immediate surroundings on every exit.
The initial profile can reject references that escape their mask's dynamic extent.
Do not encode restore as unconditional `interruptible`, or as a compile-time Boolean.
Do not add GHC's third masking state unless an Effect behavior needs it.
Cleanup invocation and successful cleanup completion remain separate claims; a blocked finalizer needs its own termination premise.

### 2. Separate scheduling ownership from child ownership

Keep `Task` as scheduling data with existing `Eff` content where execution needs a program body.
Specify dispatcher owner, execution identity, lifetime owner, captured context, and cancellation behavior separately.
A deferred fork remains allocation plus supervision plus a queued first run.
A queued notification need not acquire a new child lifetime.
A helper implementation needs a relation covering lifetime and cancellation as well as hidden identity.
DB-13's dispatcher-after-owner-exit rule remains a required current premise.

### 3. Use an explicit consumption boundary for the first Queue

Recommend the target-compatible boundary, subject to owner ratification.
Before atomic consumption, cancellation withdraws the taker's request without consuming a message.
At atomic consumption, the operation commits its state change.
After commitment, restoring interruption may report `Interrupt` before the caller's continuation receives the value.
Committed state remains committed.
Record commitment, operation exit, continuation entry, and whole-fiber exit separately.
Do not claim an interrupted take implies no consumption or that every consumed value reaches its caller's continuation.

The [new isolated probe](../../atomic/cancel-return/README.md) confirms this distinction on rc.112 and 4.0.1.
Its no-cancellation and inherited-mask controls distinguish operation return from whole-fiber exit.
Its pre-consumption cancellation control leaves a later offer available.
`setInterruptible` and `FiberImpl.getCont` implement this behavior in both inspected runtimes.
The receipt identifies their exact paths, versions, hashes, and pinned source locations.

Trio's cancellation-without-effect guarantee remains a stronger, separate profile requiring an adapter and proof.
Masking alone cannot provide it on the inspected Effect runtimes.
For each parked token, require at most one effective completion and retain ownership of outstanding notifications.
A stale callback may remain inert, as the current machine requires.
Cleanup must account for pending registrations and captured batches.

Keep allocation and permit lifetimes distinct from destructive queue consumption.
Those resources still require protected acquisition, installed cleanup, and release during scope unwinding.
A committed acquisition does not permit abandoning its resource.

### 4. Freeze notification semantics separately from result delivery

Use notification to request another attempt, unless the profile explicitly reserves and transfers a result.
Make decision-to-wait and registration indivisible relative to resource-changing operations, or use a checked revalidation protocol.
A generic wrapper needs an invariant that each newly eligible waiter has an owned notification or another specified retry path.
Predicate retry alone cannot repair a notification that was never registered.

For every producer, record selection time, traversal style, count, coalescing key, cancellation handling, owner, and priority.
A Latch body must read the pending batch when it runs, including joiners added after posting.
A Queue or Semaphore callback may need to resume one waiter and reread state before selecting another.
Neither POSIX's selected snapshot nor Trio's parking-lot snapshot automatically supplies that Effect behavior.
FIFO must follow from the module's request discipline, not from the existence of a condition variable.

### 5. Keep cancellation, scheduling, and bounded evaluation distinct

Masking says which interruption transitions are available. It does not establish that only one fiber can run.
A bounded callback pass limits callbacks per pass, not the work inside each callback.
No inspected external source proves a sufficient Lean driver budget or reconstructs discarded driver work.
Use the current row 84 proposal for a finite admitted first body only after its embedded-budget connector is proved.
Otherwise retain all driver continuation data, or replay the original invocation with its compatible decisions.
Do not interpret resuming from the partly changed state as replay from the original state.

## Proposed obligations and placement

These are proposed semantics-registry entries and planned-goal names, not installed declarations.
Add each missing required property to `docs/core/semantics.md` and `tools/Tools/SemanticsRegistry.lean` in its implementation slice.
The existing source review at `../../task/review.md` names the relevant machine and proof declarations.

| Planned goal | Concept, property, and role | Consumer and immediate prerequisite | Premises and observation | Exclusions |
| --- | --- | --- | --- | --- |
| `mask_restore_activation` | `scope-lifetime-finalization`; new `mask-restore` required property; preservation | Mask/restore compiler and frame clauses, then Semaphore `withPermits`; first settle the binder signature and captured-state policy | Well-scoped mask references, identified dynamic activation, ordinary/failure/interruption exits; observe interruption state, pending cause, and continuation | No isolation, successful cleanup, or progress claim; serves R11 and M5/M6 |
| `posted_task_lifetime_agrees` | `translation-simulation`; producer-specific scheduled-delivery claim serving `run-eq-ref`; simulation | Queue's first posted producer, existing `TaskMeans` and `book_fireState`; first choose execution and lifetime owners | Named source version and profile, known dispatcher, compatible decisions, explicit helper relation; observe exit, output, stores, and public handle relations | No all-producer agreement, arbitrary scheduler equivalence, or hidden-fiber assumption; rows 79/81, DB-13; M7/R8/R10 |
| `wait_cancel_arbitration` | `reactive-scheduling`; new wait-ownership property serving `decision-keeps-typed`; preservation | Common wait wrapper and active/stale delivery; first choose the commit-to-return rule and cancellation states | Unique registration/token, valid cleanup, explicit reservation owner; observe at most one effective completion, preserved resource accounting, and live delivery ownership | No eventual wake without scheduler/body premises; rows 80/81/86; M6/R11 |
| `wait_registration_no_gap` | `reactive-scheduling`; new notification-coverage property; preservation | Queue service pass and retry wrapper; first define predicate/read dependency and atomic registration or revalidation | Store transition and registration serialization, cleanup-before-unmask, declared wake policy; observe each eligible waiter as retrying or owning a notification | No FIFO from notification alone, no unbounded fairness, no generic proof for arbitrary `Eff`; rows 80/81; M6/R12 |
| `posted_producer_step_agrees` | `translation-simulation`; helper of the producer's agreement claim; simulation | Latch/Queue/Semaphore profile connector; first freeze selection timing, reentry, and coalescing | Matching store/handle relations and explicit callback decisions; observe selected requests, mutations between resumes, and next pending batch | No substitution of snapshot for live traversal without proof; rows 79/81; M7/R10 |
| `attempt_budget_or_resume` | `reactive-scheduling`; serves `drivestate-lift` and `frontier-names-work`; preservation and inversion must be distinct claims | Atomic wait wrapper and first finite posted body; first choose sufficient budget, full suspension, or original-state replay | Admitted body, typed captures, complete inner and outer driver state or embedded bound; observe store, pending commands, owner, mask, and owed deliveries | No conversion of fuel exhaustion to failure; no liveness from bounded callback entry; rows 80/84; M6/R12 |

The first implementation can stay narrow: the queue's pure fold inside one atomic update, plus one chosen notification contract.
Mask/restore can land with Semaphore's protected permit operation.
General retained behavior values and general resumable transactions remain later consumers of the same contracts.
