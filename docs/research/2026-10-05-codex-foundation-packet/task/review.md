# Posted programs: source review

Reuse `Eff` for executable bodies. Keep the execution identity, cancellation guard, dispatcher ownership, and delivery policy explicit.

Scope: read-only review of `docs/research/2026-10-05-claude-lead/transactions-and-clock.md`, particularly F4, F6, and proposals 1–3.
The inspected HEAD is `9b372555b85d983313d422b036cd59f6a5e84f30`.
No build, generator, installation, or new runtime probe ran.
The pinned source is rc.112. This review makes no independent claim about Effect 4.0.1.

The current machine already shares one command loop across its code carriers.
`Task`, `taskCmds`, `driveStep`, and `fireState` live in `src/Effect4/Machine/Fibers.lean`.
`Task` describes scheduled work. It is not a second application program representation.
`TaskMeans`, `taskCmds_rel`, `book_fireState`, and `book_flushAllState` live in `src/Effect4/Laws/Machine/Book.lean`.
These relations provide the existing integration route.

## Findings and smallest repairs

### 1. F4 and F6.3: posting is only one part of a deferred fork

`RunMachine.spawn` allocates a fiber, records its origin, selects its mask, and copies the parent's context.
`RunMachine.start` either starts that child immediately or posts its first evaluation.
`Cmd.trackChild` and `exitFiber` implement supervision in `src/Effect4/Machine/Fibers.lean`.
The pin's `forkUnsafe` does the corresponding allocation, context copy, posting, and child tracking (`internal/effect.ts:5264–5284`).

The retained `postedWake` control gives a concrete distinction.
Its files are `/private/tmp/codex-effect4-overnight-monitor/2026-10-05-deferred-latch-probes/runtime/probe.ts` and `results.json`.
Under its finite manual scheduler, Latch's wake survives opener exit.
An ordinary forked child is interrupted before its wake, leaving the waiter pending.
A detached child wakes the waiter but adds a fiber. Joining the child keeps the opener pending until the wake.
This is retained finite rc.112 host evidence, not a new run or a general simulation.

`postTask` still accepts an exited owner's retained dispatcher. DB-13 explicitly requires this behavior.
`driveStep` ignores `evaluate` on an exited fiber.
Therefore running a posted body as the dispatcher's owner also fails to reproduce the existing rule.

**Repair:** Replace “A fork is a posted program” with “A deferred fork allocates a supervised child and posts its first evaluation.”
F6.3 must choose the helper's supervision, mask, context, completion, and cancellation rules before discussing identity erasure.
A detached helper remains a candidate under a named observation and relation.
Reusing `Eff` does not require equating that helper with the posting owner or resumed waiter.

### 2. F4's consumer table: capture timing includes reentrant traversal

The three controls listed after F4's table omit what can run between selections.
The pin's `Queue.releaseTakers` resumes one taker, then rereads messages (`Queue.ts:1955–1966`).
`Semaphore.releaseUnsafe` similarly rereads free permits while iterating its live waiter set (`Semaphore.ts:257–267`).
A resumed waiter can change the resource before the next selection.

`Pool.wakeWaiters` instead retains the set object when posting, chooses members when running, then invokes a fixed snapshot (`Pool.ts:700–714`).
`Latch.flushScheduled` clears the pending batch before invoking its captured callbacks (`internal/effect.ts:5592–5598`).
Those choices are observably different policies even when every body uses `Eff`.

A source-derived control can distinguish a pure initial selection from Semaphore's live sweep.
Start with one occupied permit and two waiters. Release it, then let the first waiter acquire and release during its resumed continuation.
The source callback can see the returned permit and reach the second waiter in that callback.
A pure selection made before resuming the first waiter cannot use that returned permit.
This control was not executed in this review.

**Repair:** Add selection timing, live versus snapshot traversal, and reentry points to F4's table.
Use a pure `listFold` for the queue's atomic state calculation.
Do not identify that fold with every source callback's wake pass.
The first fold consumer needs its own typed scope, capture, evaluation, and one-`Ref.modify` contract.
A broad abstraction census is not a prerequisite for that consumer.

### 3. F6.3: capture the batch reference, not necessarily the initial batch contents

`WakeList.schedule` in `src/Effect4/Machine/Wake.lean` posts only when it creates a batch.
A later schedule appends pending waiters to that batch without posting again.
`WakeList.runBatch` reads the current batch and clears it.
The pin's `Latch.scheduleUnsafe` follows this policy (`internal/effect.ts:5577–5590`).

Here is a source-derived counterexample to two tempting encodings.
Scheduling waiter A creates a batch, advances phase to 1, and posts one task.
Registering B and scheduling again extends the batch, advances phase to 2, and posts no task.
Freezing the initial waiter list in the program loses B.
Rejecting the task because its stored phase differs from the current phase loses the entire batch.
`Stores.wakeList` currently ignores its phase argument in `src/Effect4/Machine/Stores.lean`.
That argument cannot become a freshness check without changing the batch protocol.

**Repair:** State each producer's capture rule explicitly.
For Latch, retain access to the mutable pending batch until dispatch, then detach the batch before resuming anyone.
If a stale-batch guard is required, give it a separate identity with a stated lifetime.
Do not infer coalescing from equal program bodies.
The pin's transaction commit posts callbacks per journal entry, including unchanged entries (`Effect.ts:24343–24355`).

### 4. F6.3 and proposal 3: a typed body is only part of typed scheduled work

`driveStep` resumes the existing fiber only when its parked token matches.
It then preserves that fiber's saved continuation, context, and mask through `core.answerWith`.
Stale tokens do nothing. A fresh helper does not replace this receiver protocol.
The dispatch owner and resumed target can differ.
`drainOwed` preserves the chosen owner, priority, target, and token in `Task.resume`.

`SnapshotTyped`, `EditTask`, and `edit_task` in `src/Effect4/Laws/Program/Typed/Assembly.lean` type the actual scheduled command queue.
Their supporting facts currently depend on the three existing `taskCmds` shapes.
A new body must enter that proof path, not only pass the source program checker.

Future execution also needs a resolved program entry and a valid captured environment.
`captureTyped_mono` in `src/Effect4/Laws/Program/Typed/Commands/Bookkeeping.lean` already transports existing captures across world extension.
It does not establish general retained behavior values.
Row 82 distinguishes lexical captures, service context, entry resolution, and lifetime.

**Repair:** Start with an `Eff` body supplied at the posting site and its existing typed environment.
Retain target/token guards and dispatcher metadata outside that body where their interpretation requires them.
Specify whether service context is captured at posting or selected when executing.
Do not promote the whole machine `Capture` into a value to make this reuse possible.

### 5. F8 and proposals 1–2: a common wrapper needs separate execution and progress contracts

The note already identifies admission as open. Make that admission a premise of the wrapper's generic law.
A body that can complete a Deferred may run a resumed fiber before returning, even when masked and prevented from yielding.
`evaluatePrim` and `drainOwed` in `src/Effect4/Machine/Fibers.lean` expose that route.
An atomic state calculation and the later signal delivery therefore need distinct boundaries.

An arbitrary posted `Eff` body may park, yield, fail, or exhaust the driver budget.
`fireState` drains a dispatcher snapshot before running its tasks.
`fireStep` stops later tasks when its command budget expires.
`driveState` retains command residue, but the public decision boundary does not retain the complete outer driver remainder.
`docs/core/machine-state.md` §5 already requires a replay or retained-suspension contract.

`flush_fair` in `src/Effect4/Laws/Machine/Scheduling.lean` proves bounded callback entry under `FlushReady`.
It does not prove that arbitrary task bodies finish or that every owed wake occurs.

**Repair:** Define dispatch entry, body completion, and delivery of owed signals separately.
For the first atomic body, use an admitted finite fragment and prove an embedded sufficient budget.
Row 84's standalone `Straight` bound does not supply that connector automatically.
For general bodies, choose replay from the original state or retain the complete driver continuation.
Keep eventual delivery conditional on the chosen scheduler and body-progress assumptions.

## Proposed proof placement

These are proposed obligations, not installed goals or proved statements.
Each new claim needs its semantics and registry entry in the implementation slice.
Existing placements live in `docs/core/semantics.md` and `tools/Tools/SemanticsRegistry.lean`.

| Proposed obligation | Concept, property, and registry question | Exact reach and exclusions | Consumer |
| --- | --- | --- | --- |
| `postedBody_entry_typed` | `residual-program-typing`; serves `denote-typed`, role `preservation`; planned goal for source entry and captures | A checked supplied `Eff` body, resolved entry, typed lexical environment, selected service policy, future world extension; row 82. Does not establish lifetime, delivery, or general behavior values. | `SnapshotTyped` and `EditTask`, then `decision-keeps-typed`; M5 to M6, R4/R7 |
| `postedTask_decision_preserves` | `reactive-scheduling`; serves `decision-keeps-typed` and `waiter-completion-typing`, role `preservation` | Chosen execution identity, known dispatch owner, receiver/token correlation, stale delivery, exit and cancellation rules; rows 81/86 and DB-13. Does not establish source agreement or progress. | `edit_task`, `driveState_lift`, and `decision_preserves`; M6 |
| `postedWake_profile_agrees` | `translation-simulation`; serves `run-eq-ref`, new producer-specific claim, role `simulation` | One producer, explicit observation, helper identity relation, tape relation, dispatch order, capture timing, coalescing, and cancellation; rows 79/81. Does not establish agreement for other producers or arbitrary schedulers. | Existing `TaskMeans`/`Book` relations and the module's profile connector; M7, R8/R10 |
| `admittedAttempt_single_owner` | `reactive-scheduling`; new atomic-region property and claim, role `preservation` | Transitively admitted body, cleanup installed before registration, atomic decision/registration, rollback domain, and budget or retained continuation; rows 80/84. Does not establish eventual retry success or host atomicity. | Common wait wrapper and first queue attempt, then the transaction connector; M6, R4/R11 |
| `postedWake_debt_progress` | `reactive-scheduling`; serves `scheduler-progress`, new restricted delivery claim, role `progress` | Explicit finite body progress, sufficient fuel or retained suspension, fair compatible decisions, known owners, and cancellation outcomes; rows 79/80/81. Does not follow from typing or `flush_fair`, and does not establish infinite fairness. | First producer's progress clause and `frontier-names-work`; R12 |

The first slice can remain small: one typed fold consumer and one explicitly admitted posting policy.
The common program representation is already available. Its execution contract is the part this proposal still needs to choose.

## Acceptance recommendations and order

The final plan check sees HEAD `0741ab17cc99d1c3944e1cf52e838b93bf5fec65`.
The recommendations below answer the latest questions in `groundwork-plan.md`.

1. **Accept reuse of `Eff`; retain the scheduler contract.** Keep `Task` as the description of scheduled work.
   A generalized body uses the existing program carrier and interpreter.
   Its metadata names dispatch owner, priority, execution identity, capture policy, and cancellation behavior.
   Keep start, resume, and batch wake distinctions until their replacement relation states those behaviors.
   Do not require a separate callback program language.
2. **Design mask and restore now. Land them with their first consumer.** Use a first-order mask binder and lexically addressed restore occurrence.
   The mask records the caller's interruption state dynamically. Restore selects that saved state, not unconditional interruptibility.
   State nested-mask, exit, pending interruption, and cleanup behavior before implementation.
   The first profile can refuse escaping restore references.
   `Semaphore.withPermits` is the named consumer. Queue operations needing no restore need not wait for it.
   Changing the reported owner ruling's timing needs the owner's explicit amendment.
   Existing `actionAt` in `src/Effect4/Program/Compile.lean` only provides fixed true/false masks.
3. **Prefer application-signature rows for clients.** Use the existing `Eff` representation for client programs.
   Give the law kit abstract request rows, a typed expansion into implementation `Eff`, and a data profile.
   Keep its client alphabet separate from the native implementation operations as a signature, not another program syntax.
   The expansion must retain the client's result, error, environment, handle, and observation relations.
   Instantiate the kit for Queue first. Do not require a universal law framework before that checked instance.
4. **Defer retained behavior values.** A body supplied at posting or a lexically closed `Eff` entry does not require a general value containing code.
   Row 82 remains the design boundary for storing and invoking behavior through user-visible values.
   Choose Cache's retained lookup as its first consumer when that module is scheduled.
   That consumer makes the entry signature, captured keys, service context, and invocation lifetime concrete.
5. **Land the smallest dependent slices.** Finish the approved term update, then add the fold with the queue service pass.
   Establish handle storage and identity with that consumer.
   Next fix the queue profile, delivery ownership, and wait wrapper, using the law kit's first instance.
   Land mask and restore before Semaphore's protected permit wrapper.
   Generalize retained behavior and transactions only when their first consumers need them.

These recommendations accept the reusable structure without treating the finite transaction model as the machine's generic wrapper proof.
