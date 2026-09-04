# The deep fiber: rc.112's run loop, what Lean already has, and the shape of a program-carrying machine

Research note, 2026-09-03. Read-only survey plus one elaboration probe. Nothing
in this note is a theorem, a gate result, or a coverage claim. Every fact is
cited `path:line` and labelled **[read]** (I read those exact lines) or
**[inferred]** (a conclusion drawn from lines I read).

## Summary

1. rc.112's fiber is one class with seventeen state fields worth modelling (`vendor/effect-4.0.0-rc.112/src/internal/effect.ts:526-555`); `Effect4/Runtime/Runtime.lean:221-232` models five and says so at `:217-220`.
2. The run loop is `evaluate` (`internal/effect.ts:599-628`) wrapping `runLoop` (`:629-679`); parking, resuming, observers and child interruption are all inside those 80 lines, and forking is the 21 lines `:5264-5284`.
3. Four decisions a Lean tape must supply: which dispatcher's host callback fires (`Scheduler.ts:83-103, 207-212`), the `shouldYield` verdict (`Scheduler.ts:174-176`, overridable because `Scheduler` is a service, `Scheduler.ts:78-81`), when an async `resume` is called (`internal/effect.ts:1117-1125`), and the interruptor id (`internal/effect.ts:574-578`).
4. rc.112 has **no global run queue**: each fiber lazily owns its own dispatcher (`internal/effect.ts:552-555`), a deferred fork enqueues on the *parent's* (`:5277`), a yield resume on the fiber's *own* (`:986`). "Which fiber runs next" is host `setImmediate` ordering across dispatchers.
5. `Effect4/Concurrency/Scheduler.lean` carries `Machine τ = List (FiberState τ) × Trace τ` (`:64-66`) — seven scalar fields per fiber (`Effect4/Concurrency/Fiber.lean:58-65`), no program, no stack, no cause.
6. Nineteen census rows are witnessed by the three concurrency modules; eighteen of them are `partial`, and `docs/SUPERVISION-DAG.md:166-183` names every missing clause. Every missing clause is some form of "actual body evaluation" — exactly the program the carrier does not have.
7. `Effect4/Concurrency/Race.lean` (681 lines, 47 theorems) witnesses **zero** census rows and is absent from `generated/fiber-assurance.tsv`'s pinned inputs; it is the cheapest thing in the tree to retire.
8. Three partial rows — `interrupt.unsafe-entry`, `scheduler.run-tasks-drain-once`, `rule.record-and-apply-separate` — carry no "Remaining source clause" comment, which `docs/RUNTIME-COVERAGE.md:44` requires of every `partial` row.
9. Under DB-02 the park thunk is not a closure problem: its entire body is `resumed = true` (`internal/effect.ts:990-992, 1128-1130`), so a token names it exactly.
10. Observers reduce to a three-constructor named alphabet (await-resume, untrack-child, drop-scope-finalizer) covering every `addObserver` call site in the file.
11. Dispatcher tasks reduce to two constructors, `start child` and `resume target token`, covering `:986` and `:5277`.
12. I declared the whole proposal — `RunFiber`, `RunMachine`, `RunDecision`, `RunPrim`, `Parked`, `Observer`, `Task`, `Dispatcher`, `Pending`, `RunEvent` — and it **elaborates against the built library at exit 0**, with `DecidableEq` and a ground `by decide` receipt, staying in `Type (max u v)`.
13. All five `FrameFiber` fields carry over unchanged as the first five of `RunFiber`, and `Prim`, `PrimInterp`, `ContAnswer`, `FramePop`, `ensure`, `answerOf`, `armA`, `armE`, `popFrom`, `getCont`, `resumeValue`, `resumeCause` are reused verbatim; only `step` and `run` need new equations.
14. `Race.lean` should be retired, `Scheduler.lean` kept beside (as the `FiberState` projection target), `Supervision.lean` kept beside until its 15 rows are re-witnessed — retiring either would touch ~2 100 frozen names and 22 pinned digests.
15. Modelling the dispatcher does **not** raise the coverage number by itself: 10 of the rows it would reach are `targetOnly` and outside the denominator (`Effect4Test/Audit/RuntimeCoverage.lean:2559-2560`), so promoting them raises the denominator first.

---

## 1. The rc.112 fiber, read precisely

### 1.1 State table for one fiber

Every mutable field of `FiberImpl`, `internal/effect.ts:505-555`. All rows
**[read]** — I enumerated the write and read sites with a per-field scan of the
whole file.

| Field | Declared | Written at | Read at | Modelled in `Runtime.lean`? |
| --- | --- | --- | --- | --- |
| `id` | `:528` | ctor `:512` (`++fiberIdStore.id`, `:499`) | `:859` (`fiberInterrupt` uses *self* id), `:895`, `:913`, `:4299`, `:5374`, `:5454`, `:5370` | no |
| `interruptible` | `:529` | ctor `:514`; `:1151` (AsyncFinalizer `contAll`); `:4016`; `:4307` (`uninterruptible`); `:4315` (`SetInterruptible` `contAll`); `:4325` (`setFiberInterruptible`) | `:588` (the interrupt gate), `:1150`, `:4306`, `:4316`, `:4335`, `:5272` (child mask derivation) | **yes**, `Runtime.lean:227` |
| `currentOpCount` | `:530` | `:636` (reset on every `runLoop` entry), `:643` (`++` once per iteration) | `Scheduler.ts:175` | no |
| `_stack` | `:531` | `:625` (`length = 0` at exit), `:689` (`pop`), pushes at `:1134, 1152, 1368, 1686, 2498, 3462, 3628, 4010, 4015, 4308, 4326, 4350` | `:689` | **yes**, `Runtime.lean:225` |
| `_observers` | `:532` | `:565` push, `:570` splice (the unsubscribe closure), `:624` clear | `:561-562` (fire immediately if already exited), `:621-623` (fire in index order) | no |
| `_exit` | `:533` | `:619` only | `:561, 567, 575, 597, 600, 771, 816, 5279, 5367, 5423, 5451` | no |
| `_children` | `:534` | `:626` (`undefined` at exit), `:704` (lazy `new Set`), `:5280` (add), `:5281` (delete, from the child's own observer) | `:760-763` (`interruptChildren`), `:5318-5322` (`awaitAllChildren` snapshot) | no |
| `_interruptedCause` | `:535` | `:585-587` — accumulate by `causeCombine`, never replace | `:592, 641, 739, 742, 4316-4317, 4327` | **yes**, `Runtime.lean:229` |
| `_yielded` | `:536` | `:604` clear, `:660`/`:663` clear, `:700` (`yieldWith`), `:1128` (Async park guard) | `:602-605` (a pending thunk is fired on the next `evaluate`), `:657-664` | no |
| `_running` | `:537` | `:633` (`true`), `:676` (restore `prevRunning`) | `:589` — the only reader: it chooses *defer* over *apply now* | no |
| `_deferredInterrupt` | `:538` | `:590` set, `:639-640` clear at loop top, `:659` clear, `:685` clear in `getCont` | `:639, 662, 684` | **yes**, `Runtime.lean:231` |
| `context` | `:541` | `setContext` `:709-711`; `Context.empty()` at exit `:627` | `:558` (`getRef`), `:5273` (child inherits it) | no |
| `currentScheduler` | `:542` | `setContext` `:716-717` | `:554` (`makeDispatcher`), `:647` (`shouldYield`), `:1113` (`register` is `bind`-ed to it) | no |
| `maxOpsBeforeYield` | `:549` | `setContext` `:726` only | `Scheduler.ts:175` only | no |
| `currentPreventYield` | `:550` | `setContext` `:727` only | `:646` only | no |
| `_dispatcher` | `:552` | `:554` (lazy `??=`), `:718` (invalidated when the scheduler reference changes) | `:986, 5277, 5542, 5583` | no |
| `currentStackFrame` | `:547` | `setContext` `:725` | `:579-580` (annotates the interrupt cause), `:753` | no |

`current` (the primitive being threaded) is *not* a field: it is the local
`current` of `runLoop` (`:635`). `Runtime.lean:223` promotes it to a field,
which is the right move for a machine that must be resumable. **[read]**

Two facts the table makes visible and the census does not:

- `_running` is read for a decision in exactly one place, `:589` (`:632` reads it
  only to save it for the `finally` at `:676`). The whole of "record now, apply
  at the next checkpoint" (`rule.record-and-apply-separate`) is that one branch.
- `maxOpsBeforeYield` and `currentPreventYield` are pure `Context` caches
  refreshed only in `setContext`; nothing else writes them. A model that has no
  `Context` can carry them as two plain fields with no loss. **[inferred]**

### 1.2 The run loop, numbered

`evaluate` is `internal/effect.ts:599-628`; `runLoop` is `:629-679`. All
**[read]**.

1. `evaluate`: return at once if `_exit` is set (`:600-601`).
2. Otherwise, if `_yielded !== undefined`, cast it to a thunk, clear the field,
   and call it (`:602-606`). This is the resume-guard fire: the queued task from
   `yieldNowWith`/`Async` runs `evaluate`, which first disarms the guard.
3. `runLoop`: save the previous global current-fiber and `prevRunning`, set
   `_running = true`, `yielding = false`, `currentOpCount = 0` (`:630-636`).
4. **Top of loop.** If `_deferredInterrupt`, clear it and replace `current` with
   `failCause(this._interruptedCause!)` (`:639-642`). Census
   `checkpoint.runloop-top`.
5. `currentOpCount++` (`:643`).
6. **Yield injection.** If `!yielding && !currentPreventYield &&
   currentScheduler.shouldYield(this)`, set `yielding = true` and replace
   `current` with `flatMap(yieldNow, () => prev)` (`:644-652`). The `yielding`
   latch means at most one injection per `runLoop` entry. Census
   `rule.budget-per-runloop-entry`.
7. **Evaluate one op.** `currentTracerContext(current, this)` when a tracer is
   installed, else `current[evaluate](this)` (`:653-655`). The tracer hook is
   exactly where `harness/trace/tracer.ts:405-419` counts primitives.
8. **The `Yield` sentinel is overloaded** (`:656-668`), census
   `rule.yield-is-overloaded`:
   - `_yielded` is an `Exit` → clear `_deferredInterrupt`, clear `_yielded`,
     **return the exit** (`:657-661`). The fiber finished.
   - `_yielded` is a thunk *and* `_deferredInterrupt` is set → clear `_yielded`,
     **fire the thunk as a cancel guard**, `continue` (`:662-666`). The fiber
     does **not** park. Census `checkpoint.post-yield-cancel`.
   - otherwise → **return `Yield`** (`:667`). The fiber is parked.
9. `catch`: if `current` has no `evaluate`, return `exitDie(...)`; otherwise
   re-enter `runLoop(exitDie(error))` (`:670-674`).
10. `finally`: restore `_running = prevRunning` and the global current fiber
    (`:675-678`). Note `prevRunning`, not `false` — reentrancy is explicit.
11. Back in `evaluate`: if the result is `Yield`, **return with nothing done**
    (`:608-610`). No exit, no observers, no child interruption.
12. **Children.** `fiberMiddleware.interruptChildren && fiberMiddleware
    .interruptChildren(this)` (`:613-614`); if it returns an effect, re-enter
    `evaluate(flatMap(interruptChildren, () => exit))` (`:615-617`). The exit is
    already computed and is restored afterwards. Census
    `rule.children-interrupted-after-exit`. The middleware is a **global**
    one-way latch: `interruptChildrenPatch()` does `??=` (`:6656-6658`) and is
    called only from `forkChild` (`:5253`).
13. **Exit.** `_exit = exit`; metrics; fire every observer by index (`:621-623`);
    `_observers.length = 0`; `_stack.length = 0`; `_children = undefined`;
    `context = Context.empty()` (`:619-627`).

`interruptUnsafe` (`:574-595`) is the single interruption entry: no-op if
`_exit` (`:575-577`); build `causeInterrupt(fiberId)` and annotate with the
current stack frame and the caller's annotations (`:578-584`); **always**
accumulate into `_interruptedCause` by `causeCombine` (`:585-587`); and only if
`interruptible`, either set `_deferredInterrupt` (when `_running`) or re-enter
`evaluate(failCause(...))` (`:588-594`). **[read]**

### 1.3 The decisions a tape must supply

**(a) Which fiber runs next.** There is no global queue. Each fiber lazily
constructs its own dispatcher (`:552-555`), and `MixedScheduler.makeDispatcher`
returns a fresh `MixedSchedulerDispatcher` (`Scheduler.ts:188-190`). A deferred
fork enqueues onto the **parent's** dispatcher at priority 0 (`:5277`); a
`yieldNowWith` resume enqueues onto the **fiber's own** dispatcher at the given
priority (`:986-989`). Within one dispatcher the order is fixed: buckets in
ascending priority, FIFO inside a bucket (`Scheduler.ts:105-131`), drained once
per `runTasks` so anything enqueued during the drain waits for the next host
task (`Scheduler.ts:225-233`), and only the *first* task of an idle dispatcher
arms the host callback (`Scheduler.ts:207-212`). **Across** dispatchers the
order is whatever `setImmediate` / `setTimeout(f, 0)` / a resolved-promise
microtask gives (`Scheduler.ts:83-103`). That cross-dispatcher order is decision
(a), and it is *not* expressible as a single priority queue. **[read]** for
every line; the "not a single queue" conclusion is **[inferred]**.

**(b) When `shouldYield` says yes.** `Scheduler` is a `Context.Reference`
(`Scheduler.ts:78-81`), so `shouldYield` is replaceable. The default is
`fiber.currentOpCount >= fiber.maxOpsBeforeYield` (`Scheduler.ts:174-176`) with
`MaxOpsBeforeYield` defaulting to 2048 (`Scheduler.ts:269-272`) and
`PreventSchedulerYield` to `false` (`Scheduler.ts:295-298`). The harness already
exploits the replaceability: `TapeScheduler` overrides `shouldYield` and returns
`true` whenever the tape has armed a handover (`harness/trace/tracer.ts:389-399`,
installed at `:426`). **[read]**

**(c) When an async resumes.** `callbackOptions` (`:1109-1143`) calls
`register(resume, signal)` (`:1117`). If `resume` is called synchronously the
effect is stashed in `yielded` and returned directly — the fiber never parks
(`:1120-1126`). Otherwise `yielded = true`, the park guard is installed at
`:1128-1130`, an `AsyncFinalizer` frame is pushed when there is a controller or a
cancel effect (`:1134-1140`), and `Yield` is returned (`:1141`). A later
`resume(effect)` re-enters `fiber.evaluate(effect)` (`:1121`). The *time* of that
call is the decision. **[read]**

**(d) Interruptor identity.** `interruptUnsafe(fiberId?, annotations?)` (`:574`)
feeds `causeInterrupt(fiberId)` (`:578`). Different call sites supply different
ids: `fiberInterrupt` supplies the *calling* fiber's id (`:859`),
`fiberInterruptAll` the parent's (`:895`), `fiberInterruptAllAs` an explicit one
(`:913`), `forkIn`'s closed-scope path the parent's (`:5374`), `fiberRunIn`'s the
target's *own* id (`:5454`), `runFork`'s abort listener supplies **none**
(`:5427-5429`), and `runCallback`'s returned canceller takes an arbitrary
interruptor from the caller (`:5484-5486`). **[read]**

**(e) A fifth, easy to miss.** Whether `fiberMiddleware.interruptChildren` is
installed at all. It is a global `??=` latch (`:6656-6658`) set by the first
`forkChild` anywhere in the process (`:5253`). Two otherwise identical programs
differ in whether the parent interrupts its children, depending on whether some
unrelated earlier code called `forkChild`. **[read]**

### 1.4 Scope, where fibers link to it

`Scope.ts` mentions no fiber at all — I scanned the file for `fiber`/`Fiber` and
found nothing (`vendor/effect-4.0.0-rc.112/src/Scope.ts`, whole file). The link
is made from the fiber side, in `internal/effect.ts`: `forkIn` (`:5364-5378`)
forks a **daemon**, then, if the scope is `Open`, registers a keyed finalizer
`() => withFiberId((interruptor) => interruptor === fiber.id ? void_ :
fiberInterrupt(fiber))` and an observer that removes that key (`:5369-5372`); if
the scope is already `Closed` it interrupts the child immediately with the
parent's id (`:5374`). `fiberRunIn` is the same shape for an existing fiber
(`:5447-5461`), interrupting with the fiber's *own* id on a closed scope
(`:5454`). `forkScoped` is `forkIn` on the ambient `Scope` service (`:5400-5406`).
The scope state alphabet is `Empty | Open | Closed` (`Scope.ts:122-186`). **[read]**

---

## 2. What is already modelled, and what it deliberately omits

### 2.1 Carriers

**`Effect4/Runtime/Runtime.lean`** (2549 lines). `Arm` (`:47-54`), `Prim` with
fourteen constructors (`:93-123`), `IterStep` (`:179-186`), `PrimInterp` — twelve
pure total fields, explicitly *not* canonical content (`:191-215`), `FrameFiber`
with exactly five fields (`:221-232`), `ContAnswer` (`:235-244`), `FrameEvent`
with seven constructors (`:248-263`), `FramePop` (`:266-275`), `FrameStep`
(`:280-285`). Transitions: `Prim.ensure` (`:558`), `Prim.answerOf` (`:589`),
`FrameFiber.popFrom` (`:1154-1175`), `FrameFiber.getCont` (`:1181-1189`),
`resumeValue` (`:1595-1624`), `resumeCause` (`:1629-1658`), `step` (`:1663-1717`),
`run` (`:1724-1733`). **[read]**

The omission is stated twice, in the module docstring and on the structure:

> `Yield`, `Async` and `AsyncFinalizer` are deliberately absent; they belong to
> the later run-loop and parking packet. (`Runtime.lean:90-92`)

> The five `FiberImpl` fields this packet models. `_running`, `_yielded`,
> observers, children, the op budget, the dispatcher and the `Context` cache are
> absent by construction; the run-loop, supervision and context packets own
> them. (`Runtime.lean:217-220`)

**`Effect4/Concurrency/Interrupt.lean`** (50 lines): `InterruptMask`
(`:16-19`), `CleanupState` (`:22-26`), `InterruptBoundary τ` — one field, the
distinguished interrupted observation (`:29-30`). **[read]**

**`Effect4/Concurrency/Fiber.lean`** (67 lines): `FiberId` = one `Nat`
(`:15-17`), `FiberStatus` = `runnable | running | waiting target | finalizing |
done` (`:20-26`), `FiberState τ` = seven scalar fields, `id status terminal mask
interruptPending cleanup cleanupCount` (`:58-65`). **[read]**

**`Effect4/Concurrency/Scheduler.lean`** (2761 lines; 88 theorems, 37 defs, 2
structures, 5 inductives): `SchedulerRefusal` (`:16-19`), `SchedulerDecision τ`
with seven constructors (`:22-29`), `DecisionTape τ` (`:32`), `Event τ` with ten
constructors (`:35-45`), `Trace τ` (`:61`), and the carrier

```lean
structure Machine (τ : Type u) where
  fibers : List (FiberState τ)
  trace  : Trace τ                       -- Scheduler.lean:64-66
```

`Machine.transition` replaces one identity-matched fiber and appends events
(`:130-134`); `Machine.WellFormed` is an eight-clause invariant (`:181-200+`);
`stepEval` interprets one decision (`:479-610`); `Step` is its graph (`:613-615`);
`replayEval`/`Runs` fold a finite tape with `frontier` on exhaustion
(`:622-634`). **[read]**

**`Effect4/Concurrency/Supervision.lean`** (1681 lines; 136 theorems, 53 defs, 9
structures, 10 inductives, namespace `Effect4.Supervision`): `MaskMode`,
`ForkOptions`, `Globals`, `ObserverMode`, `Subscription`, `Fiber χ β ε δ ι α`
(a `FiberState (Exit …)` plus context, children, subscriptions, an interrupted
cause — `:32-36`), `Observation`, `StartObservation`, `ForkEvent`, `ForkResult`,
`InterruptAction`, `Refusal` (15 constructors), `WaitState`, `ReplayResult`,
`ScopeMode`, `ScopeFinalizer`, `ScopeBinding`, `RaceAllState` (11 fields),
`RaceAllDecision`. Transitions: `forkUnsafe` (`:244`), `forkChild` (`:274`),
`forkDetach` (`:280`), `WaitState.observe`/`waitReplay` (`:298`, `:311`),
`bindScope` (`:355`), the `raceStep`/`raceReplay` family. **[read]**

**`Effect4/Concurrency/Race.lean`** (681 lines; 47 theorems, 20 defs, 4
structures, 4 inductives): `RaceSpec` (`:16-20`), `RaceState τ` (`:99`),
`RaceDecision`/`RaceTape` (`:257-261`), `RaceRefusal` (`:326`), `raceStepEval`
(`:474`), `RaceStep` (`:518`), `raceReplayEval` (`:524`), `RaceRuns` (`:539`). It
imports `Scheduler` (`:1`) and delegates every lifecycle transition to it,
adding only the explicit winner choice (`:5-8`). **[read]**

### 2.2 The census join, row by row

`Effect4Test/Audit/RuntimeCoverage.lean` imports `Scheduler`, `Supervision`,
`Cause`, `Exit`, `Runtime/Scope`, `Runtime/Runtime` (`:1-8`) and holds
`censusRows : List Row` (`:2573-3402`) with `Row` at `:2545-2555`. **[read]**

Witness-name to module: `Effect4.Supervision.*` → `Supervision.lean`;
`Effect4.FrameFiber.*` / `Effect4.Prim.*` / `Effect4.Arm.*` / `Effect4.FrameEvent.*`
→ `Runtime.lean`; the bare `Effect4.<lower_case>` names → `Scheduler.lean`
(verified: `masked_interrupt_defers` `Scheduler.lean:2068`,
`unmask_delivers_pending` `:2091`, `unmasked_interrupt_delivers` `:2044`,
`unmasked_request_exists` `:1798`, `masked_request_exists` `:1775`,
`pending_unmask_exists` `:1842`, `unmask_without_pending_exists` `:1866`,
`enter_mask_exists` `:1824`, `join_agreement` `:1999`, `double_join_agreement`
`:2021`, `step_deterministic` `:1499`, `fixedTape_deterministic` `:1696`);
`Effect4.Scope.*` → `Runtime/Scope.lean`; `Effect4.Cause.*` → `Semantics/Cause.lean`.
**[read]**

| Census row | Coverage | Witness modules (count) | Census summary line (`generated/effect-runtime-census.tsv`) | Clause with no theorem |
| --- | --- | --- | --- | --- |
| `op.Failure` | partial | Runtime (4) | "Failure annotates the cause with the current stack frame, pops contE frames skipping every one while the fiber is interrupted and interruptible, and yields the Exit when none answers." | "annotates the cause with the current stack frame" — `RuntimeCoverage.lean:2582` records it needs a fiber `Context` and a `StackTrace` service key. `FrameFiber` has no `Context` field (`Runtime.lean:221-232`). |
| `op.Yield` | absent | — (0) | "Yield schedules a resume task on the fiber dispatcher at the requested priority and parks with a resume guard." | all of it. No dispatcher, no park state. |
| `op.Async` | absent | — (0) | "Async calls register(resume, signal?); a synchronous resume short-circuits, otherwise the fiber parks and pushes an AsyncFinalizer when there is a cancel effect or a controller." | all of it. |
| `op.AsyncFinalizer` | absent, `excludedInternal` | — (0) | "AsyncFinalizer masks in contAll and, in contE, runs the cancel effect only when the cause carries an interrupt, then re-fails." | all of it; outside the denominator. |
| `checkpoint.runloop-top` | absent | — (0) | "At the top of each runLoop iteration a deferred interrupt is cleared and the current primitive is replaced by failCause of the accumulated cause." | all of it. `Runtime.lean` has `step`, not a loop with a top. |
| `checkpoint.post-yield-cancel` | absent | — (0) | "After a Yield carrying a park thunk, a deferred interrupt fires the thunk as a cancel guard and the loop continues instead of parking." | all of it. |
| `interrupt.unsafe-entry` | partial | Scheduler (3) | "interruptUnsafe is the single interruption entry: it no-ops after the Exit exists, always records the cause, and applies it now only when the fiber is interruptible and not inside runLoop." | **"and not inside runLoop"** — `Machine` has no `_running`, so the defer-vs-apply branch at `internal/effect.ts:589` has no counterpart. Also "no-ops after the Exit exists". No "Remaining source clause" comment is recorded for this row, contrary to `docs/RUNTIME-COVERAGE.md:44`. |
| `interrupt.accumulate` | partial | Supervision (4) | "Successive interruptors accumulate into one cause by causeCombine rather than replacing it." | "Actual FiberId/annotation interpretation and integration of the recording facet with delivery" (`RuntimeCoverage.lean:2760-2761`, `docs/SUPERVISION-DAG.md:181`). |
| `fork.unsafe` | partial | Supervision (31) | "…constructs a FiberImpl over the parent context, starts it immediately or as a priority-0 dispatcher task, and registers it only when not a daemon." | "Actual body evaluation, shared-world observation, scheduler dispatch, inherited host context/flags" (`SUPERVISION-DAG.md:168`). |
| `fork.child` | partial | Supervision (11) | "forkChild installs the interruptChildren middleware and forks a non-daemon child, so the parent exit interrupts it." | "Installing the real global middleware; child completion invoking its parent observer" (`:169`). |
| `fork.detach` | partial | Supervision (2) | "forkDetach forks a daemon: no registration, no middleware, and nothing interrupts it on the parent exit." | "Actual daemon execution and independent lifetime" (`:170`). |
| `fork.in` | partial | Supervision (10) | "forkIn forks a daemon and links it to a scope by a shared key…" | "Supplied post-start scope denotes the same mutable host scope; finalizer execution" (`:175`). |
| `fork.scoped` | partial | Supervision (1) | "forkScoped is forkIn applied to the ambient Scope service." | "Ambient Scope service resolution and composition with fork startup" (`:176`). |
| `fork.race-all` | partial | Supervision (56) | "raceAll starts entrants in order as immediate daemons until observed success stops the start loop…" | "Actual first accepted callback resumption, request delivery, dynamic shared-set interpretation, uninterruptible continuation execution" (`:180`). |
| `fork.await-all-children` | partial | Supervision (3) | "awaitAllChildren snapshots the children before running and, on exit, awaits only those added during the run." | "Before/after snapshots obtained from the same parent during actual body evaluation" (`:179`). |
| `fork.fiber-run-in` | partial | Supervision (10) | "fiberRunIn binds an existing fiber to a scope with a keyed finalizer…" | "Existing-fiber scope attachment, closed-scope request execution and child observer delivery" (`:178`). |
| `fork.join` | partial | Scheduler (2) + Supervision (16) | "join returns the stored Exit directly when the fiber is done and otherwise registers an observer; the Exit itself is the resumed effect." | "Exit resumed as an Effect through the continuation interpreter" (`:172`). |
| `fork.await` | partial | Supervision (13) | "await takes the same observer route as join but delivers the Exit as an ordinary value." | "Host callback registration, cancellation, and successful Exit-as-value resumption" (`:171`). |
| `fork.interrupt` | partial | Supervision (6) | "interrupt records the interruptor id and stack annotations through interruptUnsafe and then awaits the target." | "Request delivery, synchronous execution, and interruption followed by actual await" (`:173`). |
| `fork.interrupt-all` | partial | Supervision (19) | "interruptAll records an interrupt on every fiber first and only then awaits them all." | "Executing request calls in order before explicit await; observations may arrive during calls" (`:174`). |
| `scheduler.run-tasks-drain-once` | partial | Scheduler (2) | "runTasks drains the buckets once and runs that snapshot, so tasks enqueued during the run wait for the next host task." | **everything about buckets.** The two witnesses (`step_deterministic`, `fixedTape_deterministic`) are determinism-under-a-fixed-tape facts; they say nothing about draining, snapshots or enqueue-during-run. `Machine` has no task list. No "Remaining source clause" comment recorded. |
| `rule.only-fork-child-tracks` | partial | Supervision (10) | "Only a non-daemon fork joins the parent children set; forkIn, forkScoped, forkDetach and the races all fork daemons." | "Correspondence of all source fork call sites/options to the observed controller inputs" (`:182`). |
| `rule.children-interrupted-after-exit` | partial | Supervision (29) | "Children are interrupted after the Exit exists, between runLoop returning and observers firing, and only when the middleware was ever installed." | "Parent continuation after a successful child wait; intervening interruption can replace the local body Exit" (`:183`). Also **"between runLoop returning and observers firing"**: `Supervision` has subscriptions but no run loop, so there is no "between". |
| `rule.yield-is-overloaded` | absent | — (0) | "Yield means finished when _yielded is an Exit and parked when it is a thunk." | all of it. |
| `rule.record-and-apply-separate` | partial | Scheduler (2) | "Recording an interrupt and applying it are separate: the cause is always stored and becomes the outcome at the first checkpoint where the fiber is interruptible." | **"the first checkpoint"**. `stepEval .exitMask` (`Scheduler.lean:553-575`) delivers at exactly one syntactic point; rc.112 has three (`:592`, `:641`, `:684`). No "Remaining source clause" comment recorded. |
| `scheduler.should-yield`, `.priority-buckets`, `.dispatcher-arming`, `.flush`, `.yield-now-resume-guard`, `.max-ops-default`, `.prevent-yield-default`, `.host-loop`; `rule.start-is-asymmetric`, `rule.budget-per-runloop-entry` | absent, all `targetOnly` | — (0) | (see the TSV) | all of them; and they are **outside the denominator** (`RuntimeCoverage.lean:2559-2560`). |

Nineteen rows draw on the three concurrency modules. `Race.lean` supplies
**none** of them — I searched `RuntimeCoverage.lean` for `RaceSpec`, `RaceState`,
`raceStepEval`, `RaceDecision`, `raceReplayEval`, `settledResult`,
`contenderDone`, `needsWinner` and found zero hits. The 59 `raceStep`/`raceRuns`
witnesses under `fork.race-all` are `Effect4.Supervision.race*`, a different
race. **[read]**

### 2.3 Why the present carriers cannot state the missing clauses

One sentence, three carriers. **[inferred]**, from the structures quoted above.

- `FrameFiber` (`Runtime.lean:221-232`) has a program and no world: no fiber id,
  no other fiber, no queue, no exit slot, no observers. It can state what one
  primitive does to one stack and cannot state that a *second* fiber saw it.
- `Machine τ` (`Scheduler.lean:64-66`) has a world and no program: `FiberState τ`
  is seven scalars (`Fiber.lean:58-65`) with `terminal : Option τ` supplied by
  the caller. Every "actual body evaluation" clause in the table above is the
  same missing thing — the fiber has no `current` and no `stack`, so
  "the parent's exit" is an input, never a computed value.
- `Supervision.Fiber` (`Supervision.lean:32-36`) has a world plus a `context : χ`
  and a `children` list, and still no program: it is described in its own module
  docstring as a controller over supplied observations
  (`Supervision.lean:5-10`), and `docs/SUPERVISION-DAG.md:56-57` says the graph
  "does not close host execution, the concurrency category, or a full cutover."

The reification plan says the same thing in one line
(`docs/research/2026-09-03-reification-plan.md:204-206`):

> the Lean scheduler's `Machine` carries no program, so the Lean face of two
> fibers is a sequential projection, and scheduler insensitivity stays a host
> protocol until a two-fiber model exists (a new model, not an extension).

---

## 3. The first-order design problem

DB-02 (`docs/DESIGN-BASIS.md:103-127`) closes pure code at the canonical
boundary: "A host function, promise, thunk, custom predicate, or raw closure
must become a named and registered foreign boundary or receive a profile
refusal." `Runtime.lean:17-23` already applies it: a continuation is `ν`, a thunk
is `σ`, meaning comes from the `PrimInterp` parameter. Here is how each remaining
closure reduces.

### 3.1 The reductions

**The park thunk is not a closure problem.** Its entire body, in both places it
occurs, is one assignment:

```ts
    return fiber.yieldWith(() => { resumed = true })     // effect.ts:990-992
    fiber._yielded = () => { resumed = true }            // effect.ts:1128-1130
```

So `_yielded` reifies to a three-arm sum: not parked, parked with an `Exit`
(finished), parked with a *token* naming the pending operation whose `resumed`
flag the thunk sets. Nothing is lost. **[read]** of the two sites; the "nothing
is lost" is **[inferred]** and is the single most load-bearing inference in this
note — if some other site ever installs a `_yielded` thunk with a different body,
the reduction fails. I scanned every write to `_yielded` (`:604, 660, 663, 700,
1128`) and `yieldWith` is only ever called from `:934, 990` and the ops that
return an exit, so the claim holds for rc.112 as pinned.

**An async operation and its resumption.** `Async` becomes
`async (register : ν) (withSignal : Bool)`; the pending registration becomes a
first-order record `⟨token, register, withSignal, cancel : Option ν, resumed⟩` on
the fiber. The synchronous short-circuit (`:1120-1126`) and the later resume
(`:1121`) are the *same* tape decision `answerAsync target token answer`,
differing only in whether it is consumed before the fiber parks. `AsyncFinalizer`
becomes `asyncFinalizer (onInterrupt : ν)` — its `contAll` masks and pushes
(`:1149-1154`) and its `contE` runs `this[args]()` only when the cause carries an
interrupt (`:1155-1159`); both are expressible with the existing `Prim.ensure`
machinery, and `PrimInterp` already has the shape to give `onInterrupt` a
meaning.

**A yield and its resume task.** `yieldNowWith (priority : Nat)`; the scheduled
task is `Task.resume target token`, enqueued on the fiber's own dispatcher; the
park is `Parked.withGuard token`.

**Observers.** Every `addObserver` call site in the file: `fiberAwait` `:774`
(resume a waiter), `fiberJoin` `:818` (same), `forkUnsafe` `:5281` (delete self
from the parent's children), `forkIn` `:5372` and `fiberRunIn` `:5459` (remove a
scope finalizer key), `runForkWith` `:5431` (remove an abort listener — a host
concern), `runCallbackWith` `:5482` (the caller's `onExit`). Three constructors
cover the model-relevant ones: `resumeAwait (waiter : FiberId) (token : Nat)`,
`untrackChild (parent : FiberId)`, `dropScopeFinalizer (scope key : Nat)`.

**Children.** `List FiberId` with a `Nodup` side condition. rc.112 uses a `Set`
(`:704`), whose JS iteration order is insertion order, and `fiberInterruptAll`
iterates it (`:891-898`), so order is observable and a list is the faithful
carrier, not a weakening. **[inferred]**

**The dispatcher's priority buckets.** `List Bucket` where
`Bucket = ⟨priority : Nat, tasks : List Task⟩`, ascending in `priority`, plus one
`armed : Bool` mirroring `MixedSchedulerDispatcher.running !== undefined`
(`Scheduler.ts:195, 209-211`). One dispatcher **per fiber**, not one per machine.

**`maxOpsBeforeYield`.** Two plain `Nat`/`Bool` fields, since nothing but
`setContext` writes them (§1.1). The default-2048 and default-false facts
(`Scheduler.ts:269-272, 295-298`) become two `rfl` lemmas about an initial value,
not a `Context` model.

### 3.2 The candidate structures

Field lists, no proofs. `ν σ ε δ ι α : Type u`, `β : Type v`, as in
`Runtime.lean:287`.

```lean
inductive Parked (β : Type v) (ε δ ι α : Type u)
  | notParked | withExit (exit : Exit β ε δ ι α) | withGuard (token : Nat)

inductive Observer
  | resumeAwait (waiter : FiberId) (token : Nat)
  | untrackChild (parent : FiberId)
  | dropScopeFinalizer (scope : Nat) (key : Nat)

inductive Task
  | start (child : FiberId) | resume (target : FiberId) (token : Nat)

structure Bucket where priority : Nat; tasks : List Task
structure Dispatcher where buckets : List Bucket; armed : Bool

structure Pending (ν σ β ε δ ι α) where
  token : Nat; register : ν; withSignal : Bool; cancel : Option ν; resumed : Bool

structure RunFiber (ν σ β ε δ ι α) where
  id : FiberId
  current : Prim ν σ β ε δ ι α           -- carried over from FrameFiber
  stack : List (Prim ν σ β ε δ ι α)      -- carried over
  interruptible : Bool                    -- carried over
  interruptedCause : Option (Cause ε δ ι α)  -- carried over
  deferredInterrupt : Bool                -- carried over
  running : Bool
  parked : Parked β ε δ ι α
  pending : List (Pending ν σ β ε δ ι α)
  currentOpCount : Nat
  maxOpsBeforeYield : Nat
  preventYield : Bool
  observers : List Observer
  children : List FiberId
  exit : Option (Exit β ε δ ι α)
  dispatcher : Dispatcher

inductive RunEvent (ν σ β ε δ ι α)
  | forked (parent child : FiberId) (daemon : Bool)
  | started (fiber : FiberId)
  | scheduledTask (owner : FiberId) (priority : Nat) (task : Task)
  | ranTask (owner : FiberId) (task : Task)
  | yieldInjected (fiber : FiberId) (atOp : Nat)
  | parkedOn (fiber : FiberId) (token : Nat)
  | resumedWith (fiber : FiberId) (token : Nat) (answer : Prim ν σ β ε δ ι α)
  | interruptRecorded (interruptor : Option FiberId) (target : FiberId)
  | interruptDeferred (target : FiberId)
  | childrenInterrupted (parent : FiberId) (children : List FiberId)
  | observerFired (fiber : FiberId) (observer : Observer)
  | exited (fiber : FiberId) (exit : Exit β ε δ ι α)

structure RunMachine (ν σ β ε δ ι α) where
  fibers : List (RunFiber ν σ β ε δ ι α)
  nextId : Nat
  nextToken : Nat
  middlewareInstalled : Bool
  trace : List (RunEvent ν σ β ε δ ι α)

inductive RunDecision (ν σ β ε δ ι α)
  | fireDispatcher (owner : FiberId)
  | flush (owner : FiberId)
  | yieldVerdict (target : FiberId) (verdict : Bool)
  | answerAsync (target : FiberId) (token : Nat) (answer : Prim ν σ β ε δ ι α)
  | interruptFrom (interruptor : Option FiberId) (target : FiberId)

inductive RunPrim (ν σ β ε δ ι α)
  | lifted (prim : Prim ν σ β ε δ ι α)
  | yieldNowWith (priority : Nat)
  | async (register : ν) (withSignal : Bool)
  | asyncFinalizer (onInterrupt : ν)
```

`RunDecision` covers §1.3 (a)–(e): `fireDispatcher`/`flush` are (a),
`yieldVerdict` is (b), `answerAsync` is (c), `interruptFrom` is (d) and carries
the interruptor id the wire drops, and `RunMachine.middlewareInstalled` is (e).

### 3.3 What carries over from `FrameFiber` unchanged

The five `FrameFiber` fields — `current`, `stack`, `interruptible`,
`interruptedCause`, `deferredInterrupt` (`Runtime.lean:221-232`) — carry over
verbatim as the first five fields of `RunFiber`. So do the whole `Prim` syntax
(`:93-123`), `PrimInterp` (`:191-215`), `ContAnswer` (`:235-244`), `FramePop`
(`:266-275`), `Prim.ensure`/`answerOf`/`armA`/`armE` (`:558, 589, 718, 750`),
`popFrom` (`:1154`), `getCont` (`:1181`), `resumeValue`/`resumeCause`
(`:1595, 1629`). What is *not* reusable unchanged is `step` (`:1663`), because
three new `RunPrim` arms need equations, and `run` (`:1724`), because the loop
top and the yield injection are new. `FrameEvent` (`:248-263`) stays as the
stack-level alphabet with `RunEvent` above it — `docs/FRAMES-DAG.md` separation 7
already records why the two alphabets are distinct (`Runtime.lean:246-247`).

**One inherited obligation.** `docs/FRAMES-DAG.md:200-211` records that
`popFrom` fuses rc.112's two loops, that no frame in the frames packet is the
divergence-prone shape, and that:

> The first frame that is that shape is `AsyncFinalizer`… The later run-loop and
> parking packet that adds it **must** revisit `popFrom` and either prove the
> fusion still agrees or unfuse the loops.

That obligation lands squarely on this packet.

### 3.4 Elaboration probe — result

**[read]** — I wrote every structure above into a scratch file and elaborated it
against the built library:

```
lake env lean DeepFiberProbe.lean   →   exit 0, no output
```

(a session scratch file, not committed; to reproduce, paste the block in §3.2
into any file outside the package tree and run the command above.)

The file imports `Effect4.Runtime.Runtime` and `Effect4.Concurrency.Fiber`,
declares all ten types with `deriving DecidableEq` (plus `Repr` on the
parameter-free ones), and contains three receipts, all of which elaborate:

- a universe receipt `example : Type (max u v) := RunMachine …` — **no universe
  bump beyond `Runtime.lean`'s own `Type (max u v)`**;
- `example : DecidableEq (RunMachine Nat Nat Nat Nat Nat Nat Nat) := inferInstance`
  — `DecidableEq` derives through `Prim`, `Cause`, `Exit`, `FiberId`, `Option`
  and `List` without a hand-written instance;
- a ground `by decide` on a fully applied `RunFiber.mk`, so kernel-reducible
  ground receipts survive.

No `sorry`, no warning, no error. This is a **finite elaboration probe of the
declarations only**: it establishes that the shapes are well-formed and decidably
equal, and establishes nothing about any transition function or theorem.

---

## 4. Subsume or retire

### 4.1 What could become a projection lemma

Write `P : RunMachine ν σ β ε δ ι α → Machine (Exit β ε δ ι α)` for the erasure
that drops `current`, `stack`, `pending`, `dispatcher`, the counters and the
trace, and maps each `RunFiber` to a `FiberState` by
`status := runnable/running/waiting/finalizing/done` from `running`, `parked` and
`exit`; `terminal := exit`; `mask := if interruptible then unmasked else masked`;
`interruptPending := deferredInterrupt || interruptedCause.isSome`. All rows
**[inferred]** from the two structures; none is proved.

| Old statement | Becomes |
| --- | --- |
| `Effect4.masked_interrupt_defers` (`Scheduler.lean:2068`) | ⇐ "`interruptFrom i t` on a `RunFiber` with `interruptible = false` sets `interruptedCause` and leaves `exit` unchanged", via `P` |
| `Effect4.unmask_delivers_pending` (`:2091`) | ⇐ "the `SetInterruptible true` `contAll` substitutes `failCause` when a cause is pending" — already true in `Runtime.lean` (`Prim.ensure_setInterruptible_substitutes`, `:657`), via `P` |
| `Effect4.unmasked_interrupt_delivers` (`:2044`) | ⇐ "`interruptFrom` on an interruptible, non-`running` fiber re-enters `evaluate(failCause …)`", via `P` |
| `Effect4.join_agreement`, `double_join_agreement` (`:1999, 2021`) | ⇐ "an observer added after `exit` fires immediately with the stored exit, and firing twice yields the same exit" (`internal/effect.ts:561-562`), via `P` |
| `Effect4.cleanup_at_most_once`, `cleanup_events_at_most_once`, `cleanup_count_monotone` (`:2148, 2160, 2249`) | ⇐ "`observers.length = 0` after firing" (`:624`) — the cleanup counter is exactly "did the observer list get drained", via `P` |
| `Effect4.step_deterministic`, `fixedTape_deterministic` (`:1499, 1696`) | ⇐ the same statements about `RunDecision`, unchanged in shape; `P` is not even needed |
| `Effect4.Supervision.forkUnsafe_*` family (~31 theorems) | ⇐ equations of a real `forkUnsafe : RunMachine → …` that constructs a child over the parent's fields and enqueues on the parent's dispatcher, via a second projection to `Supervision.Fiber` |
| `Effect4.Supervision.WaitState.*` / `waitReplay_*` (~17) | ⇐ "the parent's `awaitAllChildren` frame is discharged when the last tracked child's `untrackChild` observer has fired" |
| `Effect4.Supervision.Globals.*` (~8) | ⇐ `RunMachine.nextId` freshness plus `middlewareInstalled` monotonicity |
| `Effect4.Race.*` (all 47) | ⇐ nothing yet; see below |

### 4.2 What cannot

- **`Machine.WellFormed`'s cleanup clauses** (`Scheduler.lean:181-200+`). They
  are a *bookkeeping* invariant over a `cleanupCount : Nat` that rc.112 does not
  have. A program-carrying machine has observers and an exit, not a cleanup
  counter; the invariant is re-derivable but is not literally a projection.
- **`Supervision.Refusal`'s 15 constructors** (`Supervision.lean:61-77`). They
  classify *invalid controller inputs* — `wrongStartMode`, `duplicateEntrant`,
  `wrongRacePhase`. A machine that actually runs the program cannot be handed a
  wrong start mode; the refusals evaporate rather than project. Their loss is a
  loss of a *frozen surface*, not of a fact.
- **`Race.lean`'s explicit winner choice** (`Race.lean:5-8`, `RaceDecision`
  `:257-261`). This is a genuinely different decision kind from
  `Supervision.RaceAllDecision` (`Supervision.lean:108-113`): binary
  first-completion with tie resolution versus rc.112's n-ary `raceAll`. Neither
  projects onto the other, and neither witnesses a census row.
- **The `targetOnly` rows** (`scheduler.*`, `rule.start-is-asymmetric`,
  `rule.budget-per-runloop-entry`). A model can state them, but they are outside
  the denominator by disposition (`RuntimeCoverage.lean:2559-2560`), so making
  them statable is a `PORT-MANIFEST.md` decision, not a modelling one.

### 4.3 Consumers, by path

All **[read]** — from `import` scans and declaration-name greps over `Effect4/`,
`Effect4Test/`, `docs/`, `test/`, `harness/`, `scripts/`, `generated/`.

**`Effect4/Concurrency/Scheduler.lean`** — imported by
`Effect4/Concurrency/Race.lean:1`, `Effect4/Target/TypeScript/Simulation.lean`,
`Effect4.lean`, `Effect4Test/Audit/RuntimeCoverage.lean:3`,
`Effect4Test/Concurrency/FiberAssurance.lean:3`,
`Effect4Test/Concurrency/FiberAxiomReport.lean`,
`Effect4Test/Concurrency/FiberRepresentativeContract.lean`,
`Effect4Test/Concurrency/FiberSupervisionContract.lean`,
`Effect4Test/Concurrency/RaceRepresentativeContract.lean`,
`Effect4Test/Counterexamples/Concurrency/FiberSupervision.lean`,
`Effect4Test/Counterexamples/Concurrency/RaceRepresentative.lean:1` (11 files).
Frozen surfaces: `Effect4Test/Concurrency/FiberAssurance.lean:228-1187`
(`expectedSchedulerOwned`, ≈981 name tokens); `generated/fiber-assurance.tsv`
pins it by sha256 (`:6`) and 532 of its 2 308 rows mention `Scheduler`. Docs:
`docs/FIBER-DAG.md`. Contract: `test/contracts/fiber-representative.contract.md`.
Census: 5 rows. Notable: `Effect4/Target/TypeScript/Simulation.lean:56-58` uses
the `Event` alphabet for exactly one thing — `.completed _ r → .done (result r)`,
everything else `none`.

**`Effect4/Concurrency/Supervision.lean`** — imported by `Effect4.lean`,
`Effect4Test/Audit/RuntimeCoverage.lean:4`,
`Effect4Test/Concurrency/FiberAssurance.lean:4`,
`Effect4Test/Concurrency/FiberSupervisionAxiomReport.lean`,
`Effect4Test/Concurrency/FiberSupervisionContract.lean` (5 files). Frozen:
`FiberAssurance.lean:1188-2331` (`supervisionOwned`, ≈1 135 name tokens) and
`:2332-2402` (`supervisionShapes`, ≈101); `generated/fiber-assurance.tsv` pins it
(`input` list, entry 12) and 1 341 rows mention `Supervision`. Docs:
`docs/SUPERVISION-DAG.md`, `docs/SUPERVISION-IMPLEMENTATION.md`. Contract:
`test/contracts/fiber-supervision.contract.md`. Counterexamples:
`Effect4Test/Counterexamples/Concurrency/FiberSupervision.lean` (15 witnesses,
`docs/SUPERVISION-DAG.md:239-245`). Host: `harness/fiber-supervision/runtime-check.ts`
and `harness/fiber-supervision/host-pin.json`, both pinned inputs of
`generated/fiber-assurance.tsv`; gates `scripts/check-fiber-supervision-host.sh`
and `scripts/check-supervision-evidence.py`, also pinned. Census: 15 rows.

**`Effect4/Concurrency/Race.lean`** — imported by `Effect4.lean:62` and
`Effect4Test/Concurrency/RaceRepresentativeContract.lean:11` (2 files).
Declaration-name consumers outside itself: `docs/RACE-DAG.md`,
`docs/SUPERVISION-DAG.md` (one contrast line, `:86`), `PORT-MANIFEST.md`,
`test/contracts/race-representative.contract.md`,
`test/counterexamples/REGISTER.md`,
`test/counterexamples/concurrency/ATTACKS.md`. **Not** in
`Effect4Test/Concurrency/FiberAssurance.lean` (it is not imported there), **not**
among the 22 pinned inputs of `generated/fiber-assurance.tsv`, **not** cited by
`Effect4Test/Audit/RuntimeCoverage.lean`, **not** referenced by any file under
`harness/`. `Effect4Test/Counterexamples/Concurrency/RaceRepresentative.lean:1`
imports `Scheduler`, not `Race`, and states in its own docstring (`:5-8`) that
its four witnesses "constrain the binary `raceFirst` packet without depending on
its production implementation."

**Import DAG inside `Effect4/Concurrency/`**: `Interrupt` ← `Fiber` ←
`Scheduler` ← `Race`; `Fiber` ← `Supervision` (which also imports
`Effect4.Runtime.Scope`); `FiberFamily.lean:1` imports only
`Effect4.Meta.Derive` and depends on none of them.

### 4.4 Cost table

Estimates are mine, **[inferred]**, from the line counts and consumer lists
above. "Census rows kept" counts rows whose *current* witness set survives
unchanged; "newly reachable" counts in-denominator rows a program-carrying
machine could raise above `absent` or complete to `green`.

| Option | Census rows kept | Census rows newly reachable | Files touched | Frozen lists touched | Est. Lean lines |
| --- | --- | --- | --- | --- | --- |
| **Retire `Race.lean`** | 19 of 19 (it carries none) | 0 | 8: `Effect4/Concurrency/Race.lean` (delete), `Effect4.lean` (1 import), `Effect4Test/Concurrency/RaceRepresentativeContract.lean`, `docs/RACE-DAG.md`, `test/contracts/race-representative.contract.md`, `PORT-MANIFEST.md`, `test/counterexamples/REGISTER.md`, `test/counterexamples/concurrency/ATTACKS.md` | **0** — not in `FiberAssurance.lean`, not a pinned input of `generated/fiber-assurance.tsv`, not in `RuntimeCoverage.lean` | −681 |
| **Retire `Scheduler.lean` + `Supervision.lean`** | 0 without re-witnessing; 19 only if every one of ~130 witness entries and ~90 `#check` ascriptions is replaced | 5 (`op.Yield`, `op.Async`, `checkpoint.runloop-top`, `checkpoint.post-yield-cancel`, `rule.yield-is-overloaded`) + the 18 partial rows' missing clauses | ≈30: 16 importers/consumers listed in §4.3, plus `generated/fiber-assurance.tsv`, `scripts/generate-fiber-assurance.sh`, `scripts/check-fiber-assurance.sh`, `scripts/check-supervision-evidence.py`, `scripts/check-fiber-supervision-host.sh`, `docs/FIBER-DAG.md`, `docs/SUPERVISION-DAG.md`, `docs/SUPERVISION-IMPLEMENTATION.md`, `PORT-MANIFEST.md`, `PLAN.md` (P7 row) | **≈2 217 names** (`expectedSchedulerOwned` ≈981, `supervisionOwned` ≈1 135, `supervisionShapes` ≈101) + 22 pinned digests + 2 308 generated rows | −4 442 old, +~2 500 new |
| **Subsume with projections** (new machine beside; old theorems re-proved as corollaries via `P`) | 19 of 19 | same 5 + the 18 missing clauses | ≈12: 2 new `Effect4/Runtime/*.lean`, 2 new contracts, 2 new test modules, 1 new DAG, `Effect4.lean`, `Effect4Test.lean`, `RuntimeCoverage.lean` (row edits only), `REGISTER.md`, `test/counterexamples/runtime/ATTACKS.md` | **0** — every frozen name keeps its declaration; only the *proof* of each theorem changes | +~2 400 new, +~400 projection lemmas, 0 removed |
| **Keep beside** (new machine, no projections) | 19 of 19 | same 5 + the 18 missing clauses | ≈11 (as above, minus `RuntimeCoverage.lean` row edits if the new rows are a separate join packet) | 0 | +~2 400 |

Reading of the table: **retire `Race.lean`; keep the other two beside; add
projections only where the projection is cheaper than the re-proof.** The
retire-both row is dominated — it buys nothing the subsume row does not, and
costs the two largest frozen lists in the repository.

One caveat that belongs in the number, not in the prose: modelling the
dispatcher makes ten `targetOnly` rows *statable* but does not by itself move
the metric, because they are excluded from the denominator
(`RuntimeCoverage.lean:2559-2560`). Re-disposing them to `separateCalculus` would
raise the denominator from 117 to 127 before a single one turned green.

---

## 5. Host evidence for two fibers

All facts in this section were gathered by a delegated read of the harness and
goldens and are **[read]** unless marked.

### 5.1 What the host already observes

`harness/trace/fiber-tail.ts` (192 lines) runs **two** rc.112 fibers, "with the
tape choosing which of them holds the processor" (`:20-22`). Its shared fork body
(`:114-127`) forks the child with `startImmediately: false`, consults the tape,
and on `true` arms the scheduler and spends one primitive so the run loop drains
its queue. Forks are `Effect.forkChild` and `Effect.forkDetach` (`:129-133`);
`join`, `awaitValue`, `awaitError`, `interrupt` are `:134-145`. A fiber never
reaches the wire as an object: `registerHandle` brands it and it is encoded as
its index in first-seen order (`:41-54`). Output is one JSON blob
(`:172-191`) including `expectYields: true` with the comment "A two-fiber run
yields by construction: every `true` on the tape is one handover."

`harness/fiber-supervision/runtime-check.ts` (172 lines) is the untraced host
check. It has **ten** assertions, not nine — `:170` asserts
`cases === 10`; "nine" is the number that became goldens. In order:
race-immediate-success-stops-launch (`:21`), race-failure-allows-next-launch
(`:33`), race-all-failures-retain-order-and-duplicates (`:45`),
empty-race-pending-until-interrupted (`:51`),
parent-publishes-after-tracked-child-cleanup (`:71`),
daemon-survives-parent-exit (`:82`), await-value-distinct-from-join-effect
(`:90`), race-reentrant-empty-set-bypasses-late-insertion (`:132`),
race-reentrant-nonempty-set-includes-late-insertion (`:125`), and
parent-interrupt-during-child-wait-changes-result (`:168`). The tenth is refused
as a golden (`Effect4/Concurrency/FiberFamily.lean:329-338`) because "this family
has no former for a child that completes another child."

`harness/trace/tracer.ts`: `TapeScheduler extends MixedScheduler` overriding
`shouldYield` (`:389-399`) — "the tape first: an armed decision hands the
processor over whatever rc.112's op counter would have said"; installed at
`:426`. There is **no `withBudget`**: the budget is `RunOptions.budget` (`:342`)
enforced inside the `Tracer.context` hook (`:405-419`) behind a `budgetHit` latch
(`:387`, rationale `:383-386`, counterexample `E4-TARGET-CE-018`).
`maxOpsBeforeYield` is `RunOptions.maxOpsBeforeYield` (`:343`) provided as the
rc.112 service at `:422`. The in-memory event union is `:17-27`; the rendered TSV
row shapes are `:468-482`; `RunReport` is `:361-369` and still carries
`scheduled: number[]` as a stub — `:379`, "priorities are recorded once the
dispatcher is instrumented (P-T11)".

`generated/traces/fiber/` holds nine goldens (860–1 078 bytes, 20–30 lines
each): `awaitValueDistinctFromJoinEffect`, `daemonSurvivesParentExit`,
`emptyRacePendingUntilInterrupted`, `parentInterruptDuringChildWait`,
`parentPublishesAfterChildCleanup`, `raceAllFailuresRetainOrder`,
`raceFailureAllowsNextLaunch`, `raceImmediateSuccessStopsLaunch`,
`raceReentrantEmptySetBypasses`. Every file carries `face	lean` — **the goldens
are the Lean face's expectation and the host is compared to them.** The
trace-event tags actually appearing across the whole family are five: `op`,
`answer`, `failed`, `decide`, `done`. Operation names: `fork`, `forkDetach`,
`join`, `awaitValue`, `awaitError`, `interrupt`, `started`, `cleanups`. The
family is defined at `Effect4/Concurrency/FiberFamily.lean:95-111` (signature)
and `:473-500` (nine programs with their tapes); goldens are written by
`harness/trace/Generate.lean:1477-1490, 1567-1572`; regenerated by
`./scripts/generate-trace-goldens.sh`; checked by
`scripts/check-trace-host.sh:191`, the one family in that script with the
yield-every-op flag **off** (`E4-SEM-CE-011`).

### 5.2 What the alphabet can and cannot carry

Can: a fiber *handle index* (0-based, first-seen order — `answer fork 0`), a fork
decision (`decide <site> <true|false>`, one per fork, plus a `tape` header row),
an operation and its answer, a failure, and the run outcome.

Cannot:

- **The interruptor id.** `answer interrupt []` — the answer is `Unit`
  (`FiberFamily.lean:105-106`). The plan states it directly
  (`docs/research/2026-09-03-reification-plan.md:196-197`): "Nine census rows
  observed; the interruptor id stays unwitnessable (the wire drops it)."
  `COORDINATION.md:1116` repeats it. The model-side receipt is
  `Effect4Test/Counterexamples/Flow/Interrupt.lean:148-151`, whose `#guard`
  literally spells `.interrupt none`. Meanwhile rc.112 *does* carry it —
  `generated/effect-runtime-census.tsv:92` (row `cause.reason-interrupt`) says an
  interrupt reason "carries an optional interruptor fiber id", and
  `runtime-check.ts:164-167` observes `reasons[0].fiberId === 99`. That gap is
  exactly why assertion 10 cannot become a golden.
- **Which fiber ran.** No per-row fiber field; only the `decide` rows and the
  `tape` header.
- **Scheduler priorities.** `RunReport.scheduled` is an empty stub
  (`tracer.ts:379`).
- **`join` of an interrupted child.** `FiberFamily.lean:49-58`: the host ends
  `{"interrupted":true}`, the family's abort channel is `Nat`, the two faces
  cannot agree, so the model sets `FiberTable.stuck` and emits no golden
  (`E4-SEM-CE-010`).
- **Region events.** No `enter`/`leave`/`finalizer` rows appear; this family has
  no region.

`docs/TRACE-DAG.md:63` states the limit in one place: the scheduler's `Machine`
"carries no program, so nothing in Lean steps two fibers against each other".
The doc never uses the word "interruptor"; its nearest general statements are
separation 3 (`:79-81`) and the "what agreement does not establish" list
(`:107-113`).

### 5.3 What a Lean two-fiber model would need to emit

**[inferred]** from §5.1–5.2 and §3.2. To turn the nine goldens from checks of a
sequential projection into checks of a model, the Lean side would have to emit,
per run:

1. **A `decide` row per fork with the *same* site numbering** — already true, and
   the `RunDecision.fireDispatcher` / `yieldVerdict` pair reproduces exactly what
   `TapeScheduler` consumes (`tracer.ts:389-399`). This is the cheapest edge: the
   existing tape format needs no change.
2. **A per-row fiber attribution.** Not present today. Adding `RunEvent.started`
   / `ranTask` gives the model a "who ran" fact the wire currently discards; the
   wire would need one new column, or a masked projection that drops it (the
   `docs/TRACE-DAG.md` mask discipline already supports "the model may know more
   than the wire carries").
3. **An interruptor field on the interrupt answer.** `RunDecision.interruptFrom
   (interruptor : Option FiberId)` supplies it; `answer interrupt []` would have
   to become `answer interrupt <id>` — a family-alphabet change
   (`FiberFamily.lean:105-106`) and a golden regeneration. This is what unlocks
   `runtime-check.ts:140-167` as a golden.
4. **A third `Exit` arm.** `awaitValue`/`awaitError` both answering `none` for an
   interrupted child (`FiberFamily.lean:69-79`) is a stratum-V spelling
   limitation, not a model limitation. A `RunFiber.exit : Option (Exit …)` has the
   third arm natively; the family alphabet does not.
5. **A "child completes another child" former**, for the refused tenth assertion
   (`FiberFamily.lean:329-338`). A program-carrying machine has this for free —
   the child's program can contain a `fork`/`interrupt` of a sibling — so this is
   the assertion most improved by the deeper approach.
6. **Nothing about the host loop.** `Scheduler.ts:83-103` (setImmediate vs
   setTimeout vs microtask) stays evidence. The model supplies
   `fireDispatcher owner` and refuses to say when the host would have fired it.

---

## What I could not verify

- **Whether the fused `popFrom` still agrees once `AsyncFinalizer` is present.**
  `docs/FRAMES-DAG.md:200-211` states the obligation; I did not attempt the
  proof or a counterexample. It is the single most likely place this proposal
  breaks.
- **Whether `_yielded` thunks other than `resumed = true` can exist.** I scanned
  every write site in the pinned file (`:604, 660, 663, 700, 1128`) and every
  `yieldWith` caller, and found none. I did not scan the rest of
  `vendor/effect-4.0.0-rc.112/src/` for a `_yielded` write from another module.
- **The exact current coverage block.** I did not run
  `scripts/report-effect-runtime-coverage.sh` or
  `scripts/check-effect-runtime-census.sh` (they may build). The last recorded
  block is `COORDINATION.md:658-660`: "denominator 117; owned-with-green 3;
  green 49, partial 25, absent 43", and the file counts I took by hand agree
  (137 mechanism rows; 49 green, 25 partial, 63 absent of which 20 excluded).
- **Any transition function of the proposal.** The probe declares structures
  only. Nothing about `step`, `run`, `Runs`, determinism or termination was
  checked.
- **`Effect4Test/Concurrency/**` is claimed by Codex** (`COORDINATION.md:40`,
  "in progress, red"), so the FiberAssurance name counts I report (≈981, ≈1 135,
  ≈101) are counts of `` `Effect4 `` tokens in the current worktree, not a
  guaranteed-stable surface.
- **Whether retiring `Race.lean` is *wanted*.** I established only that it is
  cheap: it witnesses no census row and is in no frozen assurance input. Its
  `docs/RACE-DAG.md` and `test/contracts/race-representative.contract.md` may
  encode a commitment I did not read in full.

Two defects found in passing, offered as observations, not as claims about the
gate:

- Three `partial` rows carry no "Remaining source clause" comment —
  `interrupt.unsafe-entry` (`RuntimeCoverage.lean:2755-2759`),
  `scheduler.run-tasks-drain-once` (`:3139-3142`),
  `rule.record-and-apply-separate` (`:3353-3356`) — while
  `docs/RUNTIME-COVERAGE.md:44` says a `partial` row "must list what is missing
  in the row's comment".
- `docs/research/2026-09-03-reification-plan.md:202` says "the nine assertions of
  `harness/fiber-supervision/runtime-check.ts`"; the file has ten
  (`runtime-check.ts:170`).

---

## Recommended packet shape

Two packets, in order. Neither touches `Effect4/Runtime/Runtime.lean`
(built, green, `COORDINATION.md`) or `Effect4/Concurrency/**` (Codex).

### R1 — the run-loop and parking packet

The packet `Runtime.lean:90-92` and `:217-220` already name. **Single fiber.**

Fence (all new unless marked): `Effect4/Runtime/RunLoop.lean`;
`test/contracts/run-loop.contract.md`;
`Effect4Test/Runtime/RunLoopContract.lean`;
`Effect4Test/Runtime/RunLoopAxiomReport.lean`;
`docs/RUNLOOP-DAG.md`;
`Effect4Test/Counterexamples/Runtime/RunLoop.lean`;
append-only: `Effect4.lean`, `Effect4Test.lean`,
`test/counterexamples/REGISTER.md` (`E4-RUN-CE-022` onward),
`test/counterexamples/runtime/ATTACKS.md`,
`test/fixtures/trust-gate/known-red.txt`.
Explicitly **not** in the fence: `Effect4/Runtime/Runtime.lean`,
`Effect4/Concurrency/**`, `Effect4Test/Concurrency/**`,
`Effect4Test/Audit/RuntimeCoverage.lean` (the census join is a separate packet,
as it was for `FRAME-L8` and `SCOPE-L7`).

Statement list:

1. `RunPrim` and the three new `step` equations: `yieldNowWith` parks with a
   guard and enqueues `Task.resume`; `async` short-circuits on a supplied answer
   and otherwise parks and conditionally pushes `asyncFinalizer`;
   `asyncFinalizer`'s `contAll` masks and pushes, its `contE` runs the cancel
   only on an interrupt-bearing cause. Census `op.Yield`, `op.Async`,
   `op.AsyncFinalizer`.
2. `runLoop_top_deferred`: at the top of an iteration a set `deferredInterrupt`
   is cleared and `current := failure pendingCause`. Census
   `checkpoint.runloop-top`.
3. `yield_exit_finishes` / `yield_guard_parks`: the sentinel means finished when
   `parked = withExit`, parked when `parked = withGuard`. Census
   `rule.yield-is-overloaded`.
4. `post_yield_cancel_continues`: parked-with-guard plus `deferredInterrupt`
   fires the guard and continues rather than parking. Census
   `checkpoint.post-yield-cancel`.
5. `opCount_resets_on_entry` and `at_most_one_injection_per_entry`. Census
   `rule.budget-per-runloop-entry` (statable but `targetOnly`).
6. **The inherited obligation**: either `popFrom_agrees_with_unfused` in the
   presence of `asyncFinalizer`, or an unfused `popFrom'` plus an agreement
   theorem on the `asyncFinalizer`-free fragment. `docs/FRAMES-DAG.md:200-211`.

Size estimate: 550–750 Lean lines plus a ~200-line battery. Prerequisites: none
beyond the built `Runtime.lean`; the census rows already exist so no census
re-pin is needed. Risk concentrated entirely in statement 6.

### R2 — the program-carrying multi-fiber machine

Fence: `Effect4/Runtime/Fibers.lean`;
`test/contracts/fiber-machine.contract.md`;
`Effect4Test/Runtime/FiberMachine{Contract,AxiomReport}.lean`;
`docs/FIBER-MACHINE-DAG.md`;
`Effect4Test/Counterexamples/Runtime/FiberMachine.lean`; append-only root wiring
and register rows. Requires a `COORDINATION.md` claim row before any edit,
because it overlaps Codex's concurrency lane conceptually even where it does not
overlap it by path.

Statement list:

1. `RunMachine`, `RunDecision`, `stepEval`, `Step`, `replayEval`, `Runs` — the
   `Scheduler.lean:479-634` shape, over the carrier of §3.2, with tape exhaustion
   a `frontier` (DB-04).
2. `fork_deferred_enqueues_on_parent`, `fork_immediate_runs_now`,
   `fork_daemon_untracked`, `fork_child_installs_middleware`. Census
   `fork.unsafe`, `fork.child`, `fork.detach`, `rule.only-fork-child-tracks`,
   `rule.start-is-asymmetric`.
3. `dispatcher_drains_once` (a task enqueued during a drain waits),
   `buckets_ascending_fifo`, `first_task_arms`, `flush_loops_until_empty`. Census
   `scheduler.run-tasks-drain-once`, `.priority-buckets`, `.dispatcher-arming`,
   `.flush`.
4. `children_interrupted_after_exit` with the exit already computed and restored.
   Census `rule.children-interrupted-after-exit` — the "between runLoop returning
   and observers firing" clause becomes statable for the first time.
5. `observers_fire_after_exit_in_order`, `observer_added_after_exit_fires_now`,
   `observers_cleared_once`. Census `fork.join`, `fork.await`.
6. `interrupt_records_always`, `interrupt_defers_while_running`,
   `interrupt_applies_when_idle`, `interrupt_noop_after_exit`,
   `interrupt_accumulates_by_combine`, with a real `Option FiberId` interruptor.
   Census `interrupt.unsafe-entry` (the `_running` clause), `interrupt.accumulate`,
   `rule.record-and-apply-separate`.
7. `shouldYield_default_eq` plus the tape override. Census
   `scheduler.should-yield`, `.max-ops-default`, `.prevent-yield-default`.
8. Projection lemmas: `P_preserves_step` for each old `Scheduler.lean` theorem in
   §4.1, and a second projection to `Supervision.Fiber` for the `forkUnsafe`
   family.

Size estimate: 1 400–1 900 Lean lines for statements 1–7, plus ~400 for the
projections in 8, plus a ~500-line battery. Prerequisites: R1 landed; a breaker
freeze of the new alphabet before any implementation (`AGENTS.md:31-44`); a
`COORDINATION.md` claim; and, before any coverage claim, a separate join packet
against `Effect4Test/Audit/RuntimeCoverage.lean` with a `PORT-MANIFEST.md`
decision on whether the ten `targetOnly` rows are re-disposed.

Do not, in either packet, retire `Scheduler.lean` or `Supervision.lean`. Do
retire `Race.lean` — separately, as an eight-file change with zero frozen-list
cost — or leave it, but do not entangle that decision with these two packets.
