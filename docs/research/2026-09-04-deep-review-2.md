# The Deep model, reviewed again against rc.112 (2026-09-04)

Ruling: "review the deep model again" — done by me, source in hand (`effect@4.0.0-rc.112`,
`src/internal/effect.ts`, `src/Scheduler.ts`, `src/Deferred.ts` at the pinned install
`C:\Users\kokok\Dev\effect4-host\node_modules\effect`), arm by arm against
`Effect4/Deep/Fibers.lean`, `Stores.lean` and `Effect4/Runtime/Runtime.lean`. The class looked
for is the one the day's two findings belong to (`E4-RUN-CE-027/028`): state rc.112 keeps in an
object or a closure that the model abstracted into a name, orders it gets wrong, arms it lacks,
mislabelled refusals. Each finding cites the source line, says what the model does, and names
the fix. "Trace-level" means outcomes agree and only the frame stream differs; those are owed
to R4 (the host loop), not to this pass.

## Confirmed as modelled

The loop top and the deferred interrupt (`:639-642`), the op count and the yield injection
condition (`:643-648`), `getCont`'s deferred check and its pop discipline (`:680-698`),
`interruptUnsafe`'s record/accumulate/apply split and its two annotation sources (`:574-595`),
`yieldNowWith`'s scheduled resume and disarming `_yielded` (`:982-994`, the model's guard
token), `Async`'s synchronous resume, park and conditional `AsyncFinalizer` push (`:1112-1142`),
`AsyncFinalizer`'s mask and cancel-then-refail (`:1149-1159`), `Sync`/`Suspend`/`WithFiber`,
`Iterator` and `While` after today's corrections (`:1356-1379`, `:4624-4645`), the three handler
frames, `Exit` and `OnExit`'s arms (`:3624-3637`, `:4002-4029`), `SetInterruptible`'s
substitution (`:4312-4328`), `uninterruptible`/`interruptible` (`:4302-4337`), `forkUnsafe`'s
mask and start (`:5264-5278`), `fiberRunIn`'s closed-scope interrupt with the fiber's own id and
no annotations (`:5454`), `Deferred.await`'s registration and splice-out cancel
(`Deferred.ts:173-186`), `doneUnsafe`'s clear-then-resume (`:1648-1660`), the scope's
close-state-first, single-finalizer-unmerged and strategy split (`:3779-3827`), `runSyncExit`'s
`AsyncFiberError` (`:5543`), `runPromise`'s squash (`:5521`).

## Findings — behaviour

| id | class | rc.112 | the model | fix |
| --- | --- | --- | --- | --- |
| R2-1 | order | `Sync[evaluate]` runs the thunk, *then* `getCont` (`:931-935`); `Deferred.succeed`'s thunk resumes every waiter inside `doneUnsafe` (`Deferred.ts:1655-1658`), so an interrupt a waiter records on the completer is seen by the completer's very next pop, which returns `deferredInterruptCont` without popping | the store `sync` pops the continuation (`resumeValue`) and only then drains the owed resumes as nested commands; the frame the pop consumed is gone when the deferred interrupt fires at the next loop top, so a handler frame under the `sync` (`matchCauseEffect`, `catchCause`, `onExit`) never sees the interrupt | a fourth outcome `Outcome.answered value`: the store step ends the iteration with its value pending; `drive` runs the nested commands, re-reads the fiber, then pops with `resumeValue` (whose `getCont` now sees the flag). Same op count |
| R2-2 | flag | when the loop returns an exit, `_deferredInterrupt = false` (`:659`) before the middleware runs | `exitInterruptChildren` keeps the fiber's frame, flag included; the next loop top after the children countdown would replace the body's exit | clear `deferredInterrupt` in both branches of `exitFiber` |
| R2-3 | park | `fiberJoin`/`fiberAwait`/`fiberAwaitAll` are `callback` parks whose cancel splices the observer out (`:767-821`); the interrupted awaiter runs that cancel through `AsyncFinalizer[contE]` under the mask | join/await park on a bare guard (`ParkKind.join`) and countdowns likewise; an interrupted awaiter leaves its observer on the target and no `AsyncFinalizer` frame is pushed | join/await/countdown parks push `asyncFinalizer (cancelName …)`; the cancel program is a new `WithFiberAction.dropObserver target token` (drops every observer of that token); `interruptRecord_parked_applies` then runs it as it runs `Deferred.await`'s |
| R2-4 | order | `fiberAwaitAll` walks the fibers in input order, attaching one observer at a time, and answers the exits in input order (`:789-811`) | `countdownPark` registers on all live targets at once and answers in completion order (`collected ++ [exit]`) | `Pending.collected : List (FiberId × Exit)`; `resumePrim` orders by `targets` |
| R2-5 | annotations | `fiberInterrupt`/`fiberInterruptAll`/`fiberInterruptAllAs` pass the *caller's* stack annotations (`:880-883`, `:892-895`, `:910-913`) | `interruptThenJoin` and `interruptAll` pass `ReasonAnnotations.empty`; only `forkIn`'s closed-scope arm passes them (M10) | `interp.stackAnnotations f.id` in both |
| R2-6 | latch | `forkChild` calls `interruptChildrenPatch()` (`:5253`, `:6656-6658`): the first non-daemon fork installs the middleware for the process | the latch is a tape decision only; `w5_no_middleware_leaves_children` pins a non-daemon child surviving its parent's exit, which rc.112 never does | the `fork` arm with `daemon = false` sets `middlewareInstalled`; the witness becomes the daemon case (the host golden `daemonSurvivesParentExit`); `RunDecision.installMiddleware` stays for `RequestResolver`-style installs |
| R2-7 | shape | `awaitAllChildren` is `onExit(self, …)` (`:5319-5333`): the new children are awaited on *any* exit, under the finalizer mask | `ProgName.awaitAllNew` compiles to an `onSuccess` chain: a failing body never awaits its children | `onExit (body) (awaitNew snapshot) false` with `finalizerProgram`; a failing-body witness |
| R2-8 | order | `forkIn` forks and, when immediate, *runs* the child first, then links only `if (!fiber._exit)` (`:5366-5376`) | `forkIn` links before starting; an immediately finishing child in a closed scope is interrupted before it runs | for `startImmediately` the link is a command after the child's evaluate (`Cmd.link …`), skipped on an exited child |
| R2-9 | guard | `fiberRunIn` on an exited fiber returns it unlinked (`:5451-5452`) | `linkScope`'s open arm links an exited target and leaves a stale keyed finalizer | check the target's exit in the open arm |
| R2-10 | mask | race entrants are forked with `uninterruptible = false`, i.e. interruptible (`:1521`) | `raceAll` spawns entrants with `MaskMode.inherit` | `⟨true, true, .interruptible⟩` (the retired `raceForkOptions` had it right) |
| R2-11 | existence | entrants are forked one by one inside the register loop and the loop `break`s once `done` (`:1520-1528`): a skipped entrant is never created and its id is never allocated | every entrant is spawned before any launch; a skipped one is "interrupted and kept" (M8), which rested on a *Lean-face* golden (`raceImmediateSuccessStopsLaunch.tsv`, `face lean`), not on the host | `Cmd.launch raceId program` spawns at launch; no `raceSkipped` fiber; `fiberCount` and ids follow the host |
| R2-12 | mask | the winner resumes the host with `flatMap(uninterruptible(fiberInterruptAll(live)), () => exit)` (`:1510-1514`) | `settleRace` interrupts the live entrants and parks the host on an unmasked countdown | resume the host with that program: `setInterruptible (interruptAll live) false` then the exit |
| R2-13 | cancel | the race park's cancel is `fiberInterruptAll(fibers)` (`:1530`): a host interrupted while racing interrupts its entrants | the host parks on a bare guard; an interrupted host leaks its entrants (`w3_empty_until_interrupted` only checks the host) | the race is an `Async` park with `asyncFinalizer (cancelRace raceId)`; the cancel program interrupts the live entrants |
| R2-14 | flush | `runSyncExit` flushes the *root's* dispatcher only (`:5542`); dispatchers are per fiber (`Scheduler.ts:552-555`, `:188-190`) | `runSyncExit` flushes every armed dispatcher in fiber order, so a child's yield or a grandchild's deferred start completes under `runSync` where rc.112 answers `AsyncFiberError` | `runSyncExit` fires the root's dispatcher until it is empty; `RunDecision.flush` keeps its meaning for the async mode |
| R2-15 | order | dispatchers arm a `setImmediate`/microtask in the order they are armed (`Scheduler.ts:207-212`); the event loop runs them in that order | `flushAll` runs armed dispatchers in fiber order ("assumption, recorded") | the machine keeps an arming queue; `flush` runs it in arming order, re-arming at the tail |

## Findings — trace-level (owed to R4)

| id | rc.112 | the model |
| --- | --- | --- |
| R2-16 | the injected yield is `flatMap(yieldNow, () => prev)` (`:650-651`): an `OnSuccess` frame sits on the stack while parked | the park carries `prev` in the resume task; no frame |
| R2-17 | `forkUnsafe` tracks the child *after* the immediate evaluate and only if it has not exited (`:5279-5282`) | tracked before; an immediately finishing child produces an `untrackChild` observer row the host has no counterpart for |
| R2-18 | `scoped` is one `withFiber` (make the scope, set the context) and one `OnExit` (restore, close) (`:3938-3947`) | the compile's chain is `onSuccess(sync scopeMake) → onExit → onSuccess(withFiber getCtx) → onSuccess(withFiber setCtx) → onExit(restore)`; a `WithFiberAction.withScope` would make it two frames |
| R2-19 | a multi-finalizer close runs a generator (`Iterator` frame) with an `Exit` frame per sequential finalizer (`:3806-3827`); `OnExit`'s success path composes with `flatMap`, its failure path with `combineFinalizerCause` (`:4019-4028`) | `closeSeqChain` is an `OnSuccessAndFailure` chain; `finalizerOr` pushes one two-armed frame |

## Order of repair

1. Small and local: R2-2, R2-5, R2-6 (with the witness rewritten), R2-9, R2-10.
   **Landed 2026-09-04.** R2-2: `exitFiber` clears `deferredInterrupt` in both branches
   (`exitStore_fields`, `exitInterruptChildren_eq`). R2-5: `interruptEach` takes the caller's
   annotations; every site passes `interp.stackAnnotations caller` (`interruptEach_known`,
   `interruptThenJoin_eq`, `withFiber_interruptAll`, `drive_launch_skipped`); register row
   `E4-RUN-CE-030`, witness `w6_close_interrupt_carries_closer_annotations`. R2-6: the `fork`
   arm latches the middleware unless `daemon` (`withFiber_fork`); `w5_no_middleware_leaves_children`
   is replaced by `w5_fork_latches_the_middleware` and `w5_daemon_child_survives_parent_exit`;
   register row `E4-RUN-CE-029`. The witnesses whose child must outlive the root (W2, W10, W11,
   the compile battery's mask pins) fork it as `daemonChild`. R2-9: `linkScope`'s open arm
   checks the target's exit (`linkScope_open` with the liveness hypothesis,
   `linkScope_open_exited`). R2-10: `raceEntrant_options` reads `.interruptible`. Coverage
   join unchanged at 134 green / 1 partial / 0 absent of 135.
2. The store-sync ordering R2-1 (`Outcome.answered`), with a witness: a completer under
   `matchCauseEffect` whose waiter interrupts it.
3. The park redesign R2-3/R2-4/R2-12/R2-13 (join, await, awaitAll and the race as `Async`
   parks with cancels; input-order exits; masked settle), with witnesses for each.
4. The fork family R2-7, R2-8, R2-11 and the scheduler R2-14/R2-15.
5. The trace-level four with R4.

Every closed finding lands as a clause in `Effect4/Deep/Clauses.lean`, a witness in
`Witnesses.lean` or the S1 battery, and where it corrects a pinned decision (M8, the flush
assumption, W5's second witness) a register row.
