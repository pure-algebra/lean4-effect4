# R4 for the Deep machine — the host loop, the deep wire, and the four trace-level findings

Date: 2026-09-04. Status: design (grilled below), not started. Parents:
`docs/research/2026-09-04-ast-relation-plan.md` §7 (R4 restated over `Eff`),
`docs/TRACE-DAG.md` row `fibers` ("the two-fiber model exists in Lean; the host loop for
it is owed"), `docs/research/2026-09-04-deep-review-2.md` (R2-16..19 and R2-11b, "owed to
R4"). Ruling: design first, land once; the mechanical pieces go to Opus after the design is
fixed (`delegate-mechanical-to-opus`).

## 0. What R4 says, and what it does not

R4: rc.112 running `print e` at the same decision tape produces, per fiber, the stream the
machine produces for `compile e`, under a named mask; and every fiber's outcome is equal.
Nothing here is a Lean theorem about the host (TRACE-DAG separation: "no Lean statement
reaches the host"); the receipt is finite host evidence, exactly as the service-level
families have it, but now at the fiber and frame level, which is where the machine lives.

What it does not establish: anything about programs outside the corpus; host error
identity or stack-annotation payloads (the outcome wire is annotation-blind, separation 3);
timing; `setImmediate` versus microtask ordering beyond what the tape fixes (R2-15's
arming order is the model's claim, and the tape's `flush` is where the host is asked to
agree with it).

## 1. The deep wire (new alphabet, `effect4-deep-v1`)

One row per event, tab-separated, rendered on the Lean side by an exact-module renderer
beside `Effect4/Target/TypeScript/Trace.lean` (`Effect4/Target/TypeScript/DeepTrace.lean`,
strings only at the boundary, admitted like `Trace.lean`), and on the host side by
`harness/trace/deep-tail.ts`. Fiber ids are creation order, `0` the root — the machine's
`nextId` and the host's `forkUnsafe` order (hunk `fiber.fork`, §4) coincide.

| row | from `RunEvent` | host source |
| --- | --- | --- |
| `forked <parent> <child> <daemon>` | `forked` | hunk `fiber.fork` |
| `started <f>` | `started` | hook, first primitive of a fiber (and the root's `runFork`) |
| `prim <f> <tag> <depth>` | `evaluated f tag depth` (new, §2.1) | `Tracer.context` hook: `primitive["~effect/Effect/identifier"]`, `fiber._stack.length` |
| `yield <f>` | `yieldInjected` | `TapeScheduler.shouldYield` answering `true` |
| `interrupt <who|-> <target>` | `interruptRecorded` | hunk `fiber.interrupt` on `interruptUnsafe` (§4) |
| `exited <f> <outcome>` | `exited` | `addObserver` installed by hunk `fiber.fork` (and on the root by the tail); `outcomeWire` |
| `decide <site> <bool>` | the tape's `yieldVerdict` | as today |
| `frontier` | fuel out / stall | as today (`stallMs`, budget) |

`tag` is the 17-name census alphabet (`Success`, `Failure`, `Sync`, `Suspend`, `WithFiber`,
`YieldableError`, `Iterator`, `OnSuccess`, `OnFailure`, `OnSuccessAndFailure`, `Exit`,
`OnExit`, `SetInterruptible`, `While`, `Yield`, `Async`, `AsyncFinalizer`): a closed
`PrimTag` enum with `Prim.tag : Prim → PrimTag` in Lean, rendered at the wire.

Masks: `outcome` (the `exited` rows), `fibers` (`outcome` + `forked`, `started`,
`interrupt`, `yield`, `decide`), `frames` (`fibers` + `prim`). The patched hunks' pop rows
(`frame.pop`, `frame.deferred-interrupt`, …) are recorded as a second channel and not
compared in this phase (TRACE-DAG `bridges` stays open by construction).

**Which mask at which yield setting.** `outcome` and `fibers` at both settings (a large
`MaxOpsBeforeYield` and rc.112's floor of 3, separation 8); `frames` at the large setting
only. Reason: R2-16 — rc.112's injected yield is `flatMap(yieldNow, () => prev)`
(`internal/effect.ts:650-651`), an `OnSuccess` frame the model does not hold (its resume
task carries `prev`); the model cannot hold it because the frame's continuation would have
to be a name resolving to an arbitrary `Prim`, which the interp's pure `contA` cannot do.
The injected rows differ, and only at the floor. Recorded, not fixed: it is the one
trace-level item that stays trace-level.

## 2. What the machine owes before the streams can agree

### 2.1 The per-primitive event

`iteration` emits `RunEvent.evaluated f.id (Prim.tag f.frame.current) f.frame.stack.length`
after `countOp (runloopTop f)` and before `injectYield`/`evaluatePrim` — the hook runs at
`:653-655`, after the injection wraps `current`; at the large setting no injection
happens, so the row is the primitive the loop evaluates. `Cmd.deliver` (R2-1's pop) emits
nothing: rc.112's `Sync[evaluate]` is one hook call. Clause `iteration_evaluated`; the
witnesses' projections ignore the row; `traceWellFormed` unchanged.

### 2.2 R2-11b — the race is an `Async` whose registration is the launch loop

rc.112: `raceAll` is `withFiber(parent => callback(resume => { for … forkUnsafe …; if (done)
break; return fiberInterruptAll(fibers) }))` (`:1490-1531`). The `Async` arm runs the
register loop *inside* `Async[evaluate]` and parks only if no entrant resumed it
synchronously (`yielded !== false → return yielded`, `:1120-1126`); when it parks it pushes
the cleanup frame (`:1128-1141`). The model today parks first and launches as commands,
so a synchronous winner produces a park/resume pair and a cleanup frame the host never had
— visible as a depth difference on the next `prim` row.

Fix: `WithFiberAction.raceAll entrants` answers `current := Prim.async
(interp.raceRegisterName raceId) false (some (interp.raceCancelName raceId))` with the race
recorded (`programs := entrants`, `settledWith := none`) and nested `[Cmd.launch raceId]`,
`Outcome.continue_`. The `Prim.async` arm consults a new hook `interp.raceOfRegister : ν →
Option Nat` before `registerAsync`: for a race name, if `race.settledWith = some p` (an
entrant settled it during the launches, which ran as nested commands before this loop
iteration) then `current := p`, no park, no frame; else push the cleanup frame and park on
the token as the `Async` arm does for every cancel-carrying registration. `settleRace`:
when the host is parked on the race token, `Cmd.resume` as now; when not (the host is still
inside its registration), store `settledWith := some (interp.raceSettle live accepted)`.
Clauses `evaluatePrim_async_race_settled`, `evaluatePrim_async_race_parks`,
`settleRace_before_park`; witnesses `w3_immediate_success_stops_launch` (no park/resume
rows now — pin `parkedRows`), `w3_empty_is_a_frontier` (parks). Stores: `Name.raceRegister
(race : Nat)`, `stores.raceOfRegister`.

### 2.3 R2-18 — `scoped` is one `WithFiber` and one `OnExit`

rc.112 (`:3938-3947`): `withFiber(fiber => { const scope = makeScope; const prev =
fiber.context; fiber.setContext(add prev Scope scope); return onExit(body, exit => {
fiber.setContext(prev); return scopeClose(scope, exit) }) })`. The compile's chain today is
five primitives. Fix: `WithFiberAction.enterScope (strategy)`: mints the scope in the store
(`SyncOp.scopeMake`), sets the fiber's context, and answers `current := Prim.onExit body
(interp.leaveScopeName prev scope) false` where the finalizer program is
`onSuccess (withFiber (setContext prev)) (closeScope scope exit)` — one `WithFiber` row,
one `OnExit` frame, exactly the host's. `Effect4/Syntax/Compile.lean`'s `.scoped` arm
emits it; `EffThunk.enterScope`, `EffName.leaveScope prev scope`; clause
`withFiber_enterScope`; the compile battery's `pScoped` pins re-derived (the scope's key
stays the point's fuel).

### 2.4 R2-19 — the close generator and `OnExit`'s two arms

rc.112 (`:3806-3827`): a scope with several finalizers closes through a generator — an
`Iterator` frame with one `Exit` frame per sequential finalizer — and (`:4019-4028`)
`OnExit` composes its success path with `flatMap` and its failure path with
`combineFinalizerCause`. The model's `closeSeqChain` is an `OnSuccessAndFailure` chain
and `finalizerOr` pushes one two-armed frame. Fix: `finalizerOr` installs `current :=
Prim.onSuccess (Prim.exitFrame program) (interp.restoreName exit)` — the `Exit` frame
captures the finalizer's exit and the `OnSuccess` continuation is
`restoreAfterFinalizer`/`mergeFinalizer` by the exit's arm — two frames, as
`:4019-4028` has (`flatMap(exit(finalizer(exit_)), …)`); `storesCloseScope` for the
multi-finalizer sequential close emits `Prim.iterator (closeGen scope exit) cursor` whose
`iterNext` yields `Prim.exitFrame (finProgram fin exit)` per finalizer and finishes with
the merged exit — the `Iterator` and `Exit` rows of the host. Clauses restated
(`finalizerOr_*`, `closeSeqChain_*`); witnesses W2, W6, W13 re-pinned (outcomes unchanged,
frame rows change).

### 2.5 R2-17 — invisible on the wire

`forkUnsafe` tracks the child after an immediate evaluate and only if it has not exited
(`:5279-5282`); the model tracks before and untracks by observer. No wire row shows it
(`observerFired` is not projected) and no outcome depends on it (`awaitAllChildren`'s walk
collects an exited child's exit at once). Recorded; fixed only if a later mask projects
observers.

## 3. The corpus and the goldens

Programs: the compile battery's `NativeEff` values (`Effect4Test/Syntax/CompileContract.lean`
— `pDeferred`, `pForkJoin`, `pAwaitFailing`, `pJoinFailing`, `pRace`, `pMiddleware`,
`pDaemon`, `pScoped`, `pMasked`, `pUnmasked`, the generators, the loops) plus the
`ProgName` witnesses W1–W15 respelled as `NativeEff` where the alphabet allows (those with
tape-answered external parks are not in this corpus; §4 says why). Each program is printed
by A2 (`print nativeSignature 0 p`, `printDecl`) into `harness/trace/deep-fixture.ts`
(generated by `Generate.lean deep-fixture`, regenerated and drift-checked like
`deferred-fixture.ts`) and run in Lean by `replayEff p tape` to the golden
`generated/traces/deep/<program>.<tapeName>.tsv` (face `lean`; prologue as
`Trace.golden` with `format effect4-deep-v1` and a `deep-tape` row, §4).

## 4. The host tail (`harness/trace/deep-tail.ts`) and two hunks

The tape is a `RunDecision` list on the wire: `evaluate:0`, `fire:<f>`, `flush`,
`interrupt:<who|->:<target>`, `verdict:<f>:<0|1>`, `middleware`; `answerAsync` is not on
the wire in this phase (an external park of the corpus would need a host-side resume
registry; the corpus has none — Deferred waits are completed by sibling fibers).

* `evaluate:0`: `Effect.runFork(traced, { scheduler: deepScheduler })` — rc.112 evaluates
  the root synchronously on the caller's stack (`:5423`), which is what the model's
  `Cmd.evaluate` does.
* Dispatchers: `deepScheduler.makeDispatcher()` returns an instrumented
  `MixedSchedulerDispatcher` whose `setImmediate` is the tail's own queue: arming records
  `(owner, dispatcher)` in arming order and schedules nothing. The owner is
  `getCurrentFiber()` at `makeDispatcher` time (`currentDispatcher` is created lazily by
  the fiber that schedules, `:553-554`; a deferred fork schedules on the parent's,
  `:5277`; a yield on its own, `:986`). `fire:<f>` runs that dispatcher's `runTasks()`
  (`Scheduler.ts:225-233`); `flush` runs the queue head-first until empty, a re-armed
  dispatcher going to the back (R2-15). `runSyncExit` is not used: the tail is the host loop.
* `interrupt:<who>:<target>`: `fibers[target].interruptUnsafe(who === "-" ? undefined :
  fibers[who].id)` — the second argument is the interruptor's id, the annotations are the
  fiber's own (`:578-584`), which the outcome wire drops (separation 3).
* `verdict:<f>:<b>`: the `TapeScheduler.shouldYield` override answers `b` for fiber `f`'s
  next check and consumes it (the `armed` mechanism of `tracer.ts:389-399`, per fiber).
* `middleware`: nothing — a non-daemon fork installs it (R2-6); the row is accepted for
  tape parity and ignored.
* Fiber numbering and exits: hunk `fiber.fork` in `harness/trace/patched/` — one
  observation-only insertion after `const child = new FiberImpl(…)` in `forkUnsafe`
  (`:5272`) calling `globalThis.__effect4Fiber?.("fork", parent, child, daemon)`; the tail
  numbers `child` in creation order, records `forked`, and installs `child.addObserver`
  for the `exited` row. The root is numbered `0` by the tail before `runFork`. Hunk
  `fiber.interrupt` at the top of `interruptUnsafe` (`:575`) records `interrupt`.
* Primitives: the `Tracer.context` hook of `runTraced` already records `(op, depth)`; it
  gains the fiber index (`fibers.indexOf(fiber)`), and `started` on a fiber's first hook
  call. The budget latch and `stallMs` stay.

`patch-manifest.json` grows by the two hunks; `apply.mjs` is unchanged;
`scripts/check-trace-patched.sh` keeps its three scope facts.

## 5. The gate

`scripts/check-trace-host.sh` gains the `deep` family: regenerate `deep-fixture.ts`, then
for every golden under `generated/traces/deep/`: `deep-tail.ts` with `EFFECT4_PROGRAM` and
`EFFECT4_DEEP_TAPE` at the large setting under `outcome`, `fibers`, `frames`, and at the
floor of 3 under `outcome`, `fibers`; receipts under `harness/trace/receipts/deep/`. The
mask table `generated/traces/masks.tsv` gains the three deep masks. TRACE-DAG row `fibers`
moves to "host loop landed; frames agree at the large setting; R2-16 recorded".

## 6. Attacks on this design

* *The hook sees the wrapper, not the primitive, on an injected yield.* Yes — that is
  R2-16 and the reason `frames` is compared at the large setting only.
* *Fiber numbering by first primitive would differ from creation order for deferred
  starts.* It would; hence the `fiber.fork` hunk.
* *A `Deferred` completion resumes waiters inside the completer's `sync` — do the two
  sides interleave the `prim` rows the same way?* Yes since R2-1: the model runs the owed
  resumes before the completer's pop, as `doneUnsafe` does, so the waiter's rows sit
  between the completer's `Sync` row and its next row on both sides.
* *`runFork`'s abort signal, `runSyncExit`'s root-only flush.* Out of scope: the tail is
  the loop; `runSyncExit` (R2-14) is pinned in Lean and needs no host row here.
* *Object identity of handles in `prim` rows.* None: a `prim` row carries a tag and a
  depth, never a value.
* *Two agents, one `lake`.* The Lean part is one module set (`Fibers`, `Clauses`,
  `Witnesses`, `Compile`, `DeepTrace`, `Generate`); the host part touches
  `harness/trace/` only; they can run in parallel on disjoint files with one build each.

## 7. Order and ownership

1. Machine (mine): §2.1, §2.2, §2.3, §2.4, with clauses, witnesses, register rows for the
   reversed pins (`pScoped`'s chain, the race's park), and the coverage re-render.
2. Wire (Opus, mechanical after 1): `PrimTag`/`Prim.tag`, `Effect4/Target/TypeScript/
   DeepTrace.lean` (projection + renderer + masks), `Generate.lean deep` and
   `deep-fixture`, the goldens.
3. Host (Opus, in parallel with 2): `deep-tail.ts`, the two hunks, the gate section,
   receipts.
4. Landing (mine): TRACE-DAG, LOWERING-COVERAGE refusal rows, register rows for whatever
   the host disagrees with — every disagreement is a finding, and this is the lane where
   the model's fidelity, not its consistency, is tested (S4 of the stress plan follows on
   the same rails).
