# Fiber machine, Pass A: the domain contract before any declaration

Status: Pass A of the Lean formalization strategy, 2026-09-03. Input to the breaker of plan
packets R1 and R2 (`docs/research/2026-09-03-deep-plan.md`). Source reading:
`docs/research/2026-09-03-deep-fiber-runloop.md` §1, every row of which cites
`vendor/effect-4.0.0-rc.112/src/internal/effect.ts` or `Scheduler.ts` by line. Nothing here is
a declaration; Pass B freezes those after the model exists.

The governing rule: **this is a transcription, not a design.** rc.112's fiber is one class with
seventeen fields and an eighty-line loop, and every arm of the Lean step relation names the
source line it transcribes, the way the census rows do. The literature supplies the theorem
shapes, not the model. Where the source leaves a choice to the host (which callback fires
first), the model takes a decision from a tape and says so.

## 1. Domain contract

### Objects

| Object | rc.112 | Model | Notes |
| --- | --- | --- | --- |
| primitive | the fourteen `makePrimitive` classes plus `Yield`, `Async`, `AsyncFinalizer` | `Prim` (exists, `Effect4/Runtime/Runtime.lean`) extended by `RunPrim` | first-order; continuation slots are names `ν`, thunks names `σ` |
| fiber | `FiberImpl`, `effect.ts:505-555` | `RunFiber` | the five `FrameFiber` fields plus `running`, `parked`, pending asyncs, op count, budget, prevent-yield, observers, children, exit, dispatcher |
| dispatcher | `MixedSchedulerDispatcher`, `Scheduler.ts:105-233` | `Dispatcher` = priority buckets, FIFO within, `armed` flag | one per fiber, lazily; there is no global queue |
| task | `Scheduler.ts` task thunks | `Task.start child` or `Task.resume target token` | covers `effect.ts:986` and `:5277`, the only two enqueue sites |
| observer | closures at `effect.ts:565` | `Observer.resumeAwait`, `.untrackChild`, `.dropScopeFinalizer` | covers every `addObserver` site |
| machine | the process: all live fibers, the id counter, the middleware latch | `RunMachine` | `fibers`, `nextId`, `nextToken`, `middlewareInstalled`, `trace` |
| service state | Ref cells, Deferred completions, scopes | a parameter `St` of the machine | unresolved question Q2 below |

### Operations

Transitions of the machine, each a transcription:

| Operation | Source | Kind |
| --- | --- | --- |
| evaluate one primitive of a running fiber | `effect.ts:653-655` via the frame machine's `step` | total, deterministic given the interp |
| top-of-loop deferred interrupt | `:639-642` | total |
| op count and yield injection, at most once per entry | `:643-652`, `Scheduler.ts:174-176` | needs decision (b) |
| park (`Yield`) and resume | `:656-668`, `:602-606`, `:986-989` | needs decisions (a), (c) |
| async register, short-circuit or park, cancel frame | `:1109-1143` | needs decision (c) |
| exit: store, fire observers in index order, clear | `:619-627` | total |
| children interrupted between exit and observers | `:613-617` | conditional on the middleware latch, decision (e) |
| fork: derive child mask, construct over parent context, start deferred on the parent's dispatcher or immediately | `:5264-5284`, `:5277`, `:5272` | needs decision (a) for deferred starts |
| interrupt: record always, apply only if interruptible, defer if running | `:574-595` | needs decision (d) for the interruptor id |
| join, await, awaitAllChildren, interruptAll | `:561-562`, `:5318-5322`, `:895` | observer registration |
| scope linkage: `forkIn`, `fiberRunIn`, `forkScoped` | `:5364-5378`, `:5447-5461`, `:5400-5406` | writes a keyed finalizer into a scope; needs the scope store |

### Observables

- Per fiber: the exit, when it exists; the order in which observers fired; whether an interrupt
  was deferred or applied; which finalizers ran and in which order (already `FrameEvent`).
- Per machine: the event trace `RunEvent` (forked, started, scheduled task, ran task, yield
  injected, parked, resumed, interrupt recorded, interrupt deferred, children interrupted,
  observer fired, exited), and its projection to the shared service-level trace alphabet
  under the existing masks (`docs/TRACE-DAG.md`), with one new fact the wire lacks: which
  fiber ran a row.

### Equivalences

- Semantic: two machine runs are equal when their `RunEvent` traces and final exits are equal.
- Up to scheduling: a statement is scheduler-insensitive when it holds for every decision tape;
  the Fibers goldens' "identical service trace at both yield settings" is the host face of that.
- Irrelevant: task thunk identity, closure identity, the numeric fiber id beyond freshness,
  `Context` contents beyond the three cached fields, host timer kind.

### Environment and decisions

The tape supplies exactly the five decisions the source leaves to the host or the caller
(fiber note §1.3): (a) which dispatcher fires, (b) the `shouldYield` verdict, (c) when an async
resumes and with what, (d) the interruptor id, (e) whether the child-interruption middleware is
installed. Tape exhaustion is a live frontier, never a failure (DB-04).

### Scope

In: one process, any number of fibers, the frame machine as the per-fiber evaluator, the scope
store for linkage, the decision tape. Out, and named as evidence: the host event loop's
cross-dispatcher order, `setImmediate` versus microtask, JavaScript exceptions from user code
(a defect payload), `Context` beyond three cached references, metrics and tracer hooks.

### Examples

Positive witnesses that must be expressible and run to the expected exit:

1. Parent forks a child deferred, yields, the child runs to exit, the parent joins and
   receives the exit (`fork.join`, the first two-fiber theorem).
2. A masked fiber receives an interrupt: recorded, deferred, applied at the `SetInterruptible`
   frame's `contAll` (existing frame theorem, now reached from a second fiber).
3. `raceAll` with no entrants stays pending until interrupted
   (`generated/traces/fiber/emptyRacePendingUntilInterrupted.tsv`).
4. A child completes a sibling's Deferred and the sibling resumes (the tenth host assertion
   the sequential projection refused).

Forbidden, must be unreachable or refused by the step relation:

1. An observer firing before the exit is stored (`:619` precedes `:621`).
2. An interrupt applied while `running = true` (must set `deferredInterrupt`, `:589-590`).
3. A `SetInterruptible` frame evaluated as `current` (a defect, existing theorem).
4. A task enqueued during a drain running in the same drain (`Scheduler.ts:225-233`).
5. A second exit for a fiber that has one (`:600-601`, `:575-577`).

Edge cases: join on an exited fiber fires the observer at once; interrupt after exit is a
no-op; a synchronous async resume never parks; `prevRunning` restore on reentrant evaluate;
`forkIn` on a closed scope interrupts the child immediately with the parent's id.

Counterexample to the strongest overclaim, "the machine computes what rc.112 computes": two
fibers on two dispatchers whose relative order depends on `setImmediate` versus a resolved
promise. The model takes decision (a) from the tape; rc.112 takes it from the host. The
theorem is "for every tape", never "the host's tape".

### Assumptions, facts to prove, facts to test

| Assumptions (named hypotheses) | Facts to prove | Deployment facts, tested on the host |
| --- | --- | --- |
| the service is stateless or `St` threads it (Q2) | every step equation, one per source arm | the tracer hook counts what `currentOpCount` counts |
| the tape is compatible (no site mismatch) | invariants: at most one exit, observers cleared once, running restored, ids fresh | cross-dispatcher order matches the tape used for the golden |
| `Prim` names are given meaning by a pure `PrimInterp` | projection: one fiber with no fork equals `FrameFiber.run` | the wire's per-row fiber attribution once added |
| the middleware latch is a tape fact | projection: `RunMachine → Scheduler.Machine` preserves step | interruptor identity on the wire |

## 2. Prior-art ledger

No Lean formalization of a fiber runtime was found in the pinned corpus; the reuse column is
therefore local, and the literature is pattern or adapt. Licences are irrelevant for patterns.

| Source | Role | Guarantee it gives | Mismatch | Class |
| --- | --- | --- | --- | --- |
| `Effect4/Runtime/Runtime.lean` (own, green) | per-fiber evaluator | 28 census rows, `compile_simulates` | no run loop, no parking | **reuse** unchanged |
| `Effect4/Runtime/Scope.lean` (own, green) | scope state | 98 theorems | no store of scopes | **reuse**, plus M3 |
| `Effect4/Concurrency/Supervision.lean` (own) | observer protocol `observe`/`publish`, fork options | 136 theorems, 15 census rows partial | no program | **adapt** by projection |
| `Effects` package (own, pinned) | `Program`, `Handler`, trace alphabet | algebra laws | none | **reuse** |
| Reynolds 1972, definitional interpreters | defunctionalization: continuations as data plus an apply function | the method | none; `Prim` with `ν` and `PrimInterp` is exactly this | **pattern**, already applied |
| Felleisen and Friedman 1986, CEK | control and continuation stack as a machine state | machine shape | rc.112 carries values in primitives, so CK not CEK | **pattern**, already applied |
| Ager, Biernacki, Danvy, Midtgaard 2003, functional correspondence | an evaluator and its abstract machine are related by CPS plus defunctionalization | the shape of `compile_simulates` and of the general theorem T5/T6 | none | **pattern** for the proof method |
| Marlow, Peyton Jones, Moran, Reppy 2001, asynchronous exceptions | `block`/`unblock` masks, interruptible points, `throwTo`, bracket laws, small-step semantics | theorem shapes for masks and delivery: an exception is delivered only at an interruptible point; a finalizer runs exactly once | Effect records then applies; masks are frames, not scopes of a primitive | **adapt**: their delivery lemmas are the statements for `interrupt.*` and `checkpoint.*` |
| Abadi and Plotkin 2009, a model of cooperative threads | operational semantics of a thread pool with `yield`, `async`, `block`; equational laws; adequacy | the `RunMachine` step shape: run one thread to its next yield; laws for yield and spawn | Effect adds interruption, observers and priorities | **adapt**: the step relation and the adequacy statement |
| Ahman and Pretnar 2021, asynchronous effects | interrupts arriving during a computation, handled at `await` points; promises | the model of an interrupt reaching a parked or running fiber; `await` as a park on a promise | algebraic-effect handlers, not a stack machine | **adapt**: the async park and resume shape |
| Dolan et al. 2017; Sivaramakrishnan et al. 2021, OCaml effect handlers | fibers as one-shot continuations; a scheduler as a handler with a run queue | cooperative scheduling over captured continuations | Effect's continuations are frames, not captured | **pattern** |
| Xia et al. 2020, interaction trees | event traces with internal steps; weak bisimulation | already informative in DB-03 | none | **pattern** |
| ZIO 2 `FiberRuntime` | the direct ancestor design: op count, yield, interrupt status, observers | design intent | different language, not pinned here | **pattern** only; cite, never copy |

The consequence for the plan: no new dependency. The frame machine is reused as is; the
theorem statements for interruption and masks are transcribed from Marlow et al. into the
Effect vocabulary; the machine step and its adequacy statement follow Abadi and Plotkin; the
general Flow-to-machine theorem follows the functional correspondence.

## 3. Semantic level and the open representation questions

Level: a small-step transition relation `Step : RunMachine → RunDecision → RunMachine → Prop`
(the meaning, DB-03), with a fuel-bounded executable `replayEval` as the simulator (an
approximation, DB-04) and the existing `FrameFiber.step` as the per-fiber evaluator. Events
are emitted per step into the machine's trace. Determinism per decision is a theorem, not an
assumption.

Questions Pass B must close, each with the alternative that is not recommended:

- **Q1, fork at the Flow level.** The machine runs `Prim`; Flow v3 has no term carrying a child
  block to run concurrently, so no Flow denotes a two-fiber run and the lowering cannot emit
  `Effect.fork`. Recommended: a Flow term `fork body args target` answering a fiber handle,
  shaped like `enter region body` under DB-05, as a lean4-effects breaker; join, await and
  interrupt stay operations over `Handle "Fiber"`; the concurrent meaning of a Flow is compile
  to `Prim` then the machine. Not recommended: a fork *operation* whose request names a block,
  which hides a child in an opaque request and defeats admission.
- **Q2, where service state lives.** `PrimInterp` is pure, so a single fiber's Ref, Deferred
  and Scope effects are oracle-answered. Two fibers sharing a Ref, and `Deferred.await` resumed
  by a completion, need the store inside the machine. Recommended: keep `PrimInterp` pure and
  the frames contract frozen; make `RunMachine` parametric in `St` with a `RunInterp` extending
  `PrimInterp` by `syncState : σ → St → St × β`, the state models being components of `St`; the
  oracle form is a corollary. Not recommended: a state slot in `PrimInterp` (re-freezes 28 rows).
- **Q3, the interruptor id.** `RunDecision.interruptFrom (interruptor : Option FiberId)`
  carries what the wire drops; the Flow face needs a `Cause` to carry it (`E4-FLOW-CE-023`).
- **Q4, cross-dispatcher order.** Decision (a) is a tape entry per firing; it is not a priority
  queue and must not be modelled as one.
- **Q5, the fused `popFrom` with `AsyncFinalizer`.** Either the fused pop still agrees with the
  unfused one, or the agreement is restated on the finalizer-free fragment
  (`docs/FRAMES-DAG.md`). The single most likely place the model breaks; R1 proves it first.
- **Q6, couple, do not rebuild.** Resolved here, by reading the carriers. `Supervision.Fiber`
  (`Effect4/Concurrency/Supervision.lean:32-37`) reads its `core : FiberState` only through
  `id`, `status`, `terminal`, `mask`, `interruptPending`, `cleanup` and `cleanupCount`
  (51, 11, 12, 2, and 9 reads each); every one of those is a projection of a `FrameFiber`
  together with a parked flag and a stored exit. `Scheduler.stepEval`
  (`Effect4/Concurrency/Scheduler.lean:479`) already consumes the tape and emits the events;
  its one oracle decision, `complete id result`, is exactly what a carried program computes.
  The cleanest carrier is therefore a **fresh record with one source of truth**, not a product
  with a coherence invariant: `RunFiber` holds the frame (the five `FrameFiber` fields), the
  parked flag, the stored exit, the pending asyncs, the counters, and the supervision-only
  fields `context`, `children`, `subscriptions`, `interrupted`. The old `FiberState` is
  *computed*, `RunFiber.toSup : RunFiber → Supervision.Fiber` (status from running, parked and
  exit; mask from `interruptible`; `interruptPending` from `deferredInterrupt` or a stored
  cause; terminal from exit; the cleanup pair from whether observers have fired), and the old
  `Scheduler.Machine` is computed, `RunMachine.toSched`. Nothing is stored twice and there is
  no invariant to preserve. The old modules stay frozen and untouched, and their proofs are
  not redone: each old theorem transfers through one projection lemma of the form
  `toSup (exitFiber r e) = ((toSup r).publish e).1` or
  `toSched (step m d) = stepEval boundary (toSched m) (decisionOf d)`, which is `rfl`-shaped
  because the old functions never write the fields the frame owns. `Race.lean` alone is
  retired. What is genuinely new: the parking arms (R1), the machine step, the projection
  lemmas, the census clauses about "actual body evaluation", and, if wanted, the per-fiber
  dispatcher. The dispatcher can be deferred: keeping `SchedulerDecision.schedule id` as
  decision (a) is the reuse path, and the bucketed dispatcher is a later refinement of it whose
  rows are `targetOnly` today.

## 4. Declaration DAG

Definitions and theorem signatures only, dependency ordered. The definitions exist in
`workshop/Deep/Fibers.lean` (module `Deep.Fibers`) and build; the theorems are the
landing's.

```text
S1  Effect4/Runtime/Runtime.lean            (the frozen frame machine, re-frozen once)
    Prim.yieldNowWith | Prim.async | Prim.asyncFinalizer; cases_receipt at seventeen
    arms/ensure/armA/armE/step extended; PrimInterp.cancelThenFail
    popFrom_agrees_with_asyncFinalizer (or the unfused loops and their agreement)

Deep.Fibers                                  (imports Runtime, Scheduler, Supervision)
    ParkKind | Parked | Pending | Observer | Task | Bucket | Dispatcher
    RunFiber; RunFiber.toCore, toSup, make, park
    WithFiberAction; RunEvent; Race; RunMachine St; RunDecision; RunInterp St
    interruptRecord, countdownPark, spawn, start, linkScope, iteration (finalizerOr,
    stepFrame, finishFrame, withFiber, interruptThenJoin), fireObserver, exitFiber
    Cmd; drive; stepDecision (fire, flushAll); replayEval; Step
    runFork, runCallback, runSyncExit, promiseOutcome; RunMachine.toSched, finished, empty

Deep.Stores  (S2)                            (imports Deep.Fibers, Scope)
    RefHeap, DeferredStore, ScopeStore, Stores; the RunInterp instance at Name/Thunk/Val
Deep.ForkFlow (S3)                           (imports Deep.Fibers, RegionSimulation, ScriptFlow)
    the fiber profile's OpSpec rows; compileForkAt; the root refusal; WellSourced;
    the decision partition; the per-fiber-sum fuel bound
Deep.Witnesses (S2)                          the Pass A witnesses, executable

Theorems (landing):
    step equations, one per rc.112 arm; exit_unique, observers_cleared_once,
    running_restored, ids_fresh, parked_not_running; the five forbidden examples unreachable
    toSup_exitFiber_publish, toSched_step_stepEval; single_fiber_eq_frameFiber_run
    interrupt_only_at_interruptible_point, masked_cause_delivered_at_unmask,
    finalizer_runs_once, decision_kinds_separated (sitesSeparated shape)
    adequacy over the traced service under the masks; fuel bound as a sum over live fibers
    state_threaded_out_on_failure (DB-07); oracle form as a corollary (statelessRun)
```

## 5. Obligation ledger

| Kind | Obligation | Falsified by |
| --- | --- | --- |
| step equations | one per source arm, cited by `effect.ts` line in the docstring, as the census rows are | a reviewer reading the cited lines and the arm side by side |
| invariants | at most one exit; observers cleared exactly once; `running` restored; fresh ids; a parked fiber is not running | a reachable machine state violating one |
| projection | one fiber, no fork, no async: `replayEval` equals `FrameFiber.run` | a single-fiber program with different exits under the two |
| projection | `P : RunMachine → Scheduler.Machine` maps `Step` to the old `stepEval` where defined | an old theorem that fails to follow from the new one via `P` |
| adequacy, Abadi-Plotkin shape | for a compatible tape the machine's service-level trace equals the traced service's, under the existing masks | a Fibers golden whose tape reproduces the host and whose machine trace differs |
| masks, Marlow et al. shape | an interrupt is applied only at an interruptible point; a masked fiber's pending cause is delivered at the unmask frame; a finalizer runs exactly once | the existing counterexample rows `E4-RUN-CE-025/026` re-run against the machine |
| negative | the five forbidden examples are unreachable from any well-formed start | a `decide` witness reaching one |
| trust boundary | `PrimInterp` and `RunInterp` are parameters; the tape is data; the host is evidence | any theorem whose statement mentions the host |

## 6. Handoffs

- To `$lean-algebraic-systems`: the carriers above are the system-model record's inputs; the
  composition is monadic bind at the frame level (already) and a labelled transition relation
  at the machine level; two interpreters exist from day one, `replayEval` (simulator) and the
  trace projection (analyzer), with `FrameFiber.run` as the third.
- To `$lean-model-invariants`: `RunFiber` well-formedness (a parked fiber is not running; an
  exited fiber has no children, no stack, no observers) as a structure of `Prop` fields, the
  `Scope.WellFormed` shape.
- To Pass B, after modelling: freeze the signatures of R1 first, R2 second; Q1 to Q5 answered
  or carried as named hypotheses with their downstream consequence written down.
