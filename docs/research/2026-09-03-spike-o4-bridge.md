# Spike O4: the bridge note — `OCaml5.Machine` against `Deep.RunFiber`

Date: 2026-09-03. Base commit `3e2b919` (spike O1). Plan:
`docs/research/2026-09-03-ocaml5-deep-plan.md` §3 row O4. Companions:
`2026-09-03-ocaml-jsoo-relevance.md` (§2, the goal A / goal B split),
`2026-09-03-deep-plan.md` (§0–§1, the Effect4 reference fiber machine),
`2026-09-03-spike-o1-runtime-machine.md` (the machine this note reads).

**Goal A**, prose only: what "OCaml as an execution backend for Effect4" would cost, carrier
by carrier. Effect4 is **not** the reference for `OCaml5.Machine` (O1 rule 2), and nothing
here changes either model. `D` = `workshop/Deep/Fibers.lean`, `R` =
`Effect4/Runtime/Runtime.lean`, `O` = `workshop/OCaml5/Effect.lean`.

## 1. The carrier table

| Deep carrier | OCaml5 counterpart | Verdict | Why |
| --- | --- | --- | --- |
| `RunFiber` (`D:157`, 15 fields) | `StackInfo` (`O:277`), a slot of `Machine.stacks` (`O:336`) | weaker | A stack is frames plus a handler triple plus a parent and nothing else: no exit, observers, children, dispatcher, context, op counter or budget. |
| `FrameFiber.current` (`R:271`) | `Machine.control` (`O:339`), `Control` (`O:283-286`) | same shape | One slot naming what is being stepped; OCaml splits it three ways (`eval`/`ret`/`throw`) where `Prim` carries exits as `success`/`failure`. |
| `FrameFiber.stack` (`R:273`) | `StackInfo.frames` (`O:278`) through `Machine.frames` (`O:396`) | stronger | Same top-first frame list, but the OCaml stack is itself a first-class value (`Value.stack`, `O:186`) that `perform` captures whole, traps included (`Frame.trap`, `O:242`); no Effect carrier can capture `FrameFiber.stack`. |
| `FrameFiber.interruptible` (`R:275`) | nothing | nothing | The runtime has no asynchronous interrupt, so a stack carries no mask bit. |
| `FrameFiber.interruptedCause` (`R:277`) | nothing | nothing | No cause is ever recorded on a stack from outside it. |
| `FrameFiber.deferredInterrupt` (`R:279`) | nothing | nothing | Nothing can arrive while a stack runs, so there is nothing to defer. |
| `Prim.yieldNowWith` (`R:134`) | nothing | nothing | There is no queue to re-enter; `perform` switches to the parent immediately. |
| `Prim.async` (`R:141`) | `Term.perform` (`O:149`), `doPerform` (`O:467`), `takeCont` (`O:445`) | same shape | Both suspend and hand a one-shot token to whoever will answer; the `withSignal`/`cancel` half of `async` has no counterpart. |
| `Prim.asyncFinalizer` (`R:146`) | `Frame.trap` (`O:242`), `stepThrow` trap arm (`O:753-757`) | weaker | A trap catches on its own stack and runs a handler; it has no `contAll` masking (`R:639-647`) and cannot ask whether the cause carries an interrupt (`R:874-881`). |
| `ParkKind` (`D:56`) | nothing | nothing | Join/await names another fiber's exit; OCaml has no second fiber to observe. |
| `Parked` (`D:62`) | `Machine.conts` (`O:337`), `takeCont` (`O:445`) | same shape | `withGuard token` and a `Cont_tag` block nulled on use are the same one-shot guard; the difference is where it lives — on the parked fiber, versus in a heap block the handler holds. |
| `Pending` (`D:81`) | `Machine.conts` entry (`O:337`) | weaker | The `token` field has a counterpart; `waitingOn`, `remaining`, `collected` and `resumeWith` (`Resume`, `D:68`) have none. |
| `Observer` (`D:93`, six shapes) | `StackHandler.handleValue`/`handleExn` (`O:269-270`), fired by `doReturnToParent`/`doRaiseToParent` (`O:553`, `O:562`) | weaker | Exactly one value-observer and one exception-observer per stack, fixed at `caml_alloc_stack` (`O:569`) and never appended to; there is no table and no third shape. |
| `Task` (`D:104`) | nothing | nothing | Nothing is ever enqueued; every switch is immediate. |
| `Bucket` (`D:110`) | nothing | nothing | No priorities exist in the runtime. |
| `Dispatcher` (`D:117`) | nothing | nothing | `run` (`O:770`) is a bare fuel loop over `step`; there is no armed host callback. |
| `WithFiberAction` (`D:258`, 18 arms) | `Term.allocStack` + `Term.runstack` (`O:162`, `O:155`), `doAllocStack`/`doRunstack` (`O:569`, `O:505`) | weaker | Only "make a fresh stack and run something on it" exists, and it is synchronous — the parent is suspended under it; the other seventeen arms have nothing. |
| `Race` (`D:339`) | nothing | nothing | No concurrent entrants, so no settlement bookkeeping. |
| `RunEvent` (`D:305`) | `Event` (`O:291`) | same shape | Both are a decidable trace alphabet with one constructor per transition; the alphabets differ because OCaml's names no second fiber. |
| `Stuck` (`D:332`) | `Outcome.stuck` (`O:326`) | weaker | One nullary constructor with no reason, where `Stuck` names the unknown fiber or scope. |
| `RunMachine` (`D:349`) | `Machine` (`O:334`) | same shape | A first-order process record: current locus, population (`fibers` vs `stacks`), fresh-name counters (`nextId`/`nextToken` vs `freshStack`/`freshCont`, `O:361`, `O:363`), a store slot (`state : St` vs `cell`), a trace. |
| `RunDecision` (`D:362`) | nothing | nothing | `run` is deterministic given fuel; nothing external can answer a park, fire a dispatcher or deliver an interrupt. |
| `RunInterp` (`D:386`) | nothing | nothing | OCaml5 stores terms in values (`Value.closure`, `O:177`), so meanings live in the machine rather than in a parameter record, and there is no store interface. |
| `interruptRecord` (`D:550`) | `Stdlib.deepDiscontinue` (`O:1205`) over `doResume` (`O:494`) | weaker | Throwing into a captured continuation matches the parked branch (`D:591-594`); the running/defer branch, the mask test and the cause accumulation have nothing. |
| `countdownPark` (`D:576`) | nothing | nothing | Nothing awaits several terminations at once. |
| `iteration` (`D:683`) | `step` (`O:762`) | weaker | One transition of the term machine, matching only `iteration`'s `stepFrame` delegation; the op counter, the yield injection, the three parks and the `withFiber` arms have nothing. |
| `exitFiber` (`D:992`) | `doReturnToParent` (`O:553`), theorem `doReturnToParent_handler` (`O:1092`) | weaker | A stack that ends frees itself and calls its own `handle_value` on the parent — the "store the exit, fire the observer" half; the children-interrupt-and-await prologue has nothing. |
| `fireObserver` (`D:923`) | `doReturnToParent` / `doRaiseToParent` (`O:553`, `O:562`) | weaker | Firing is arity one and built into the runtime; no observer list, no index order, no resulting resume commands. |
| `Cmd` (`D:526`) | nothing | nothing | There is no queue of synchronous nested work: a switch is a `setCurrent` (`O:389`). |
| `drive` (`D:1025`) | `run` (`O:770`) | weaker | Same fuel-bounded loop, but over one relation with no command list; with a single current stack the stale-local problem `drive` guards against cannot arise. |
| `stepDecision` (`D:1108`) | nothing | nothing | There are no host decisions to step. |
| `replayEval` (`D:1164`) | nothing | nothing | No tape; `run` takes fuel and a start state only. |
| `runFork` (`D:1184`) | `Machine.start` (`O:348`) + `run` (`O:770`) | weaker | A root stack over a closed term run synchronously; no fiber handle is answered and there is no abort signal. |
| `runCallback` (`D:1194`) | nothing | nothing | No callback key, and the root stack's triple can never be called (`O:331-333`, `O:350`). |
| `runSyncExit` (`D:1205`) | `run` (`O:770`) into `Outcome` (`O:323`) | weaker | The exit projection is there; there is no flush and no `AsyncFiberError`, because unfinished means only that fuel ran out. |
| `promiseOutcome` (`D:1216`) | `Outcome.value` / `Outcome.uncaught` (`O:324-325`) | same shape | A two-way projection of a finished run; Effect squashes a `Cause`, OCaml's error is already one exception value. |
| `RunFiber.toSup` (`D:221`) | nothing | nothing | There is no supervision view to project onto. |
| `RunMachine.toSched` (`D:491`) | `Machine.rows` (`O:779`) | same shape | A `filterMap` of the trace onto a coarser alphabet, for comparison with something outside the machine. |

**Counts.** same shape 7, stronger 1, weaker 13, nothing 17; 38 rows.

## 2. What an OCaml backend for Effect4 would have to add

Every `nothing`/`weaker` row, with the rc.112 mechanism the deep plan pins it to
(`2026-09-03-deep-plan.md:73-88`) and whether OCaml 5 effects can express it natively.

| Carrier | rc.112 mechanism | Native, or host state |
| --- | --- | --- |
| `RunFiber` | `FiberImpl` (`:505-555`, plan `:76`) | Host state: a record per fiber, keyed by id, outside the effect system; only its frame half is a stack. |
| `FrameFiber.interruptible` / `interruptedCause` / `deferredInterrupt` | the mask fields (`R:275-279`; `:574-595`, plan `:81`) | Host state, necessarily: OCaml has no asynchronous interrupt, so masking is a handler-side flag the scheduler consults, never a runtime property. |
| `Prim.yieldNowWith` | `yieldNowWith` (`:982-994`, plan `:73`) | Native: a `Yield` effect whose handler enqueues the continuation at the given priority and returns to the scheduler loop. |
| `Prim.asyncFinalizer` | the parking finalizer (`:1145-1160`, plan `:81`) | Host state: `discontinue` can deliver the cause, but the "mask, then run the cancel only if the cause carries an interrupt" decision is a scheduler-side test on a `Cause` the runtime does not model. |
| `ParkKind`, `Pending` (beyond the token) | `fiberJoin`/`fiberAwait` (`:5291`, `:5304`), `:1109-1143`, plan `:73` | Native for the park, host for the bookkeeping: `perform (Join f)` parks, but `waitingOn`/`remaining`/`collected` are a scheduler table. |
| `Observer` | the six `addObserver` shapes (`:561-565`, `:5281`, `:5370`, plan `:74`) | Host state: a handler-side table from fiber id to observer list; the stack triple is arity one and fixed at allocation. |
| `Task`, `Bucket`, `Dispatcher` | `:986`, `:5277`, `Scheduler.ts:105-233` (plan `:75`) | Host state: a scheduler loop over parked continuations, with the priority buckets and the armed flag in OCaml data, not in the runtime. |
| `WithFiberAction` fork arms (`fork`, `forkIn`, `forkScoped`, `runIn`) | `:5264-5284`, `:5364-5378`, `:5400-5406`, `:5447-5461` (plan `:78`) | Native: a fork is a fresh stack (`caml_alloc_stack`) entered under the scheduler's handler; the scope linkage and the key-dropping observer are host state. |
| `WithFiberAction` interrupt arms (`interrupt`, `interruptScoped`, `interruptAll`) | `:859`, `:895`, `:913` (plan `:78`) | Native at a park: `discontinue k cause` on the target's stored continuation; not native for a running target, which must reach an interrupt point first. |
| `WithFiberAction` await arms (`awaitAll`, `snapshotChildren`, `awaitNewChildren`) | `:5318-5322` (plan `:78`) | Host state: a countdown over observer firings in the scheduler. |
| `WithFiberAction` context arms (`setContext`, `getContext`, `getId`, `closeScope`) | `:709-727`, `:1147` (plan `:78`) | Host state: per-fiber context and the scope store; expressible as effects, but their meaning is a table. |
| `Race` | rc.112 `raceAll` (plan `:79`) | Host state: entrants are forks, but the settlement, the skip-once-settled rule and the loser cleanup are scheduler bookkeeping. |
| `Stuck` | DB-04's observable frontier (plan `:80`) | Host state: a scheduler-side error value; `Outcome.stuck` carries no reason. |
| `RunDecision` | `fire`, `flush`, `evaluate`, `yieldVerdict`, `answerAsync`, `interruptFrom`, `installMiddleware` (Pass A §1, plan `:80`) | Host state: the tape is the host's, by construction — it is exactly what the runtime leaves to the caller. |
| `RunInterp` | the store interface and minted values (plan `:80`) | Host state, but cheaper: OCaml closures can carry the meanings `RunInterp` parameterises, at the cost of leaving the first-order discipline. |
| `interruptRecord` | `:574-595`, `:1147-1160` (plan `:81`) | Half native: `discontinue` at a park; the record-always/defer-if-running/accumulate-the-cause logic is host state. |
| `countdownPark` | `:561-562`, `:5318-5322` (plan `:82`) | Host state: one counter and one exit list per park, in the scheduler. |
| `iteration` | one `runLoop` iteration (`:638-668`, plan `:83`) | Mixed: the frame step is the OCaml term machine; the op counter, yield injection and park dispatch are the scheduler's loop body. |
| `exitFiber`, `fireObserver` | `:611-627`, `:1121` (plan `:84`) | Half native: `handle_value`/`handle_exn` fire on the parent when a stack ends, which is the hook; the observer list, the middleware latch and the children prologue are host state. |
| `Cmd`, `drive` | `:599-628` (plan `:85`) | Host state: the command list and the re-read-from-the-machine discipline are the scheduler's. |
| `stepDecision`, `replayEval` | `Scheduler.ts:207-233` (plan `:86`) | Host state: replay over a decision tape is a property of the model, not of the runtime. |
| `runFork`, `runCallback`, `runSyncExit` | `:5410-5530` (plan `:87`) | Host state: entry points over the scheduler; `runstack` supplies only the synchronous root. |
| `RunFiber.toSup` | the computed supervision view (plan `:77`) | Host state: a projection of the scheduler's own tables. |

The bill's shape: **fork, join, yield and interrupt-at-a-park are native**; everything that
makes rc.112 a *runtime* — dispatcher, observer tables, races, countdowns, masks, decision
tape — is host state written in OCaml above the effect system. This matches the relevance
note's finding for the Rocq machine (§2 there): the deep plan's centre of gravity is exactly
the part OCaml does not give away.

## 3. What Effect4 could take from the OCaml model

**One-shot as a heap index.** `Parked.withGuard token` (`D:63`) is a guard *on the fiber*:
`drive`'s `Cmd.resume` arm compares `parkedToken = token` and drops a resume that does not
match, and drops any resume at all once `parked = Parked.notParked` (`D:1067-1082`). OCaml
puts the guard in the object passed around: `takeCont` nulls the field and answers the null
stack forever after (`O:445-450`), so a *stale holder* cannot resume even after the fiber
re-parks on a fresh token. Effect's spelling admits token reuse in principle, `nextToken`
being the only thing keeping tokens apart (`D:354`). A cheap hardening: make the pending
entry, not the fiber, the thing consumed.

**Per-stack traps versus the `contE` arm.** OCaml traps live on the stack they were pushed
on (plan rule 5; `Frame.trap`, `O:242`; `stepThrow`, `O:740-757`), so a captured continuation
carries its own handlers and a raise walks *this* stack's frames before reaching the parent.
Effect's `contE` walk (`R:864-895`) has the same shape and two powers OCaml lacks: `contAll`
runs on every passed frame (`R:631`), and the arm can read the cause (`R:874-881`). Nothing
to take — the shapes coincide and Effect's is the richer one.

**Reperform versus the absence of forwarding.** `doReperform` (`O:520`) lets a handler that
does not know an effect pass it outward, splicing its own stack onto the continuation's chain
(`doReperform_chain`, `O:1031`), and `doResume` then re-roots the *outermost* captured stack
while switching to the *innermost* (`doResumeStack_outermost_parent`, `O:1058`). Effect has
no analogue and needs none: a fiber has one runtime, not a chain of handlers, so there is
nothing to forward to. A deliberate difference, not a gap — but an OCaml backend must ensure
the scheduler handler is the *only* handler, or `reperform` becomes an observable Effect's
model cannot see.

**`handle_exn` on the parent versus `exitFiber`.** Both say "when this computation ends,
somebody else runs code, on their own stack, with the result". OCaml fixes that somebody at
allocation and has the runtime call it (`doRaiseToParent_handler`, `O:1121`); Effect stores
an exit and fires a list (`D:1010-1020`). OCaml's is the stronger invariant — it cannot leak,
cannot fire twice, and frees the stack first (`doReturnToParent_frees`, `O:1078`) — and it is
what an Effect4 theorem about `exitFiber` firing each observer exactly once would look like.

**The `parkOf` debt.** The deep plan records one representational debt: until `Prim` has the
park constructors, a join/await park is recognised by a predicate, `RunInterp.parkOf`
(`D:389-393`; plan `:90-92`), which S1 closes. OCaml has **no analogue** of the debt, and that
is the point: every park is a term constructor (`Term.perform`, `O:149`) and `stepEval`
dispatches on it, so no predicate can disagree with the syntax. `OCaml5.Machine` is the
"after" picture of S1, and is worth citing as evidence that the S1 shape is the right one.

## 4. One theorem, and whether to extract a shared carrier

Both machines state, or want to state, the same theorem: **a captured resume is consumed
once**. OCaml has it twice over, as `takeCont_twice` (`O:947`: however many times a
continuation is taken, only the first answer is a stack) and `doResume_null` (`O:970`:
resuming a taken handle raises and changes nothing else), and witness `w02-double-resume`
executes it on three hosts. Deep has the *mechanism* — the token compare and the `notParked`
fallthrough in `drive` (`D:1067-1082`) — and no theorem; `Fibers.lean` closes with three
decidable-equality gates only (`D:1225-1238`).

Extracting a common abstract "fiber stack with handler triple" carrier would be **premature,
and I recommend against it**. Three reasons. The arithmetic: 8 of 38 rows agree and 17 are
`nothing`, so a shared carrier abstracts the small part and says nothing about the part a
backend decision turns on. The agreements are not the same agreement: Effect's population is
a list of fiber records each owning its frames, OCaml's a heap of stacks with one global
`control` (`O:339`), so a common carrier must first quotient one by a re-indexing — and that
re-indexing is the work, not the carrier. And both models are still moving: S1 changes `Prim`
and deletes `parkOf`, O5 adds the tail-position admission clause.

What *is* worth doing is small and concrete: at the S1 landing, state the one-shot lemma on
the Deep side in the shape `takeCont_twice` already has — "a second `Cmd.resume` on a
consumed token leaves the machine unchanged" — so the one property both machines share is a
theorem in both. If a goal-A backend is ever costed for real, that lemma is the first thing a
simulation argument would need, and it makes the shared carrier's price visible before
anybody pays it.
