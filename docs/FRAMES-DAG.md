# Frame-machine runtime proof DAG

Status: breaker-frozen, RED, 2026-09-02

This document is the bounded ownership and proof graph for the Effect v4
continuation-stack machine as a first-order model: primitives as frames, the
stack, `getCont`, popping, handler skipping under interruption, mask frames, and
finalizer bracketing. It is not an Effect compatibility claim, not a run loop,
not a scheduler, not a fiber tree, and not a cutover approval.
`Effect4/Runtime/Runtime.lean` remains an annotation-only stub until the red
contract in `test/contracts/frames.contract.md` has an independently implemented
green proof graph.

The pinned source is `effect@4.0.0-rc.112` as vendored under
`vendor/effect-4.0.0-rc.112/src/`. Its reading is
`docs/effect-rc112-fiber-runtime.html` sections 1-4.

## Module placement

The builder's module is **`Effect4/Runtime/Runtime.lean`**, chosen over
`Effect4/Runtime/Lifecycle.lean`. `docs/ARCHITECTURE.md` gives `Effect4/Runtime`
"interpreters, scopes, managed runtimes and execution boundaries"; the stub
docstring of `Runtime.lean` reads "Owner: Reference execution runtime", which is
exactly what a frame machine is. `Lifecycle.lean` reads "Owner: Runtime state
and disposal laws", which is the managed-runtime disposal row, a different
owner. `Lifecycle.lean` stays an untouched stub.

## Scope

The packet contains only the polynomial information needed to state the
thirty-one Effect runtime census rows named below, relative to the four cause
alphabets already owned by `Effect4/Semantics/Cause.lean` and two new externally
admitted alphabets:

- `ν` — the **continuation name**. rc.112 stores JavaScript closures in the
  three continuation slots: `onSuccess[contA] = f` (`internal/effect.ts:1682`),
  `onFailure[contE] = f` (`:2492`), the two arms `matchCauseEffect` assigns
  (`:3452-3456`), the `OnExit` finalizer `this[args][1]` (`:4021`), the
  generator behind `Iterator` (`:1363`), and the `while`/`body`/`step` thunks of
  `whileLoop` (`:4624-4645`). DB-02 forbids a Lean closure in canonical program
  content, so a slot stores a nominal `ν` and nothing else.
- `σ` — the **thunk name**, for `sync`, `suspend` and `withFiber`, whose one
  argument is a `LazyArg` or a `(fiber) => Effect`.

What a name *does* is supplied by one parameter, `PrimInterp`, exactly the way
`Effect4.Scope.close` takes its `run`.

**Why the interpretation is a supplied record and not stored fields, a relation,
or a family of constructors.** Four shapes were considered.

1. *Stored closures.* `Prim.onSuccess (body : Prim) (contA : β -> Prim)` is
   precisely what DB-02 excludes: `Prim` would carry Lean function data, so it
   would have no decidable equality, no serialisable spelling, and no
   first-order identity, and the whole `frame-arm` census family would become a
   statement about Lean functions rather than about frames. Rejected.
2. *A relation.* `ContA : ν -> β -> Prim -> Prop` supplied as a parameter would
   let a later packet model a nondeterministic continuation. Nothing in the
   pinned stack code is nondeterministic: `cont[contA](value, fiber)` is one
   call producing one primitive. A relation would turn every pop law into an
   existential over an unconstrained witness and would state *less* about rc.112
   than a function does. Rejected for this packet, and recoverable later: DB-03
   keeps meaning relational exactly where a decision source exists, and the
   decision source for a fiber is the scheduler, not the stack. This is the same
   ruling `docs/SCOPE-DAG.md` records for `run`.
3. *Loose function arguments.* Passing eleven functions to every operation, as
   the Scope packet passes one, would put eleven binders on every `step`
   ascription. Rejected on legibility alone; nothing semantic separates it from
   the record.
4. *One supplied record, chosen.* `PrimInterp` is passed to `Prim.armA`,
   `Prim.armE`, `FrameFiber.resumeValue`, `FrameFiber.resumeCause`,
   `FrameFiber.step` and `FrameFiber.run`. It never enters `Prim` or
   `FrameFiber`, so both keep `DecidableEq`, first-order content, and
   kernel-reducible ground receipts.

Two `PrimInterp` fields need their own justification.

- `iterNext : ν -> β -> List β × IterStep`. rc.112's `Iterator[contA]` is a
  `while (true)` loop that folds every `Success` exit the generator yields
  *inline*, without touching the stack, and stops at the first `done`, `Failure`
  exit, or non-Exit effect (`internal/effect.ts:1362-1377`). Re-deriving that
  loop in Lean would need either fuel — which DB-04 then makes a live frontier
  rather than a value, for a mechanism that is not a frontier — or a
  well-foundedness argument about an opaque generator, which is not available.
  The maximal inline run and the outcome that ended it are therefore supplied as
  first-order data. `Effect4.Prim.iterator_folds_inline` is the statement that
  earns this: the arm's result depends only on the outcome, so the folded values
  never reach the stack or become a current primitive, which is exactly what
  "folded inline" means and exactly what makes the fold skip the `getCont`
  checkpoints an intervening pop would provide. `E4-RUN-CE-018` is the attack.
- `notImplemented : δ`. rc.112's `makePrimitiveProto` installs
  `defaultEvaluate`, which returns
  `exitDie("Effect.evaluate: Not implemented")` (`internal/core.ts:378-380`), and
  `setInterruptible` declares no `evaluate`. A `SetInterruptible` primitive that
  is ever stepped as the current effect is therefore a defect, and the defect
  payload is an admitted `δ`. `Effect4.FrameFiber.step_setInterruptible_not_evaluable`
  is the frozen consequence; it is the sharpest possible form of "declares
  `contAll` only".

The packet supplies:

- a closed three-value continuation-slot alphabet with the two demandable arms
  separated from `contAll`;
- a fourteen-constructor primitive syntax, one constructor per pinned op in this
  packet's scope;
- the frame-arm matrix of the reference page's section 3, verbatim;
- the `contAll` ensure hook, the answer selection, and the pass trace;
- the two arms, with `OnExit` restoring through the already-owned
  `Effect4.Exit.restoreAfterFinalizer`;
- the fused `getCont`/`exitFailCause` pop loop, its deferred-interrupt answer,
  and its handler-skipping condition;
- the five-field fiber state, one-step function, bounded runner, and event
  trace; and
- the mask combinators and the stack side of `scoped` and `acquireRelease`.

It reuses `Effect4.Exit` and `Effect4.Cause` unchanged and mints no second exit
or cause carrier. Nothing here imports or mentions `Effect4/Concurrency/`.

## Required semantic separations

1. **This is not a second `FiberState`/`Machine`.**
   `Effect4/Concurrency/Scheduler.lean` owns `Effect4.Machine`,
   `Effect4.FiberState`, `Effect4.Step` and `Effect4.SchedulerDecision`: a
   *relational* scheduler over a fiber map, with statuses, masks, cleanup
   states, pending-interrupt bits, terminal observations and an event trace,
   whose meaning is a `Step` relation over `SchedulerDecision` tapes.
   `Effect4.FrameFiber` is a *single* fiber's continuation stack: five fields,
   no fiber id, no status, no map, no decision, and a total one-step function
   rather than a relation. The two are separate calculi with no conversion
   claimed in either direction, because they answer different questions — which
   fiber runs next, versus which frame answers the value this fiber just
   produced. A later packet that wants a fiber whose body is a frame machine
   must state that embedding explicitly; nothing here does.
2. **No dependency on Concurrency.** `Effect4/Runtime/Runtime.lean` imports
   `Effect4.Semantics.Exit` (hence `Effect4.Semantics.Cause`) and nothing else
   from Effect4. `docs/ARCHITECTURE.md` "Dependency direction" places Runtime
   above Semantics, and `Effect4/Concurrency/Supervision.lean` already depends on
   `Effect4/Runtime/Scope.lean`, so the edge runs Concurrency → Runtime. An
   import of `Effect4/Concurrency/Interrupt.lean` would reverse it.
3. **The mask vocabulary is shared by correspondence, not by carrier.**
   `Effect4.InterruptMask` (`unmasked | masked`) is the concurrency-side mask
   alphabet. Separation 2 forbids importing it here, so this model uses rc.112's
   own spelling: a `Bool` field `interruptible`, exactly as
   `FiberImpl.interruptible` (`internal/effect.ts:529`).
   `Effect4.FrameFiber.masked` is the named observation that carries the shared
   word, and the intended correspondence is
   `masked = true ↔ InterruptMask.masked`. That correspondence is **not claimed
   here**: it is a later bridge obligation, recorded as `FRAME-PG.bridges`, and
   it must be stated in whichever packet is allowed to see both carriers.
4. **A continuation is a name, not a computation.** DB-02 closes the pure
   fragment at the reification boundary, and DB-05's no-`HHandler` ruling is
   conditional on exactly this: a scoped operation stores stable first-order
   references, not actual subcomputations. `ν` is that name.
   `Effect4.Prim.withFiber_refused` and
   `Effect4.Prim.yieldableError_host_class_refused` are the theorem-shaped
   halves of the two boundaries where a name is not enough.
5. **The nested body is a subterm, and that is not a stored closure.**
   `Prim.onSuccess (body : Prim …) (onValue : ν)` stores the inner *effect* as a
   first-order subterm, which is what rc.112's `onSuccess[args] = self` holds
   (`internal/effect.ts:1680`). Only the continuation slot is nominal, because
   only the slot is a closure upstream. A subterm is inspectable, decidable and
   serialisable; a closure is none of those. The distinction is the whole
   content of DB-02 and is not blurred here.
6. **Refusal, frontier, defect and interruption remain distinct.**
   `FrameFiber.run` is a bounded runner: `FrameStep.running` at exhausted fuel is
   a live frontier under DB-04, never a failure, never a refusal, and never an
   interruption. This packet mints no refusal carrier and no frontier carrier.
7. **`FrameEvent` is not `Effect4.Event`.** `Effect4/Concurrency/Scheduler.lean`
   owns `Effect4.Event`, the scheduler's trace alphabet (fiber starts, mask
   entries, interrupt deliveries). `Effect4.FrameEvent` is the stack's trace
   alphabet (frames popped, `contAll` run, frames pushed, finalizers run,
   continuations substituted, the deferred answer, the yielded exit). They have
   no common constructor, no conversion and no shared owner; the same argument
   as separation 1 applies.
8. **The two loops are fused, deliberately.** rc.112 has two nested loops:
   `getCont`'s `while (true) { pop; contAll; answer? }`
   (`internal/effect.ts:688-697`) and `exitFailCause`'s
   `while (fiber.interruptible && fiber._interruptedCause && cont) cont = getCont(contE)`
   (`internal/core.ts:539-542`). `Effect4.FrameFiber.popFrom` is the two of them
   as one structural recursion over the stack, with `skipInterrupted` as a
   parameter. See "Where the fusion could diverge" below.

## Where the fusion could diverge

The fused loop and the two nested loops agree for every frame this packet
declares, and could disagree for one shape it does not.

- The inner loop re-runs `contAll` on every popped frame and stops as soon as a
  frame either returns a replacement or declares the demanded arm. The outer
  loop then discards that answer while the fiber is interruptible with a pending
  cause and calls `getCont` again. Fusing them means the discard happens in the
  same traversal, which is observationally identical as long as the discarded
  frame's `contAll` has already run — and it has, in both readings.
- The deferred-interrupt check sits at the top of `getCont`. With skipping on,
  rc.112 answers `deferredInterruptCont`, the outer loop sees a truthy `cont`
  and discards it, and the *next* `getCont` finds the flag already cleared. The
  fused loop therefore clears the flag and proceeds straight into the pop when
  `skipInterrupted` is set: `Effect4.FrameFiber.getCont_skip_clears_deferred`
  freezes that, and the discarded answer carried the same accumulated cause, so
  no observation is lost.
- **The one shape that could diverge.** A frame that *pushes during `contAll`*
  and *does not answer the demanded arm* would, in rc.112, have its pushed frame
  popped next; in the fused loop the push is threaded through the fiber and
  restored on top of the frames that are left. No frame in this packet is that
  shape: `OnExit` pushes and always answers both arms; `SetInterruptible` never
  pushes. The first frame that is that shape is `AsyncFinalizer`, which declares
  `contE` and `contAll` and no `contA` (`internal/effect.ts:1145-1160`), so a
  `contA` demand passes it, masks, and does not answer. `AsyncFinalizer` is
  explicitly out of this packet. The later run-loop and parking packet that adds
  it **must** revisit `popFrom` and either prove the fusion still agrees or
  unfuse the loops. This is recorded as `FRAME-FB-ASYNC-FINALIZER` and is the
  single most likely place for a reviewer to disagree with this model.

## Census rows this packet targets

Row summaries are the clauses that must become theorems. Take the exact text
from `generated/effect-runtime-census.tsv`. The "after the join" column is the
coverage state `Effect4Test/Audit/RuntimeCoverage.lean` should carry once a
later packet joins these witnesses, under the clause-by-clause rule in
`docs/RUNTIME-COVERAGE.md`. This packet writes no coverage row.

| Census row | Clauses this packet closes | Clauses left to another packet | After the join |
| --- | --- | --- | --- |
| `op.Success` | pops a `contA` frame and calls it with the value; with an empty stack yields itself as the Exit — `FrameFiber.step_success`, `resumeValue_frame`, `resumeValue_empty`, `getCont_empty_stack`, `step_ofExit_finishes` | none | **green** |
| `op.Failure` | pops `contE` frames skipping every one while the fiber is interrupted and interruptible; yields the Exit when none answers — `FrameFiber.step_failure`, `resumeCause_frame`, `resumeCause_empty`, `interrupt_skips_every_handler` | "annotates the cause with the current stack frame": `causeAnnotate` with `fiber.currentStackFrame` needs a fiber context and a `StackTrace` service key, neither of which this model carries | **partial** |
| `op.Sync` | runs the thunk, then behaves like `Success` with its result — `FrameFiber.step_sync`, and the `provided = none` argument that distinguishes `yieldWith(exitSucceed(value))` from `Success`'s `yieldWith(this)` | none | **green** |
| `op.Suspend` | returns the result of calling the thunk, with no stack interaction — `FrameFiber.step_suspend` | none | **green** |
| `op.WithFiber` | `foreignBoundary`: the raw `FiberImpl` is handed to a function — `FrameFiber.step_withFiber` models the effect it returns, `Prim.withFiber_refused` refuses the object identity | none; the boundary is closed by refusal, not by a model, exactly as `cause.annotations` is | **green** |
| `op.YieldableError` | `foreignBoundary`: `evaluate` is `exitFail(this)` — `FrameFiber.step_yieldableError` models the failure, `Prim.yieldableError_host_class_refused` refuses the host `Error` class identity | none; same shape | **green** |
| `op.Iterator` | drives the generator; an Exit yielded from it is folded inline; any other effect is pushed under this frame — `FrameFiber.step_iterator`, `Prim.armA_iterator_done`, `armA_iterator_halt`, `armA_iterator_resume`, `iteratorFolded_eq`, `iterator_folds_inline` | none | **green** |
| `op.OnSuccess` | pushes itself and returns the inner effect; the `contA` arm is assigned per instance — `FrameFiber.step_onSuccess`, `Prim.armA_onSuccess`, `onSuccess_arm_is_per_instance` | none | **green** |
| `op.OnFailure` | pushes itself and returns the inner effect; the `contE` arm is assigned per instance — `FrameFiber.step_onFailure`, `Prim.armE_onFailure`, `onFailure_arm_is_per_instance` | none | **green** |
| `op.OnSuccessAndFailure` | pushes itself and returns the inner effect; both arms are assigned per instance — `FrameFiber.step_onSuccessAndFailure`, `Prim.armA_onSuccessAndFailure`, `armE_onSuccessAndFailure`, `onSuccessAndFailure_arms_are_per_instance` | none | **green** |
| `op.Exit` | pushes itself; either arm resumes with the Exit value, reusing the exit argument the pop supplies when present — `FrameFiber.step_exitFrame`, `Prim.armA_exitFrame_provided`, `armA_exitFrame_none`, `armE_exitFrame_provided`, `armE_exitFrame_none` | none. `PrimInterp.reifyExit` is how an Exit becomes a value of the one value alphabet; rc.112's values are `unknown`, so every Exit is already a value there | **green** |
| `op.OnExit` | pushes itself; `contAll` masks the finalizer unless `args[2]` is true; either arm runs the finalizer then restores the original exit — `FrameFiber.step_onExit`, `Prim.ensure_onExit_masks`, `ensure_onExit_told_not_to`, `ensure_onExit_already_masked`, `armA_onExit`, `armE_onExit`, `onExit_finalizer_success_restores`, `onExit_finalizer_failure_merges`, `onExit_success_finalizer_failure` | none. The finalizer's own *effect* is collapsed to its outcome exit under `FRAME-FB-FINALIZER-EFFECT`, the same defunctionalization that makes `scope.add-after-closed` green | **green** |
| `op.SetInterruptible` | defines `contAll` only; restores the flag; when the fiber becomes interruptible with a pending cause, replaces the continuation with `failCause(cause)` — `Prim.arms_setInterruptible`, `ensure_setInterruptible_flag`, `ensure_setInterruptible_stack`, `ensure_setInterruptible_substitutes`, `ensure_setInterruptible_false_no_replacement`, `ensure_setInterruptible_no_pending`, `armA_setInterruptible_none`, `armE_setInterruptible_none`, `FrameFiber.step_setInterruptible_not_evaluable` | none | **green** |
| `op.While` | tests, pushes itself and runs the body; `contA` steps and re-tests until the predicate is false — `FrameFiber.step_whileLoop_true`, `step_whileLoop_false`, `Prim.armA_whileLoop_continue`, `armA_whileLoop_stop` | none. rc.112 finishes with `exitVoid`; the abstract value alphabet has no distinguished void inhabitant, so the loop's terminal value is `PrimInterp.loopDone`, an admitted per-loop value | **green** |
| `frame-arm.OnSuccess` | answers `contA` only — `Prim.arms_onSuccess`, `armE_onSuccess_none`, `armA_isSome`, `armE_isSome`, `onSuccess_arm_is_per_instance` | none | **green** |
| `frame-arm.OnFailure` | answers `contE` only — `Prim.arms_onFailure`, `armA_onFailure_none`, `onFailure_arm_is_per_instance` | none | **green** |
| `frame-arm.OnSuccessAndFailure` | answers `contA` and `contE` — `Prim.arms_onSuccessAndFailure`, `onSuccessAndFailure_arms_are_per_instance` | none | **green** |
| `frame-arm.Exit` | declares `contA` and `contE` and no `contAll` — `Prim.arms_exitFrame`, `ensure_of_no_contAll` | none | **green** |
| `frame-arm.OnExit` | declares all three arms; `contAll` pushes `SetInterruptible(true)` and clears interruptible so the finalizer runs masked — `Prim.arms_onExit`, `ensure_onExit_masks`, `ensure_onExit_no_replacement`, `onExit_arm_is_per_frame` | none. The row's existing supervision witnesses stay; they are about a different carrier and neither packet supersedes the other | **green** (from `partial`) |
| `frame-arm.SetInterruptible` | declares `contAll` only and can return a replacement continuation used for either arm — `Prim.arms_setInterruptible`, `armA_setInterruptible_none`, `armE_setInterruptible_none`, `ensure_setInterruptible_substitutes`, `answerOf_replacement`, `FrameFiber.resumeValue_replacement`, `resumeCause_replacement` | none | **green** (from `partial`) |
| `frame-arm.While` | declares `contA` only, alongside its `evaluate` — `Prim.arms_whileLoop`, `armE_whileLoop_none`, `FrameFiber.step_whileLoop_true` | none | **green** |
| `frame-arm.Iterator` | declares `contA` only, and its `evaluate` delegates to that same `contA` — `Prim.arms_iterator`, `armE_iterator_none`, `FrameFiber.step_iterator` | none | **green** |
| `checkpoint.getcont-deferred` | `getCont` answers a deferred interrupt before touching the stack, returning a continuation whose both arms fail with the accumulated cause — `FrameFiber.getCont_deferred`, `getCont_deferred_pops_nothing`, `getCont_skip_clears_deferred`, `resumeValue_deferred`, `resumeCause_deferred`, `pendingCause_some`, `pendingCause_none` | none | **green** |
| `checkpoint.exit-failcause-skip` | while the fiber is interruptible with a pending cause, `exitFailCause` keeps popping `contE` frames, so every user error handler is skipped — `FrameFiber.interrupt_skips_every_handler`, `getCont_skip_of_no_pending_cause`, `popFrom_continue_answer` | none | **green** |
| `checkpoint.set-interruptible-contall` | a popped `SetInterruptible` frame that leaves the fiber interruptible with a pending cause substitutes `failCause(cause)` for both arms — `Prim.ensure_setInterruptible_substitutes`, `answerOf_replacement`, `FrameFiber.resumeValue_replacement`, `resumeCause_replacement` | none | **green** |
| `checkpoint.set-fiber-interruptible` | sets the flag, pushes the restoring frame, and returns an immediate failure when a cause is already pending — `FrameFiber.setFiberInterruptible_flag`, `setFiberInterruptible_pushes`, `setFiberInterruptible_immediate_failure`, `setFiberInterruptible_no_pending`, `interruptibleRegion_already`, `interruptibleRegion_masked` | none. The row's existing supervision witnesses stay | **green** (from `partial`) |
| `rule.frames-are-primitives` | a frame is selected by which of `contA`, `contE` and `contAll` it defines, and `contAll` runs on every frame passed during a pop, not only on the frame that answers — `Prim.isFrame_eq`, `isFrame_iff`, `hasArm_eq`, `non_frames_have_no_arms`, `armA_isSome`, `armE_isSome`, `answerOf_arm`, `answerOf_missing`, `answerOf_frame_eq`, `FrameFiber.getCont_answer_hasArm`, `popFrom_answer_hasArm`, `popFrom_ranContAll`, `getCont_ranContAll`, `passEvents_ranContAll`, `popFrom_popped_eq_events` | none | **green** |
| `rule.interrupt-bypasses-handlers` | once interrupted and interruptible, `Failure` skips every `contE` frame until a mask frame flips the flag or the stack empties — `FrameFiber.interrupt_skips_every_handler`, `getCont_mask_stops_skip`, `Prim.ensure_setInterruptible_flag`, `FrameFiber.step_failure` | none | **green** |
| `exit.success-failure` | "each is itself a primitive that can be stepped" — `Prim.ofExit`, `ofExit_asExit?`, `asExit?_success`, `asExit?_failure`, `asExit?_eq_some`, `ofExit_isFrame`, `FrameFiber.step_ofExit_finishes`, `run_zero`, `run_succ_finished`, `run_succ_running` | none; the two-constructor clause is already witnessed by the Cause/Exit packet | **green** (from `partial`) |
| `scope.scoped` | "through an `OnExit` frame" — `Prim.scopedFrame`, `scopedFrame_eq`, `scopedFrame_finalizer_masked`, `FrameFiber.step_scopedFrame` | "installs a fresh scope in the fiber context" and "restoring the previous context first": both need a fiber `Context` and `setContext`, which this packet does not model | **partial** |
| `scope.acquire-release` | "runs under `uninterruptibleMask`" and "restores interruptibility for the acquire only when asked" — `FrameFiber.uninterruptible_masks`, `uninterruptible_already_masked`, `uninterruptibleMask_eq`, `restoreAcquire_asked`, `restoreAcquire_not_asked`, `interruptibleRegion_already`, `interruptibleRegion_masked` | "with the captured context": `contextWith`/`provideContext` need a `Context` carrier | **partial** |

Twenty-eight rows are green-able and three stay `partial`. No row is claimed
green on a clause this packet does not have a theorem for. `op.Yield`,
`op.Async`, `op.AsyncFinalizer`, `checkpoint.runloop-top`,
`checkpoint.post-yield-cancel`, `rule.yield-is-overloaded` and
`rule.budget-per-runloop-entry` are **not** in this packet and must not be
touched by the join.

## Existing-type rows

Every row is native to this contract. None renames or copies an Effect
TypeScript or Foldlab carrier. `PORT-MANIFEST.md` "Effect TypeScript family
defaults" disposes of the continuation machine as a `separateCalculus`; every
row below inherits that disposition except the two `foreignBoundary` rows named
in the boundary table. `FRAME-PG` abbreviates the `FRAME-PG-STACK` graph defined
further down.

| Stable public type | Owning module | Kind | Relationship | Pin | Assurance route |
| --- | --- | --- | --- | --- | --- |
| `Effect4.Arm` | `Runtime/Runtime.lean` | canonical finite alphabet | the closed rc.112 continuation-slot alphabet; no other alphabet claims this role | `internal/core.ts:365-380` (`Primitive`), `Effect.ts` slot symbols | leaf receipts linked to `FRAME-PG.construction` |
| `Effect4.Prim` | `Runtime/Runtime.lean` | canonical carrier | canonical first-order primitive syntax; **not** `Effect4.Program` (a higher-order proof carrier, DB-01) and **not** `Effect4.CheckedFlow` (the general reifiable graph, DB-02) — this is the pinned rc.112 op family only, with no admission judgment, no block ids and no cycles | `internal/core.ts:365-563`, `internal/effect.ts:928-946, 1356-1379, 1662-1689, 2474-2501, 3426-3465, 3620-3637, 4001-4029, 4302-4367, 4623-4645` | `FRAME-PG` |
| `Effect4.IterStep` | `Runtime/Runtime.lean` | canonical finite alphabet | the three outcomes that stop a generator's inline fold | `internal/effect.ts:1362-1377` | leaf receipts linked to `FRAME-PG.construction` |
| `Effect4.PrimInterp` | `Runtime/Runtime.lean` | `separate-calculus` parameter record | the externally supplied meaning of a continuation name; a *parameter*, never canonical program content, and therefore carrying no `DecidableEq`. Sibling of the `run` argument of `Effect4.Scope.close` | `internal/effect.ts:1682, 2492, 3452-3456, 4021` | `FRAME-PG.semantics` |
| `Effect4.FrameFiber` | `Runtime/Runtime.lean` | canonical carrier | the single-fiber continuation state; `separate-calculus` from `Effect4.FiberState` and `Effect4.Machine` in `Effect4/Concurrency/Scheduler.lean` (a relational scheduler over a fiber map) — see separation 1. No conversion, embedding or erasure is claimed | `internal/effect.ts:505-550` (the five modelled fields only) | `FRAME-PG` |
| `Effect4.ContAnswer` | `Runtime/Runtime.lean` | canonical finite alphabet | what a pop answers: the deferred continuation, a replacement, the answering frame, or nothing | `internal/effect.ts:680-698, 737-744` | leaf receipts linked to `FRAME-PG.semantics` |
| `Effect4.FrameEvent` | `Runtime/Runtime.lean` | canonical finite alphabet | the stack's trace alphabet; `separate-calculus` from `Effect4.Event` in `Effect4/Concurrency/Scheduler.lean` — see separation 7 | authored; the trace is an Effect4 observation, not an rc.112 value | leaf receipts linked to `FRAME-PG.semantics` |
| `Effect4.FramePop` | `Runtime/Runtime.lean` | canonical carrier | the four observations of one pop | `internal/effect.ts:680-698` | `FRAME-PG.semantics` |
| `Effect4.FrameStep` | `Runtime/Runtime.lean` | canonical finite alphabet | one step either continues or finishes with an Exit; `FrameStep.running` at exhausted `run` fuel is a live frontier under DB-04, never a failure | `internal/effect.ts:653-668` | leaf receipts linked to `FRAME-PG.semantics` |
| `Effect4.Exit` | `Semantics/Exit.lean` | **reused, not re-declared** | already canonical, owned by `docs/CAUSE-DAG.md` `CAUSE-L4-EXIT`; this packet adds no arm, no view and no adapter, and `Prim.ofExit`/`Prim.asExit?` are the embedding both directions of `exit.success-failure`'s "each is itself a primitive" | `Exit.ts:118-157` | `CAUSE-PG-FLAT` (unchanged) |
| `Effect4.Cause` | `Semantics/Cause.lean` | **reused, not re-declared** | already canonical, owned by `docs/CAUSE-DAG.md` `CAUSE-L2-CAUSE`; the finalizer merge of `op.OnExit` is exactly `Effect4.Exit.restoreAfterFinalizer` over `Cause.combine` | `internal/core.ts:138-176`, `internal/effect.ts:3800-3804` | `CAUSE-PG-FLAT` (unchanged) |
| `Effect4.InterruptMask` | `Concurrency/Interrupt.lean` | **named, not imported** | the concurrency-side mask alphabet. Separation 3: the dependency direction forbids importing it, so this model uses rc.112's own `Bool`, and the correspondence is a later bridge obligation | `internal/effect.ts:529` | not claimed here |

The duplicate-prevention check run before freezing was

```sh
grep -rhE '^[[:space:]]*(inductive|structure|abbrev|def)[[:space:]]+[A-Za-z]' \
  Effect4 --include='*.lean' \
  | grep -oE '(inductive|structure|abbrev|def) [A-Za-z0-9_.?]+' \
  | grep -iE 'prim|frame|stack|cont|arm|fiber|machine|step|event|interp|iter' | sort -u
grep -rnE '^\s*namespace\s+(Prim|Arm|Frame[A-Za-z]*|ContAnswer|PrimInterp|IterStep)\b' \
  Effect4 --include='*.lean'
```

It found no `Prim`, `Arm`, `IterStep`, `PrimInterp`, `FrameFiber`, `ContAnswer`,
`FrameEvent`, `FramePop` or `FrameStep` declaration or namespace anywhere under
`Effect4/`. It did find `Effect4.Machine`, `Effect4.FiberState`, `Effect4.Step`,
`Effect4.StepResult` and `Effect4.Event` in `Effect4/Concurrency/Scheduler.lean`
and `Effect4.Supervision.Fiber` in `Effect4/Concurrency/Supervision.lean`;
separations 1 and 7 record why this packet is not a second spelling of any of
them, and why it deliberately does not reuse those names.

### Public declaration records

249 public declarations are frozen: nine types, forty-two constructors and
projections, thirty-four definitions, and one hundred and forty-nine theorems.
Six derived `DecidableEq` instances are available on the first-order carriers;
`PrimInterp` deliberately has none, because it stores functions. Per
`docs/AGENT-ROUTING.md` "Public declaration records", the routine constructors,
projections and theorems inherit their owner, disposition, duplicate-prevention
relationship and assurance route from the type row above them; the table below
records the ones that do not inherit cleanly, which is every definition plus the
two refusals.

| Declaration | Module | Role | Origin / disposition | Relationship | Assurance route |
| --- | --- | --- | --- | --- | --- |
| `Effect4.Arm.all`, `.demandable` | `Runtime/Runtime.lean` | the slot census, and the two slots `getCont` may demand | native; `getCont<S extends contA \| contE>` is a type-level restriction upstream and first-order data here | `derived` from `Effect4.Arm` | leaf receipts under `FRAME-PG.construction` |
| `Effect4.Prim.arms`, `.hasArm`, `.isFrame` | `Runtime/Runtime.lean` | the frame-arm matrix and the frame predicate | native; models the reference page's section 3 table | `canonical` observation of `Effect4.Prim` | `FRAME-PG.semantics` |
| `Effect4.Prim.ofExit`, `.asExit?` | `Runtime/Runtime.lean` | the embedding of an `Exit` as a primitive and its partial inverse | native; models `makeExit` (`internal/core.ts:472-516`) | `adapter` between `Effect4.Exit` and `Effect4.Prim`; not a second exit carrier and not a quotient | `FRAME-PG.representation` |
| `Effect4.Prim.ensure` | `Runtime/Runtime.lean` | rc.112's `[contAll](fiber)` | native | `canonical` transition of `Effect4.FrameFiber` | `FRAME-PG.semantics` |
| `Effect4.Prim.answerOf` | `Runtime/Runtime.lean` | which answer a popped frame gives | native; the `if (cont) … if (op[symbol])` decision of `internal/effect.ts:692-696` | `canonical`; exists so "a frame is selected by which arms it defines" is a statement rather than a comment | `FRAME-PG.laws` |
| `Effect4.Prim.passEvents`, `.finalizerEvents` | `Runtime/Runtime.lean` | the trace one pop and one answering arm leave | native; authored observation | `helper` for `Effect4.FrameEvent` | `FRAME-PG.semantics` |
| `Effect4.Prim.armA`, `.armE` | `Runtime/Runtime.lean` | the two demandable arms, per frame | native | `canonical` | `FRAME-PG.laws` |
| `Effect4.Prim.iteratorFolded` | `Runtime/Runtime.lean` | the values a generator folds inline before it stops | native | `derived` from `PrimInterp.iterNext`; exists so `op.Iterator`'s "folded inline" clause is observable | `FRAME-PG.semantics` |
| `Effect4.Prim.scopedFrame` | `Runtime/Runtime.lean` | rc.112 `scoped`, stack side only: the body under one `OnExit` frame whose finalizer name stands for `scopeCloseUnsafe(scope, exit)` | native | `view` of `Effect4.Prim.onExit`; **not** a second `Effect4.Scope.runScoped`, which owns the scope side of the same census row and is not imported here | `FRAME-PG.laws` |
| `Effect4.FrameFiber.start` | `Runtime/Runtime.lean` | `new FiberImpl(context, true)`, restricted to the five modelled fields | native | `canonical` constructor | `FRAME-PG.construction` |
| `Effect4.FrameFiber.pendingCause`, `.masked`, `.interrupted` | `Runtime/Runtime.lean` | the accumulated cause read totally, the shared mask word, and the skip condition | native. `pendingCause` answers `Cause.empty` in the state rc.112 asserts unreachable with `_interruptedCause!`; `FRAME-FB-NONNULL` records that | `derived` from `Effect4.FrameFiber` | `FRAME-PG.semantics` |
| `Effect4.FrameFiber.popFrom` | `Runtime/Runtime.lean` | the fused pop loop | native; `internal/effect.ts:688-697` fused with `internal/core.ts:539-542` | `canonical`; public because every pop law is stated over it and because the fusion must be inspectable | `FRAME-PG.laws` |
| `Effect4.FrameFiber.getCont` | `Runtime/Runtime.lean` | rc.112's `getCont`, deferred answer included | native | `canonical` | `FRAME-PG.laws` |
| `Effect4.FrameFiber.uninterruptible`, `.setFiberInterruptible`, `.interruptibleRegion`, `.uninterruptibleMask`, `.restoreAcquire` | `Runtime/Runtime.lean` | the four mask combinators and the `restore` an `uninterruptibleMask` hands its body | native; `internal/effect.ts:4302-4367`. `interruptibleRegion` carries rc.112's `interruptible` because `Effect4.FrameFiber.interruptible` is already the field name | `canonical` transitions | `FRAME-PG.laws` |
| `Effect4.FrameFiber.resumeValue`, `.resumeCause` | `Runtime/Runtime.lean` | the pop-and-resume of a produced value and of a produced cause | native; the bodies of `exitSucceed[evaluate]` and `exitFailCause[evaluate]` | `canonical`; separate because only the failure path skips handlers | `FRAME-PG.laws` |
| `Effect4.FrameFiber.step` | `Runtime/Runtime.lean` | one machine step | native | `canonical`; a total function, not a relation — see "Determinism" below | `FRAME-PG.semantics` |
| `Effect4.FrameFiber.run` | `Runtime/Runtime.lean` | the bounded runner | native | `derived` from `step`; a DB-04 approximation, never a denotation | `FRAME-PG.laws` |
| `Effect4.FrameEvent.poppedFrame?`, `.finalizer?`, `.poppedFrames`, `.finalizersRun` | `Runtime/Runtime.lean` | the two trace projections the packet promises: what was popped and which finalizers ran | native | `derived` from `Effect4.FrameEvent` | `FRAME-PG.semantics` |
| `Effect4.Prim.withFiber_refused` | `Runtime/Runtime.lean` | the theorem-shaped refusal of the raw `FiberImpl` handover | native | `separate-calculus` boundary receipt, sibling of `Effect4.Scope.key_freshness_refused` | `FRAME-PG.bridges` |
| `Effect4.Prim.yieldableError_host_class_refused` | `Runtime/Runtime.lean` | the theorem-shaped refusal of the host `Error` class identity | native | `separate-calculus` boundary receipt, sibling of `Effect4.Reason.host_memory_refused` | `FRAME-PG.bridges` |

Auxiliary lemmas beyond the frozen list are permitted in the implementation but
must be `private`, so the generated declaration snapshot has no unannotated
public export. The reference implementation this packet was checked against
needed exactly three.

## Named boundary and refusal

| Boundary | Row | What is refused | Evidence |
| --- | --- | --- | --- |
| `FRAME-FB-RAW-FIBER` | `op.WithFiber` | `withFiber` hands its argument the raw `FiberImpl` (`internal/core.ts:555-563`), whose observable surface includes `_observers`, `_children`, `_dispatcher`, `_running`, `currentScheduler` and the whole `Context`. None of those is modelled. | `Effect4.Prim.withFiber_refused`: any Effect4 interpretation of a `WithFiber` body is a function of the modelled state, so two fibers agreeing on the five modelled fields get the same effect and the host distinction is not representable. `E4-RUN-CE-021` exhibits two host fibers that differ only outside the model. A theorem-shaped refusal, not a model of object identity. |
| `FRAME-FB-HOST-ERROR` | `op.YieldableError` | `YieldableError` is an `Error` subclass whose prototype is overwritten with a primitive proto and whose `toString` is deleted (`internal/core.ts:565-583`). The failing value *is* the host `Error`, carrying `message`, `stack`, `cause` and `instanceof` identity. | `Effect4.Prim.yieldableError_host_class_refused`: any Effect4 rendering is a function of the admitted error payload, so two host errors with equal payloads and different messages or stacks are one Effect4 cause. `E4-RUN-CE-021` exhibits the pair. The *behaviour* — `evaluate` is `exitFail(this)` — is modelled by `Effect4.FrameFiber.step_yieldableError`. |
| `FRAME-FB-FINALIZER-EFFECT` | `op.OnExit`, `frame-arm.OnExit`, `scope.scoped` | rc.112's `OnExit` arms return a *program*: `flatMap(eff, _ => exit)` on the success arm and `flatMap(combineFinalizerCause(exit, eff), _ => exit)` on the failure arm (`internal/effect.ts:4021-4027`). That program can push its own frames, park, or be interrupted. | Authored refusal row. DB-02 forbids storing the finalizer closure, so `PrimInterp.finalizerExit` supplies its *outcome exit* instead, exactly as `Effect4.Scope.close` supplies `run`. The composite is then literally `Effect4.Exit.restoreAfterFinalizer`, which is already owned and already proved. What is dropped is the finalizer's own frame activity; a packet that models a finalizer as a sub-execution must supersede this. This is the most arguable of the four green `OnExit`-family rows. |
| `FRAME-FB-STACK-ANNOTATION` | `op.Failure` | `exitFailCause[evaluate]` annotates the cause with `fiber.currentStackFrame` under `StackTraceKey` before popping, and passes `undefined` instead of `this` when it did (`internal/core.ts:531-546`). | Authored refusal row. `currentStackFrame` is a `Context` reference refreshed by `setContext`; no `Context` is modelled here. The consequence is recorded honestly: `op.Failure` stays **partial**, and the model always supplies the failure primitive as the pop's exit argument, which is rc.112's un-annotated branch. |
| `FRAME-FB-ASYNC-FINALIZER` | `checkpoint.exit-failcause-skip`, `rule.frames-are-primitives` | `AsyncFinalizer` declares `contE` and `contAll` and no `contA` (`internal/effect.ts:1145-1160`), so a `contA` demand runs its mask hook, pushes a restoring frame, and continues popping. It is the first frame that pushes during `contAll` without answering. | Authored refusal row, and an obligation on the next packet. `Effect4.FrameFiber.popFrom` fuses rc.112's two loops and restores `contAll` pushes on top of the frames that are left; that agrees with rc.112 for every frame declared here and must be re-derived when `AsyncFinalizer` lands. See "Where the fusion could diverge". |
| `FRAME-FB-NONNULL` | `checkpoint.getcont-deferred`, `checkpoint.set-interruptible-contall` | rc.112 reads the accumulated cause with the non-null assertion `fiber._interruptedCause!` in `deferredInterruptCont` (`internal/effect.ts:738-743`) and in `setInterruptible[contAll]` (`:4319`). | Authored refusal row. `Effect4.FrameFiber.pendingCause` is total and answers `Cause.empty` in the state the assertion claims is unreachable. `Effect4.FrameFiber.pendingCause_none` states that reading plainly rather than hiding it; the invariant that a deferred interrupt always has a cause is not proved here, because nothing in this packet *records* an interrupt — that is the supervision packet's `interrupt.unsafe-entry`. |
| `FRAME-FB-MASK-CARRIER` | `checkpoint.set-fiber-interruptible`, `frame-arm.SetInterruptible` | `Effect4.InterruptMask` is the project's mask alphabet and lives in `Effect4/Concurrency/`. | Authored separation, not a loss to rc.112: the model matches rc.112's own `Bool`. The obligation is the correspondence `FrameFiber.masked = true ↔ InterruptMask.masked`, which cannot be stated from this side of the dependency edge. Recorded on `FRAME-PG.bridges`. |

## Declaration and proof graph

```text
FRAME-L0-ARM ------------.
FRAME-L0-ITERSTEP -------|
                          v
                   FRAME-L1-PRIM
                          |
                          v
                   FRAME-L2-MATRIX
                    /           \
                   v             v
        FRAME-L3-ENSURE     FRAME-L3-ARMS
                   \             /
                    v           v
                   FRAME-L4-POP
                          |
                          v
                   FRAME-L5-STEP
                          |
                          v
                  FRAME-L6-BRACKETS
                          |
                          v
              FRAME-L7-COUNTEREXAMPLES
                          |
                          v
        FRAME-L8-COVERAGE-JOIN (later obligation)
                          |
                          v
        FRAME-L9-HOST-EVIDENCE (later obligation)
```

`FRAME-L0-ARM` and `FRAME-L0-ITERSTEP` close with local receipts and link to one
named parent edge each; they do not receive invented graphs. `FRAME-L1` through
`FRAME-L7` form one graph, `FRAME-PG-STACK`, because changing any of them
changes what a continuation *is*. The graph route is required, not optional:
this owner carries an interpreter, a recursive traversal invariant
(`popFrom_ranContAll`, `popFrom_popped_eq_events`), a protocol-state invariant
on the interruptible flag, and a nontrivial composition law between the pop and
the arms, all of which `docs/AGENT-ROUTING.md` "Assurance threshold" lists as
graph triggers.

`Effect4.Exit` and `Effect4.Cause` are **not** nodes of this graph. They are
closed by `CAUSE-PG-FLAT` and are consumed here unchanged; the only edges
between the graphs are that `Prim.armA`/`armE` on an `OnExit` frame are stated
over `Exit.restoreAfterFinalizer` and its already-green `Cause.combine`
receipts, and that `Prim.ofExit`/`asExit?` embed `Exit` into `Prim`.

## Node ownership

| Node | Production owner after dispatch | Required receipt |
| --- | --- | --- |
| `FRAME-L0-ARM` | `Effect4/Runtime/Runtime.lean` | three constructors, `Nodup`, `mem_all`, exhaustive cases, the demandable pair, `contAll` excluded from it, `DecidableEq`, `Repr` |
| `FRAME-L0-ITERSTEP` | `Effect4/Runtime/Runtime.lean` | three constructors and `DecidableEq` |
| `FRAME-L1-PRIM` | `Effect4/Runtime/Runtime.lean` | fourteen constructors; exhaustive cases; `DecidableEq` from the seven alphabets; the `Exit` embedding and its partial inverse; `PrimInterp`'s twelve fields |
| `FRAME-L2-MATRIX` | `Effect4/Runtime/Runtime.lean` | the eight frame equations of the reference page's section 3, the six non-frame equations, `hasArm`, `isFrame` and its characterisation |
| `FRAME-L3-ENSURE` | `Effect4/Runtime/Runtime.lean` | the no-`contAll` no-op; the three `OnExit` mask arms and its absent replacement; the four `SetInterruptible` arms; the answer selection and its inversion |
| `FRAME-L3-ARMS` | `Effect4/Runtime/Runtime.lean` | `armA`/`armE` definedness exactly on the declared arm; the per-instance arms of the three handler frames; the four `Exit`-frame arms; the two `OnExit` arms and their three restore laws; the two `While` arms; the three `Iterator` arms and the inline-fold independence law; the finalizer trace |
| `FRAME-L4-POP` | `Effect4/Runtime/Runtime.lean` | the deferred answer and that it pops nothing; the reduction of `getCont` to `popFrom`; the empty-stack answer; the four answering projections; the four continuing projections; that an answering frame declares the demanded arm; that `contAll` ran on every popped frame; that `popped` is the trace's popped frames; that the skip is inert without a pending cause; that with no mask frame the skip empties the stack; that a mask frame stops it |
| `FRAME-L5-STEP` | `Effect4/Runtime/Runtime.lean` | the four resume arms on each of the two paths; the fourteen `step` equations; that a bare `Exit` with an empty stack finishes; the three `run` equations |
| `FRAME-L6-BRACKETS` | `Effect4/Runtime/Runtime.lean` | the three `uninterruptible` laws; the four `setFiberInterruptible` laws; the two `interruptibleRegion` laws; the two `restoreAcquire` laws; the three `scopedFrame` laws |
| `FRAME-L7-COUNTEREXAMPLES` | `Effect4Test/Counterexamples/Runtime/Frames.lean` | twelve registered attacks, twenty-three proved witnesses, all within the axiom ceiling |
| `FRAME-L8-COVERAGE-JOIN` | `Effect4Test/Audit/RuntimeCoverage.lean` (not this packet) | later obligation; see below |
| `FRAME-L9-HOST-EVIDENCE` | a later Effect TypeScript conformance packet | later obligation; direct rc.112 runtime and type receipts |

## Graph-edge ledger

The graph-bearing owner is `FRAME-PG-STACK`. Passive leaves link to it; they do
not receive duplicate graphs.

| Edge | Breaker state | Reason and closure evidence |
| --- | --- | --- |
| identity | `required-open` | the exact public declaration snapshot plus the twelve existing-type rows above, three of which are reuse or naming rows for carriers this packet does not own; closed when the frozen battery's 249 ascriptions elaborate |
| construction | `required-open` | the nine carriers, the two finite alphabets' censuses, `PrimInterp`'s field list, and the derived `DecidableEq` instances |
| semantics | `required-open` | the observations this packet exposes: `Prim.arms`/`hasArm`/`isFrame`/`asExit?`/`iteratorFolded`, `FrameFiber.pendingCause`/`masked`/`interrupted`, `FramePop`'s four fields, and `FrameEvent.poppedFrames`/`finalizersRun`. `ensure`, `popFrom`, `resumeValue`, `resumeCause` and `step` are total functions; no relation and no fuel is claimed for any of them, and `run`'s fuel is an approximation under DB-04, not a denotation |
| laws | `required-open` | the matrix, ensure, arm, pop, skip, step and bracket theorem spine |
| representation | `required-open` | `Prim.ofExit_asExit?` and `asExit?_eq_some` are the claimed round trip; `popFrom_popped_eq_events` is the claimed normalization fact between the two pop observations. No serialization or wire round trip is claimed by this packet |
| counterexamples | `required-open` | all twelve `E4-RUN-CE-*` attacks have proved witnesses, but their repairs cannot close before implementation |
| bridges | `required-open` | `Effect4/Target/TypeScript/Simulation.lean` (P-T11) now projects `FrameEvent` finalizers and yielded exits into the service-level trace alphabet, and the patched rc.112 copy records `frame.pop`, `frame.deferred-interrupt`, `frame.exit-fail-cause.skip` and the scope-close arms per run (`harness/trace/receipts/patched/`); the correspondence between a recorded row and a `FrameEvent` is still unstated. The six `FRAME-FB-*` rows are the declared loss to the pinned host and the declared separations. Two are theorem-shaped; four are authored and stay open until a later packet either states or retires them, and `FRAME-FB-MASK-CARRIER` and `FRAME-FB-ASYNC-FINALIZER` are obligations on named later packets rather than losses. The `Exit`/`Cause` reuse is a consumption plus one declared adapter, `Prim.ofExit`/`asExit?` |
| targets | `not-applicable` | no TypeScript lowering, byte stability or runtime observation is claimed here. Refusing the raw fiber and the host `Error` class under `FRAME-FB-RAW-FIBER` and `FRAME-FB-HOST-ERROR` does not erase the semantic obligations above |
| trust | `required-open` | `#print axioms` receipts for all one hundred and forty-nine public theorems, in `Effect4Test/Runtime/FramesAxiomReport.lean`, within `propext`/`Quot.sound` |
| coverage | `required-open` | the frozen contract must join every exported declaration to one owner route, and the generated declaration snapshot must show no unannotated exported type |

No edge is omitted. `targets` is the only `not-applicable` row and it carries its
reason.

## The generated assurance join is a later obligation

This packet writes no generated projection and edits no file under `generated/`,
`Effect4Test/Audit/` or `Effect4Test/Concurrency/`, except that appending rows to
`test/counterexamples/REGISTER.md` and `test/counterexamples/runtime/ATTACKS.md`
changes an input digest pinned by `generated/fiber-assurance.tsv`. That
projection is **not** regenerated in this commit, because a concurrent lane owns
`scripts/generate-fiber-assurance.sh`; `./scripts/check-fiber-assurance.sh` will
report a stale projection until that lane lands and the generator is run once.
Three joins remain open after the builder turns the battery green:

1. **The Effect runtime coverage join.** A theorem in `Effect4/` moves no
   coverage number by itself. Each witness must be added to the matching row in
   `Effect4Test/Audit/RuntimeCoverage.lean` with its axiom receipt and its exact
   `#check (@name : proposition)` ascription, `snapshotWitnesses` must be
   extended in the same order, and `./scripts/check-effect-runtime-census.sh`
   must pass. `docs/RUNTIME-COVERAGE.md` owns the rules; that edit is a separate
   packet with a separate claim. The per-row table above states the expected
   states, not the achieved ones. The three rows that already carry supervision
   witnesses — `frame-arm.OnExit`, `frame-arm.SetInterruptible`,
   `checkpoint.set-fiber-interruptible` — keep them; this packet adds to those
   rows and supersedes nothing.
2. **The declaration and assurance snapshot.** The generated per-declaration
   assurance join must show every exported declaration of
   `Effect4/Runtime/Runtime.lean` resolving to exactly one of the routes in the
   existing-type and declaration-record tables. No such generator exists for
   `Effect4/Runtime/` today; standing one up, or extending an existing one, is
   the coverage edge's real closure condition.
3. **Host evidence.** `FRAME-L9` needs direct rc.112 runtime and type
   observations — in particular for the inline generator fold and for the
   `AsyncFinalizer` pop shape, both of which this model claims or defers and no
   Lean theorem can confirm about JavaScript.

Until those land, this graph may be reported as *breaker-frozen with an open
coverage edge*, never as a closed category and never as a coverage number.

## Determinism, totality, and claim boundary

Every operation in this packet is a total first-order function over finite data,
parameterised by one externally supplied record of total functions. There is no
relation, no choice and no decision source, and therefore no determinism theorem
to state: determinism is a property of the carrier here, not a result. This is
the deliberate complement of `Effect4/Concurrency/Scheduler.lean`, whose meaning
*is* relational because scheduling is a decision source (DB-03). The one place a
budget appears is `FrameFiber.run`, whose exhausted fuel is a live frontier under
DB-04 and is never reclassified as failure, defect, interruption or refusal.

Nothing here claims that `Effect4.Prim` is *equivalent* to rc.112's `Primitive`,
or that `Effect4.FrameFiber` is equivalent to `FiberImpl`. The claim is that each
named clause of each named census row in the per-row table has an exact theorem
over the Effect4 model, and that the six `FRAME-FB-*` rows name what was
deliberately dropped or deferred: the raw fiber handover, the host `Error` class,
the finalizer's own frame activity, the stack-frame cause annotation, the
`AsyncFinalizer` pop shape, and the mask-carrier correspondence.

Three of the thirty-one assigned rows are explicitly **partial**. Reporting any
of them green on the strength of this packet would be a false green.
