/-
Contract packet: `Test/contracts/frames.contract.md`

Breaker-owned red battery. The implementation phase must not edit this file.
It is red until `src/Effect4/Machine/Frames.lean` declares the frozen surface.

Owner-approved D7 constructor amendment, 2026-09-06: the frozen section 6 of
`docs/research/2026-09-06-p3-source-repairs.md` authorizes the constant
`OnSuccess` constructor, its exhaustive receipt and the local F11 checks below.

Until 2026-09-13 every public declaration was also frozen here by a hand-typed
`#check (@name : proposition)` copy of its statement; those copies were retired, since a
statement lives in its theorem and its change is that file's diff. What remains is what
only this battery says: the guards over named programs and the counterexample theorems. Names are written
fully qualified; this module deliberately does not `open Effect4`. Every theorem
carries a `census:` tag naming the `generated/effect-runtime-census.tsv` rows
it witnesses, which the builder carries into the declaration docstring.

Pinned source: `effect@4.0.0-rc.112` under `vendor/effect-4.0.0-rc.112/src/`.
Reading: `docs/effect-rc112-fiber-runtime.html` sections 1-4.
-/

import Effect4.Machine.Exit
import Effect4.Machine.Frames

set_option autoImplicit false

namespace Test.Runtime.FramesContract

universe u v

/-! F0: the three continuation slots (census: rule.frames-are-primitives).

rc.112 stores `contA`, `contE` and `contAll` on the primitive prototype, and
`getCont<S extends contA | contE>` can only ever demand the first two. The
alphabet is closed and carries no payload. -/

-- census: rule.frames-are-primitives

-- census: rule.frames-are-primitives

-- census: rule.frames-are-primitives

-- census: rule.frames-are-primitives

-- census: rule.frames-are-primitives

/-! F1: the primitive syntax (census: op.Success, op.Failure, op.Sync,
op.Suspend, op.WithFiber, op.YieldableError, op.Iterator, op.OnSuccess,
op.OnFailure, op.OnSuccessAndFailure, op.Exit, op.OnExit, op.SetInterruptible,
op.While, op.Yield, op.Async, op.AsyncFinalizer).

Eighteen data constructors represent seventeen pinned ops: `onSuccessConst`
is the constant instance of `OnSuccess` used by automatic yielding. `ν` is the
externally admitted continuation-name alphabet and `σ` the thunk-name alphabet.
A continuation is a nominal name or a constant program subterm, never a stored
Lean closure (DB-02). Nested bodies are first-order subterms.
`Yield`, `Async` and `AsyncFinalizer` were reserved for the run-loop and parking
packet and are here now, as first-order names. -/

-- census: rule.frames-are-primitives

/-! F1b: the generator outcome (census: op.Iterator, frame-arm.Iterator).

rc.112's `Iterator` frame drives a JavaScript generator in a `while (true)` loop
that folds every `Success` exit inline. The maximal run of inline values and the
outcome that ended it are supplied as first-order data by `PrimInterp.iterNext`;
`docs/research/FRAMES-DAG.md` records why. -/

/-! F1c: the externally supplied interpretation (census: op.Sync, op.Suspend,
op.Iterator, op.Exit, op.OnExit, op.While).

The one parameter that says what a name *does*, the same shape
`Effect4.Scope.close` takes for `run`. It never enters `Prim`, so a primitive
keeps first-order identity and decidable equality. -/

/-! F2: the fiber state this packet models (census: rule.frames-are-primitives).

Exactly five fields: the current primitive, the stack of frames, the
interruptible flag, the accumulated interruption cause, and the deferred flag.
No `_running`, `_yielded`, observers, children, budget or dispatcher: those
belong to the run-loop and supervision packets. -/

-- census: rule.frames-are-primitives

-- census: checkpoint.getcont-deferred

-- census: checkpoint.getcont-deferred

-- census: rule.frames-are-primitives

-- census: rule.frames-are-primitives

/-! F2b: what a pop answers, what it leaves in the trace, and what a step
produces (census: checkpoint.getcont-deferred, rule.frames-are-primitives). -/

-- census: rule.frames-are-primitives

-- census: rule.frames-are-primitives

-- census: rule.frames-are-primitives

-- census: rule.frames-are-primitives

-- census: rule.frames-are-primitives

/-! F3: the frame-arm matrix (census: frame-arm.OnSuccess, frame-arm.OnFailure,
frame-arm.OnSuccessAndFailure, frame-arm.Exit, frame-arm.OnExit,
frame-arm.SetInterruptible, frame-arm.While, frame-arm.Iterator,
rule.frames-are-primitives).

Frozen exactly as `docs/effect-rc112-fiber-runtime.html` section 3 states it. A
frame is selected by which arms it defines; the six non-frame primitives define
none and are never pushed. -/

-- census: rule.frames-are-primitives

-- census: rule.frames-are-primitives

-- census: rule.frames-are-primitives

-- census: frame-arm.OnSuccess

-- census: frame-arm.OnFailure

-- census: frame-arm.OnSuccessAndFailure

-- census: frame-arm.Exit

-- census: frame-arm.OnExit

-- census: frame-arm.SetInterruptible

-- census: frame-arm.While

-- census: frame-arm.Iterator

-- census: frame-arm.AsyncFinalizer

-- census: frame-arm.AsyncFinalizer

-- census: rule.frames-are-primitives

/-! F3b: an Exit is itself a primitive that can be stepped
(census: exit.success-failure). -/

-- census: exit.success-failure

-- census: exit.success-failure

-- census: exit.success-failure

-- census: exit.success-failure

-- census: exit.success-failure

/-! F4: the ensure hook and the answer selection (census: frame-arm.OnExit,
frame-arm.SetInterruptible, op.OnExit, op.SetInterruptible,
checkpoint.set-interruptible-contall, rule.frames-are-primitives). -/

-- census: frame-arm.Exit

-- census: frame-arm.OnExit

-- census: frame-arm.OnExit

-- census: frame-arm.OnExit

-- census: frame-arm.OnExit

-- census: op.SetInterruptible

-- census: op.SetInterruptible

-- census: op.SetInterruptible

-- census: op.SetInterruptible

-- census: op.SetInterruptible

-- census: op.AsyncFinalizer

-- census: op.AsyncFinalizer

-- census: op.AsyncFinalizer

-- census: rule.frames-are-primitives

-- census: rule.frames-are-primitives

-- census: rule.frames-are-primitives

-- census: rule.frames-are-primitives

/-! F5: the arms themselves (census: op.OnSuccess, op.OnFailure,
op.OnSuccessAndFailure, op.Exit, op.OnExit, op.Iterator, op.While,
frame-arm.*). -/

-- census: rule.frames-are-primitives

-- census: rule.frames-are-primitives

-- census: op.OnSuccess

-- census: op.OnSuccessAndFailure

-- census: op.OnFailure

-- census: op.OnSuccessAndFailure

-- census: frame-arm.OnSuccess

-- census: frame-arm.OnFailure

-- census: frame-arm.AsyncFinalizer

-- census: op.AsyncFinalizer

-- census: op.AsyncFinalizer

-- census: op.AsyncFinalizer

-- census: frame-arm.SetInterruptible

-- census: frame-arm.SetInterruptible

-- census: frame-arm.While

-- census: frame-arm.Iterator

-- census: op.Exit

-- census: op.Exit

-- census: op.Exit

-- census: op.Exit

-- census: op.OnExit

-- census: op.OnExit

-- census: op.OnExit

-- census: op.OnExit

-- census: op.OnExit

-- census: frame-arm.OnExit

-- census: op.OnSuccess

-- census: op.OnFailure

-- census: op.OnSuccessAndFailure

-- census: op.While

-- census: op.While

-- census: op.Iterator

-- census: op.Iterator

-- census: op.Iterator

-- census: op.Iterator

-- census: op.Iterator

-- census: op.OnExit

-- census: op.OnExit

-- census: op.OnExit

/-! F6: the pop (census: checkpoint.getcont-deferred,
checkpoint.exit-failcause-skip, rule.frames-are-primitives,
rule.interrupt-bypasses-handlers, op.Success, op.Failure).

`popFrom` is rc.112's `getCont` pop loop fused with the handler-skipping loop of
`exitFailCause`, and *unfused* from the frame list it started with: rc.112 pops
from the live `_stack`, so a frame a `contAll` pushed is popped before the
frames already below it. `docs/research/FRAMES-DAG.md:200-211` reserved that obligation
for the packet that adds `AsyncFinalizer`; `popFrom_pass_no_push` is the half
that still agrees with the old, list-recursive reading and
`popFrom_asyncFinalizer_pops_its_push` is the half that does not. -/

-- census: rule.frames-are-primitives

-- census: rule.frames-are-primitives

-- census: checkpoint.set-interruptible-contall

-- census: rule.frames-are-primitives

-- census: op.AsyncFinalizer

-- census: checkpoint.getcont-deferred

-- census: checkpoint.getcont-deferred

-- census: rule.frames-are-primitives

-- census: checkpoint.getcont-deferred

-- census: rule.frames-are-primitives

-- census: rule.frames-are-primitives

-- census: rule.frames-are-primitives

-- census: rule.frames-are-primitives

-- census: rule.frames-are-primitives

-- census: rule.frames-are-primitives

-- census: rule.frames-are-primitives

-- census: rule.frames-are-primitives

-- census: rule.frames-are-primitives

-- census: rule.frames-are-primitives

-- census: rule.frames-are-primitives

-- census: rule.frames-are-primitives

-- census: rule.frames-are-primitives

-- census: rule.frames-are-primitives

-- census: rule.frames-are-primitives

-- census: rule.frames-are-primitives

-- census: rule.frames-are-primitives

-- census: checkpoint.exit-failcause-skip

-- census: checkpoint.exit-failcause-skip

-- census: rule.interrupt-bypasses-handlers

/-! F7: resuming and stepping (census: op.Success, op.Failure, op.Sync,
op.Suspend, op.WithFiber, op.YieldableError, op.Iterator, op.OnSuccess,
op.OnFailure, op.OnSuccessAndFailure, op.Exit, op.OnExit, op.SetInterruptible,
op.While, exit.success-failure). -/

-- census: op.Success

-- census: checkpoint.getcont-deferred

-- census: checkpoint.set-interruptible-contall

-- census: op.Success

-- census: op.Failure

-- census: checkpoint.getcont-deferred

-- census: checkpoint.set-interruptible-contall

-- census: op.Failure

-- census: op.Success

-- census: op.Failure

-- census: op.Sync

-- census: op.Suspend

-- census: op.WithFiber

-- census: op.YieldableError

-- census: op.OnSuccess

-- census: op.OnFailure

-- census: op.OnSuccessAndFailure

-- census: op.Exit

-- census: op.OnExit

-- census: op.SetInterruptible

-- census: op.AsyncFinalizer

-- census: op.Yield

-- census: op.Async

-- census: op.While

-- census: op.While

-- census: op.Iterator

-- census: exit.success-failure

-- census: exit.success-failure

-- census: exit.success-failure

-- census: exit.success-failure

/-! F8: masks and the stack side of the two brackets
(census: checkpoint.set-fiber-interruptible, scope.scoped,
scope.acquire-release). -/

-- census: scope.acquire-release

-- census: scope.acquire-release

-- census: scope.acquire-release

-- census: checkpoint.set-fiber-interruptible

-- census: checkpoint.set-fiber-interruptible

-- census: checkpoint.set-fiber-interruptible

-- census: checkpoint.set-fiber-interruptible

-- census: checkpoint.set-fiber-interruptible

-- census: checkpoint.set-fiber-interruptible

-- census: scope.acquire-release

-- census: scope.acquire-release

-- census: scope.scoped

-- census: scope.scoped

-- census: scope.scoped

/-! F9: the two foreign boundaries (census: op.WithFiber, op.YieldableError).

Both rows are `foreignBoundary` in `PORT-MANIFEST.md` terms: they close with a
registered boundary identity and a theorem-shaped refusal, the way
`Effect4.Scope.key_freshness_refused` and `Effect4.Reason.host_memory_refused`
do, not with a behavioural model of the host object. -/

-- census: op.WithFiber

-- census: op.YieldableError

/-! F10: the uninterrupted fragment and fuel additivity (census:
checkpoint.getcont-deferred, checkpoint.exit-failcause-skip,
exit.success-failure).

Fence A of packet D4, `docs/research/2026-09-03-frame-simulation.md`. Nothing in
`src/Effect4/Machine/Frames.lean` writes `interruptedCause`, so
`interruptedCause = none` together with `deferredInterrupt = false` is a `step`
invariant, and under it the pop loop never skips an answering frame and
`getCont` never answers a deferred interrupt. `FRAME-FB-NONNULL` is *vacuous* on
that fragment and is not retired: the hypothesis is a fragment fact, not a model
fact. `run_add` / `run_mono` are the composition and monotonicity laws the
bounded runner lacked, and are what makes a `forall fuel >= bound` statement
sayable without contradicting DB-04. -/

-- census: checkpoint.getcont-deferred

-- census: checkpoint.getcont-deferred

-- census: checkpoint.getcont-deferred

-- census: checkpoint.exit-failcause-skip

-- census: checkpoint.getcont-deferred

-- census: checkpoint.getcont-deferred

-- census: checkpoint.getcont-deferred

-- census: checkpoint.getcont-deferred

-- census: exit.success-failure

-- census: exit.success-failure

-- census: exit.success-failure

-- census: exit.success-failure

/-! F11: the frozen D7 constant `OnSuccess` amendment.

rc.112 `internal/effect.ts:649-655` injects `flatMap(yieldNow, () => previous)`.
These local checks concern the wrapper's ordinary frame behavior. They do not
claim the run loop injects or parks at the correct checkpoint. -/

-- census: frame-arm.OnSuccess

-- census: frame-arm.OnSuccess

-- census: op.OnSuccess

-- census: frame-arm.OnSuccess

-- census: op.OnSuccess

-- census: op.OnSuccess

-- census: op.OnSuccess

private abbrev ConstPrim := Effect4.Prim Nat Nat Nat Nat Nat Nat Nat
private abbrev ConstFiber := Effect4.FrameFiber Nat Nat Nat Nat Nat Nat Nat

private def constInterp : Effect4.PrimInterp Nat Nat Nat Nat Nat Nat Nat where
  contA := fun name value => .success (name + value)
  contE := fun name _ => .success name
  syncValue := id
  suspendBody := fun name => .success name
  finalizerExit := fun _ _ => .success ()
  reifyExit := fun _ => 0
  iterNext := fun _ value => ([], .done value)
  loopTest := fun _ _ => false
  loopBody := fun name _ => .success name
  loopStep := fun _ cursor _ => cursor
  loopDone := fun _ => 0
  notImplemented := 0
  cancelThenFail := fun _ cause => .failure cause

private def savedConst : ConstPrim := .onSuccessConst (.yieldNowWith 0) (.success 27)
private def olderHandler : ConstPrim := .onFailure (.success 0) 13
private def constCleanup : ConstPrim := .onExit (.success 0) 31 false

-- The saved program is data and does not depend on the delivered value or exit.
#guard savedConst.armA constInterp 99 (some (.failure (.fail 7))) = some (.success 27, [])
#guard savedConst.armE constInterp (.fail 7) none = none

-- Enter the wrapper above an existing handler; controls and saved code survive.
#guard (Effect4.FrameFiber.mk savedConst [olderHandler] false (some (.fail 42)) true).step
    constInterp =
  (Effect4.FrameStep.running
    (Effect4.FrameFiber.mk (.yieldNowWith 0) [savedConst, olderHandler] false
      (some (.fail 42)) true), [Effect4.FrameEvent.pushed savedConst])

-- Success does not take the failure path's skip, even with an interrupt pending.
#guard (Effect4.FrameFiber.mk (.success 99) [savedConst, olderHandler] true
      (some (.fail 42)) false).step constInterp =
  (Effect4.FrameStep.running
    (Effect4.FrameFiber.mk (.success 27) [olderHandler] true (some (.fail 42)) false),
    [Effect4.FrameEvent.popped savedConst])

-- A deferred interrupt wins before touching either the constant frame or its tail.
#guard (Effect4.FrameFiber.mk (.success 99) [savedConst, olderHandler] true
      (some (.fail 42)) true).step constInterp =
  (Effect4.FrameStep.running
    (Effect4.FrameFiber.mk (.failure (.fail 42)) [savedConst, olderHandler] true
      (some (.fail 42)) false), [Effect4.FrameEvent.deferred (.fail 42)])

-- Failure discards the constant continuation and reaches the older cause handler.
#guard (Effect4.FrameFiber.mk (.failure (.fail 7))
      [savedConst, olderHandler, .setInterruptible false] true none false).step constInterp =
  (Effect4.FrameStep.running
    (Effect4.FrameFiber.mk (.success 13) [.setInterruptible false] true none false),
    [Effect4.FrameEvent.popped savedConst, Effect4.FrameEvent.popped olderHandler])

-- Nested saved programs return in stack order, one success per return.
private def outerConst : ConstPrim := .onSuccessConst (.yieldNowWith 0) (.success 41)
private def nestedConstFiber : ConstFiber :=
  Effect4.FrameFiber.mk (.success 1) [savedConst, outerConst, olderHandler] true none false

#guard nestedConstFiber.run constInterp 1 =
  (Effect4.FrameStep.running
    (Effect4.FrameFiber.mk (.success 27) [outerConst, olderHandler] true none false),
    [Effect4.FrameEvent.popped savedConst])
#guard nestedConstFiber.run constInterp 2 =
  (Effect4.FrameStep.running
    (Effect4.FrameFiber.mk (.success 41) [olderHandler] true none false),
    [Effect4.FrameEvent.popped savedConst, Effect4.FrameEvent.popped outerConst])

-- The older cleanup still runs once and restores its mask above the older handler.
private def cleanupConstFiber : ConstFiber :=
  Effect4.FrameFiber.mk (.failure (.fail 7)) [savedConst, constCleanup, olderHandler]
    true none false

#guard cleanupConstFiber.step constInterp =
  (Effect4.FrameStep.running
    (Effect4.FrameFiber.mk (.failure (.fail 7)) [.setInterruptible true, olderHandler]
      false none false),
    [Effect4.FrameEvent.popped savedConst, Effect4.FrameEvent.popped constCleanup,
      Effect4.FrameEvent.ranContAll constCleanup,
      Effect4.FrameEvent.ranFinalizer 31 (.failure (.fail 7))])
#guard cleanupConstFiber.run constInterp 2 =
  (Effect4.FrameStep.running
    (Effect4.FrameFiber.mk (.success 13) [] true none false),
    [Effect4.FrameEvent.popped savedConst, Effect4.FrameEvent.popped constCleanup,
      Effect4.FrameEvent.ranContAll constCleanup,
      Effect4.FrameEvent.ranFinalizer 31 (.failure (.fail 7)),
      Effect4.FrameEvent.popped (.setInterruptible true),
      Effect4.FrameEvent.ranContAll (.setInterruptible true),
      Effect4.FrameEvent.popped olderHandler])

#print axioms Effect4.Prim.cases_receipt
#print axioms Effect4.Prim.arms_onSuccessConst
#print axioms Effect4.Prim.ensure_onSuccessConst
#print axioms Effect4.Prim.armA_onSuccessConst
#print axioms Effect4.Prim.armE_onSuccessConst_none
#print axioms Effect4.FrameFiber.step_onSuccessConst
#print axioms Effect4.FrameFiber.resumeValue_onSuccessConst
#print axioms Effect4.FrameFiber.step_success_onSuccessConst

end Test.Runtime.FramesContract
