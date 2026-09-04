/-
Contract packet: `test/contracts/frames.contract.md`

Breaker-owned red battery. The implementation phase must not edit this file.
It is red until `Effect4/Runtime/Runtime.lean` declares the frozen surface.

Every public declaration is frozen by an exact `#check (@name : proposition)`
ascription so no weaker statement satisfies this contract. Names are written
fully qualified; this module deliberately does not `open Effect4`, so a
locally shadowed spelling cannot silently satisfy an ascription. Every theorem
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

#check (@Effect4.Arm : Type)

#check (@Effect4.Arm.contA : Effect4.Arm)

#check (@Effect4.Arm.contE : Effect4.Arm)

#check (@Effect4.Arm.contAll : Effect4.Arm)

#check (@Effect4.Arm.all : List Effect4.Arm)

#check (@Effect4.Arm.demandable : List Effect4.Arm)

-- census: rule.frames-are-primitives
#check (@Effect4.Arm.all_nodup : List.Nodup Effect4.Arm.all)

-- census: rule.frames-are-primitives
#check (@Effect4.Arm.mem_all : ∀ (arm : Effect4.Arm), arm ∈ Effect4.Arm.all)

-- census: rule.frames-are-primitives
#check (@Effect4.Arm.cases_receipt :
  ∀ (arm : Effect4.Arm), arm = Effect4.Arm.contA ∨ arm = Effect4.Arm.contE ∨ arm =
  Effect4.Arm.contAll)

-- census: rule.frames-are-primitives
#check (@Effect4.Arm.demandable_eq :
  Effect4.Arm.demandable = [Effect4.Arm.contA, Effect4.Arm.contE])

-- census: rule.frames-are-primitives
#check (@Effect4.Arm.contAll_not_demandable : ¬Effect4.Arm.contAll ∈ Effect4.Arm.demandable)

/-! F1: the primitive syntax (census: op.Success, op.Failure, op.Sync,
op.Suspend, op.WithFiber, op.YieldableError, op.Iterator, op.OnSuccess,
op.OnFailure, op.OnSuccessAndFailure, op.Exit, op.OnExit, op.SetInterruptible,
op.While, op.Yield, op.Async, op.AsyncFinalizer).

One constructor per pinned op. `ν` is the externally admitted continuation-name
alphabet and `σ` the thunk-name alphabet: a continuation slot is a nominal name,
never a stored Lean closure (DB-02). Nested bodies are first-order subterms.
`Yield`, `Async` and `AsyncFinalizer` were reserved for the run-loop and parking
packet and are here now, as first-order names. -/

#check (@Effect4.Prim :
  Type u → Type u → Type v → Type u → Type u → Type u → Type u → Type (max u v))

#check (@Effect4.Prim.success :
  {ν σ : Type u} → {β : Type v} → {ε δ ι α : Type u} → β → Effect4.Prim ν σ β ε δ ι α)

#check (@Effect4.Prim.failure :
  {ν σ : Type u} → {β : Type v} → {ε δ ι α : Type u} → Effect4.Cause ε δ ι α → Effect4.Prim ν σ
  β ε δ ι α)

#check (@Effect4.Prim.sync :
  {ν σ : Type u} → {β : Type v} → {ε δ ι α : Type u} → σ → Effect4.Prim ν σ β ε δ ι α)

#check (@Effect4.Prim.suspend :
  {ν σ : Type u} → {β : Type v} → {ε δ ι α : Type u} → σ → Effect4.Prim ν σ β ε δ ι α)

#check (@Effect4.Prim.withFiber :
  {ν σ : Type u} → {β : Type v} → {ε δ ι α : Type u} → σ → Effect4.Prim ν σ β ε δ ι α)

#check (@Effect4.Prim.yieldableError :
  {ν σ : Type u} → {β : Type v} → {ε δ ι α : Type u} → ε → Effect4.Prim ν σ β ε δ ι α)

#check (@Effect4.Prim.iterator :
  {ν σ : Type u} → {β : Type v} → {ε δ ι α : Type u} → ν → β → Effect4.Prim ν σ β ε δ ι α)

#check (@Effect4.Prim.onSuccess :
  {ν σ : Type u} → {β : Type v} → {ε δ ι α : Type u} → Effect4.Prim ν σ β ε δ ι α → ν →
  Effect4.Prim ν σ β ε δ ι α)

#check (@Effect4.Prim.onFailure :
  {ν σ : Type u} → {β : Type v} → {ε δ ι α : Type u} → Effect4.Prim ν σ β ε δ ι α → ν →
  Effect4.Prim ν σ β ε δ ι α)

#check (@Effect4.Prim.onSuccessAndFailure :
  {ν σ : Type u} → {β : Type v} → {ε δ ι α : Type u} → Effect4.Prim ν σ β ε δ ι α → ν → ν →
  Effect4.Prim ν σ β ε δ ι α)

#check (@Effect4.Prim.exitFrame :
  {ν σ : Type u} → {β : Type v} → {ε δ ι α : Type u} → Effect4.Prim ν σ β ε δ ι α → Effect4.Prim
  ν σ β ε δ ι α)

#check (@Effect4.Prim.onExit :
  {ν σ : Type u} → {β : Type v} → {ε δ ι α : Type u} → Effect4.Prim ν σ β ε δ ι α → ν → Bool →
  Effect4.Prim ν σ β ε δ ι α)

#check (@Effect4.Prim.setInterruptible :
  {ν σ : Type u} → {β : Type v} → {ε δ ι α : Type u} → Bool → Effect4.Prim ν σ β ε δ ι α)

#check (@Effect4.Prim.whileLoop :
  {ν σ : Type u} → {β : Type v} → {ε δ ι α : Type u} → ν → β → Effect4.Prim ν σ β ε δ ι α)

#check (@Effect4.Prim.yieldNowWith :
  {ν σ : Type u} → {β : Type v} → {ε δ ι α : Type u} → Nat → Effect4.Prim ν σ β ε δ ι α)

#check (@Effect4.Prim.async :
  {ν σ : Type u} → {β : Type v} → {ε δ ι α : Type u} → ν → Bool → Option ν → Effect4.Prim ν σ β
  ε δ ι α)

#check (@Effect4.Prim.asyncFinalizer :
  {ν σ : Type u} → {β : Type v} → {ε δ ι α : Type u} → ν → Effect4.Prim ν σ β ε δ ι α)

-- census: rule.frames-are-primitives
#check (@Effect4.Prim.cases_receipt :
  ∀ {ν σ : Type u} {β : Type v} {ε δ ι α : Type u} (self : Effect4.Prim ν σ β ε δ ι α), (∃
  value, self = Effect4.Prim.success value) ∨ (∃ cause, self = Effect4.Prim.failure cause) ∨ (∃
  thunk, self = Effect4.Prim.sync thunk) ∨ (∃ thunk, self = Effect4.Prim.suspend thunk) ∨ (∃
  thunk, self = Effect4.Prim.withFiber thunk) ∨ (∃ error, self = Effect4.Prim.yieldableError
  error) ∨ (∃ generator cursor, self = Effect4.Prim.iterator generator cursor) ∨ (∃ body
  onValue, self = Effect4.Prim.onSuccess body onValue) ∨ (∃ body onCause, self =
  Effect4.Prim.onFailure body onCause) ∨ (∃ body onValue onCause, self =
  Effect4.Prim.onSuccessAndFailure body onValue onCause) ∨ (∃ body, self =
  Effect4.Prim.exitFrame body) ∨ (∃ body finalizer flag, self = Effect4.Prim.onExit body
  finalizer flag) ∨ (∃ flag, self = Effect4.Prim.setInterruptible flag) ∨ (∃ loop cursor, self =
  Effect4.Prim.whileLoop loop cursor) ∨ (∃ priority, self = Effect4.Prim.yieldNowWith priority)
  ∨ (∃ register withSignal cancel, self = Effect4.Prim.async register withSignal cancel) ∨ ∃
  onInterrupt, self = Effect4.Prim.asyncFinalizer onInterrupt)

/-! F1b: the generator outcome (census: op.Iterator, frame-arm.Iterator).

rc.112's `Iterator` frame drives a JavaScript generator in a `while (true)` loop
that folds every `Success` exit inline. The maximal run of inline values and the
outcome that ended it are supplied as first-order data by `PrimInterp.iterNext`;
`docs/FRAMES-DAG.md` records why. -/

#check (@Effect4.IterStep :
  Type u → Type u → Type v → Type u → Type u → Type u → Type u → Type (max u v))

#check (@Effect4.IterStep.done :
  {ν σ : Type u} → {β : Type v} → {ε δ ι α : Type u} → β → Effect4.IterStep ν σ β ε δ ι α)

#check (@Effect4.IterStep.halt :
  {ν σ : Type u} → {β : Type v} → {ε δ ι α : Type u} → Effect4.Cause ε δ ι α → Effect4.IterStep
  ν σ β ε δ ι α)

#check (@Effect4.IterStep.resume :
  {ν σ : Type u} →
    {β : Type v} → {ε δ ι α : Type u} → Effect4.Prim ν σ β ε δ ι α → ν → Effect4.IterStep ν σ β ε δ ι α)

/-! F1c: the externally supplied interpretation (census: op.Sync, op.Suspend,
op.Iterator, op.Exit, op.OnExit, op.While).

The one parameter that says what a name *does*, the same shape
`Effect4.Scope.close` takes for `run`. It never enters `Prim`, so a primitive
keeps first-order identity and decidable equality. -/

#check (@Effect4.PrimInterp :
  Type u → Type u → Type v → Type u → Type u → Type u → Type u → Type (max u v))

#check (@Effect4.PrimInterp.mk :
  {ν σ : Type u} →
    {β : Type v} →
      {ε δ ι α : Type u} →
        (ν → β → Effect4.Prim ν σ β ε δ ι α) →
          (ν → Effect4.Cause ε δ ι α → Effect4.Prim ν σ β ε δ ι α) →
            (σ → β) →
              (σ → Effect4.Prim ν σ β ε δ ι α) →
                (ν → Effect4.Exit β ε δ ι α → Effect4.Exit Unit ε δ ι α) →
                  (Effect4.Exit β ε δ ι α → β) →
                    (ν → β → List β × Effect4.IterStep ν σ β ε δ ι α) →
                      (ν → β → Bool) →
                        (ν → β → Effect4.Prim ν σ β ε δ ι α) →
                          (ν → β → β → β) →
                            (ν → β) →
                              δ →
                                (ν → Effect4.Cause ε δ ι α → Effect4.Prim ν σ β ε δ ι α) →
                                  Effect4.PrimInterp ν σ β ε δ ι α)

#check (@Effect4.PrimInterp.contA :
  {ν σ : Type u} → {β : Type v} → {ε δ ι α : Type u} → Effect4.PrimInterp ν σ β ε δ ι α → ν → β
  → Effect4.Prim ν σ β ε δ ι α)

#check (@Effect4.PrimInterp.contE :
  {ν σ : Type u} → {β : Type v} → {ε δ ι α : Type u} → Effect4.PrimInterp ν σ β ε δ ι α → ν →
  Effect4.Cause ε δ ι α → Effect4.Prim ν σ β ε δ ι α)

#check (@Effect4.PrimInterp.syncValue :
  {ν σ : Type u} → {β : Type v} → {ε δ ι α : Type u} → Effect4.PrimInterp ν σ β ε δ ι α → σ → β)

#check (@Effect4.PrimInterp.suspendBody :
  {ν σ : Type u} → {β : Type v} → {ε δ ι α : Type u} → Effect4.PrimInterp ν σ β ε δ ι α → σ →
  Effect4.Prim ν σ β ε δ ι α)

#check (@Effect4.PrimInterp.finalizerExit :
  {ν σ : Type u} → {β : Type v} → {ε δ ι α : Type u} → Effect4.PrimInterp ν σ β ε δ ι α → ν →
  Effect4.Exit β ε δ ι α → Effect4.Exit Unit ε δ ι α)

#check (@Effect4.PrimInterp.reifyExit :
  {ν σ : Type u} → {β : Type v} → {ε δ ι α : Type u} → Effect4.PrimInterp ν σ β ε δ ι α →
  Effect4.Exit β ε δ ι α → β)

#check (@Effect4.PrimInterp.iterNext :
  {ν σ : Type u} → {β : Type v} → {ε δ ι α : Type u} → Effect4.PrimInterp ν σ β ε δ ι α → ν → β
  → List β × Effect4.IterStep ν σ β ε δ ι α)

#check (@Effect4.PrimInterp.loopTest :
  {ν σ : Type u} → {β : Type v} → {ε δ ι α : Type u} → Effect4.PrimInterp ν σ β ε δ ι α → ν → β
  → Bool)

#check (@Effect4.PrimInterp.loopBody :
  {ν σ : Type u} → {β : Type v} → {ε δ ι α : Type u} → Effect4.PrimInterp ν σ β ε δ ι α → ν → β
  → Effect4.Prim ν σ β ε δ ι α)

#check (@Effect4.PrimInterp.loopStep :
  {ν σ : Type u} →
    {β : Type v} → {ε δ ι α : Type u} → Effect4.PrimInterp ν σ β ε δ ι α → ν → β → β → β)

#check (@Effect4.PrimInterp.loopDone :
  {ν σ : Type u} → {β : Type v} → {ε δ ι α : Type u} → Effect4.PrimInterp ν σ β ε δ ι α → ν → β)

#check (@Effect4.PrimInterp.notImplemented :
  {ν σ : Type u} → {β : Type v} → {ε δ ι α : Type u} → Effect4.PrimInterp ν σ β ε δ ι α → δ)

#check (@Effect4.PrimInterp.cancelThenFail :
  {ν σ : Type u} → {β : Type v} → {ε δ ι α : Type u} → Effect4.PrimInterp ν σ β ε δ ι α → ν →
  Effect4.Cause ε δ ι α → Effect4.Prim ν σ β ε δ ι α)

/-! F2: the fiber state this packet models (census: rule.frames-are-primitives).

Exactly five fields: the current primitive, the stack of frames, the
interruptible flag, the accumulated interruption cause, and the deferred flag.
No `_running`, `_yielded`, observers, children, budget or dispatcher: those
belong to the run-loop and supervision packets. -/

#check (@Effect4.FrameFiber :
  Type u → Type u → Type v → Type u → Type u → Type u → Type u → Type (max u v))

#check (@Effect4.FrameFiber.mk :
  {ν σ : Type u} → {β : Type v} → {ε δ ι α : Type u} → Effect4.Prim ν σ β ε δ ι α → List
  (Effect4.Prim ν σ β ε δ ι α) → Bool → Option (Effect4.Cause ε δ ι α) → Bool →
  Effect4.FrameFiber ν σ β ε δ ι α)

#check (@Effect4.FrameFiber.current :
  {ν σ : Type u} → {β : Type v} → {ε δ ι α : Type u} → Effect4.FrameFiber ν σ β ε δ ι α →
  Effect4.Prim ν σ β ε δ ι α)

#check (@Effect4.FrameFiber.stack :
  {ν σ : Type u} → {β : Type v} → {ε δ ι α : Type u} → Effect4.FrameFiber ν σ β ε δ ι α → List
  (Effect4.Prim ν σ β ε δ ι α))

#check (@Effect4.FrameFiber.interruptible :
  {ν σ : Type u} → {β : Type v} → {ε δ ι α : Type u} → Effect4.FrameFiber ν σ β ε δ ι α → Bool)

#check (@Effect4.FrameFiber.interruptedCause :
  {ν σ : Type u} → {β : Type v} → {ε δ ι α : Type u} → Effect4.FrameFiber ν σ β ε δ ι α → Option
  (Effect4.Cause ε δ ι α))

#check (@Effect4.FrameFiber.deferredInterrupt :
  {ν σ : Type u} → {β : Type v} → {ε δ ι α : Type u} → Effect4.FrameFiber ν σ β ε δ ι α → Bool)

#check (@Effect4.FrameFiber.start :
  {ν σ : Type u} → {β : Type v} → {ε δ ι α : Type u} → Effect4.Prim ν σ β ε δ ι α →
  Effect4.FrameFiber ν σ β ε δ ι α)

#check (@Effect4.FrameFiber.pendingCause :
  {ν σ : Type u} → {β : Type v} → {ε δ ι α : Type u} → Effect4.FrameFiber ν σ β ε δ ι α →
  Effect4.Cause ε δ ι α)

#check (@Effect4.FrameFiber.masked :
  {ν σ : Type u} → {β : Type v} → {ε δ ι α : Type u} → Effect4.FrameFiber ν σ β ε δ ι α → Bool)

#check (@Effect4.FrameFiber.interrupted :
  {ν σ : Type u} → {β : Type v} → {ε δ ι α : Type u} → Effect4.FrameFiber ν σ β ε δ ι α → Bool)

-- census: rule.frames-are-primitives
#check (@Effect4.FrameFiber.start_eq :
  ∀ {ν σ : Type u} {β : Type v} {ε δ ι α : Type u} (current : Effect4.Prim ν σ β ε δ ι α),
  Effect4.FrameFiber.start current = Effect4.FrameFiber.mk current [] Bool.true Option.none
  Bool.false)

-- census: checkpoint.getcont-deferred
#check (@Effect4.FrameFiber.pendingCause_some :
  ∀ {ν σ : Type u} {β : Type v} {ε δ ι α : Type u} (self : Effect4.FrameFiber ν σ β ε δ ι α)
  (cause : Effect4.Cause ε δ ι α), self.interruptedCause = Option.some cause →
  Effect4.FrameFiber.pendingCause self = cause)

-- census: checkpoint.getcont-deferred
#check (@Effect4.FrameFiber.pendingCause_none :
  ∀ {ν σ : Type u} {β : Type v} {ε δ ι α : Type u} (self : Effect4.FrameFiber ν σ β ε δ ι α),
  self.interruptedCause = Option.none → Effect4.FrameFiber.pendingCause self =
  Effect4.Cause.empty)

-- census: rule.frames-are-primitives
#check (@Effect4.FrameFiber.masked_eq :
  ∀ {ν σ : Type u} {β : Type v} {ε δ ι α : Type u} (self : Effect4.FrameFiber ν σ β ε δ ι α),
  Effect4.FrameFiber.masked self = !self.interruptible)

-- census: rule.frames-are-primitives
#check (@Effect4.FrameFiber.interrupted_eq :
  ∀ {ν σ : Type u} {β : Type v} {ε δ ι α : Type u} (self : Effect4.FrameFiber ν σ β ε δ ι α),
  Effect4.FrameFiber.interrupted self = (self.interruptible && Option.isSome
  self.interruptedCause))

/-! F2b: what a pop answers, what it leaves in the trace, and what a step
produces (census: checkpoint.getcont-deferred, rule.frames-are-primitives). -/

#check (@Effect4.ContAnswer :
  Type u → Type u → Type v → Type u → Type u → Type u → Type u → Type (max u v))

#check (@Effect4.ContAnswer.deferred :
  {ν σ : Type u} → {β : Type v} → {ε δ ι α : Type u} → Effect4.Cause ε δ ι α →
  Effect4.ContAnswer ν σ β ε δ ι α)

#check (@Effect4.ContAnswer.replacement :
  {ν σ : Type u} → {β : Type v} → {ε δ ι α : Type u} → Effect4.Prim ν σ β ε δ ι α →
  Effect4.ContAnswer ν σ β ε δ ι α)

#check (@Effect4.ContAnswer.frame :
  {ν σ : Type u} → {β : Type v} → {ε δ ι α : Type u} → Effect4.Prim ν σ β ε δ ι α →
  Effect4.ContAnswer ν σ β ε δ ι α)

#check (@Effect4.ContAnswer.empty :
  {ν σ : Type u} → {β : Type v} → {ε δ ι α : Type u} → Effect4.ContAnswer ν σ β ε δ ι α)

#check (@Effect4.FrameEvent :
  Type u → Type u → Type v → Type u → Type u → Type u → Type u → Type (max u v))

#check (@Effect4.FrameEvent.popped :
  {ν σ : Type u} → {β : Type v} → {ε δ ι α : Type u} → Effect4.Prim ν σ β ε δ ι α →
  Effect4.FrameEvent ν σ β ε δ ι α)

#check (@Effect4.FrameEvent.ranContAll :
  {ν σ : Type u} → {β : Type v} → {ε δ ι α : Type u} → Effect4.Prim ν σ β ε δ ι α →
  Effect4.FrameEvent ν σ β ε δ ι α)

#check (@Effect4.FrameEvent.pushed :
  {ν σ : Type u} → {β : Type v} → {ε δ ι α : Type u} → Effect4.Prim ν σ β ε δ ι α →
  Effect4.FrameEvent ν σ β ε δ ι α)

#check (@Effect4.FrameEvent.ranFinalizer :
  {ν σ : Type u} → {β : Type v} → {ε δ ι α : Type u} → ν → Effect4.Exit β ε δ ι α →
  Effect4.FrameEvent ν σ β ε δ ι α)

#check (@Effect4.FrameEvent.substituted :
  {ν σ : Type u} → {β : Type v} → {ε δ ι α : Type u} → Effect4.Cause ε δ ι α →
  Effect4.FrameEvent ν σ β ε δ ι α)

#check (@Effect4.FrameEvent.deferred :
  {ν σ : Type u} → {β : Type v} → {ε δ ι α : Type u} → Effect4.Cause ε δ ι α →
  Effect4.FrameEvent ν σ β ε δ ι α)

#check (@Effect4.FrameEvent.yielded :
  {ν σ : Type u} → {β : Type v} → {ε δ ι α : Type u} → Effect4.Exit β ε δ ι α →
  Effect4.FrameEvent ν σ β ε δ ι α)

#check (@Effect4.FramePop :
  Type u → Type u → Type v → Type u → Type u → Type u → Type u → Type (max u v))

#check (@Effect4.FramePop.mk :
  {ν σ : Type u} → {β : Type v} → {ε δ ι α : Type u} → Effect4.ContAnswer ν σ β ε δ ι α → List
  (Effect4.Prim ν σ β ε δ ι α) → List (Effect4.FrameEvent ν σ β ε δ ι α) → Effect4.FrameFiber ν
  σ β ε δ ι α → Effect4.FramePop ν σ β ε δ ι α)

#check (@Effect4.FramePop.answer :
  {ν σ : Type u} → {β : Type v} → {ε δ ι α : Type u} → Effect4.FramePop ν σ β ε δ ι α →
  Effect4.ContAnswer ν σ β ε δ ι α)

#check (@Effect4.FramePop.popped :
  {ν σ : Type u} → {β : Type v} → {ε δ ι α : Type u} → Effect4.FramePop ν σ β ε δ ι α → List
  (Effect4.Prim ν σ β ε δ ι α))

#check (@Effect4.FramePop.events :
  {ν σ : Type u} → {β : Type v} → {ε δ ι α : Type u} → Effect4.FramePop ν σ β ε δ ι α → List
  (Effect4.FrameEvent ν σ β ε δ ι α))

#check (@Effect4.FramePop.fiber :
  {ν σ : Type u} → {β : Type v} → {ε δ ι α : Type u} → Effect4.FramePop ν σ β ε δ ι α →
  Effect4.FrameFiber ν σ β ε δ ι α)

#check (@Effect4.FrameStep :
  Type u → Type u → Type v → Type u → Type u → Type u → Type u → Type (max u v))

#check (@Effect4.FrameStep.running :
  {ν σ : Type u} → {β : Type v} → {ε δ ι α : Type u} → Effect4.FrameFiber ν σ β ε δ ι α →
  Effect4.FrameStep ν σ β ε δ ι α)

#check (@Effect4.FrameStep.finished :
  {ν σ : Type u} → {β : Type v} → {ε δ ι α : Type u} → Effect4.Exit β ε δ ι α →
  Effect4.FrameStep ν σ β ε δ ι α)

#check (@Effect4.FrameEvent.poppedFrame? :
  {ν σ : Type u} → {β : Type v} → {ε δ ι α : Type u} → Effect4.FrameEvent ν σ β ε δ ι α → Option
  (Effect4.Prim ν σ β ε δ ι α))

#check (@Effect4.FrameEvent.finalizer? :
  {ν σ : Type u} → {β : Type v} → {ε δ ι α : Type u} → Effect4.FrameEvent ν σ β ε δ ι α → Option
  ν)

#check (@Effect4.FrameEvent.poppedFrames :
  {ν σ : Type u} → {β : Type v} → {ε δ ι α : Type u} → List (Effect4.FrameEvent ν σ β ε δ ι α) →
  List (Effect4.Prim ν σ β ε δ ι α))

#check (@Effect4.FrameEvent.finalizersRun :
  {ν σ : Type u} → {β : Type v} → {ε δ ι α : Type u} → List (Effect4.FrameEvent ν σ β ε δ ι α) →
  List ν)

-- census: rule.frames-are-primitives
#check (@Effect4.FrameEvent.poppedFrames_nil :
  ∀ {ν σ : Type u} {β : Type v} {ε δ ι α : Type u}, Effect4.FrameEvent.poppedFrames [] = [])

-- census: rule.frames-are-primitives
#check (@Effect4.FrameEvent.poppedFrames_cons_popped :
  ∀ {ν σ : Type u} {β : Type v} {ε δ ι α : Type u} (frame : Effect4.Prim ν σ β ε δ ι α) (rest :
  List (Effect4.FrameEvent ν σ β ε δ ι α)), Effect4.FrameEvent.poppedFrames
  (Effect4.FrameEvent.popped frame :: rest) = frame :: Effect4.FrameEvent.poppedFrames rest)

-- census: rule.frames-are-primitives
#check (@Effect4.FrameEvent.finalizersRun_nil :
  ∀ {ν σ : Type u} {β : Type v} {ε δ ι α : Type u}, Effect4.FrameEvent.finalizersRun [] = [])

-- census: rule.frames-are-primitives
#check (@Effect4.FrameEvent.finalizersRun_cons_ran :
  ∀ {ν σ : Type u} {β : Type v} {ε δ ι α : Type u} (finalizer : ν) (exit : Effect4.Exit β ε δ ι
  α) (rest : List (Effect4.FrameEvent ν σ β ε δ ι α)), Effect4.FrameEvent.finalizersRun
  (Effect4.FrameEvent.ranFinalizer finalizer exit :: rest) = finalizer ::
  Effect4.FrameEvent.finalizersRun rest)

-- census: rule.frames-are-primitives
#check (@Effect4.FrameEvent.finalizersRun_cons_popped :
  ∀ {ν σ : Type u} {β : Type v} {ε δ ι α : Type u} (frame : Effect4.Prim ν σ β ε δ ι α) (rest :
  List (Effect4.FrameEvent ν σ β ε δ ι α)), Effect4.FrameEvent.finalizersRun
  (Effect4.FrameEvent.popped frame :: rest) = Effect4.FrameEvent.finalizersRun rest)

/-! F3: the frame-arm matrix (census: frame-arm.OnSuccess, frame-arm.OnFailure,
frame-arm.OnSuccessAndFailure, frame-arm.Exit, frame-arm.OnExit,
frame-arm.SetInterruptible, frame-arm.While, frame-arm.Iterator,
rule.frames-are-primitives).

Frozen exactly as `docs/effect-rc112-fiber-runtime.html` section 3 states it. A
frame is selected by which arms it defines; the six non-frame primitives define
none and are never pushed. -/

#check (@Effect4.Prim.arms :
  {ν σ : Type u} → {β : Type v} → {ε δ ι α : Type u} → Effect4.Prim ν σ β ε δ ι α → List
  Effect4.Arm)

#check (@Effect4.Prim.hasArm :
  {ν σ : Type u} → {β : Type v} → {ε δ ι α : Type u} → Effect4.Prim ν σ β ε δ ι α → Effect4.Arm
  → Bool)

#check (@Effect4.Prim.isFrame :
  {ν σ : Type u} → {β : Type v} → {ε δ ι α : Type u} → Effect4.Prim ν σ β ε δ ι α → Bool)

-- census: rule.frames-are-primitives
#check (@Effect4.Prim.hasArm_eq :
  ∀ {ν σ : Type u} {β : Type v} {ε δ ι α : Type u} (self : Effect4.Prim ν σ β ε δ ι α) (arm :
  Effect4.Arm), Effect4.Prim.hasArm self arm = List.contains (Effect4.Prim.arms self) arm)

-- census: rule.frames-are-primitives
#check (@Effect4.Prim.isFrame_eq :
  ∀ {ν σ : Type u} {β : Type v} {ε δ ι α : Type u} (self : Effect4.Prim ν σ β ε δ ι α),
  Effect4.Prim.isFrame self = !List.isEmpty (Effect4.Prim.arms self))

-- census: rule.frames-are-primitives
#check (@Effect4.Prim.isFrame_iff :
  ∀ {ν σ : Type u} {β : Type v} {ε δ ι α : Type u} (self : Effect4.Prim ν σ β ε δ ι α),
  Effect4.Prim.isFrame self = Bool.true ↔ Effect4.Prim.arms self ≠ [])

-- census: frame-arm.OnSuccess
#check (@Effect4.Prim.arms_onSuccess :
  ∀ {ν σ : Type u} {β : Type v} {ε δ ι α : Type u} (body : Effect4.Prim ν σ β ε δ ι α) (onValue
  : ν), Effect4.Prim.arms (Effect4.Prim.onSuccess body onValue) = [Effect4.Arm.contA])

-- census: frame-arm.OnFailure
#check (@Effect4.Prim.arms_onFailure :
  ∀ {ν σ : Type u} {β : Type v} {ε δ ι α : Type u} (body : Effect4.Prim ν σ β ε δ ι α) (onCause
  : ν), Effect4.Prim.arms (Effect4.Prim.onFailure body onCause) = [Effect4.Arm.contE])

-- census: frame-arm.OnSuccessAndFailure
#check (@Effect4.Prim.arms_onSuccessAndFailure :
  ∀ {ν σ : Type u} {β : Type v} {ε δ ι α : Type u} (body : Effect4.Prim ν σ β ε δ ι α) (onValue
  onCause : ν), Effect4.Prim.arms (Effect4.Prim.onSuccessAndFailure body onValue onCause) =
  [Effect4.Arm.contA, Effect4.Arm.contE])

-- census: frame-arm.Exit
#check (@Effect4.Prim.arms_exitFrame :
  ∀ {ν σ : Type u} {β : Type v} {ε δ ι α : Type u} (body : Effect4.Prim ν σ β ε δ ι α),
  Effect4.Prim.arms (Effect4.Prim.exitFrame body) = [Effect4.Arm.contA, Effect4.Arm.contE])

-- census: frame-arm.OnExit
#check (@Effect4.Prim.arms_onExit :
  ∀ {ν σ : Type u} {β : Type v} {ε δ ι α : Type u} (body : Effect4.Prim ν σ β ε δ ι α)
  (finalizer : ν) (flag : Bool), Effect4.Prim.arms (Effect4.Prim.onExit body finalizer flag) =
  [Effect4.Arm.contA, Effect4.Arm.contE, Effect4.Arm.contAll])

-- census: frame-arm.SetInterruptible
#check (@Effect4.Prim.arms_setInterruptible :
  ∀ {ν σ : Type u} {β : Type v} {ε δ ι α : Type u} (flag : Bool), Effect4.Prim.arms
  (Effect4.Prim.setInterruptible flag) = [Effect4.Arm.contAll])

-- census: frame-arm.While
#check (@Effect4.Prim.arms_whileLoop :
  ∀ {ν σ : Type u} {β : Type v} {ε δ ι α : Type u} (loop : ν) (cursor : β), Effect4.Prim.arms
  (Effect4.Prim.whileLoop loop cursor) = [Effect4.Arm.contA])

-- census: frame-arm.Iterator
#check (@Effect4.Prim.arms_iterator :
  ∀ {ν σ : Type u} {β : Type v} {ε δ ι α : Type u} (generator : ν) (cursor : β),
  Effect4.Prim.arms (Effect4.Prim.iterator generator cursor) = [Effect4.Arm.contA])

-- census: frame-arm.AsyncFinalizer
#check (@Effect4.Prim.arms_asyncFinalizer :
  ∀ {ν σ : Type u} {β : Type v} {ε δ ι α : Type u} (onInterrupt : ν), Effect4.Prim.arms
  (Effect4.Prim.asyncFinalizer onInterrupt) = [Effect4.Arm.contE, Effect4.Arm.contAll])

-- census: frame-arm.AsyncFinalizer
#check (@Effect4.Prim.hasArm_asyncFinalizer_contA_false :
  ∀ {ν σ : Type u} {β : Type v} {ε δ ι α : Type u} (onInterrupt : ν), Effect4.Prim.hasArm
  (Effect4.Prim.asyncFinalizer onInterrupt) Effect4.Arm.contA = Bool.false)

-- census: rule.frames-are-primitives
#check (@Effect4.Prim.non_frames_have_no_arms :
  ∀ {ν σ : Type u} {β : Type v} {ε δ ι α : Type u} (value : β) (cause : Effect4.Cause ε δ ι α)
  (thunk : σ) (error : ε) (priority : Nat) (register : ν) (withSignal : Bool) (cancel : Option
  ν), Effect4.Prim.arms (Effect4.Prim.success value) = [] ∧
  Effect4.Prim.arms (Effect4.Prim.failure cause) = [] ∧ Effect4.Prim.arms (Effect4.Prim.sync
  thunk) = [] ∧ Effect4.Prim.arms (Effect4.Prim.suspend thunk) = [] ∧ Effect4.Prim.arms
  (Effect4.Prim.withFiber thunk) = [] ∧ Effect4.Prim.arms (Effect4.Prim.yieldableError error) =
  [] ∧ Effect4.Prim.arms (Effect4.Prim.yieldNowWith priority) = [] ∧ Effect4.Prim.arms
  (Effect4.Prim.async register withSignal cancel) = [])

/-! F3b: an Exit is itself a primitive that can be stepped
(census: exit.success-failure). -/

#check (@Effect4.Prim.ofExit :
  {ν σ : Type u} → {β : Type v} → {ε δ ι α : Type u} → Effect4.Exit β ε δ ι α → Effect4.Prim ν σ
  β ε δ ι α)

#check (@Effect4.Prim.asExit? :
  {ν σ : Type u} → {β : Type v} → {ε δ ι α : Type u} → Effect4.Prim ν σ β ε δ ι α → Option
  (Effect4.Exit β ε δ ι α))

-- census: exit.success-failure
#check (@Effect4.Prim.ofExit_asExit? :
  ∀ {ν σ : Type u} {β : Type v} {ε δ ι α : Type u} (exit : Effect4.Exit β ε δ ι α),
  Effect4.Prim.asExit? (Effect4.Prim.ofExit exit) = Option.some exit)

-- census: exit.success-failure
#check (@Effect4.Prim.asExit?_success :
  ∀ {ν σ : Type u} {β : Type v} {ε δ ι α : Type u} (value : β), Effect4.Prim.asExit?
  (Effect4.Prim.success value) = Option.some (Effect4.Exit.success value))

-- census: exit.success-failure
#check (@Effect4.Prim.asExit?_failure :
  ∀ {ν σ : Type u} {β : Type v} {ε δ ι α : Type u} (cause : Effect4.Cause ε δ ι α),
  Effect4.Prim.asExit? (Effect4.Prim.failure cause) = Option.some (Effect4.Exit.failure cause))

-- census: exit.success-failure
#check (@Effect4.Prim.asExit?_eq_some :
  ∀ {ν σ : Type u} {β : Type v} {ε δ ι α : Type u} (self : Effect4.Prim ν σ β ε δ ι α) (exit :
  Effect4.Exit β ε δ ι α), Effect4.Prim.asExit? self = Option.some exit → self =
  Effect4.Prim.ofExit exit)

-- census: exit.success-failure
#check (@Effect4.Prim.ofExit_isFrame :
  ∀ {ν σ : Type u} {β : Type v} {ε δ ι α : Type u} (exit : Effect4.Exit β ε δ ι α),
  Effect4.Prim.isFrame (Effect4.Prim.ofExit exit) = Bool.false)

/-! F4: the ensure hook and the answer selection (census: frame-arm.OnExit,
frame-arm.SetInterruptible, op.OnExit, op.SetInterruptible,
checkpoint.set-interruptible-contall, rule.frames-are-primitives). -/

#check (@Effect4.Prim.ensure :
  {ν σ : Type u} → {β : Type v} → {ε δ ι α : Type u} → Effect4.Prim ν σ β ε δ ι α →
  Effect4.FrameFiber ν σ β ε δ ι α → Effect4.FrameFiber ν σ β ε δ ι α × Option (Effect4.Prim ν σ
  β ε δ ι α))

#check (@Effect4.Prim.answerOf :
  {ν σ : Type u} → {β : Type v} → {ε δ ι α : Type u} → Effect4.Prim ν σ β ε δ ι α → Effect4.Arm
  → Option (Effect4.Prim ν σ β ε δ ι α) → Option (Effect4.ContAnswer ν σ β ε δ ι α))

#check (@Effect4.Prim.passEvents :
  {ν σ : Type u} → {β : Type v} → {ε δ ι α : Type u} → Effect4.Prim ν σ β ε δ ι α → Option
  (Effect4.Prim ν σ β ε δ ι α) → List (Effect4.FrameEvent ν σ β ε δ ι α))

-- census: frame-arm.Exit
#check (@Effect4.Prim.ensure_of_no_contAll :
  ∀ {ν σ : Type u} {β : Type v} {ε δ ι α : Type u} (frame : Effect4.Prim ν σ β ε δ ι α) (fiber :
  Effect4.FrameFiber ν σ β ε δ ι α), Effect4.Prim.hasArm frame Effect4.Arm.contAll = Bool.false
  → Effect4.Prim.ensure frame fiber = (fiber, Option.none))

-- census: frame-arm.OnExit
#check (@Effect4.Prim.ensure_onExit_masks :
  ∀ {ν σ : Type u} {β : Type v} {ε δ ι α : Type u} (body : Effect4.Prim ν σ β ε δ ι α)
  (finalizer : ν) (fiber : Effect4.FrameFiber ν σ β ε δ ι α), fiber.interruptible = Bool.true →
  Effect4.Prim.ensure (Effect4.Prim.onExit body finalizer Bool.false) fiber =
  (Effect4.FrameFiber.mk fiber.current (Effect4.Prim.setInterruptible Bool.true :: fiber.stack)
  Bool.false fiber.interruptedCause fiber.deferredInterrupt, Option.none))

-- census: frame-arm.OnExit
#check (@Effect4.Prim.ensure_onExit_told_not_to :
  ∀ {ν σ : Type u} {β : Type v} {ε δ ι α : Type u} (body : Effect4.Prim ν σ β ε δ ι α)
  (finalizer : ν) (fiber : Effect4.FrameFiber ν σ β ε δ ι α), Effect4.Prim.ensure
  (Effect4.Prim.onExit body finalizer Bool.true) fiber = (fiber, Option.none))

-- census: frame-arm.OnExit
#check (@Effect4.Prim.ensure_onExit_already_masked :
  ∀ {ν σ : Type u} {β : Type v} {ε δ ι α : Type u} (body : Effect4.Prim ν σ β ε δ ι α)
  (finalizer : ν) (flag : Bool) (fiber : Effect4.FrameFiber ν σ β ε δ ι α), fiber.interruptible
  = Bool.false → Effect4.Prim.ensure (Effect4.Prim.onExit body finalizer flag) fiber = (fiber,
  Option.none))

-- census: frame-arm.OnExit
#check (@Effect4.Prim.ensure_onExit_no_replacement :
  ∀ {ν σ : Type u} {β : Type v} {ε δ ι α : Type u} (body : Effect4.Prim ν σ β ε δ ι α)
  (finalizer : ν) (flag : Bool) (fiber : Effect4.FrameFiber ν σ β ε δ ι α), (Effect4.Prim.ensure
  (Effect4.Prim.onExit body finalizer flag) fiber).snd = Option.none)

-- census: op.SetInterruptible
#check (@Effect4.Prim.ensure_setInterruptible_flag :
  ∀ {ν σ : Type u} {β : Type v} {ε δ ι α : Type u} (flag : Bool) (fiber : Effect4.FrameFiber ν σ
  β ε δ ι α), (Effect4.Prim.ensure (Effect4.Prim.setInterruptible flag) fiber).fst.interruptible
  = flag)

-- census: op.SetInterruptible
#check (@Effect4.Prim.ensure_setInterruptible_stack :
  ∀ {ν σ : Type u} {β : Type v} {ε δ ι α : Type u} (flag : Bool) (fiber : Effect4.FrameFiber ν σ
  β ε δ ι α), (Effect4.Prim.ensure (Effect4.Prim.setInterruptible flag) fiber).fst.stack =
  fiber.stack)

-- census: op.SetInterruptible
#check (@Effect4.Prim.ensure_setInterruptible_substitutes :
  ∀ {ν σ : Type u} {β : Type v} {ε δ ι α : Type u} (cause : Effect4.Cause ε δ ι α) (fiber :
  Effect4.FrameFiber ν σ β ε δ ι α), fiber.interruptedCause = Option.some cause →
  Effect4.Prim.ensure (Effect4.Prim.setInterruptible Bool.true) fiber = (Effect4.FrameFiber.mk
  fiber.current fiber.stack Bool.true fiber.interruptedCause fiber.deferredInterrupt,
  Option.some (Effect4.Prim.failure cause)))

-- census: op.SetInterruptible
#check (@Effect4.Prim.ensure_setInterruptible_false_no_replacement :
  ∀ {ν σ : Type u} {β : Type v} {ε δ ι α : Type u} (fiber : Effect4.FrameFiber ν σ β ε δ ι α),
  (Effect4.Prim.ensure (Effect4.Prim.setInterruptible Bool.false) fiber).snd = Option.none)

-- census: op.SetInterruptible
#check (@Effect4.Prim.ensure_setInterruptible_no_pending :
  ∀ {ν σ : Type u} {β : Type v} {ε δ ι α : Type u} (flag : Bool) (fiber : Effect4.FrameFiber ν σ
  β ε δ ι α), fiber.interruptedCause = Option.none → Effect4.Prim.ensure
  (Effect4.Prim.setInterruptible flag) fiber = (Effect4.FrameFiber.mk fiber.current fiber.stack
  flag fiber.interruptedCause fiber.deferredInterrupt, Option.none))

-- census: op.AsyncFinalizer
#check (@Effect4.Prim.ensure_asyncFinalizer_masks :
  ∀ {ν σ : Type u} {β : Type v} {ε δ ι α : Type u} (onInterrupt : ν) (fiber :
  Effect4.FrameFiber ν σ β ε δ ι α), fiber.interruptible = Bool.true → Effect4.Prim.ensure
  (Effect4.Prim.asyncFinalizer onInterrupt) fiber = (Effect4.FrameFiber.mk fiber.current
  (Effect4.Prim.setInterruptible Bool.true :: fiber.stack) Bool.false fiber.interruptedCause
  fiber.deferredInterrupt, Option.none))

-- census: op.AsyncFinalizer
#check (@Effect4.Prim.ensure_asyncFinalizer_already_masked :
  ∀ {ν σ : Type u} {β : Type v} {ε δ ι α : Type u} (onInterrupt : ν) (fiber :
  Effect4.FrameFiber ν σ β ε δ ι α), fiber.interruptible = Bool.false → Effect4.Prim.ensure
  (Effect4.Prim.asyncFinalizer onInterrupt) fiber = (fiber, Option.none))

-- census: op.AsyncFinalizer
#check (@Effect4.Prim.ensure_asyncFinalizer_no_replacement :
  ∀ {ν σ : Type u} {β : Type v} {ε δ ι α : Type u} (onInterrupt : ν) (fiber :
  Effect4.FrameFiber ν σ β ε δ ι α), (Effect4.Prim.ensure (Effect4.Prim.asyncFinalizer
  onInterrupt) fiber).snd = Option.none)

-- census: rule.frames-are-primitives
#check (@Effect4.Prim.answerOf_replacement :
  ∀ {ν σ : Type u} {β : Type v} {ε δ ι α : Type u} (frame next : Effect4.Prim ν σ β ε δ ι α)
  (demand : Effect4.Arm), Effect4.Prim.answerOf frame demand (Option.some next) = Option.some
  (Effect4.ContAnswer.replacement next))

-- census: rule.frames-are-primitives
#check (@Effect4.Prim.answerOf_arm :
  ∀ {ν σ : Type u} {β : Type v} {ε δ ι α : Type u} (frame : Effect4.Prim ν σ β ε δ ι α) (demand
  : Effect4.Arm), Effect4.Prim.hasArm frame demand = Bool.true → Effect4.Prim.answerOf frame
  demand Option.none = Option.some (Effect4.ContAnswer.frame frame))

-- census: rule.frames-are-primitives
#check (@Effect4.Prim.answerOf_missing :
  ∀ {ν σ : Type u} {β : Type v} {ε δ ι α : Type u} (frame : Effect4.Prim ν σ β ε δ ι α) (demand
  : Effect4.Arm), Effect4.Prim.hasArm frame demand = Bool.false → Effect4.Prim.answerOf frame
  demand Option.none = Option.none)

-- census: rule.frames-are-primitives
#check (@Effect4.Prim.answerOf_frame_eq :
  ∀ {ν σ : Type u} {β : Type v} {ε δ ι α : Type u} (frame answering : Effect4.Prim ν σ β ε δ ι
  α) (demand : Effect4.Arm) (replacement : Option (Effect4.Prim ν σ β ε δ ι α)),
  Effect4.Prim.answerOf frame demand replacement = Option.some (Effect4.ContAnswer.frame
  answering) → answering = frame ∧ Effect4.Prim.hasArm frame demand = Bool.true)

/-! F5: the arms themselves (census: op.OnSuccess, op.OnFailure,
op.OnSuccessAndFailure, op.Exit, op.OnExit, op.Iterator, op.While,
frame-arm.*). -/

#check (@Effect4.Prim.armA :
  {ν σ : Type u} → {β : Type v} → {ε δ ι α : Type u} → [DecidableEq ε] → [DecidableEq δ] →
  [DecidableEq ι] → [DecidableEq α] → Effect4.PrimInterp ν σ β ε δ ι α → Effect4.Prim ν σ β ε δ
  ι α → β → Option (Effect4.Exit β ε δ ι α) → Option (Effect4.Prim ν σ β ε δ ι α × List
  (Effect4.Prim ν σ β ε δ ι α)))

#check (@Effect4.Prim.armE :
  {ν σ : Type u} → {β : Type v} → {ε δ ι α : Type u} → [DecidableEq ε] → [DecidableEq δ] →
  [DecidableEq ι] → [DecidableEq α] → Effect4.PrimInterp ν σ β ε δ ι α → Effect4.Prim ν σ β ε δ
  ι α → Effect4.Cause ε δ ι α → Option (Effect4.Exit β ε δ ι α) → Option (Effect4.Prim ν σ β ε δ
  ι α × List (Effect4.Prim ν σ β ε δ ι α)))

#check (@Effect4.Prim.finalizerEvents :
  {ν σ : Type u} → {β : Type v} → {ε δ ι α : Type u} → Effect4.Prim ν σ β ε δ ι α → Effect4.Exit
  β ε δ ι α → List (Effect4.FrameEvent ν σ β ε δ ι α))

#check (@Effect4.Prim.iteratorFolded :
  {ν σ : Type u} → {β : Type v} → {ε δ ι α : Type u} → Effect4.PrimInterp ν σ β ε δ ι α →
  Effect4.Prim ν σ β ε δ ι α → β → List β)

-- census: rule.frames-are-primitives
#check (@Effect4.Prim.armA_isSome :
  ∀ {ν σ : Type u} {β : Type v} {ε δ ι α : Type u} [inst : DecidableEq ε] [inst_1 : DecidableEq
  δ] [inst_2 : DecidableEq ι] [inst_3 : DecidableEq α] (interp : Effect4.PrimInterp ν σ β ε δ ι
  α) (frame : Effect4.Prim ν σ β ε δ ι α) (value : β) (provided : Option (Effect4.Exit β ε δ ι
  α)), Option.isSome (Effect4.Prim.armA interp frame value provided) = Effect4.Prim.hasArm frame
  Effect4.Arm.contA)

-- census: rule.frames-are-primitives
#check (@Effect4.Prim.armE_isSome :
  ∀ {ν σ : Type u} {β : Type v} {ε δ ι α : Type u} [inst : DecidableEq ε] [inst_1 : DecidableEq
  δ] [inst_2 : DecidableEq ι] [inst_3 : DecidableEq α] (interp : Effect4.PrimInterp ν σ β ε δ ι
  α) (frame : Effect4.Prim ν σ β ε δ ι α) (cause : Effect4.Cause ε δ ι α) (provided : Option
  (Effect4.Exit β ε δ ι α)), Option.isSome (Effect4.Prim.armE interp frame cause provided) =
  Effect4.Prim.hasArm frame Effect4.Arm.contE)

-- census: op.OnSuccess
#check (@Effect4.Prim.armA_onSuccess :
  ∀ {ν σ : Type u} {β : Type v} {ε δ ι α : Type u} [inst : DecidableEq ε] [inst_1 : DecidableEq
  δ] [inst_2 : DecidableEq ι] [inst_3 : DecidableEq α] (interp : Effect4.PrimInterp ν σ β ε δ ι
  α) (body : Effect4.Prim ν σ β ε δ ι α) (onValue : ν) (value : β) (provided : Option
  (Effect4.Exit β ε δ ι α)), Effect4.Prim.armA interp (Effect4.Prim.onSuccess body onValue)
  value provided = Option.some (interp.contA onValue value, []))

-- census: op.OnSuccessAndFailure
#check (@Effect4.Prim.armA_onSuccessAndFailure :
  ∀ {ν σ : Type u} {β : Type v} {ε δ ι α : Type u} [inst : DecidableEq ε] [inst_1 : DecidableEq
  δ] [inst_2 : DecidableEq ι] [inst_3 : DecidableEq α] (interp : Effect4.PrimInterp ν σ β ε δ ι
  α) (body : Effect4.Prim ν σ β ε δ ι α) (onValue onCause : ν) (value : β) (provided : Option
  (Effect4.Exit β ε δ ι α)), Effect4.Prim.armA interp (Effect4.Prim.onSuccessAndFailure body
  onValue onCause) value provided = Option.some (interp.contA onValue value, []))

-- census: op.OnFailure
#check (@Effect4.Prim.armE_onFailure :
  ∀ {ν σ : Type u} {β : Type v} {ε δ ι α : Type u} [inst : DecidableEq ε] [inst_1 : DecidableEq
  δ] [inst_2 : DecidableEq ι] [inst_3 : DecidableEq α] (interp : Effect4.PrimInterp ν σ β ε δ ι
  α) (body : Effect4.Prim ν σ β ε δ ι α) (onCause : ν) (cause : Effect4.Cause ε δ ι α) (provided
  : Option (Effect4.Exit β ε δ ι α)), Effect4.Prim.armE interp (Effect4.Prim.onFailure body
  onCause) cause provided = Option.some (interp.contE onCause cause, []))

-- census: op.OnSuccessAndFailure
#check (@Effect4.Prim.armE_onSuccessAndFailure :
  ∀ {ν σ : Type u} {β : Type v} {ε δ ι α : Type u} [inst : DecidableEq ε] [inst_1 : DecidableEq
  δ] [inst_2 : DecidableEq ι] [inst_3 : DecidableEq α] (interp : Effect4.PrimInterp ν σ β ε δ ι
  α) (body : Effect4.Prim ν σ β ε δ ι α) (onValue onCause : ν) (cause : Effect4.Cause ε δ ι α)
  (provided : Option (Effect4.Exit β ε δ ι α)), Effect4.Prim.armE interp
  (Effect4.Prim.onSuccessAndFailure body onValue onCause) cause provided = Option.some
  (interp.contE onCause cause, []))

-- census: frame-arm.OnSuccess
#check (@Effect4.Prim.armE_onSuccess_none :
  ∀ {ν σ : Type u} {β : Type v} {ε δ ι α : Type u} [inst : DecidableEq ε] [inst_1 : DecidableEq
  δ] [inst_2 : DecidableEq ι] [inst_3 : DecidableEq α] (interp : Effect4.PrimInterp ν σ β ε δ ι
  α) (body : Effect4.Prim ν σ β ε δ ι α) (onValue : ν) (cause : Effect4.Cause ε δ ι α) (provided
  : Option (Effect4.Exit β ε δ ι α)), Effect4.Prim.armE interp (Effect4.Prim.onSuccess body
  onValue) cause provided = Option.none)

-- census: frame-arm.OnFailure
#check (@Effect4.Prim.armA_onFailure_none :
  ∀ {ν σ : Type u} {β : Type v} {ε δ ι α : Type u} [inst : DecidableEq ε] [inst_1 : DecidableEq
  δ] [inst_2 : DecidableEq ι] [inst_3 : DecidableEq α] (interp : Effect4.PrimInterp ν σ β ε δ ι
  α) (body : Effect4.Prim ν σ β ε δ ι α) (onCause : ν) (value : β) (provided : Option
  (Effect4.Exit β ε δ ι α)), Effect4.Prim.armA interp (Effect4.Prim.onFailure body onCause)
  value provided = Option.none)

-- census: frame-arm.AsyncFinalizer
#check (@Effect4.Prim.armA_asyncFinalizer_none :
  ∀ {ν σ : Type u} {β : Type v} {ε δ ι α : Type u} [inst : DecidableEq ε] [inst_1 : DecidableEq
  δ] [inst_2 : DecidableEq ι] [inst_3 : DecidableEq α] (interp : Effect4.PrimInterp ν σ β ε δ ι
  α) (onInterrupt : ν) (value : β) (provided : Option (Effect4.Exit β ε δ ι α)),
  Effect4.Prim.armA interp (Effect4.Prim.asyncFinalizer onInterrupt) value provided =
  Option.none)

-- census: op.AsyncFinalizer
#check (@Effect4.Prim.armE_asyncFinalizer_interrupt :
  ∀ {ν σ : Type u} {β : Type v} {ε δ ι α : Type u} [inst : DecidableEq ε] [inst_1 : DecidableEq
  δ] [inst_2 : DecidableEq ι] [inst_3 : DecidableEq α] (interp : Effect4.PrimInterp ν σ β ε δ ι
  α) (onInterrupt : ν) (cause : Effect4.Cause ε δ ι α) (provided : Option (Effect4.Exit β ε δ ι
  α)), Effect4.Cause.hasInterrupts cause = Bool.true → Effect4.Prim.armE interp
  (Effect4.Prim.asyncFinalizer onInterrupt) cause provided = Option.some (interp.cancelThenFail
  onInterrupt cause, []))

-- census: op.AsyncFinalizer
#check (@Effect4.Prim.armE_asyncFinalizer_no_interrupt :
  ∀ {ν σ : Type u} {β : Type v} {ε δ ι α : Type u} [inst : DecidableEq ε] [inst_1 : DecidableEq
  δ] [inst_2 : DecidableEq ι] [inst_3 : DecidableEq α] (interp : Effect4.PrimInterp ν σ β ε δ ι
  α) (onInterrupt : ν) (cause : Effect4.Cause ε δ ι α) (provided : Option (Effect4.Exit β ε δ ι
  α)), Effect4.Cause.hasInterrupts cause = Bool.false → Effect4.Prim.armE interp
  (Effect4.Prim.asyncFinalizer onInterrupt) cause provided = Option.some (Effect4.Prim.failure
  cause, []))

-- census: op.AsyncFinalizer
#check (@Effect4.Prim.armE_asyncFinalizer_pushes_nothing :
  ∀ {ν σ : Type u} {β : Type v} {ε δ ι α : Type u} [inst : DecidableEq ε] [inst_1 : DecidableEq
  δ] [inst_2 : DecidableEq ι] [inst_3 : DecidableEq α] (interp : Effect4.PrimInterp ν σ β ε δ ι
  α) (onInterrupt : ν) (cause : Effect4.Cause ε δ ι α) (left right : Option (Effect4.Exit β ε δ
  ι α)), Effect4.Prim.armE interp (Effect4.Prim.asyncFinalizer onInterrupt) cause left =
  Effect4.Prim.armE interp (Effect4.Prim.asyncFinalizer onInterrupt) cause right)

-- census: frame-arm.SetInterruptible
#check (@Effect4.Prim.armA_setInterruptible_none :
  ∀ {ν σ : Type u} {β : Type v} {ε δ ι α : Type u} [inst : DecidableEq ε] [inst_1 : DecidableEq
  δ] [inst_2 : DecidableEq ι] [inst_3 : DecidableEq α] (interp : Effect4.PrimInterp ν σ β ε δ ι
  α) (flag : Bool) (value : β) (provided : Option (Effect4.Exit β ε δ ι α)), Effect4.Prim.armA
  interp (Effect4.Prim.setInterruptible flag) value provided = Option.none)

-- census: frame-arm.SetInterruptible
#check (@Effect4.Prim.armE_setInterruptible_none :
  ∀ {ν σ : Type u} {β : Type v} {ε δ ι α : Type u} [inst : DecidableEq ε] [inst_1 : DecidableEq
  δ] [inst_2 : DecidableEq ι] [inst_3 : DecidableEq α] (interp : Effect4.PrimInterp ν σ β ε δ ι
  α) (flag : Bool) (cause : Effect4.Cause ε δ ι α) (provided : Option (Effect4.Exit β ε δ ι α)),
  Effect4.Prim.armE interp (Effect4.Prim.setInterruptible flag) cause provided = Option.none)

-- census: frame-arm.While
#check (@Effect4.Prim.armE_whileLoop_none :
  ∀ {ν σ : Type u} {β : Type v} {ε δ ι α : Type u} [inst : DecidableEq ε] [inst_1 : DecidableEq
  δ] [inst_2 : DecidableEq ι] [inst_3 : DecidableEq α] (interp : Effect4.PrimInterp ν σ β ε δ ι
  α) (loop : ν) (cursor : β) (cause : Effect4.Cause ε δ ι α) (provided : Option (Effect4.Exit β
  ε δ ι α)), Effect4.Prim.armE interp (Effect4.Prim.whileLoop loop cursor) cause provided =
  Option.none)

-- census: frame-arm.Iterator
#check (@Effect4.Prim.armE_iterator_none :
  ∀ {ν σ : Type u} {β : Type v} {ε δ ι α : Type u} [inst : DecidableEq ε] [inst_1 : DecidableEq
  δ] [inst_2 : DecidableEq ι] [inst_3 : DecidableEq α] (interp : Effect4.PrimInterp ν σ β ε δ ι
  α) (generator : ν) (cursor : β) (cause : Effect4.Cause ε δ ι α) (provided : Option
  (Effect4.Exit β ε δ ι α)), Effect4.Prim.armE interp (Effect4.Prim.iterator generator cursor)
  cause provided = Option.none)

-- census: op.Exit
#check (@Effect4.Prim.armA_exitFrame_provided :
  ∀ {ν σ : Type u} {β : Type v} {ε δ ι α : Type u} [inst : DecidableEq ε] [inst_1 : DecidableEq
  δ] [inst_2 : DecidableEq ι] [inst_3 : DecidableEq α] (interp : Effect4.PrimInterp ν σ β ε δ ι
  α) (body : Effect4.Prim ν σ β ε δ ι α) (value : β) (exit : Effect4.Exit β ε δ ι α),
  Effect4.Prim.armA interp (Effect4.Prim.exitFrame body) value (Option.some exit) = Option.some
  (Effect4.Prim.success (interp.reifyExit exit), []))

-- census: op.Exit
#check (@Effect4.Prim.armA_exitFrame_none :
  ∀ {ν σ : Type u} {β : Type v} {ε δ ι α : Type u} [inst : DecidableEq ε] [inst_1 : DecidableEq
  δ] [inst_2 : DecidableEq ι] [inst_3 : DecidableEq α] (interp : Effect4.PrimInterp ν σ β ε δ ι
  α) (body : Effect4.Prim ν σ β ε δ ι α) (value : β), Effect4.Prim.armA interp
  (Effect4.Prim.exitFrame body) value Option.none = Option.some (Effect4.Prim.success
  (interp.reifyExit (Effect4.Exit.success value)), []))

-- census: op.Exit
#check (@Effect4.Prim.armE_exitFrame_provided :
  ∀ {ν σ : Type u} {β : Type v} {ε δ ι α : Type u} [inst : DecidableEq ε] [inst_1 : DecidableEq
  δ] [inst_2 : DecidableEq ι] [inst_3 : DecidableEq α] (interp : Effect4.PrimInterp ν σ β ε δ ι
  α) (body : Effect4.Prim ν σ β ε δ ι α) (cause : Effect4.Cause ε δ ι α) (exit : Effect4.Exit β
  ε δ ι α), Effect4.Prim.armE interp (Effect4.Prim.exitFrame body) cause (Option.some exit) =
  Option.some (Effect4.Prim.success (interp.reifyExit exit), []))

-- census: op.Exit
#check (@Effect4.Prim.armE_exitFrame_none :
  ∀ {ν σ : Type u} {β : Type v} {ε δ ι α : Type u} [inst : DecidableEq ε] [inst_1 : DecidableEq
  δ] [inst_2 : DecidableEq ι] [inst_3 : DecidableEq α] (interp : Effect4.PrimInterp ν σ β ε δ ι
  α) (body : Effect4.Prim ν σ β ε δ ι α) (cause : Effect4.Cause ε δ ι α), Effect4.Prim.armE
  interp (Effect4.Prim.exitFrame body) cause Option.none = Option.some (Effect4.Prim.success
  (interp.reifyExit (Effect4.Exit.failure cause)), []))

-- census: op.OnExit
#check (@Effect4.Prim.armA_onExit :
  ∀ {ν σ : Type u} {β : Type v} {ε δ ι α : Type u} [inst : DecidableEq ε] [inst_1 : DecidableEq
  δ] [inst_2 : DecidableEq ι] [inst_3 : DecidableEq α] (interp : Effect4.PrimInterp ν σ β ε δ ι
  α) (body : Effect4.Prim ν σ β ε δ ι α) (finalizer : ν) (flag : Bool) (value : β) (exit :
  Effect4.Exit β ε δ ι α), Effect4.Prim.armA interp (Effect4.Prim.onExit body finalizer flag)
  value (Option.some exit) = Option.some (Effect4.Prim.ofExit
  (Effect4.Exit.restoreAfterFinalizer exit (interp.finalizerExit finalizer exit)), []))

-- census: op.OnExit
#check (@Effect4.Prim.armE_onExit :
  ∀ {ν σ : Type u} {β : Type v} {ε δ ι α : Type u} [inst : DecidableEq ε] [inst_1 : DecidableEq
  δ] [inst_2 : DecidableEq ι] [inst_3 : DecidableEq α] (interp : Effect4.PrimInterp ν σ β ε δ ι
  α) (body : Effect4.Prim ν σ β ε δ ι α) (finalizer : ν) (flag : Bool) (cause : Effect4.Cause ε
  δ ι α) (exit : Effect4.Exit β ε δ ι α), Effect4.Prim.armE interp (Effect4.Prim.onExit body
  finalizer flag) cause (Option.some exit) = Option.some (Effect4.Prim.ofExit
  (Effect4.Exit.restoreAfterFinalizer exit (interp.finalizerExit finalizer exit)), []))

-- census: op.OnExit
#check (@Effect4.Prim.onExit_finalizer_success_restores :
  ∀ {ν σ : Type u} {β : Type v} {ε δ ι α : Type u} [inst : DecidableEq ε] [inst_1 : DecidableEq
  δ] [inst_2 : DecidableEq ι] [inst_3 : DecidableEq α] (interp : Effect4.PrimInterp ν σ β ε δ ι
  α) (body : Effect4.Prim ν σ β ε δ ι α) (finalizer : ν) (flag : Bool) (value : β) (exit :
  Effect4.Exit β ε δ ι α), interp.finalizerExit finalizer exit = Effect4.Exit.success () →
  Effect4.Prim.armA interp (Effect4.Prim.onExit body finalizer flag) value (Option.some exit) =
  Option.some (Effect4.Prim.ofExit exit, []))

-- census: op.OnExit
#check (@Effect4.Prim.onExit_finalizer_failure_merges :
  ∀ {ν σ : Type u} {β : Type v} {ε δ ι α : Type u} [inst : DecidableEq ε] [inst_1 : DecidableEq
  δ] [inst_2 : DecidableEq ι] [inst_3 : DecidableEq α] (interp : Effect4.PrimInterp ν σ β ε δ ι
  α) (body : Effect4.Prim ν σ β ε δ ι α) (finalizer : ν) (flag : Bool) (cause finalizerCause :
  Effect4.Cause ε δ ι α), interp.finalizerExit finalizer (Effect4.Exit.failure cause) =
  Effect4.Exit.failure finalizerCause → Effect4.Prim.armE interp (Effect4.Prim.onExit body
  finalizer flag) cause (Option.some (Effect4.Exit.failure cause)) = Option.some
  (Effect4.Prim.failure (Effect4.Cause.combine cause finalizerCause), []))

-- census: op.OnExit
#check (@Effect4.Prim.onExit_success_finalizer_failure :
  ∀ {ν σ : Type u} {β : Type v} {ε δ ι α : Type u} [inst : DecidableEq ε] [inst_1 : DecidableEq
  δ] [inst_2 : DecidableEq ι] [inst_3 : DecidableEq α] (interp : Effect4.PrimInterp ν σ β ε δ ι
  α) (body : Effect4.Prim ν σ β ε δ ι α) (finalizer : ν) (flag : Bool) (value produced : β)
  (finalizerCause : Effect4.Cause ε δ ι α), interp.finalizerExit finalizer (Effect4.Exit.success
  produced) = Effect4.Exit.failure finalizerCause → Effect4.Prim.armA interp
  (Effect4.Prim.onExit body finalizer flag) value (Option.some (Effect4.Exit.success produced))
  = Option.some (Effect4.Prim.failure finalizerCause, []))

-- census: frame-arm.OnExit
#check (@Effect4.Prim.onExit_arm_is_per_frame :
  ∀ {ν σ : Type u} {β : Type v} {ε δ ι α : Type u} [inst : DecidableEq ε] [inst_1 : DecidableEq
  δ] [inst_2 : DecidableEq ι] [inst_3 : DecidableEq α] (interp : Effect4.PrimInterp ν σ β ε δ ι
  α) (body other : Effect4.Prim ν σ β ε δ ι α) (finalizer : ν) (flag otherFlag : Bool) (value :
  β) (provided : Option (Effect4.Exit β ε δ ι α)), Effect4.Prim.armA interp (Effect4.Prim.onExit
  body finalizer flag) value provided = Effect4.Prim.armA interp (Effect4.Prim.onExit other
  finalizer otherFlag) value provided)

-- census: op.OnSuccess
#check (@Effect4.Prim.onSuccess_arm_is_per_instance :
  ∀ {ν σ : Type u} {β : Type v} {ε δ ι α : Type u} [inst : DecidableEq ε] [inst_1 : DecidableEq
  δ] [inst_2 : DecidableEq ι] [inst_3 : DecidableEq α] (interp : Effect4.PrimInterp ν σ β ε δ ι
  α) (body : Effect4.Prim ν σ β ε δ ι α) (left right : ν) (value : β) (provided : Option
  (Effect4.Exit β ε δ ι α)), interp.contA left value ≠ interp.contA right value →
  Effect4.Prim.armA interp (Effect4.Prim.onSuccess body left) value provided ≠ Effect4.Prim.armA
  interp (Effect4.Prim.onSuccess body right) value provided)

-- census: op.OnFailure
#check (@Effect4.Prim.onFailure_arm_is_per_instance :
  ∀ {ν σ : Type u} {β : Type v} {ε δ ι α : Type u} [inst : DecidableEq ε] [inst_1 : DecidableEq
  δ] [inst_2 : DecidableEq ι] [inst_3 : DecidableEq α] (interp : Effect4.PrimInterp ν σ β ε δ ι
  α) (body : Effect4.Prim ν σ β ε δ ι α) (left right : ν) (cause : Effect4.Cause ε δ ι α)
  (provided : Option (Effect4.Exit β ε δ ι α)), interp.contE left cause ≠ interp.contE right
  cause → Effect4.Prim.armE interp (Effect4.Prim.onFailure body left) cause provided ≠
  Effect4.Prim.armE interp (Effect4.Prim.onFailure body right) cause provided)

-- census: op.OnSuccessAndFailure
#check (@Effect4.Prim.onSuccessAndFailure_arms_are_per_instance :
  ∀ {ν σ : Type u} {β : Type v} {ε δ ι α : Type u} [inst : DecidableEq ε] [inst_1 : DecidableEq
  δ] [inst_2 : DecidableEq ι] [inst_3 : DecidableEq α] (interp : Effect4.PrimInterp ν σ β ε δ ι
  α) (body : Effect4.Prim ν σ β ε δ ι α) (onValue onCause : ν) (value : β) (cause :
  Effect4.Cause ε δ ι α) (provided : Option (Effect4.Exit β ε δ ι α)), Effect4.Prim.armA interp
  (Effect4.Prim.onSuccessAndFailure body onValue onCause) value provided = Option.some
  (interp.contA onValue value, []) ∧ Effect4.Prim.armE interp (Effect4.Prim.onSuccessAndFailure
  body onValue onCause) cause provided = Option.some (interp.contE onCause cause, []))

-- census: op.While
#check (@Effect4.Prim.armA_whileLoop_continue :
  ∀ {ν σ : Type u} {β : Type v} {ε δ ι α : Type u} [inst : DecidableEq ε]
    [inst_1 : DecidableEq δ] [inst_2 : DecidableEq ι] [inst_3 : DecidableEq α] (interp : Effect4.PrimInterp ν σ β ε δ ι α)
    (loop : ν) (cursor value : β) (provided : Option (Effect4.Exit β ε δ ι α)),
    interp.loopTest loop (interp.loopStep loop cursor value) = Bool.true →
      Effect4.Prim.armA interp (Effect4.Prim.whileLoop loop cursor) value provided =
        Option.some
          (interp.loopBody loop (interp.loopStep loop cursor value),
            [Effect4.Prim.whileLoop loop (interp.loopStep loop cursor value)]))

-- census: op.While
#check (@Effect4.Prim.armA_whileLoop_stop :
  ∀ {ν σ : Type u} {β : Type v} {ε δ ι α : Type u} [inst : DecidableEq ε]
    [inst_1 : DecidableEq δ] [inst_2 : DecidableEq ι] [inst_3 : DecidableEq α] (interp : Effect4.PrimInterp ν σ β ε δ ι α)
    (loop : ν) (cursor value : β) (provided : Option (Effect4.Exit β ε δ ι α)),
    interp.loopTest loop (interp.loopStep loop cursor value) = Bool.false →
      Effect4.Prim.armA interp (Effect4.Prim.whileLoop loop cursor) value provided =
        Option.some (Effect4.Prim.success (interp.loopDone loop), []))

-- census: op.Iterator
#check (@Effect4.Prim.armA_iterator_done :
  ∀ {ν σ : Type u} {β : Type v} {ε δ ι α : Type u} [inst : DecidableEq ε] [inst_1 : DecidableEq
  δ] [inst_2 : DecidableEq ι] [inst_3 : DecidableEq α] (interp : Effect4.PrimInterp ν σ β ε δ ι
  α) (generator : ν) (cursor value result : β) (provided : Option (Effect4.Exit β ε δ ι α)),
  (interp.iterNext generator value).snd = Effect4.IterStep.done result → Effect4.Prim.armA
  interp (Effect4.Prim.iterator generator cursor) value provided = Option.some
  (Effect4.Prim.success result, []))

-- census: op.Iterator
#check (@Effect4.Prim.armA_iterator_halt :
  ∀ {ν σ : Type u} {β : Type v} {ε δ ι α : Type u} [inst : DecidableEq ε] [inst_1 : DecidableEq
  δ] [inst_2 : DecidableEq ι] [inst_3 : DecidableEq α] (interp : Effect4.PrimInterp ν σ β ε δ ι
  α) (generator : ν) (cursor value : β) (cause : Effect4.Cause ε δ ι α) (provided : Option
  (Effect4.Exit β ε δ ι α)), (interp.iterNext generator value).snd = Effect4.IterStep.halt cause
  → Effect4.Prim.armA interp (Effect4.Prim.iterator generator cursor) value provided =
  Option.some (Effect4.Prim.failure cause, []))

-- census: op.Iterator
#check (@Effect4.Prim.armA_iterator_resume :
  ∀ {ν σ : Type u} {β : Type v} {ε δ ι α : Type u} [inst : DecidableEq ε]
    [inst_1 : DecidableEq δ] [inst_2 : DecidableEq ι] [inst_3 : DecidableEq α] (interp : Effect4.PrimInterp ν σ β ε δ ι α)
    (generator : ν) (cursor value : β) (next : Effect4.Prim ν σ β ε δ ι α) (continueAs : ν)
    (provided : Option (Effect4.Exit β ε δ ι α)),
    (interp.iterNext generator value).snd = Effect4.IterStep.resume next continueAs →
      Effect4.Prim.armA interp (Effect4.Prim.iterator generator cursor) value provided =
        Option.some (next, [Effect4.Prim.iterator continueAs cursor]))

-- census: op.Iterator
#check (@Effect4.Prim.iteratorFolded_eq :
  ∀ {ν σ : Type u} {β : Type v} {ε δ ι α : Type u} [DecidableEq ε] [DecidableEq δ] [DecidableEq
  ι] [DecidableEq α] (interp : Effect4.PrimInterp ν σ β ε δ ι α) (generator : ν) (cursor value :
  β), Effect4.Prim.iteratorFolded interp (Effect4.Prim.iterator generator cursor) value =
  (interp.iterNext generator value).fst)

-- census: op.Iterator
#check (@Effect4.Prim.iterator_folds_inline :
  ∀ {ν σ : Type u} {β : Type v} {ε δ ι α : Type u} [inst : DecidableEq ε] [inst_1 : DecidableEq
  δ] [inst_2 : DecidableEq ι] [inst_3 : DecidableEq α] (left right : Effect4.PrimInterp ν σ β ε
  δ ι α) (generator : ν) (cursor value : β) (provided : Option (Effect4.Exit β ε δ ι α)),
  (left.iterNext generator value).snd = (right.iterNext generator value).snd → Effect4.Prim.armA
  left (Effect4.Prim.iterator generator cursor) value provided = Effect4.Prim.armA right
  (Effect4.Prim.iterator generator cursor) value provided)

-- census: op.OnExit
#check (@Effect4.Prim.finalizerEvents_onExit :
  ∀ {ν σ : Type u} {β : Type v} {ε δ ι α : Type u} (body : Effect4.Prim ν σ β ε δ ι α)
  (finalizer : ν) (flag : Bool) (exit : Effect4.Exit β ε δ ι α), Effect4.Prim.finalizerEvents
  (Effect4.Prim.onExit body finalizer flag) exit = [Effect4.FrameEvent.ranFinalizer finalizer
  exit])

-- census: op.OnExit
#check (@Effect4.Prim.finalizerEvents_onSuccess :
  ∀ {ν σ : Type u} {β : Type v} {ε δ ι α : Type u} (body : Effect4.Prim ν σ β ε δ ι α) (onValue
  : ν) (exit : Effect4.Exit β ε δ ι α), Effect4.Prim.finalizerEvents (Effect4.Prim.onSuccess
  body onValue) exit = [])

-- census: op.OnExit
#check (@Effect4.Prim.finalizerEvents_onFailure :
  ∀ {ν σ : Type u} {β : Type v} {ε δ ι α : Type u} (body : Effect4.Prim ν σ β ε δ ι α) (onCause
  : ν) (exit : Effect4.Exit β ε δ ι α), Effect4.Prim.finalizerEvents (Effect4.Prim.onFailure
  body onCause) exit = [])

/-! F6: the pop (census: checkpoint.getcont-deferred,
checkpoint.exit-failcause-skip, rule.frames-are-primitives,
rule.interrupt-bypasses-handlers, op.Success, op.Failure).

`popFrom` is rc.112's `getCont` pop loop fused with the handler-skipping loop of
`exitFailCause`, and *unfused* from the frame list it started with: rc.112 pops
from the live `_stack`, so a frame a `contAll` pushed is popped before the
frames already below it. `docs/FRAMES-DAG.md:200-211` reserved that obligation
for the packet that adds `AsyncFinalizer`; `popFrom_pass_no_push` is the half
that still agrees with the old, list-recursive reading and
`popFrom_asyncFinalizer_pops_its_push` is the half that does not. -/

#check (@Effect4.FrameFiber.popFrom :
  {ν σ : Type u} → {β : Type v} → {ε δ ι α : Type u} → Effect4.Arm → Bool → List (Effect4.Prim ν
  σ β ε δ ι α) → Effect4.FrameFiber ν σ β ε δ ι α → Effect4.FramePop ν σ β ε δ ι α)

#check (@Effect4.FrameFiber.passOn :
  {ν σ : Type u} → {β : Type v} → {ε δ ι α : Type u} → Effect4.Prim ν σ β ε δ ι α → Option
  (Effect4.Prim ν σ β ε δ ι α) → Effect4.FramePop ν σ β ε δ ι α → Effect4.FramePop ν σ β ε δ ι
  α)

#check (@Effect4.FrameFiber.continueFrom :
  {ν σ : Type u} → {β : Type v} → {ε δ ι α : Type u} → Effect4.Arm → Bool → Effect4.Prim ν σ β ε
  δ ι α → List (Effect4.Prim ν σ β ε δ ι α) → Effect4.FrameFiber ν σ β ε δ ι α →
  Effect4.FramePop ν σ β ε δ ι α)

-- census: rule.frames-are-primitives
#check (@Effect4.FrameFiber.stack_nil_eq :
  ∀ {ν σ : Type u} {β : Type v} {ε δ ι α : Type u} (fiber : Effect4.FrameFiber ν σ β ε δ ι α),
  fiber.stack = [] → Effect4.FrameFiber.mk fiber.current [] fiber.interruptible
  fiber.interruptedCause fiber.deferredInterrupt = fiber)

-- census: rule.frames-are-primitives
#check (@Effect4.FrameFiber.ensure_stack_cases :
  ∀ {ν σ : Type u} {β : Type v} {ε δ ι α : Type u} (frame : Effect4.Prim ν σ β ε δ ι α) (fiber :
  Effect4.FrameFiber ν σ β ε δ ι α), (Effect4.Prim.ensure frame fiber).fst.stack = fiber.stack ∨
  (Effect4.Prim.ensure frame fiber).fst.stack = Effect4.Prim.setInterruptible Bool.true ::
  fiber.stack ∧ fiber.interruptible = Bool.true ∧ (Effect4.Prim.ensure frame
  fiber).fst.interruptible = Bool.false)

#check (@Effect4.FrameFiber.passPushed :
  {ν σ : Type u} → {β : Type v} → {ε δ ι α : Type u} → Effect4.Arm → Bool → Effect4.FrameFiber ν
  σ β ε δ ι α → Effect4.FramePop ν σ β ε δ ι α)

#check (@Effect4.FrameFiber.joinPushed :
  {ν σ : Type u} → {β : Type v} → {ε δ ι α : Type u} → Effect4.Arm → Bool → Effect4.FrameFiber ν
  σ β ε δ ι α → List (Effect4.Prim ν σ β ε δ ι α) → Effect4.FramePop ν σ β ε δ ι α →
  Effect4.FramePop ν σ β ε δ ι α)

-- census: checkpoint.set-interruptible-contall
#check (@Effect4.FrameFiber.passPushed_setInterruptible_substitutes :
  ∀ {ν σ : Type u} {β : Type v} {ε δ ι α : Type u} (demand : Effect4.Arm) (fiber :
  Effect4.FrameFiber ν σ β ε δ ι α) (below : List (Effect4.Prim ν σ β ε δ ι α)) (cause :
  Effect4.Cause ε δ ι α), fiber.stack = Effect4.Prim.setInterruptible Bool.true :: below →
  fiber.interruptedCause = Option.some cause → Effect4.FrameFiber.passPushed demand Bool.false
  fiber = Effect4.FramePop.mk (Effect4.ContAnswer.replacement (Effect4.Prim.failure cause))
  [Effect4.Prim.setInterruptible Bool.true] (Effect4.Prim.passEvents
  (Effect4.Prim.setInterruptible Bool.true) (Option.some (Effect4.Prim.failure cause)))
  (Effect4.FrameFiber.mk fiber.current below Bool.true fiber.interruptedCause
  fiber.deferredInterrupt))

-- census: rule.frames-are-primitives
#check (@Effect4.FrameFiber.popFrom_pass_no_push :
  ∀ {ν σ : Type u} {β : Type v} {ε δ ι α : Type u} (demand : Effect4.Arm) (skip : Bool) (frame :
  Effect4.Prim ν σ β ε δ ι α) (rest : List (Effect4.Prim ν σ β ε δ ι α)) (fiber :
  Effect4.FrameFiber ν σ β ε δ ι α), fiber.stack = [] → (Effect4.Prim.ensure frame
  fiber).fst.stack = fiber.stack → Effect4.FrameFiber.continueFrom demand skip frame rest fiber
  = Effect4.FrameFiber.popFrom demand skip rest (Effect4.Prim.ensure frame fiber).fst)

-- census: op.AsyncFinalizer
#check (@Effect4.FrameFiber.popFrom_asyncFinalizer_pops_its_push :
  ∀ {ν σ : Type u} {β : Type v} {ε δ ι α : Type u} (onInterrupt : ν) (cause : Effect4.Cause ε δ
  ι α) (fiber : Effect4.FrameFiber ν σ β ε δ ι α), fiber.stack = [] → fiber.interruptible =
  Bool.true → fiber.interruptedCause = Option.some cause → (Effect4.FrameFiber.popFrom
  Effect4.Arm.contA Bool.false [Effect4.Prim.asyncFinalizer onInterrupt] fiber).answer =
  Effect4.ContAnswer.replacement (Effect4.Prim.failure cause) ∧ (Effect4.FrameFiber.popFrom
  Effect4.Arm.contA Bool.false [Effect4.Prim.asyncFinalizer onInterrupt] fiber).popped =
  [Effect4.Prim.asyncFinalizer onInterrupt, Effect4.Prim.setInterruptible Bool.true])

#check (@Effect4.FrameFiber.getCont :
  {ν σ : Type u} → {β : Type v} → {ε δ ι α : Type u} → Effect4.FrameFiber ν σ β ε δ ι α →
  Effect4.Arm → Bool → Effect4.FramePop ν σ β ε δ ι α)

-- census: checkpoint.getcont-deferred
#check (@Effect4.FrameFiber.getCont_deferred :
  ∀ {ν σ : Type u} {β : Type v} {ε δ ι α : Type u} (self : Effect4.FrameFiber ν σ β ε δ ι α)
  (demand : Effect4.Arm), self.deferredInterrupt = Bool.true → Effect4.FrameFiber.getCont self
  demand Bool.false = Effect4.FramePop.mk (Effect4.ContAnswer.deferred
  (Effect4.FrameFiber.pendingCause self)) [] [Effect4.FrameEvent.deferred
  (Effect4.FrameFiber.pendingCause self)] (Effect4.FrameFiber.mk self.current self.stack
  self.interruptible self.interruptedCause Bool.false))

-- census: checkpoint.getcont-deferred
#check (@Effect4.FrameFiber.getCont_deferred_pops_nothing :
  ∀ {ν σ : Type u} {β : Type v} {ε δ ι α : Type u} (self : Effect4.FrameFiber ν σ β ε δ ι α)
  (demand : Effect4.Arm), self.deferredInterrupt = Bool.true → (Effect4.FrameFiber.getCont self
  demand Bool.false).popped = [])

-- census: rule.frames-are-primitives
#check (@Effect4.FrameFiber.getCont_eq_popFrom :
  ∀ {ν σ : Type u} {β : Type v} {ε δ ι α : Type u} (self : Effect4.FrameFiber ν σ β ε δ ι α)
  (demand : Effect4.Arm) (skip : Bool), self.deferredInterrupt = Bool.false →
  Effect4.FrameFiber.getCont self demand skip = Effect4.FrameFiber.popFrom demand skip
  self.stack (Effect4.FrameFiber.mk self.current [] self.interruptible self.interruptedCause
  Bool.false))

-- census: checkpoint.getcont-deferred
#check (@Effect4.FrameFiber.getCont_skip_clears_deferred :
  ∀ {ν σ : Type u} {β : Type v} {ε δ ι α : Type u} (self : Effect4.FrameFiber ν σ β ε δ ι α)
  (demand : Effect4.Arm), Effect4.FrameFiber.getCont self demand Bool.true =
  Effect4.FrameFiber.popFrom demand Bool.true self.stack (Effect4.FrameFiber.mk self.current []
  self.interruptible self.interruptedCause Bool.false))

-- census: rule.frames-are-primitives
#check (@Effect4.FrameFiber.getCont_empty_stack :
  ∀ {ν σ : Type u} {β : Type v} {ε δ ι α : Type u} (self : Effect4.FrameFiber ν σ β ε δ ι α)
  (demand : Effect4.Arm) (skip : Bool), self.deferredInterrupt = Bool.false → self.stack = [] →
  Effect4.FrameFiber.getCont self demand skip = Effect4.FramePop.mk Effect4.ContAnswer.empty []
  [] (Effect4.FrameFiber.mk self.current [] self.interruptible self.interruptedCause
  Bool.false))

-- census: rule.frames-are-primitives
#check (@Effect4.FrameFiber.popFrom_nil :
  ∀ {ν σ : Type u} {β : Type v} {ε δ ι α : Type u} (demand : Effect4.Arm) (skip : Bool) (fiber :
  Effect4.FrameFiber ν σ β ε δ ι α), Effect4.FrameFiber.popFrom demand skip [] fiber =
  Effect4.FramePop.mk Effect4.ContAnswer.empty [] [] fiber)

-- census: rule.frames-are-primitives
#check (@Effect4.FrameFiber.popFrom_answer_answer :
  ∀ {ν σ : Type u} {β : Type v} {ε δ ι α : Type u} (demand : Effect4.Arm) (skip : Bool) (frame :
  Effect4.Prim ν σ β ε δ ι α) (rest : List (Effect4.Prim ν σ β ε δ ι α)) (fiber :
  Effect4.FrameFiber ν σ β ε δ ι α) (answer : Effect4.ContAnswer ν σ β ε δ ι α),
  Effect4.Prim.answerOf frame demand (Effect4.Prim.ensure frame fiber).snd = Option.some answer
  → (skip && Effect4.FrameFiber.interrupted (Effect4.Prim.ensure frame fiber).fst) = Bool.false
  → (Effect4.FrameFiber.popFrom demand skip (frame :: rest) fiber).answer = answer)

-- census: rule.frames-are-primitives
#check (@Effect4.FrameFiber.popFrom_answer_popped :
  ∀ {ν σ : Type u} {β : Type v} {ε δ ι α : Type u} (demand : Effect4.Arm) (skip : Bool) (frame :
  Effect4.Prim ν σ β ε δ ι α) (rest : List (Effect4.Prim ν σ β ε δ ι α)) (fiber :
  Effect4.FrameFiber ν σ β ε δ ι α) (answer : Effect4.ContAnswer ν σ β ε δ ι α),
  Effect4.Prim.answerOf frame demand (Effect4.Prim.ensure frame fiber).snd = Option.some answer
  → (skip && Effect4.FrameFiber.interrupted (Effect4.Prim.ensure frame fiber).fst) = Bool.false
  → (Effect4.FrameFiber.popFrom demand skip (frame :: rest) fiber).popped = [frame])

-- census: rule.frames-are-primitives
#check (@Effect4.FrameFiber.popFrom_answer_events :
  ∀ {ν σ : Type u} {β : Type v} {ε δ ι α : Type u} (demand : Effect4.Arm) (skip : Bool) (frame :
  Effect4.Prim ν σ β ε δ ι α) (rest : List (Effect4.Prim ν σ β ε δ ι α)) (fiber :
  Effect4.FrameFiber ν σ β ε δ ι α) (answer : Effect4.ContAnswer ν σ β ε δ ι α),
  Effect4.Prim.answerOf frame demand (Effect4.Prim.ensure frame fiber).snd = Option.some answer
  → (skip && Effect4.FrameFiber.interrupted (Effect4.Prim.ensure frame fiber).fst) = Bool.false
  → (Effect4.FrameFiber.popFrom demand skip (frame :: rest) fiber).events =
  Effect4.Prim.passEvents frame (Effect4.Prim.ensure frame fiber).snd)

-- census: rule.frames-are-primitives
#check (@Effect4.FrameFiber.popFrom_answer_fiber :
  ∀ {ν σ : Type u} {β : Type v} {ε δ ι α : Type u} (demand : Effect4.Arm) (skip : Bool) (frame :
  Effect4.Prim ν σ β ε δ ι α) (rest : List (Effect4.Prim ν σ β ε δ ι α)) (fiber :
  Effect4.FrameFiber ν σ β ε δ ι α) (answer : Effect4.ContAnswer ν σ β ε δ ι α),
  Effect4.Prim.answerOf frame demand (Effect4.Prim.ensure frame fiber).snd = Option.some answer
  → (skip && Effect4.FrameFiber.interrupted (Effect4.Prim.ensure frame fiber).fst) = Bool.false
  → (Effect4.FrameFiber.popFrom demand skip (frame :: rest) fiber).fiber = have __src :=
  (Effect4.Prim.ensure frame fiber).fst; Effect4.FrameFiber.mk __src.current
  ((Effect4.Prim.ensure frame fiber).fst.stack ++ rest) __src.interruptible
  __src.interruptedCause __src.deferredInterrupt)

-- census: rule.frames-are-primitives
#check (@Effect4.FrameFiber.popFrom_continue_answer :
  ∀ {ν σ : Type u} {β : Type v} {ε δ ι α : Type u} (demand : Effect4.Arm) (skip : Bool) (frame :
  Effect4.Prim ν σ β ε δ ι α) (rest : List (Effect4.Prim ν σ β ε δ ι α)) (fiber :
  Effect4.FrameFiber ν σ β ε δ ι α), Effect4.Prim.answerOf frame demand (Effect4.Prim.ensure
  frame fiber).snd = Option.none ∨ (skip && Effect4.FrameFiber.interrupted (Effect4.Prim.ensure
  frame fiber).fst) = Bool.true → (Effect4.FrameFiber.popFrom demand skip (frame :: rest)
  fiber).answer = (Effect4.FrameFiber.continueFrom demand skip frame rest fiber).answer)

-- census: rule.frames-are-primitives
#check (@Effect4.FrameFiber.popFrom_continue_popped :
  ∀ {ν σ : Type u} {β : Type v} {ε δ ι α : Type u} (demand : Effect4.Arm) (skip : Bool) (frame :
  Effect4.Prim ν σ β ε δ ι α) (rest : List (Effect4.Prim ν σ β ε δ ι α)) (fiber :
  Effect4.FrameFiber ν σ β ε δ ι α), Effect4.Prim.answerOf frame demand (Effect4.Prim.ensure
  frame fiber).snd = Option.none ∨ (skip && Effect4.FrameFiber.interrupted (Effect4.Prim.ensure
  frame fiber).fst) = Bool.true → (Effect4.FrameFiber.popFrom demand skip (frame :: rest)
  fiber).popped = frame :: (Effect4.FrameFiber.continueFrom demand skip frame rest
  fiber).popped)

-- census: rule.frames-are-primitives
#check (@Effect4.FrameFiber.popFrom_continue_events :
  ∀ {ν σ : Type u} {β : Type v} {ε δ ι α : Type u} (demand : Effect4.Arm) (skip : Bool) (frame :
  Effect4.Prim ν σ β ε δ ι α) (rest : List (Effect4.Prim ν σ β ε δ ι α)) (fiber :
  Effect4.FrameFiber ν σ β ε δ ι α), Effect4.Prim.answerOf frame demand (Effect4.Prim.ensure
  frame fiber).snd = Option.none ∨ (skip && Effect4.FrameFiber.interrupted (Effect4.Prim.ensure
  frame fiber).fst) = Bool.true → (Effect4.FrameFiber.popFrom demand skip (frame :: rest)
  fiber).events = Effect4.Prim.passEvents frame (Effect4.Prim.ensure frame fiber).snd ++
  (Effect4.FrameFiber.continueFrom demand skip frame rest fiber).events)

-- census: rule.frames-are-primitives
#check (@Effect4.FrameFiber.popFrom_continue_fiber :
  ∀ {ν σ : Type u} {β : Type v} {ε δ ι α : Type u} (demand : Effect4.Arm) (skip : Bool) (frame :
  Effect4.Prim ν σ β ε δ ι α) (rest : List (Effect4.Prim ν σ β ε δ ι α)) (fiber :
  Effect4.FrameFiber ν σ β ε δ ι α), Effect4.Prim.answerOf frame demand (Effect4.Prim.ensure
  frame fiber).snd = Option.none ∨ (skip && Effect4.FrameFiber.interrupted (Effect4.Prim.ensure
  frame fiber).fst) = Bool.true → (Effect4.FrameFiber.popFrom demand skip (frame :: rest)
  fiber).fiber = (Effect4.FrameFiber.continueFrom demand skip frame rest fiber).fiber)

-- census: rule.frames-are-primitives
#check (@Effect4.FrameFiber.popFrom_answer_hasArm :
  ∀ {ν σ : Type u} {β : Type v} {ε δ ι α : Type u} (demand : Effect4.Arm) (skip : Bool) (frames
  : List (Effect4.Prim ν σ β ε δ ι α)) (fiber : Effect4.FrameFiber ν σ β ε δ ι α) (frame :
  Effect4.Prim ν σ β ε δ ι α), (Effect4.FrameFiber.popFrom demand skip frames fiber).answer =
  Effect4.ContAnswer.frame frame → Effect4.Prim.hasArm frame demand = Bool.true)

-- census: rule.frames-are-primitives
#check (@Effect4.FrameFiber.getCont_answer_hasArm :
  ∀ {ν σ : Type u} {β : Type v} {ε δ ι α : Type u} (self : Effect4.FrameFiber ν σ β ε δ ι α)
  (demand : Effect4.Arm) (skip : Bool) (frame : Effect4.Prim ν σ β ε δ ι α),
  (Effect4.FrameFiber.getCont self demand skip).answer = Effect4.ContAnswer.frame frame →
  Effect4.Prim.hasArm frame demand = Bool.true)

-- census: rule.frames-are-primitives
#check (@Effect4.FrameFiber.passEvents_ranContAll :
  ∀ {ν σ : Type u} {β : Type v} {ε δ ι α : Type u} (frame : Effect4.Prim ν σ β ε δ ι α)
  (replacement : Option (Effect4.Prim ν σ β ε δ ι α)), Effect4.Prim.hasArm frame
  Effect4.Arm.contAll = Bool.true → Effect4.FrameEvent.ranContAll frame ∈
  Effect4.Prim.passEvents frame replacement)

-- census: rule.frames-are-primitives
#check (@Effect4.FrameFiber.passEvents_poppedFrames :
  ∀ {ν σ : Type u} {β : Type v} {ε δ ι α : Type u} (frame : Effect4.Prim ν σ β ε δ ι α)
  (replacement : Option (Effect4.Prim ν σ β ε δ ι α)), Effect4.FrameEvent.poppedFrames
  (Effect4.Prim.passEvents frame replacement) = [frame])

-- census: rule.frames-are-primitives
#check (@Effect4.FrameFiber.popFrom_popped_eq_events :
  ∀ {ν σ : Type u} {β : Type v} {ε δ ι α : Type u} (demand : Effect4.Arm) (skip : Bool) (frames
  : List (Effect4.Prim ν σ β ε δ ι α)) (fiber : Effect4.FrameFiber ν σ β ε δ ι α),
  (Effect4.FrameFiber.popFrom demand skip frames fiber).popped = Effect4.FrameEvent.poppedFrames
  (Effect4.FrameFiber.popFrom demand skip frames fiber).events)

-- census: rule.frames-are-primitives
#check (@Effect4.FrameFiber.popFrom_ranContAll :
  ∀ {ν σ : Type u} {β : Type v} {ε δ ι α : Type u} (demand : Effect4.Arm) (skip : Bool) (frames
  : List (Effect4.Prim ν σ β ε δ ι α)) (fiber : Effect4.FrameFiber ν σ β ε δ ι α) (frame :
  Effect4.Prim ν σ β ε δ ι α), Effect4.Prim.hasArm frame Effect4.Arm.contAll = Bool.true → frame
  ∈ (Effect4.FrameFiber.popFrom demand skip frames fiber).popped → Effect4.FrameEvent.ranContAll
  frame ∈ (Effect4.FrameFiber.popFrom demand skip frames fiber).events)

-- census: rule.frames-are-primitives
#check (@Effect4.FrameFiber.getCont_ranContAll :
  ∀ {ν σ : Type u} {β : Type v} {ε δ ι α : Type u} (self : Effect4.FrameFiber ν σ β ε δ ι α)
  (demand : Effect4.Arm) (skip : Bool) (frame : Effect4.Prim ν σ β ε δ ι α),
  self.deferredInterrupt = Bool.false → Effect4.Prim.hasArm frame Effect4.Arm.contAll =
  Bool.true → frame ∈ (Effect4.FrameFiber.getCont self demand skip).popped →
  Effect4.FrameEvent.ranContAll frame ∈ (Effect4.FrameFiber.getCont self demand skip).events)

-- census: checkpoint.exit-failcause-skip
#check (@Effect4.FrameFiber.getCont_skip_of_no_pending_cause :
  ∀ {ν σ : Type u} {β : Type v} {ε δ ι α : Type u} (self : Effect4.FrameFiber ν σ β ε δ ι α)
  (demand : Effect4.Arm), self.deferredInterrupt = Bool.false → self.interruptedCause =
  Option.none → Effect4.FrameFiber.getCont self demand Bool.true = Effect4.FrameFiber.getCont
  self demand Bool.false)

-- census: checkpoint.exit-failcause-skip
#check (@Effect4.FrameFiber.interrupt_skips_every_handler :
  ∀ {ν σ : Type u} {β : Type v} {ε δ ι α : Type u} (self : Effect4.FrameFiber ν σ β ε δ ι α)
  (demand : Effect4.Arm) (cause : Effect4.Cause ε δ ι α), self.interruptible = Bool.true →
  self.interruptedCause = Option.some cause → (∀ (frame : Effect4.Prim ν σ β ε δ ι α), frame ∈
  self.stack → Effect4.Prim.hasArm frame Effect4.Arm.contAll = Bool.false) →
  (Effect4.FrameFiber.getCont self demand Bool.true).answer = Effect4.ContAnswer.empty)

-- census: rule.interrupt-bypasses-handlers
#check (@Effect4.FrameFiber.getCont_mask_stops_skip :
  ∀ {ν σ : Type u} {β : Type v} {ε δ ι α : Type u} (self : Effect4.FrameFiber ν σ β ε δ ι α)
  (skip : Bool) (rest : List (Effect4.Prim ν σ β ε δ ι α)), self.deferredInterrupt = Bool.false
  → self.stack = Effect4.Prim.setInterruptible Bool.false :: rest → (Effect4.FrameFiber.getCont
  self Effect4.Arm.contE skip).answer = (Effect4.FrameFiber.getCont (Effect4.FrameFiber.mk
  self.current rest Bool.false self.interruptedCause Bool.false) Effect4.Arm.contE skip).answer)

/-! F7: resuming and stepping (census: op.Success, op.Failure, op.Sync,
op.Suspend, op.WithFiber, op.YieldableError, op.Iterator, op.OnSuccess,
op.OnFailure, op.OnSuccessAndFailure, op.Exit, op.OnExit, op.SetInterruptible,
op.While, exit.success-failure). -/

#check (@Effect4.FrameFiber.resumeValue :
  {ν σ : Type u} → {β : Type v} → {ε δ ι α : Type u} → [DecidableEq ε] → [DecidableEq δ] →
  [DecidableEq ι] → [DecidableEq α] → Effect4.PrimInterp ν σ β ε δ ι α → Effect4.FrameFiber ν σ
  β ε δ ι α → β → Option (Effect4.Exit β ε δ ι α) → Effect4.FrameStep ν σ β ε δ ι α × List
  (Effect4.FrameEvent ν σ β ε δ ι α))

#check (@Effect4.FrameFiber.resumeCause :
  {ν σ : Type u} → {β : Type v} → {ε δ ι α : Type u} → [DecidableEq ε] → [DecidableEq δ] →
  [DecidableEq ι] → [DecidableEq α] → Effect4.PrimInterp ν σ β ε δ ι α → Effect4.FrameFiber ν σ
  β ε δ ι α → Effect4.Cause ε δ ι α → Option (Effect4.Exit β ε δ ι α) → Effect4.FrameStep ν σ β
  ε δ ι α × List (Effect4.FrameEvent ν σ β ε δ ι α))

#check (@Effect4.FrameFiber.step :
  {ν σ : Type u} → {β : Type v} → {ε δ ι α : Type u} → [DecidableEq ε] → [DecidableEq δ] →
  [DecidableEq ι] → [DecidableEq α] → Effect4.PrimInterp ν σ β ε δ ι α → Effect4.FrameFiber ν σ
  β ε δ ι α → Effect4.FrameStep ν σ β ε δ ι α × List (Effect4.FrameEvent ν σ β ε δ ι α))

#check (@Effect4.FrameFiber.run :
  {ν σ : Type u} → {β : Type v} → {ε δ ι α : Type u} → [DecidableEq ε] → [DecidableEq δ] →
  [DecidableEq ι] → [DecidableEq α] → Effect4.PrimInterp ν σ β ε δ ι α → Nat →
  Effect4.FrameFiber ν σ β ε δ ι α → Effect4.FrameStep ν σ β ε δ ι α × List (Effect4.FrameEvent
  ν σ β ε δ ι α))

-- census: op.Success
#check (@Effect4.FrameFiber.resumeValue_empty :
  ∀ {ν σ : Type u} {β : Type v} {ε δ ι α : Type u} [inst : DecidableEq ε] [inst_1 : DecidableEq
  δ] [inst_2 : DecidableEq ι] [inst_3 : DecidableEq α] (interp : Effect4.PrimInterp ν σ β ε δ ι
  α) (self : Effect4.FrameFiber ν σ β ε δ ι α) (value : β) (provided : Option (Effect4.Exit β ε
  δ ι α)), (Effect4.FrameFiber.getCont self Effect4.Arm.contA Bool.false).answer =
  Effect4.ContAnswer.empty → Effect4.FrameFiber.resumeValue interp self value provided =
  (Effect4.FrameStep.finished (Option.getD provided (Effect4.Exit.success value)),
  (Effect4.FrameFiber.getCont self Effect4.Arm.contA Bool.false).events ++
  [Effect4.FrameEvent.yielded (Option.getD provided (Effect4.Exit.success value))]))

-- census: checkpoint.getcont-deferred
#check (@Effect4.FrameFiber.resumeValue_deferred :
  ∀ {ν σ : Type u} {β : Type v} {ε δ ι α : Type u} [inst : DecidableEq ε] [inst_1 : DecidableEq
  δ] [inst_2 : DecidableEq ι] [inst_3 : DecidableEq α] (interp : Effect4.PrimInterp ν σ β ε δ ι
  α) (self : Effect4.FrameFiber ν σ β ε δ ι α) (value : β) (provided : Option (Effect4.Exit β ε
  δ ι α)) (cause : Effect4.Cause ε δ ι α), (Effect4.FrameFiber.getCont self Effect4.Arm.contA
  Bool.false).answer = Effect4.ContAnswer.deferred cause → Effect4.FrameFiber.resumeValue interp
  self value provided = (Effect4.FrameStep.running (have __src := (Effect4.FrameFiber.getCont
  self Effect4.Arm.contA Bool.false).fiber; Effect4.FrameFiber.mk (Effect4.Prim.failure cause)
  __src.stack __src.interruptible __src.interruptedCause __src.deferredInterrupt),
  (Effect4.FrameFiber.getCont self Effect4.Arm.contA Bool.false).events))

-- census: checkpoint.set-interruptible-contall
#check (@Effect4.FrameFiber.resumeValue_replacement :
  ∀ {ν σ : Type u} {β : Type v} {ε δ ι α : Type u} [inst : DecidableEq ε] [inst_1 : DecidableEq
  δ] [inst_2 : DecidableEq ι] [inst_3 : DecidableEq α] (interp : Effect4.PrimInterp ν σ β ε δ ι
  α) (self : Effect4.FrameFiber ν σ β ε δ ι α) (value : β) (provided : Option (Effect4.Exit β ε
  δ ι α)) (next : Effect4.Prim ν σ β ε δ ι α), (Effect4.FrameFiber.getCont self
  Effect4.Arm.contA Bool.false).answer = Effect4.ContAnswer.replacement next →
  Effect4.FrameFiber.resumeValue interp self value provided = (Effect4.FrameStep.running (have
  __src := (Effect4.FrameFiber.getCont self Effect4.Arm.contA Bool.false).fiber;
  Effect4.FrameFiber.mk next __src.stack __src.interruptible __src.interruptedCause
  __src.deferredInterrupt), (Effect4.FrameFiber.getCont self Effect4.Arm.contA
  Bool.false).events))

-- census: op.Success
#check (@Effect4.FrameFiber.resumeValue_frame :
  ∀ {ν σ : Type u} {β : Type v} {ε δ ι α : Type u} [inst : DecidableEq ε] [inst_1 : DecidableEq
  δ] [inst_2 : DecidableEq ι] [inst_3 : DecidableEq α] (interp : Effect4.PrimInterp ν σ β ε δ ι
  α) (self : Effect4.FrameFiber ν σ β ε δ ι α) (value : β) (provided : Option (Effect4.Exit β ε
  δ ι α)) (frame next : Effect4.Prim ν σ β ε δ ι α) (pushed : List (Effect4.Prim ν σ β ε δ ι
  α)), (Effect4.FrameFiber.getCont self Effect4.Arm.contA Bool.false).answer =
  Effect4.ContAnswer.frame frame → Effect4.Prim.armA interp frame value provided = Option.some
  (next, pushed) → Effect4.FrameFiber.resumeValue interp self value provided =
  (Effect4.FrameStep.running (have __src := (Effect4.FrameFiber.getCont self Effect4.Arm.contA
  Bool.false).fiber; Effect4.FrameFiber.mk next (pushed ++ (Effect4.FrameFiber.getCont self
  Effect4.Arm.contA Bool.false).fiber.stack) __src.interruptible __src.interruptedCause
  __src.deferredInterrupt), (Effect4.FrameFiber.getCont self Effect4.Arm.contA
  Bool.false).events ++ Effect4.Prim.finalizerEvents frame (Option.getD provided
  (Effect4.Exit.success value)) ++ List.map Effect4.FrameEvent.pushed pushed))

-- census: op.Failure
#check (@Effect4.FrameFiber.resumeCause_empty :
  ∀ {ν σ : Type u} {β : Type v} {ε δ ι α : Type u} [inst : DecidableEq ε] [inst_1 : DecidableEq
  δ] [inst_2 : DecidableEq ι] [inst_3 : DecidableEq α] (interp : Effect4.PrimInterp ν σ β ε δ ι
  α) (self : Effect4.FrameFiber ν σ β ε δ ι α) (cause : Effect4.Cause ε δ ι α) (provided :
  Option (Effect4.Exit β ε δ ι α)), (Effect4.FrameFiber.getCont self Effect4.Arm.contE
  Bool.true).answer = Effect4.ContAnswer.empty → Effect4.FrameFiber.resumeCause interp self
  cause provided = (Effect4.FrameStep.finished (Option.getD provided (Effect4.Exit.failure
  cause)), (Effect4.FrameFiber.getCont self Effect4.Arm.contE Bool.true).events ++
  [Effect4.FrameEvent.yielded (Option.getD provided (Effect4.Exit.failure cause))]))

-- census: checkpoint.getcont-deferred
#check (@Effect4.FrameFiber.resumeCause_deferred :
  ∀ {ν σ : Type u} {β : Type v} {ε δ ι α : Type u} [inst : DecidableEq ε] [inst_1 : DecidableEq
  δ] [inst_2 : DecidableEq ι] [inst_3 : DecidableEq α] (interp : Effect4.PrimInterp ν σ β ε δ ι
  α) (self : Effect4.FrameFiber ν σ β ε δ ι α) (cause deferredCause : Effect4.Cause ε δ ι α)
  (provided : Option (Effect4.Exit β ε δ ι α)), (Effect4.FrameFiber.getCont self
  Effect4.Arm.contE Bool.true).answer = Effect4.ContAnswer.deferred deferredCause →
  Effect4.FrameFiber.resumeCause interp self cause provided = (Effect4.FrameStep.running (have
  __src := (Effect4.FrameFiber.getCont self Effect4.Arm.contE Bool.true).fiber;
  Effect4.FrameFiber.mk (Effect4.Prim.failure deferredCause) __src.stack __src.interruptible
  __src.interruptedCause __src.deferredInterrupt), (Effect4.FrameFiber.getCont self
  Effect4.Arm.contE Bool.true).events))

-- census: checkpoint.set-interruptible-contall
#check (@Effect4.FrameFiber.resumeCause_replacement :
  ∀ {ν σ : Type u} {β : Type v} {ε δ ι α : Type u} [inst : DecidableEq ε] [inst_1 : DecidableEq
  δ] [inst_2 : DecidableEq ι] [inst_3 : DecidableEq α] (interp : Effect4.PrimInterp ν σ β ε δ ι
  α) (self : Effect4.FrameFiber ν σ β ε δ ι α) (cause : Effect4.Cause ε δ ι α) (provided :
  Option (Effect4.Exit β ε δ ι α)) (next : Effect4.Prim ν σ β ε δ ι α),
  (Effect4.FrameFiber.getCont self Effect4.Arm.contE Bool.true).answer =
  Effect4.ContAnswer.replacement next → Effect4.FrameFiber.resumeCause interp self cause
  provided = (Effect4.FrameStep.running (have __src := (Effect4.FrameFiber.getCont self
  Effect4.Arm.contE Bool.true).fiber; Effect4.FrameFiber.mk next __src.stack __src.interruptible
  __src.interruptedCause __src.deferredInterrupt), (Effect4.FrameFiber.getCont self
  Effect4.Arm.contE Bool.true).events))

-- census: op.Failure
#check (@Effect4.FrameFiber.resumeCause_frame :
  ∀ {ν σ : Type u} {β : Type v} {ε δ ι α : Type u} [inst : DecidableEq ε] [inst_1 : DecidableEq
  δ] [inst_2 : DecidableEq ι] [inst_3 : DecidableEq α] (interp : Effect4.PrimInterp ν σ β ε δ ι
  α) (self : Effect4.FrameFiber ν σ β ε δ ι α) (cause : Effect4.Cause ε δ ι α) (provided :
  Option (Effect4.Exit β ε δ ι α)) (frame next : Effect4.Prim ν σ β ε δ ι α) (pushed : List
  (Effect4.Prim ν σ β ε δ ι α)), (Effect4.FrameFiber.getCont self Effect4.Arm.contE
  Bool.true).answer = Effect4.ContAnswer.frame frame → Effect4.Prim.armE interp frame cause
  provided = Option.some (next, pushed) → Effect4.FrameFiber.resumeCause interp self cause
  provided = (Effect4.FrameStep.running (have __src := (Effect4.FrameFiber.getCont self
  Effect4.Arm.contE Bool.true).fiber; Effect4.FrameFiber.mk next (pushed ++
  (Effect4.FrameFiber.getCont self Effect4.Arm.contE Bool.true).fiber.stack) __src.interruptible
  __src.interruptedCause __src.deferredInterrupt), (Effect4.FrameFiber.getCont self
  Effect4.Arm.contE Bool.true).events ++ Effect4.Prim.finalizerEvents frame (Option.getD
  provided (Effect4.Exit.failure cause)) ++ List.map Effect4.FrameEvent.pushed pushed))

-- census: op.Success
#check (@Effect4.FrameFiber.step_success :
  ∀ {ν σ : Type u} {β : Type v} {ε δ ι α : Type u} [inst : DecidableEq ε] [inst_1 : DecidableEq
  δ] [inst_2 : DecidableEq ι] [inst_3 : DecidableEq α] (interp : Effect4.PrimInterp ν σ β ε δ ι
  α) (self : Effect4.FrameFiber ν σ β ε δ ι α) (value : β), Effect4.FrameFiber.step interp
  (Effect4.FrameFiber.mk (Effect4.Prim.success value) self.stack self.interruptible
  self.interruptedCause self.deferredInterrupt) = Effect4.FrameFiber.resumeValue interp
  (Effect4.FrameFiber.mk (Effect4.Prim.success value) self.stack self.interruptible
  self.interruptedCause self.deferredInterrupt) value (Option.some (Effect4.Exit.success
  value)))

-- census: op.Failure
#check (@Effect4.FrameFiber.step_failure :
  ∀ {ν σ : Type u} {β : Type v} {ε δ ι α : Type u} [inst : DecidableEq ε] [inst_1 : DecidableEq
  δ] [inst_2 : DecidableEq ι] [inst_3 : DecidableEq α] (interp : Effect4.PrimInterp ν σ β ε δ ι
  α) (self : Effect4.FrameFiber ν σ β ε δ ι α) (cause : Effect4.Cause ε δ ι α),
  Effect4.FrameFiber.step interp (Effect4.FrameFiber.mk (Effect4.Prim.failure cause) self.stack
  self.interruptible self.interruptedCause self.deferredInterrupt) =
  Effect4.FrameFiber.resumeCause interp (Effect4.FrameFiber.mk (Effect4.Prim.failure cause)
  self.stack self.interruptible self.interruptedCause self.deferredInterrupt) cause (Option.some
  (Effect4.Exit.failure cause)))

-- census: op.Sync
#check (@Effect4.FrameFiber.step_sync :
  ∀ {ν σ : Type u} {β : Type v} {ε δ ι α : Type u} [inst : DecidableEq ε] [inst_1 : DecidableEq
  δ] [inst_2 : DecidableEq ι] [inst_3 : DecidableEq α] (interp : Effect4.PrimInterp ν σ β ε δ ι
  α) (self : Effect4.FrameFiber ν σ β ε δ ι α) (thunk : σ), Effect4.FrameFiber.step interp
  (Effect4.FrameFiber.mk (Effect4.Prim.sync thunk) self.stack self.interruptible
  self.interruptedCause self.deferredInterrupt) = Effect4.FrameFiber.resumeValue interp
  (Effect4.FrameFiber.mk (Effect4.Prim.sync thunk) self.stack self.interruptible
  self.interruptedCause self.deferredInterrupt) (interp.syncValue thunk) Option.none)

-- census: op.Suspend
#check (@Effect4.FrameFiber.step_suspend :
  ∀ {ν σ : Type u} {β : Type v} {ε δ ι α : Type u} [inst : DecidableEq ε] [inst_1 : DecidableEq
  δ] [inst_2 : DecidableEq ι] [inst_3 : DecidableEq α] (interp : Effect4.PrimInterp ν σ β ε δ ι
  α) (self : Effect4.FrameFiber ν σ β ε δ ι α) (thunk : σ), Effect4.FrameFiber.step interp
  (Effect4.FrameFiber.mk (Effect4.Prim.suspend thunk) self.stack self.interruptible
  self.interruptedCause self.deferredInterrupt) = (Effect4.FrameStep.running
  (Effect4.FrameFiber.mk (interp.suspendBody thunk) self.stack self.interruptible
  self.interruptedCause self.deferredInterrupt), []))

-- census: op.WithFiber
#check (@Effect4.FrameFiber.step_withFiber :
  ∀ {ν σ : Type u} {β : Type v} {ε δ ι α : Type u} [inst : DecidableEq ε] [inst_1 : DecidableEq
  δ] [inst_2 : DecidableEq ι] [inst_3 : DecidableEq α] (interp : Effect4.PrimInterp ν σ β ε δ ι
  α) (self : Effect4.FrameFiber ν σ β ε δ ι α) (thunk : σ), Effect4.FrameFiber.step interp
  (Effect4.FrameFiber.mk (Effect4.Prim.withFiber thunk) self.stack self.interruptible
  self.interruptedCause self.deferredInterrupt) = (Effect4.FrameStep.running
  (Effect4.FrameFiber.mk (interp.suspendBody thunk) self.stack self.interruptible
  self.interruptedCause self.deferredInterrupt), []))

-- census: op.YieldableError
#check (@Effect4.FrameFiber.step_yieldableError :
  ∀ {ν σ : Type u} {β : Type v} {ε δ ι α : Type u} [inst : DecidableEq ε] [inst_1 : DecidableEq
  δ] [inst_2 : DecidableEq ι] [inst_3 : DecidableEq α] (interp : Effect4.PrimInterp ν σ β ε δ ι
  α) (self : Effect4.FrameFiber ν σ β ε δ ι α) (error : ε), Effect4.FrameFiber.step interp
  (Effect4.FrameFiber.mk (Effect4.Prim.yieldableError error) self.stack self.interruptible
  self.interruptedCause self.deferredInterrupt) = (Effect4.FrameStep.running
  (Effect4.FrameFiber.mk (Effect4.Prim.failure (Effect4.Cause.fail error)) self.stack
  self.interruptible self.interruptedCause self.deferredInterrupt), []))

-- census: op.OnSuccess
#check (@Effect4.FrameFiber.step_onSuccess :
  ∀ {ν σ : Type u} {β : Type v} {ε δ ι α : Type u} [inst : DecidableEq ε] [inst_1 : DecidableEq
  δ] [inst_2 : DecidableEq ι] [inst_3 : DecidableEq α] (interp : Effect4.PrimInterp ν σ β ε δ ι
  α) (self : Effect4.FrameFiber ν σ β ε δ ι α) (body : Effect4.Prim ν σ β ε δ ι α) (onValue :
  ν), Effect4.FrameFiber.step interp (Effect4.FrameFiber.mk (Effect4.Prim.onSuccess body
  onValue) self.stack self.interruptible self.interruptedCause self.deferredInterrupt) =
  (Effect4.FrameStep.running (Effect4.FrameFiber.mk body (Effect4.Prim.onSuccess body onValue ::
  self.stack) self.interruptible self.interruptedCause self.deferredInterrupt),
  [Effect4.FrameEvent.pushed (Effect4.Prim.onSuccess body onValue)]))

-- census: op.OnFailure
#check (@Effect4.FrameFiber.step_onFailure :
  ∀ {ν σ : Type u} {β : Type v} {ε δ ι α : Type u} [inst : DecidableEq ε] [inst_1 : DecidableEq
  δ] [inst_2 : DecidableEq ι] [inst_3 : DecidableEq α] (interp : Effect4.PrimInterp ν σ β ε δ ι
  α) (self : Effect4.FrameFiber ν σ β ε δ ι α) (body : Effect4.Prim ν σ β ε δ ι α) (onCause :
  ν), Effect4.FrameFiber.step interp (Effect4.FrameFiber.mk (Effect4.Prim.onFailure body
  onCause) self.stack self.interruptible self.interruptedCause self.deferredInterrupt) =
  (Effect4.FrameStep.running (Effect4.FrameFiber.mk body (Effect4.Prim.onFailure body onCause ::
  self.stack) self.interruptible self.interruptedCause self.deferredInterrupt),
  [Effect4.FrameEvent.pushed (Effect4.Prim.onFailure body onCause)]))

-- census: op.OnSuccessAndFailure
#check (@Effect4.FrameFiber.step_onSuccessAndFailure :
  ∀ {ν σ : Type u} {β : Type v} {ε δ ι α : Type u} [inst : DecidableEq ε] [inst_1 : DecidableEq
  δ] [inst_2 : DecidableEq ι] [inst_3 : DecidableEq α] (interp : Effect4.PrimInterp ν σ β ε δ ι
  α) (self : Effect4.FrameFiber ν σ β ε δ ι α) (body : Effect4.Prim ν σ β ε δ ι α) (onValue
  onCause : ν), Effect4.FrameFiber.step interp (Effect4.FrameFiber.mk
  (Effect4.Prim.onSuccessAndFailure body onValue onCause) self.stack self.interruptible
  self.interruptedCause self.deferredInterrupt) = (Effect4.FrameStep.running
  (Effect4.FrameFiber.mk body (Effect4.Prim.onSuccessAndFailure body onValue onCause ::
  self.stack) self.interruptible self.interruptedCause self.deferredInterrupt),
  [Effect4.FrameEvent.pushed (Effect4.Prim.onSuccessAndFailure body onValue onCause)]))

-- census: op.Exit
#check (@Effect4.FrameFiber.step_exitFrame :
  ∀ {ν σ : Type u} {β : Type v} {ε δ ι α : Type u} [inst : DecidableEq ε] [inst_1 : DecidableEq
  δ] [inst_2 : DecidableEq ι] [inst_3 : DecidableEq α] (interp : Effect4.PrimInterp ν σ β ε δ ι
  α) (self : Effect4.FrameFiber ν σ β ε δ ι α) (body : Effect4.Prim ν σ β ε δ ι α),
  Effect4.FrameFiber.step interp (Effect4.FrameFiber.mk (Effect4.Prim.exitFrame body) self.stack
  self.interruptible self.interruptedCause self.deferredInterrupt) = (Effect4.FrameStep.running
  (Effect4.FrameFiber.mk body (Effect4.Prim.exitFrame body :: self.stack) self.interruptible
  self.interruptedCause self.deferredInterrupt), [Effect4.FrameEvent.pushed
  (Effect4.Prim.exitFrame body)]))

-- census: op.OnExit
#check (@Effect4.FrameFiber.step_onExit :
  ∀ {ν σ : Type u} {β : Type v} {ε δ ι α : Type u} [inst : DecidableEq ε] [inst_1 : DecidableEq
  δ] [inst_2 : DecidableEq ι] [inst_3 : DecidableEq α] (interp : Effect4.PrimInterp ν σ β ε δ ι
  α) (self : Effect4.FrameFiber ν σ β ε δ ι α) (body : Effect4.Prim ν σ β ε δ ι α) (finalizer :
  ν) (flag : Bool), Effect4.FrameFiber.step interp (Effect4.FrameFiber.mk (Effect4.Prim.onExit
  body finalizer flag) self.stack self.interruptible self.interruptedCause
  self.deferredInterrupt) = (Effect4.FrameStep.running (Effect4.FrameFiber.mk body
  (Effect4.Prim.onExit body finalizer flag :: self.stack) self.interruptible
  self.interruptedCause self.deferredInterrupt), [Effect4.FrameEvent.pushed (Effect4.Prim.onExit
  body finalizer flag)]))

-- census: op.SetInterruptible
#check (@Effect4.FrameFiber.step_setInterruptible_not_evaluable :
  ∀ {ν σ : Type u} {β : Type v} {ε δ ι α : Type u} [inst : DecidableEq ε] [inst_1 : DecidableEq
  δ] [inst_2 : DecidableEq ι] [inst_3 : DecidableEq α] (interp : Effect4.PrimInterp ν σ β ε δ ι
  α) (self : Effect4.FrameFiber ν σ β ε δ ι α) (flag : Bool), Effect4.FrameFiber.step interp
  (Effect4.FrameFiber.mk (Effect4.Prim.setInterruptible flag) self.stack self.interruptible
  self.interruptedCause self.deferredInterrupt) = (Effect4.FrameStep.running
  (Effect4.FrameFiber.mk (Effect4.Prim.failure (Effect4.Cause.die interp.notImplemented))
  self.stack self.interruptible self.interruptedCause self.deferredInterrupt), []))

-- census: op.AsyncFinalizer
#check (@Effect4.FrameFiber.step_asyncFinalizer_not_evaluable :
  ∀ {ν σ : Type u} {β : Type v} {ε δ ι α : Type u} [inst : DecidableEq ε] [inst_1 : DecidableEq
  δ] [inst_2 : DecidableEq ι] [inst_3 : DecidableEq α] (interp : Effect4.PrimInterp ν σ β ε δ ι
  α) (self : Effect4.FrameFiber ν σ β ε δ ι α) (onInterrupt : ν), Effect4.FrameFiber.step interp
  (Effect4.FrameFiber.mk (Effect4.Prim.asyncFinalizer onInterrupt) self.stack self.interruptible
  self.interruptedCause self.deferredInterrupt) = (Effect4.FrameStep.running
  (Effect4.FrameFiber.mk (Effect4.Prim.failure (Effect4.Cause.die interp.notImplemented))
  self.stack self.interruptible self.interruptedCause self.deferredInterrupt), []))

-- census: op.Yield
#check (@Effect4.FrameFiber.step_yieldNowWith_frontier :
  ∀ {ν σ : Type u} {β : Type v} {ε δ ι α : Type u} [inst : DecidableEq ε] [inst_1 : DecidableEq
  δ] [inst_2 : DecidableEq ι] [inst_3 : DecidableEq α] (interp : Effect4.PrimInterp ν σ β ε δ ι
  α) (self : Effect4.FrameFiber ν σ β ε δ ι α) (priority : Nat), Effect4.FrameFiber.step interp
  (Effect4.FrameFiber.mk (Effect4.Prim.yieldNowWith priority) self.stack self.interruptible
  self.interruptedCause self.deferredInterrupt) = (Effect4.FrameStep.running
  (Effect4.FrameFiber.mk (Effect4.Prim.yieldNowWith priority) self.stack self.interruptible
  self.interruptedCause self.deferredInterrupt), []))

-- census: op.Async
#check (@Effect4.FrameFiber.step_async_frontier :
  ∀ {ν σ : Type u} {β : Type v} {ε δ ι α : Type u} [inst : DecidableEq ε] [inst_1 : DecidableEq
  δ] [inst_2 : DecidableEq ι] [inst_3 : DecidableEq α] (interp : Effect4.PrimInterp ν σ β ε δ ι
  α) (self : Effect4.FrameFiber ν σ β ε δ ι α) (register : ν) (withSignal : Bool) (cancel :
  Option ν), Effect4.FrameFiber.step interp (Effect4.FrameFiber.mk (Effect4.Prim.async register
  withSignal cancel) self.stack self.interruptible self.interruptedCause self.deferredInterrupt)
  = (Effect4.FrameStep.running (Effect4.FrameFiber.mk (Effect4.Prim.async register withSignal
  cancel) self.stack self.interruptible self.interruptedCause self.deferredInterrupt), []))

-- census: op.While
#check (@Effect4.FrameFiber.step_whileLoop_true :
  ∀ {ν σ : Type u} {β : Type v} {ε δ ι α : Type u} [inst : DecidableEq ε] [inst_1 : DecidableEq
  δ] [inst_2 : DecidableEq ι] [inst_3 : DecidableEq α] (interp : Effect4.PrimInterp ν σ β ε δ ι
  α) (self : Effect4.FrameFiber ν σ β ε δ ι α) (loop : ν) (cursor : β), interp.loopTest loop
  cursor = Bool.true → Effect4.FrameFiber.step interp (Effect4.FrameFiber.mk
  (Effect4.Prim.whileLoop loop cursor) self.stack self.interruptible self.interruptedCause
  self.deferredInterrupt) = (Effect4.FrameStep.running (Effect4.FrameFiber.mk (interp.loopBody
  loop cursor) (Effect4.Prim.whileLoop loop cursor :: self.stack) self.interruptible
  self.interruptedCause self.deferredInterrupt), [Effect4.FrameEvent.pushed
  (Effect4.Prim.whileLoop loop cursor)]))

-- census: op.While
#check (@Effect4.FrameFiber.step_whileLoop_false :
  ∀ {ν σ : Type u} {β : Type v} {ε δ ι α : Type u} [inst : DecidableEq ε] [inst_1 : DecidableEq
  δ] [inst_2 : DecidableEq ι] [inst_3 : DecidableEq α] (interp : Effect4.PrimInterp ν σ β ε δ ι
  α) (self : Effect4.FrameFiber ν σ β ε δ ι α) (loop : ν) (cursor : β), interp.loopTest loop
  cursor = Bool.false → Effect4.FrameFiber.step interp (Effect4.FrameFiber.mk
  (Effect4.Prim.whileLoop loop cursor) self.stack self.interruptible self.interruptedCause
  self.deferredInterrupt) = (Effect4.FrameStep.running (Effect4.FrameFiber.mk
  (Effect4.Prim.success (interp.loopDone loop)) self.stack self.interruptible
  self.interruptedCause self.deferredInterrupt), []))

-- census: op.Iterator
#check (@Effect4.FrameFiber.step_iterator :
  ∀ {ν σ : Type u} {β : Type v} {ε δ ι α : Type u} [inst : DecidableEq ε] [inst_1 : DecidableEq
  δ] [inst_2 : DecidableEq ι] [inst_3 : DecidableEq α] (interp : Effect4.PrimInterp ν σ β ε δ ι
  α) (self : Effect4.FrameFiber ν σ β ε δ ι α) (generator : ν) (cursor : β) (next : Effect4.Prim
  ν σ β ε δ ι α) (pushed : List (Effect4.Prim ν σ β ε δ ι α)), Effect4.Prim.armA interp
  (Effect4.Prim.iterator generator cursor) cursor Option.none = Option.some (next, pushed) →
  Effect4.FrameFiber.step interp (Effect4.FrameFiber.mk (Effect4.Prim.iterator generator cursor)
  self.stack self.interruptible self.interruptedCause self.deferredInterrupt) =
  (Effect4.FrameStep.running (Effect4.FrameFiber.mk next (pushed ++ self.stack)
  self.interruptible self.interruptedCause self.deferredInterrupt), List.map
  Effect4.FrameEvent.pushed pushed))

-- census: exit.success-failure
#check (@Effect4.FrameFiber.step_ofExit_finishes :
  ∀ {ν σ : Type u} {β : Type v} {ε δ ι α : Type u} [inst : DecidableEq ε] [inst_1 : DecidableEq
  δ] [inst_2 : DecidableEq ι] [inst_3 : DecidableEq α] (interp : Effect4.PrimInterp ν σ β ε δ ι
  α) (exit : Effect4.Exit β ε δ ι α), Effect4.FrameFiber.step interp (Effect4.FrameFiber.start
  (Effect4.Prim.ofExit exit)) = (Effect4.FrameStep.finished exit, [Effect4.FrameEvent.yielded
  exit]))

-- census: exit.success-failure
#check (@Effect4.FrameFiber.run_zero :
  ∀ {ν σ : Type u} {β : Type v} {ε δ ι α : Type u} [inst : DecidableEq ε] [inst_1 : DecidableEq
  δ] [inst_2 : DecidableEq ι] [inst_3 : DecidableEq α] (interp : Effect4.PrimInterp ν σ β ε δ ι
  α) (self : Effect4.FrameFiber ν σ β ε δ ι α), Effect4.FrameFiber.run interp 0 self =
  (Effect4.FrameStep.running self, []))

-- census: exit.success-failure
#check (@Effect4.FrameFiber.run_succ_finished :
  ∀ {ν σ : Type u} {β : Type v} {ε δ ι α : Type u} [inst : DecidableEq ε] [inst_1 : DecidableEq
  δ] [inst_2 : DecidableEq ι] [inst_3 : DecidableEq α] (interp : Effect4.PrimInterp ν σ β ε δ ι
  α) (self : Effect4.FrameFiber ν σ β ε δ ι α) (fuel : Nat) (exit : Effect4.Exit β ε δ ι α)
  (events : List (Effect4.FrameEvent ν σ β ε δ ι α)), Effect4.FrameFiber.step interp self =
  (Effect4.FrameStep.finished exit, events) → Effect4.FrameFiber.run interp (fuel + 1) self =
  (Effect4.FrameStep.finished exit, events))

-- census: exit.success-failure
#check (@Effect4.FrameFiber.run_succ_running :
  ∀ {ν σ : Type u} {β : Type v} {ε δ ι α : Type u} [inst : DecidableEq ε] [inst_1 : DecidableEq
  δ] [inst_2 : DecidableEq ι] [inst_3 : DecidableEq α] (interp : Effect4.PrimInterp ν σ β ε δ ι
  α) (self next : Effect4.FrameFiber ν σ β ε δ ι α) (fuel : Nat) (events : List
  (Effect4.FrameEvent ν σ β ε δ ι α)), Effect4.FrameFiber.step interp self =
  (Effect4.FrameStep.running next, events) → Effect4.FrameFiber.run interp (fuel + 1) self =
  ((Effect4.FrameFiber.run interp fuel next).fst, events ++ (Effect4.FrameFiber.run interp fuel
  next).snd))

/-! F8: masks and the stack side of the two brackets
(census: checkpoint.set-fiber-interruptible, scope.scoped,
scope.acquire-release). -/

#check (@Effect4.FrameFiber.uninterruptible :
  {ν σ : Type u} → {β : Type v} → {ε δ ι α : Type u} → Effect4.FrameFiber ν σ β ε δ ι α →
  Effect4.FrameFiber ν σ β ε δ ι α)

#check (@Effect4.FrameFiber.setFiberInterruptible :
  {ν σ : Type u} → {β : Type v} → {ε δ ι α : Type u} → Effect4.FrameFiber ν σ β ε δ ι α →
  Effect4.FrameFiber ν σ β ε δ ι α × Option (Effect4.Prim ν σ β ε δ ι α))

#check (@Effect4.FrameFiber.interruptibleRegion :
  {ν σ : Type u} → {β : Type v} → {ε δ ι α : Type u} → Effect4.FrameFiber ν σ β ε δ ι α →
  Effect4.FrameFiber ν σ β ε δ ι α × Option (Effect4.Prim ν σ β ε δ ι α))

#check (@Effect4.FrameFiber.uninterruptibleMask :
  {ν σ : Type u} → {β : Type v} → {ε δ ι α : Type u} → Effect4.FrameFiber ν σ β ε δ ι α →
  Effect4.FrameFiber ν σ β ε δ ι α)

#check (@Effect4.FrameFiber.restoreAcquire :
  {ν σ : Type u} → {β : Type v} → {ε δ ι α : Type u} → Effect4.FrameFiber ν σ β ε δ ι α → Bool →
  Effect4.FrameFiber ν σ β ε δ ι α × Option (Effect4.Prim ν σ β ε δ ι α))

#check (@Effect4.Prim.scopedFrame :
  {ν σ : Type u} → {β : Type v} → {ε δ ι α : Type u} → Effect4.Prim ν σ β ε δ ι α → ν →
  Effect4.Prim ν σ β ε δ ι α)

-- census: scope.acquire-release
#check (@Effect4.FrameFiber.uninterruptible_already_masked :
  ∀ {ν σ : Type u} {β : Type v} {ε δ ι α : Type u} (self : Effect4.FrameFiber ν σ β ε δ ι α),
  self.interruptible = Bool.false → Effect4.FrameFiber.uninterruptible self = self)

-- census: scope.acquire-release
#check (@Effect4.FrameFiber.uninterruptible_masks :
  ∀ {ν σ : Type u} {β : Type v} {ε δ ι α : Type u} (self : Effect4.FrameFiber ν σ β ε δ ι α),
  self.interruptible = Bool.true → Effect4.FrameFiber.uninterruptible self =
  Effect4.FrameFiber.mk self.current (Effect4.Prim.setInterruptible Bool.true :: self.stack)
  Bool.false self.interruptedCause self.deferredInterrupt)

-- census: scope.acquire-release
#check (@Effect4.FrameFiber.uninterruptibleMask_eq :
  ∀ {ν σ : Type u} {β : Type v} {ε δ ι α : Type u} (self : Effect4.FrameFiber ν σ β ε δ ι α),
  Effect4.FrameFiber.uninterruptibleMask self = Effect4.FrameFiber.uninterruptible self)

-- census: checkpoint.set-fiber-interruptible
#check (@Effect4.FrameFiber.setFiberInterruptible_flag :
  ∀ {ν σ : Type u} {β : Type v} {ε δ ι α : Type u} (self : Effect4.FrameFiber ν σ β ε δ ι α),
  (Effect4.FrameFiber.setFiberInterruptible self).fst.interruptible = Bool.true)

-- census: checkpoint.set-fiber-interruptible
#check (@Effect4.FrameFiber.setFiberInterruptible_pushes :
  ∀ {ν σ : Type u} {β : Type v} {ε δ ι α : Type u} (self : Effect4.FrameFiber ν σ β ε δ ι α),
  (Effect4.FrameFiber.setFiberInterruptible self).fst.stack = Effect4.Prim.setInterruptible
  Bool.false :: self.stack)

-- census: checkpoint.set-fiber-interruptible
#check (@Effect4.FrameFiber.setFiberInterruptible_immediate_failure :
  ∀ {ν σ : Type u} {β : Type v} {ε δ ι α : Type u} (self : Effect4.FrameFiber ν σ β ε δ ι α)
  (cause : Effect4.Cause ε δ ι α), self.interruptedCause = Option.some cause →
  (Effect4.FrameFiber.setFiberInterruptible self).snd = Option.some (Effect4.Prim.failure
  cause))

-- census: checkpoint.set-fiber-interruptible
#check (@Effect4.FrameFiber.setFiberInterruptible_no_pending :
  ∀ {ν σ : Type u} {β : Type v} {ε δ ι α : Type u} (self : Effect4.FrameFiber ν σ β ε δ ι α),
  self.interruptedCause = Option.none → (Effect4.FrameFiber.setFiberInterruptible self).snd =
  Option.none)

-- census: checkpoint.set-fiber-interruptible
#check (@Effect4.FrameFiber.interruptibleRegion_already :
  ∀ {ν σ : Type u} {β : Type v} {ε δ ι α : Type u} (self : Effect4.FrameFiber ν σ β ε δ ι α),
  self.interruptible = Bool.true → Effect4.FrameFiber.interruptibleRegion self = (self,
  Option.none))

-- census: checkpoint.set-fiber-interruptible
#check (@Effect4.FrameFiber.interruptibleRegion_masked :
  ∀ {ν σ : Type u} {β : Type v} {ε δ ι α : Type u} (self : Effect4.FrameFiber ν σ β ε δ ι α),
  self.interruptible = Bool.false → Effect4.FrameFiber.interruptibleRegion self =
  Effect4.FrameFiber.setFiberInterruptible self)

-- census: scope.acquire-release
#check (@Effect4.FrameFiber.restoreAcquire_asked :
  ∀ {ν σ : Type u} {β : Type v} {ε δ ι α : Type u} (self : Effect4.FrameFiber ν σ β ε δ ι α),
  Effect4.FrameFiber.restoreAcquire self Bool.true = Effect4.FrameFiber.interruptibleRegion
  self)

-- census: scope.acquire-release
#check (@Effect4.FrameFiber.restoreAcquire_not_asked :
  ∀ {ν σ : Type u} {β : Type v} {ε δ ι α : Type u} (self : Effect4.FrameFiber ν σ β ε δ ι α),
  Effect4.FrameFiber.restoreAcquire self Bool.false = (self, Option.none))

-- census: scope.scoped
#check (@Effect4.Prim.scopedFrame_eq :
  ∀ {ν σ : Type u} {β : Type v} {ε δ ι α : Type u} [DecidableEq ε] [DecidableEq δ] [DecidableEq
  ι] [DecidableEq α] (body : Effect4.Prim ν σ β ε δ ι α) (closeScope : ν),
  Effect4.Prim.scopedFrame body closeScope = Effect4.Prim.onExit body closeScope Bool.false)

-- census: scope.scoped
#check (@Effect4.Prim.scopedFrame_finalizer_masked :
  ∀ {ν σ : Type u} {β : Type v} {ε δ ι α : Type u} [DecidableEq ε] [DecidableEq δ] [DecidableEq
  ι] [DecidableEq α] (body : Effect4.Prim ν σ β ε δ ι α) (closeScope : ν) (fiber :
  Effect4.FrameFiber ν σ β ε δ ι α), fiber.interruptible = Bool.true → Effect4.Prim.ensure
  (Effect4.Prim.scopedFrame body closeScope) fiber = (Effect4.FrameFiber.mk fiber.current
  (Effect4.Prim.setInterruptible Bool.true :: fiber.stack) Bool.false fiber.interruptedCause
  fiber.deferredInterrupt, Option.none))

-- census: scope.scoped
#check (@Effect4.FrameFiber.step_scopedFrame :
  ∀ {ν σ : Type u} {β : Type v} {ε δ ι α : Type u} [inst : DecidableEq ε] [inst_1 : DecidableEq
  δ] [inst_2 : DecidableEq ι] [inst_3 : DecidableEq α] (interp : Effect4.PrimInterp ν σ β ε δ ι
  α) (self : Effect4.FrameFiber ν σ β ε δ ι α) (body : Effect4.Prim ν σ β ε δ ι α) (closeScope :
  ν), Effect4.FrameFiber.step interp (Effect4.FrameFiber.mk (Effect4.Prim.scopedFrame body
  closeScope) self.stack self.interruptible self.interruptedCause self.deferredInterrupt) =
  (Effect4.FrameStep.running (Effect4.FrameFiber.mk body (Effect4.Prim.onExit body closeScope
  Bool.false :: self.stack) self.interruptible self.interruptedCause self.deferredInterrupt),
  [Effect4.FrameEvent.pushed (Effect4.Prim.onExit body closeScope Bool.false)]))

/-! F9: the two foreign boundaries (census: op.WithFiber, op.YieldableError).

Both rows are `foreignBoundary` in `PORT-MANIFEST.md` terms: they close with a
registered boundary identity and a theorem-shaped refusal, the way
`Effect4.Scope.key_freshness_refused` and `Effect4.Reason.host_memory_refused`
do, not with a behavioural model of the host object. -/

-- census: op.WithFiber
#check (@Effect4.Prim.withFiber_refused :
  ∀ {ν σ : Type u} {β : Type v} {ε δ ι α : Type u} [DecidableEq ε] [DecidableEq δ] [DecidableEq
  ι] [DecidableEq α] {ϑ : Type u} (resolve : Effect4.FrameFiber ν σ β ε δ ι α → ϑ) (left right :
  Effect4.FrameFiber ν σ β ε δ ι α), left = right → resolve left = resolve right)

-- census: op.YieldableError
#check (@Effect4.Prim.yieldableError_host_class_refused :
  ∀ {ε : Type u} [DecidableEq ε] {ϑ : Type u} (host : ε → ϑ) (left right : ε), left = right →
  host left = host right)


/-! F10: the uninterrupted fragment and fuel additivity (census:
checkpoint.getcont-deferred, checkpoint.exit-failcause-skip,
exit.success-failure).

Fence A of packet D4, `docs/research/2026-09-03-frame-simulation.md`. Nothing in
`Effect4/Runtime/Runtime.lean` writes `interruptedCause`, so
`interruptedCause = none` together with `deferredInterrupt = false` is a `step`
invariant, and under it the pop loop never skips an answering frame and
`getCont` never answers a deferred interrupt. `FRAME-FB-NONNULL` is *vacuous* on
that fragment and is not retired: the hypothesis is a fragment fact, not a model
fact. `run_add` / `run_mono` are the composition and monotonicity laws the
bounded runner lacked, and are what makes a `forall fuel >= bound` statement
sayable without contradicting DB-04. -/

-- census: checkpoint.getcont-deferred
#check (@Effect4.FrameFiber.popFrom_interruptedCause :
  ∀ {ν σ : Type u} {β : Type v} {ε δ ι α : Type u} (demand : Effect4.Arm) (skip : Bool)
  (frames : List (Effect4.Prim ν σ β ε δ ι α)) (fiber : Effect4.FrameFiber ν σ β ε δ ι α),
  (Effect4.FrameFiber.popFrom demand skip frames fiber).fiber.interruptedCause =
  fiber.interruptedCause)

-- census: checkpoint.getcont-deferred
#check (@Effect4.FrameFiber.popFrom_deferredInterrupt :
  ∀ {ν σ : Type u} {β : Type v} {ε δ ι α : Type u} (demand : Effect4.Arm) (skip : Bool)
  (frames : List (Effect4.Prim ν σ β ε δ ι α)) (fiber : Effect4.FrameFiber ν σ β ε δ ι α),
  (Effect4.FrameFiber.popFrom demand skip frames fiber).fiber.deferredInterrupt =
  fiber.deferredInterrupt)

-- census: checkpoint.getcont-deferred
#check (@Effect4.FrameFiber.getCont_fiber_uninterrupted :
  ∀ {ν σ : Type u} {β : Type v} {ε δ ι α : Type u} (self : Effect4.FrameFiber ν σ β ε δ ι α)
  (demand : Effect4.Arm) (skip : Bool), self.interruptedCause = Option.none →
  self.deferredInterrupt = Bool.false →
  (self.getCont demand skip).fiber.interruptedCause = Option.none ∧
  (self.getCont demand skip).fiber.deferredInterrupt = Bool.false)

-- census: checkpoint.exit-failcause-skip
#check (@Effect4.FrameFiber.popFrom_never_skips :
  ∀ {ν σ : Type u} {β : Type v} {ε δ ι α : Type u} (demand : Effect4.Arm) (skip : Bool)
  (frame : Effect4.Prim ν σ β ε δ ι α) (rest : List (Effect4.Prim ν σ β ε δ ι α))
  (fiber : Effect4.FrameFiber ν σ β ε δ ι α) (answer : Effect4.ContAnswer ν σ β ε δ ι α),
  fiber.interruptedCause = Option.none →
  Effect4.Prim.answerOf frame demand (Effect4.Prim.ensure frame fiber).snd = Option.some answer →
  Effect4.FrameFiber.popFrom demand skip (frame :: rest) fiber =
  { answer := answer, popped := [frame],
    events := Effect4.Prim.passEvents frame (Effect4.Prim.ensure frame fiber).snd,
    fiber := have __src := (Effect4.Prim.ensure frame fiber).fst;
      Effect4.FrameFiber.mk __src.current
        ((Effect4.Prim.ensure frame fiber).fst.stack ++ rest) __src.interruptible
        __src.interruptedCause __src.deferredInterrupt })

-- census: checkpoint.getcont-deferred
#check (@Effect4.FrameFiber.popFrom_answer_ne_deferred :
  ∀ {ν σ : Type u} {β : Type v} {ε δ ι α : Type u} (demand : Effect4.Arm) (skip : Bool)
  (cause : Effect4.Cause ε δ ι α) (frames : List (Effect4.Prim ν σ β ε δ ι α))
  (fiber : Effect4.FrameFiber ν σ β ε δ ι α),
  (Effect4.FrameFiber.popFrom demand skip frames fiber).answer ≠
  Effect4.ContAnswer.deferred cause)

-- census: checkpoint.getcont-deferred
#check (@Effect4.FrameFiber.getCont_never_defers :
  ∀ {ν σ : Type u} {β : Type v} {ε δ ι α : Type u} (self : Effect4.FrameFiber ν σ β ε δ ι α)
  (demand : Effect4.Arm) (skip : Bool) (cause : Effect4.Cause ε δ ι α),
  self.deferredInterrupt = Bool.false →
  (self.getCont demand skip).answer ≠ Effect4.ContAnswer.deferred cause)

-- census: checkpoint.getcont-deferred
#check (@Effect4.FrameFiber.step_preserves_uninterrupted :
  ∀ {ν σ : Type u} {β : Type v} {ε δ ι α : Type u} [DecidableEq ε] [DecidableEq δ]
  [DecidableEq ι] [DecidableEq α] (interp : Effect4.PrimInterp ν σ β ε δ ι α)
  (self next : Effect4.FrameFiber ν σ β ε δ ι α), self.interruptedCause = Option.none →
  self.deferredInterrupt = Bool.false →
  (Effect4.FrameFiber.step interp self).fst = Effect4.FrameStep.running next →
  next.interruptedCause = Option.none ∧ next.deferredInterrupt = Bool.false)

-- census: checkpoint.getcont-deferred
#check (@Effect4.FrameFiber.run_preserves_uninterrupted :
  ∀ {ν σ : Type u} {β : Type v} {ε δ ι α : Type u} [DecidableEq ε] [DecidableEq δ]
  [DecidableEq ι] [DecidableEq α] (interp : Effect4.PrimInterp ν σ β ε δ ι α) (fuel : Nat)
  (self next : Effect4.FrameFiber ν σ β ε δ ι α), self.interruptedCause = Option.none →
  self.deferredInterrupt = Bool.false →
  (Effect4.FrameFiber.run interp fuel self).fst = Effect4.FrameStep.running next →
  next.interruptedCause = Option.none ∧ next.deferredInterrupt = Bool.false)

-- census: exit.success-failure
#check (@Effect4.FrameFiber.run_add :
  ∀ {ν σ : Type u} {β : Type v} {ε δ ι α : Type u} [DecidableEq ε] [DecidableEq δ]
  [DecidableEq ι] [DecidableEq α] (interp : Effect4.PrimInterp ν σ β ε δ ι α) (m n : Nat)
  (self : Effect4.FrameFiber ν σ β ε δ ι α),
  Effect4.FrameFiber.run interp (m + n) self =
  match Effect4.FrameFiber.run interp m self with
  | (Effect4.FrameStep.finished exit, events) => (Effect4.FrameStep.finished exit, events)
  | (Effect4.FrameStep.running mid, events) =>
    ((Effect4.FrameFiber.run interp n mid).fst, events ++ (Effect4.FrameFiber.run interp n mid).snd))

-- census: exit.success-failure
#check (@Effect4.FrameFiber.run_add_finished :
  ∀ {ν σ : Type u} {β : Type v} {ε δ ι α : Type u} [DecidableEq ε] [DecidableEq δ]
  [DecidableEq ι] [DecidableEq α] (interp : Effect4.PrimInterp ν σ β ε δ ι α)
  (self : Effect4.FrameFiber ν σ β ε δ ι α) (m n : Nat) (exit : Effect4.Exit β ε δ ι α)
  (events : List (Effect4.FrameEvent ν σ β ε δ ι α)),
  Effect4.FrameFiber.run interp m self = (Effect4.FrameStep.finished exit, events) →
  Effect4.FrameFiber.run interp (m + n) self = (Effect4.FrameStep.finished exit, events))

-- census: exit.success-failure
#check (@Effect4.FrameFiber.run_add_running :
  ∀ {ν σ : Type u} {β : Type v} {ε δ ι α : Type u} [DecidableEq ε] [DecidableEq δ]
  [DecidableEq ι] [DecidableEq α] (interp : Effect4.PrimInterp ν σ β ε δ ι α)
  (self mid : Effect4.FrameFiber ν σ β ε δ ι α) (m n : Nat)
  (events : List (Effect4.FrameEvent ν σ β ε δ ι α)),
  Effect4.FrameFiber.run interp m self = (Effect4.FrameStep.running mid, events) →
  Effect4.FrameFiber.run interp (m + n) self =
  ((Effect4.FrameFiber.run interp n mid).fst, events ++ (Effect4.FrameFiber.run interp n mid).snd))

-- census: exit.success-failure
#check (@Effect4.FrameFiber.run_mono :
  ∀ {ν σ : Type u} {β : Type v} {ε δ ι α : Type u} [DecidableEq ε] [DecidableEq δ]
  [DecidableEq ι] [DecidableEq α] (interp : Effect4.PrimInterp ν σ β ε δ ι α)
  (self : Effect4.FrameFiber ν σ β ε δ ι α) (m n : Nat) (exit : Effect4.Exit β ε δ ι α)
  (events : List (Effect4.FrameEvent ν σ β ε δ ι α)), m ≤ n →
  Effect4.FrameFiber.run interp m self = (Effect4.FrameStep.finished exit, events) →
  Effect4.FrameFiber.run interp n self = (Effect4.FrameStep.finished exit, events))

end Test.Runtime.FramesContract
