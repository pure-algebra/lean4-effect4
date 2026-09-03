import Effect4.Semantics.Exit

/-!
# Runtime.Runtime.lean

Owner: Reference execution runtime — the Effect v4 continuation-stack machine.

This module implements the first-order frame machine of
`effect@4.0.0-rc.112`: the closed three-value continuation-slot alphabet with
its two demandable arms, the fourteen-constructor primitive syntax, the
frame-arm matrix, the `contAll` ensure hook with its answer selection and pass
trace, the two demandable arms, the fused `getCont`/`exitFailCause` pop loop
with its deferred-interrupt answer and its handler skipping, the five-field
fiber state with its one-step function, bounded runner and event trace, and the
mask combinators together with the stack side of `scoped` and `acquireRelease`.

A continuation slot stores a nominal `ν` and a thunk a nominal `σ`, never a
stored Lean closure: `docs/DESIGN-BASIS.md` DB-02 forbids closures in canonical
program content. A nested body is a first-order `Prim` subterm, because rc.112's
`onSuccess[args]` holds the inner *effect* and a subterm is inspectable,
decidable and serialisable where a closure is none of those. What a name *does*
is supplied by the one parameter `PrimInterp`, exactly the way
`Effect4.Scope.close` takes its `run`, so `Prim` and `FrameFiber` keep decidable
equality and kernel-reducible ground receipts. `Effect4.Exit` and
`Effect4.Cause` are reused unchanged; this module mints no second exit or cause
carrier and imports only `Effect4.Semantics.Exit`. Nothing under
`Effect4/Concurrency/` is imported or mentioned, so the mask flag is rc.112's
own `Bool` rather than `Effect4.InterruptMask`.

Pinned source: `vendor/effect-4.0.0-rc.112/src/internal/core.ts` 365-583 and
`internal/effect.ts` 505-550, 653-698, 737-744, 928-946, 1356-1379, 1662-1689,
2474-2501, 3426-3465, 4001-4029, 4302-4367 and 4623-4645. The frozen surface is
`test/contracts/frames.contract.md`, held by the battery
`Effect4Test/Runtime/FramesContract.lean` and the axiom report
`Effect4Test/Runtime/FramesAxiomReport.lean`. The proof graph is
`docs/FRAMES-DAG.md`; the registered attacks are `E4-RUN-CE-010` through
`E4-RUN-CE-021`, witnessed in
`Effect4Test/Counterexamples/Runtime/Frames.lean`.
-/

namespace Effect4

universe u v

/-- rc.112's three continuation slots, stored on the primitive prototype. The
alphabet is closed and carries no payload. -/
inductive Arm
  /-- `[contA]`, the slot a produced value is handed to. -/
  | contA
  /-- `[contE]`, the slot a produced cause is handed to. -/
  | contE
  /-- `[contAll]`, the hook run on every frame a pop passes. -/
  | contAll
deriving DecidableEq, Repr

namespace Arm

/-- Every slot, in declaration order. census: rule.frames-are-primitives -/
def all : List Arm := [contA, contE, contAll]

/-- The two slots `getCont<S extends contA | contE>` may demand.
census: rule.frames-are-primitives -/
def demandable : List Arm := [contA, contE]

/-- The slot census lists no slot twice. census: rule.frames-are-primitives -/
theorem all_nodup : all.Nodup := by decide

/-- The slot census is complete. census: rule.frames-are-primitives -/
theorem mem_all (arm : Arm) : arm ∈ all := by
  cases arm <;> decide

/-- There is no fourth continuation slot. census: rule.frames-are-primitives -/
theorem cases_receipt (arm : Arm) : arm = contA \/ arm = contE \/ arm = contAll := by
  cases arm
  · exact Or.inl rfl
  · exact Or.inr (Or.inl rfl)
  · exact Or.inr (Or.inr rfl)

/-- Only the value and cause slots can be demanded.
census: rule.frames-are-primitives -/
theorem demandable_eq : demandable = [contA, contE] := rfl

/-- The ensure hook is never demanded by a pop.
census: rule.frames-are-primitives -/
theorem contAll_not_demandable : contAll ∉ demandable := by decide

end Arm

/-- The pinned rc.112 primitive syntax, one constructor per op in this packet's
scope. `Yield`, `Async` and `AsyncFinalizer` are deliberately absent; they
belong to the later run-loop and parking packet. A continuation slot stores a
nominal `ν`, a thunk a nominal `σ`, and a nested body a first-order subterm. -/
inductive Prim (ν σ : Type u) (β : Type v) (ε δ ι α : Type u) : Type (max u v)
  /-- rc.112's `Success` exit op. -/
  | success (value : β)
  /-- rc.112's `Failure` exit op. -/
  | failure (cause : Cause ε δ ι α)
  /-- `sync`: run the thunk, then behave like `Success` with its result. -/
  | sync (thunk : σ)
  /-- `suspend`: return the primitive the thunk names. -/
  | suspend (thunk : σ)
  /-- `withFiber`: hand the raw fiber to the thunk. -/
  | withFiber (thunk : σ)
  /-- `YieldableError`: a host error class whose `evaluate` is `exitFail(this)`. -/
  | yieldableError (error : ε)
  /-- `Iterator`: drive a generator from a cursor. -/
  | iterator (generator : ν) (cursor : β)
  /-- `OnSuccess`: run the body, then the named value continuation. -/
  | onSuccess (body : Prim ν σ β ε δ ι α) (onValue : ν)
  /-- `OnFailure`: run the body, then the named cause continuation. -/
  | onFailure (body : Prim ν σ β ε δ ι α) (onCause : ν)
  /-- `OnSuccessAndFailure`: both continuations, assigned per instance. -/
  | onSuccessAndFailure (body : Prim ν σ β ε δ ι α) (onValue : ν) (onCause : ν)
  /-- rc.112's `Exit` frame; the Lean spelling avoids colliding with
  `Effect4.Exit`. -/
  | exitFrame (body : Prim ν σ β ε δ ι α)
  /-- `OnExit`: run the named finalizer, then restore the body's exit. -/
  | onExit (body : Prim ν σ β ε δ ι α) (finalizer : ν) (finalizerInterruptible : Bool)
  /-- `SetInterruptible`: the mask frame; it declares `contAll` only. -/
  | setInterruptible (flag : Bool)
  /-- `While`: rc.112's `whileLoop`, driven from a cursor. -/
  | whileLoop (loop : ν) (cursor : β)
deriving DecidableEq

namespace Prim

/-- There is no fifteenth primitive in this packet.
census: rule.frames-are-primitives -/
theorem cases_receipt {ν σ : Type u} {β : Type v} {ε δ ι α : Type u}
    (self : Prim ν σ β ε δ ι α) :
    (exists value, self = success value) \/ (exists cause, self = failure cause) \/
      (exists thunk, self = sync thunk) \/ (exists thunk, self = suspend thunk) \/
      (exists thunk, self = withFiber thunk) \/
      (exists error, self = yieldableError error) \/
      (exists generator cursor, self = iterator generator cursor) \/
      (exists body onValue, self = onSuccess body onValue) \/
      (exists body onCause, self = onFailure body onCause) \/
      (exists body onValue onCause, self = onSuccessAndFailure body onValue onCause) \/
      (exists body, self = exitFrame body) \/
      (exists body finalizer flag, self = onExit body finalizer flag) \/
      (exists flag, self = setInterruptible flag) \/
      exists loop cursor, self = whileLoop loop cursor := by
  cases self with
  | success value => exact Or.inl ⟨value, rfl⟩
  | failure cause => exact Or.inr (Or.inl ⟨cause, rfl⟩)
  | sync thunk => exact Or.inr (Or.inr (Or.inl ⟨thunk, rfl⟩))
  | suspend thunk => exact Or.inr (Or.inr (Or.inr (Or.inl ⟨thunk, rfl⟩)))
  | withFiber thunk => exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨thunk, rfl⟩))))
  | yieldableError error =>
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨error, rfl⟩)))))
  | iterator generator cursor =>
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨generator, cursor, rfl⟩))))))
  | onSuccess body onValue =>
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      (Or.inl ⟨body, onValue, rfl⟩)))))))
  | onFailure body onCause =>
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      (Or.inl ⟨body, onCause, rfl⟩))))))))
  | onSuccessAndFailure body onValue onCause =>
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      (Or.inl ⟨body, onValue, onCause, rfl⟩)))))))))
  | exitFrame body =>
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      (Or.inl ⟨body, rfl⟩))))))))))
  | onExit body finalizer flag =>
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      (Or.inr (Or.inl ⟨body, finalizer, flag, rfl⟩)))))))))))
  | setInterruptible flag =>
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      (Or.inr (Or.inr (Or.inl ⟨flag, rfl⟩))))))))))))
  | whileLoop loop cursor =>
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      (Or.inr (Or.inr (Or.inr ⟨loop, cursor, rfl⟩))))))))))))

end Prim

/-- What stopped a generator's inline fold: a final value, a cause, or an
effect that has to leave the arm. -/
inductive IterStep (ν σ : Type u) (β : Type v) (ε δ ι α : Type u) : Type (max u v)
  /-- The generator returned. -/
  | done (value : β)
  /-- The generator yielded a failed exit. -/
  | halt (cause : Cause ε δ ι α)
  /-- The generator yielded a non-exit effect. -/
  | resume (next : Prim ν σ β ε δ ι α)
deriving DecidableEq

/-- The externally supplied meaning of a continuation name. It is a
*parameter*, never canonical program content: it carries no `DecidableEq` and
never enters `Prim` or `FrameFiber`. -/
structure PrimInterp (ν σ : Type u) (β : Type v) (ε δ ι α : Type u) : Type (max u v) where
  /-- `cont[contA](value, fiber)`. -/
  contA : ν -> β -> Prim ν σ β ε δ ι α
  /-- `cont[contE](cause, fiber)`. -/
  contE : ν -> Cause ε δ ι α -> Prim ν σ β ε δ ι α
  /-- The value a `sync` thunk produces. -/
  syncValue : σ -> β
  /-- The primitive a `suspend` or `withFiber` thunk returns. -/
  suspendBody : σ -> Prim ν σ β ε δ ι α
  /-- The outcome exit of a named finalizer, `FRAME-FB-FINALIZER-EFFECT`. -/
  finalizerExit : ν -> Exit β ε δ ι α -> Exit Unit ε δ ι α
  /-- How an `Exit` becomes a value of the one value alphabet. -/
  reifyExit : Exit β ε δ ι α -> β
  /-- The maximal inline run of a generator and the outcome that ended it. -/
  iterNext : ν -> β -> List β × IterStep ν σ β ε δ ι α
  /-- `whileLoop`'s predicate. -/
  loopTest : ν -> β -> Bool
  /-- `whileLoop`'s body. -/
  loopBody : ν -> β -> Prim ν σ β ε δ ι α
  /-- `whileLoop`'s cursor step. -/
  loopStep : ν -> β -> β
  /-- The terminal value of a finished loop, rc.112's `exitVoid`. -/
  loopDone : ν -> β
  /-- The defect payload of `defaultEvaluate`. -/
  notImplemented : δ

/-- The five `FiberImpl` fields this packet models. `_running`, `_yielded`,
observers, children, the op budget, the dispatcher and the `Context` cache are
absent by construction; the run-loop, supervision and context packets own
them. -/
structure FrameFiber (ν σ : Type u) (β : Type v) (ε δ ι α : Type u) : Type (max u v) where
  /-- The primitive the run loop is threading. -/
  current : Prim ν σ β ε δ ι α
  /-- rc.112's `_stack`, top first. -/
  stack : List (Prim ν σ β ε δ ι α)
  /-- rc.112's `interruptible` flag. -/
  interruptible : Bool
  /-- rc.112's `_interruptedCause`. -/
  interruptedCause : Option (Cause ε δ ι α)
  /-- rc.112's `_deferredInterrupt`. -/
  deferredInterrupt : Bool
deriving DecidableEq

/-- What a pop answers. -/
inductive ContAnswer (ν σ : Type u) (β : Type v) (ε δ ι α : Type u) : Type (max u v)
  /-- `deferredInterruptCont`, answered before the stack is touched. -/
  | deferred (cause : Cause ε δ ι α)
  /-- A continuation a passed frame's `contAll` returned. -/
  | replacement (next : Prim ν σ β ε δ ι α)
  /-- The frame that declares the demanded arm. -/
  | frame (frame : Prim ν σ β ε δ ι α)
  /-- Nothing on the stack answers. -/
  | empty
deriving DecidableEq

/-- The stack's trace alphabet. It is not `Effect4.Event`, the scheduler's
trace alphabet: `docs/FRAMES-DAG.md` separation 7 records why. -/
inductive FrameEvent (ν σ : Type u) (β : Type v) (ε δ ι α : Type u) : Type (max u v)
  /-- A frame the pop passed or answered with. -/
  | popped (frame : Prim ν σ β ε δ ι α)
  /-- A passed frame whose `contAll` ran. -/
  | ranContAll (frame : Prim ν σ β ε δ ι α)
  /-- A frame pushed onto the stack. -/
  | pushed (frame : Prim ν σ β ε δ ι α)
  /-- A named finalizer run against the exit it restores. -/
  | ranFinalizer (finalizer : ν) (exit : Exit β ε δ ι α)
  /-- A continuation substituted by a mask frame's `contAll`. -/
  | substituted (cause : Cause ε δ ι α)
  /-- The deferred interrupt answered by `getCont`. -/
  | deferred (cause : Cause ε δ ι α)
  /-- The exit the fiber yielded. -/
  | yielded (exit : Exit β ε δ ι α)
deriving DecidableEq

/-- The four observations of one pop. -/
structure FramePop (ν σ : Type u) (β : Type v) (ε δ ι α : Type u) : Type (max u v) where
  /-- What the pop answered. -/
  answer : ContAnswer ν σ β ε δ ι α
  /-- The frames it removed, in pop order. -/
  popped : List (Prim ν σ β ε δ ι α)
  /-- The trace it left. -/
  events : List (FrameEvent ν σ β ε δ ι α)
  /-- The fiber after the pop. -/
  fiber : FrameFiber ν σ β ε δ ι α
deriving DecidableEq

/-- One step either continues or finishes with an exit. `running` at exhausted
`run` fuel is a live frontier under `docs/DESIGN-BASIS.md` DB-04, never a
failure, never a defect and never a refusal. -/
inductive FrameStep (ν σ : Type u) (β : Type v) (ε δ ι α : Type u) : Type (max u v)
  /-- The machine is still running. -/
  | running (fiber : FrameFiber ν σ β ε δ ι α)
  /-- The machine finished with an exit. -/
  | finished (exit : Exit β ε δ ι α)
deriving DecidableEq

variable {ν σ : Type u} {β : Type v} {ε δ ι α : Type u}

namespace FrameFiber

/-- `new FiberImpl(context, true)`, restricted to the five modelled fields.
census: rule.frames-are-primitives -/
def start (current : Prim ν σ β ε δ ι α) : FrameFiber ν σ β ε δ ι α where
  current := current
  stack := []
  interruptible := true
  interruptedCause := none
  deferredInterrupt := false

/-- The accumulated interruption cause, read totally. rc.112 reads it with the
non-null assertion `_interruptedCause!`; `FRAME-FB-NONNULL` records that this
model answers `Cause.empty` in the state that assertion calls unreachable.
census: checkpoint.getcont-deferred -/
def pendingCause (self : FrameFiber ν σ β ε δ ι α) : Cause ε δ ι α :=
  match self.interruptedCause with
  | some cause => cause
  | none => Cause.empty

/-- The shared mask word. `FRAME-FB-MASK-CARRIER` records that the
correspondence to `Effect4.InterruptMask` is a later bridge obligation.
census: rule.frames-are-primitives -/
def masked (self : FrameFiber ν σ β ε δ ι α) : Bool := !self.interruptible

/-- The exact skip condition of `internal/core.ts:540`.
census: rule.frames-are-primitives -/
def interrupted (self : FrameFiber ν σ β ε δ ι α) : Bool :=
  self.interruptible && self.interruptedCause.isSome

/-- A started fiber has an empty stack, is interruptible, and carries neither a
cause nor a deferred interrupt. census: rule.frames-are-primitives -/
theorem start_eq (current : Prim ν σ β ε δ ι α) :
    start current = FrameFiber.mk current [] true none false := rfl

/-- A recorded cause is the pending cause. census: checkpoint.getcont-deferred -/
theorem pendingCause_some (self : FrameFiber ν σ β ε δ ι α) (cause : Cause ε δ ι α)
    (h : self.interruptedCause = some cause) : self.pendingCause = cause := by
  unfold pendingCause
  rw [h]

/-- With no recorded cause the pending cause is empty.
census: checkpoint.getcont-deferred -/
theorem pendingCause_none (self : FrameFiber ν σ β ε δ ι α)
    (h : self.interruptedCause = none) : self.pendingCause = Cause.empty := by
  unfold pendingCause
  rw [h]

/-- Masked is the negation of interruptible. census: rule.frames-are-primitives -/
theorem masked_eq (self : FrameFiber ν σ β ε δ ι α) : self.masked = !self.interruptible := rfl

/-- Interrupted is interruptible with a cause pending.
census: rule.frames-are-primitives -/
theorem interrupted_eq (self : FrameFiber ν σ β ε δ ι α) :
    self.interrupted = (self.interruptible && self.interruptedCause.isSome) := rfl

end FrameFiber

namespace FrameEvent

/-- The frame an event popped, if it popped one.
census: rule.frames-are-primitives -/
def poppedFrame? : FrameEvent ν σ β ε δ ι α -> Option (Prim ν σ β ε δ ι α)
  | popped frame => some frame
  | ranContAll _ => none
  | pushed _ => none
  | ranFinalizer _ _ => none
  | substituted _ => none
  | deferred _ => none
  | yielded _ => none

/-- The finalizer an event ran, if it ran one.
census: rule.frames-are-primitives -/
def finalizer? : FrameEvent ν σ β ε δ ι α -> Option ν
  | ranFinalizer finalizer _ => some finalizer
  | popped _ => none
  | ranContAll _ => none
  | pushed _ => none
  | substituted _ => none
  | deferred _ => none
  | yielded _ => none

/-- The frames a trace popped, in order. census: rule.frames-are-primitives -/
def poppedFrames (events : List (FrameEvent ν σ β ε δ ι α)) : List (Prim ν σ β ε δ ι α) :=
  events.filterMap poppedFrame?

/-- The finalizers a trace ran, in order. census: rule.frames-are-primitives -/
def finalizersRun (events : List (FrameEvent ν σ β ε δ ι α)) : List ν :=
  events.filterMap finalizer?

/-- The empty trace popped nothing. census: rule.frames-are-primitives -/
theorem poppedFrames_nil : poppedFrames ([] : List (FrameEvent ν σ β ε δ ι α)) = [] := rfl

/-- A pop event contributes its frame. census: rule.frames-are-primitives -/
theorem poppedFrames_cons_popped (frame : Prim ν σ β ε δ ι α)
    (rest : List (FrameEvent ν σ β ε δ ι α)) :
    poppedFrames (popped frame :: rest) = frame :: poppedFrames rest := rfl

/-- The empty trace ran no finalizer. census: rule.frames-are-primitives -/
theorem finalizersRun_nil : finalizersRun ([] : List (FrameEvent ν σ β ε δ ι α)) = [] := rfl

/-- A finalizer event contributes its name. census: rule.frames-are-primitives -/
theorem finalizersRun_cons_ran (finalizer : ν) (exit : Exit β ε δ ι α)
    (rest : List (FrameEvent ν σ β ε δ ι α)) :
    finalizersRun (ranFinalizer finalizer exit :: rest) =
      finalizer :: finalizersRun rest := rfl

/-- A pop event runs no finalizer. census: rule.frames-are-primitives -/
theorem finalizersRun_cons_popped (frame : Prim ν σ β ε δ ι α)
    (rest : List (FrameEvent ν σ β ε δ ι α)) :
    finalizersRun (popped frame :: rest) = finalizersRun rest := rfl

end FrameEvent

namespace Prim

/-- The frame-arm matrix of `docs/effect-rc112-fiber-runtime.html` section 3,
verbatim. The six non-frame primitives declare no arm and are never pushed.
census: rule.frames-are-primitives -/
def arms : Prim ν σ β ε δ ι α -> List Arm
  | onSuccess _ _ => [Arm.contA]
  | onFailure _ _ => [Arm.contE]
  | onSuccessAndFailure _ _ _ => [Arm.contA, Arm.contE]
  | exitFrame _ => [Arm.contA, Arm.contE]
  | onExit _ _ _ => [Arm.contA, Arm.contE, Arm.contAll]
  | setInterruptible _ => [Arm.contAll]
  | whileLoop _ _ => [Arm.contA]
  | iterator _ _ => [Arm.contA]
  | success _ => []
  | failure _ => []
  | sync _ => []
  | suspend _ => []
  | withFiber _ => []
  | yieldableError _ => []

/-- Whether a primitive declares a slot. census: rule.frames-are-primitives -/
def hasArm (self : Prim ν σ β ε δ ι α) (arm : Arm) : Bool := self.arms.contains arm

/-- A frame is exactly a primitive that declares at least one slot.
census: rule.frames-are-primitives -/
def isFrame (self : Prim ν σ β ε δ ι α) : Bool := !self.arms.isEmpty

/-- Slot membership is membership in the declared list.
census: rule.frames-are-primitives -/
theorem hasArm_eq (self : Prim ν σ β ε δ ι α) (arm : Arm) :
    self.hasArm arm = self.arms.contains arm := rfl

/-- Being a frame is declaring a nonempty arm list.
census: rule.frames-are-primitives -/
theorem isFrame_eq (self : Prim ν σ β ε δ ι α) : self.isFrame = !self.arms.isEmpty := rfl

/-- Being a frame is exactly declaring some arm.
census: rule.frames-are-primitives -/
theorem isFrame_iff (self : Prim ν σ β ε δ ι α) : self.isFrame = true ↔ self.arms ≠ [] := by
  simp [isFrame]

/-- `onSuccess` answers the value slot only. census: frame-arm.OnSuccess -/
theorem arms_onSuccess (body : Prim ν σ β ε δ ι α) (onValue : ν) :
    (onSuccess body onValue).arms = [Arm.contA] := rfl

/-- `onFailure` answers the cause slot only. census: frame-arm.OnFailure -/
theorem arms_onFailure (body : Prim ν σ β ε δ ι α) (onCause : ν) :
    (onFailure body onCause).arms = [Arm.contE] := rfl

/-- `onSuccessAndFailure` answers both demandable slots.
census: frame-arm.OnSuccessAndFailure -/
theorem arms_onSuccessAndFailure (body : Prim ν σ β ε δ ι α) (onValue onCause : ν) :
    (onSuccessAndFailure body onValue onCause).arms = [Arm.contA, Arm.contE] := rfl

/-- The `Exit` frame declares both demandable slots and no hook.
census: frame-arm.Exit -/
theorem arms_exitFrame (body : Prim ν σ β ε δ ι α) :
    (exitFrame body).arms = [Arm.contA, Arm.contE] := rfl

/-- `onExit` declares all three slots. census: frame-arm.OnExit -/
theorem arms_onExit (body : Prim ν σ β ε δ ι α) (finalizer : ν) (flag : Bool) :
    (onExit body finalizer flag).arms = [Arm.contA, Arm.contE, Arm.contAll] := rfl

/-- The mask frame declares the hook only. census: frame-arm.SetInterruptible -/
theorem arms_setInterruptible (flag : Bool) :
    (setInterruptible flag : Prim ν σ β ε δ ι α).arms = [Arm.contAll] := rfl

/-- `whileLoop` declares the value slot only. census: frame-arm.While -/
theorem arms_whileLoop (loop : ν) (cursor : β) :
    (whileLoop loop cursor : Prim ν σ β ε δ ι α).arms = [Arm.contA] := rfl

/-- `iterator` declares the value slot only. census: frame-arm.Iterator -/
theorem arms_iterator (generator : ν) (cursor : β) :
    (iterator generator cursor : Prim ν σ β ε δ ι α).arms = [Arm.contA] := rfl

/-- The six non-frame primitives declare no slot at all.
census: rule.frames-are-primitives -/
theorem non_frames_have_no_arms (value : β) (cause : Cause ε δ ι α) (thunk : σ) (error : ε) :
    (success value : Prim ν σ β ε δ ι α).arms = [] ∧
      (failure cause : Prim ν σ β ε δ ι α).arms = [] ∧
      (sync thunk : Prim ν σ β ε δ ι α).arms = [] ∧
      (suspend thunk : Prim ν σ β ε δ ι α).arms = [] ∧
      (withFiber thunk : Prim ν σ β ε δ ι α).arms = [] ∧
      (yieldableError error : Prim ν σ β ε δ ι α).arms = [] :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- rc.112's `makeExit`: an exit is itself a primitive.
census: exit.success-failure -/
def ofExit : Exit β ε δ ι α -> Prim ν σ β ε δ ι α
  | Exit.success value => success value
  | Exit.failure cause => failure cause

/-- The partial inverse of the exit embedding. census: exit.success-failure -/
def asExit? : Prim ν σ β ε δ ι α -> Option (Exit β ε δ ι α)
  | success value => some (Exit.success value)
  | failure cause => some (Exit.failure cause)
  | sync _ => none
  | suspend _ => none
  | withFiber _ => none
  | yieldableError _ => none
  | iterator _ _ => none
  | onSuccess _ _ => none
  | onFailure _ _ => none
  | onSuccessAndFailure _ _ _ => none
  | exitFrame _ => none
  | onExit _ _ _ => none
  | setInterruptible _ => none
  | whileLoop _ _ => none

/-- The embedding round-trips. census: exit.success-failure -/
theorem ofExit_asExit? (exit : Exit β ε δ ι α) :
    (ofExit exit : Prim ν σ β ε δ ι α).asExit? = some exit := by
  cases exit <;> rfl

/-- A success primitive is the successful exit. census: exit.success-failure -/
theorem asExit?_success (value : β) :
    (success value : Prim ν σ β ε δ ι α).asExit? = some (Exit.success value) := rfl

/-- A failure primitive is the failed exit. census: exit.success-failure -/
theorem asExit?_failure (cause : Cause ε δ ι α) :
    (failure cause : Prim ν σ β ε δ ι α).asExit? = some (Exit.failure cause) := rfl

/-- Only an embedded exit reads back as one. census: exit.success-failure -/
theorem asExit?_eq_some (self : Prim ν σ β ε δ ι α) (exit : Exit β ε δ ι α)
    (h : self.asExit? = some exit) : self = ofExit exit := by
  cases self with
  | success value =>
    rw [← Option.some.inj h]
    rfl
  | failure cause =>
    rw [← Option.some.inj h]
    rfl
  | sync _ => simp [asExit?] at h
  | suspend _ => simp [asExit?] at h
  | withFiber _ => simp [asExit?] at h
  | yieldableError _ => simp [asExit?] at h
  | iterator _ _ => simp [asExit?] at h
  | onSuccess _ _ => simp [asExit?] at h
  | onFailure _ _ => simp [asExit?] at h
  | onSuccessAndFailure _ _ _ => simp [asExit?] at h
  | exitFrame _ => simp [asExit?] at h
  | onExit _ _ _ => simp [asExit?] at h
  | setInterruptible _ => simp [asExit?] at h
  | whileLoop _ _ => simp [asExit?] at h

/-- An exit has an `evaluate` and no continuation slot, so it is never a frame.
census: exit.success-failure -/
theorem ofExit_isFrame (exit : Exit β ε δ ι α) :
    (ofExit exit : Prim ν σ β ε δ ι α).isFrame = false := by
  cases exit <;> rfl

/-- rc.112's `[contAll](fiber)`: the hook every passed frame runs. It returns
the fiber it leaves behind and, for the mask frame only, a replacement
continuation. census: frame-arm.OnExit -/
def ensure : Prim ν σ β ε δ ι α -> FrameFiber ν σ β ε δ ι α ->
    FrameFiber ν σ β ε δ ι α × Option (Prim ν σ β ε δ ι α)
  | onExit _ _ finalizerInterruptible, fiber =>
    if fiber.interruptible && !finalizerInterruptible then
      ({ fiber with
          stack := setInterruptible true :: fiber.stack,
          interruptible := false }, none)
    else (fiber, none)
  | setInterruptible flag, fiber =>
    match fiber.interruptedCause with
    | some cause =>
      if flag then
        ({ fiber with interruptible := true }, some (failure cause))
      else ({ fiber with interruptible := flag }, none)
    | none => ({ fiber with interruptible := flag }, none)
  | success _, fiber => (fiber, none)
  | failure _, fiber => (fiber, none)
  | sync _, fiber => (fiber, none)
  | suspend _, fiber => (fiber, none)
  | withFiber _, fiber => (fiber, none)
  | yieldableError _, fiber => (fiber, none)
  | iterator _ _, fiber => (fiber, none)
  | onSuccess _ _, fiber => (fiber, none)
  | onFailure _ _, fiber => (fiber, none)
  | onSuccessAndFailure _ _ _, fiber => (fiber, none)
  | exitFrame _, fiber => (fiber, none)
  | whileLoop _ _, fiber => (fiber, none)

/-- The decision rc.112 makes once `contAll` has returned: a replacement wins
for either arm, and a frame lacking the demanded arm is skipped.
census: rule.frames-are-primitives -/
def answerOf (frame : Prim ν σ β ε δ ι α) (demand : Arm)
    (replacement : Option (Prim ν σ β ε δ ι α)) : Option (ContAnswer ν σ β ε δ ι α) :=
  match replacement with
  | some next => some (ContAnswer.replacement next)
  | none => if frame.hasArm demand then some (ContAnswer.frame frame) else none

/-- The trace one passed frame leaves. census: rule.frames-are-primitives -/
def passEvents (frame : Prim ν σ β ε δ ι α) (replacement : Option (Prim ν σ β ε δ ι α)) :
    List (FrameEvent ν σ β ε δ ι α) :=
  if frame.hasArm Arm.contAll then
    match replacement with
    | some (failure cause) =>
      [FrameEvent.popped frame, FrameEvent.ranContAll frame, FrameEvent.substituted cause]
    | _ => [FrameEvent.popped frame, FrameEvent.ranContAll frame]
  else [FrameEvent.popped frame]

/-- A frame without the hook has no ensure step. census: frame-arm.Exit -/
theorem ensure_of_no_contAll (frame : Prim ν σ β ε δ ι α) (fiber : FrameFiber ν σ β ε δ ι α)
    (h : frame.hasArm Arm.contAll = false) : frame.ensure fiber = (fiber, none) := by
  cases frame <;> first | rfl | exact Bool.noConfusion h

/-- An `onExit` hook masks the fiber and pushes the restoring frame.
census: frame-arm.OnExit -/
theorem ensure_onExit_masks (body : Prim ν σ β ε δ ι α) (finalizer : ν)
    (fiber : FrameFiber ν σ β ε δ ι α) (h : fiber.interruptible = true) :
    (onExit body finalizer false).ensure fiber =
      (FrameFiber.mk fiber.current (setInterruptible true :: fiber.stack) false
        fiber.interruptedCause fiber.deferredInterrupt, none) := by
  simp [ensure, h]

/-- An `onExit` told its finalizer is interruptible masks nothing.
census: frame-arm.OnExit -/
theorem ensure_onExit_told_not_to (body : Prim ν σ β ε δ ι α) (finalizer : ν)
    (fiber : FrameFiber ν σ β ε δ ι α) :
    (onExit body finalizer true).ensure fiber = (fiber, none) := by
  simp [ensure]

/-- An already masked fiber gets no second restoring frame.
census: frame-arm.OnExit -/
theorem ensure_onExit_already_masked (body : Prim ν σ β ε δ ι α) (finalizer : ν) (flag : Bool)
    (fiber : FrameFiber ν σ β ε δ ι α) (h : fiber.interruptible = false) :
    (onExit body finalizer flag).ensure fiber = (fiber, none) := by
  simp [ensure, h]

/-- The `onExit` hook pushes and flips but never substitutes a continuation.
census: frame-arm.OnExit -/
theorem ensure_onExit_no_replacement (body : Prim ν σ β ε δ ι α) (finalizer : ν) (flag : Bool)
    (fiber : FrameFiber ν σ β ε δ ι α) :
    ((onExit body finalizer flag).ensure fiber).snd = none := by
  simp [ensure]
  split <;> rfl

/-- The mask frame restores the flag it stores. census: op.SetInterruptible -/
theorem ensure_setInterruptible_flag (flag : Bool) (fiber : FrameFiber ν σ β ε δ ι α) :
    ((setInterruptible flag).ensure fiber).fst.interruptible = flag := by
  cases hcause : fiber.interruptedCause with
  | none => simp [ensure, hcause]
  | some cause => cases flag <;> simp [ensure, hcause]

/-- The mask frame pushes nothing. census: op.SetInterruptible -/
theorem ensure_setInterruptible_stack (flag : Bool) (fiber : FrameFiber ν σ β ε δ ι α) :
    ((setInterruptible flag).ensure fiber).fst.stack = fiber.stack := by
  cases hcause : fiber.interruptedCause with
  | none => simp [ensure, hcause]
  | some cause => cases flag <;> simp [ensure, hcause]

/-- Becoming interruptible again with a cause pending substitutes
`failCause(cause)` for either arm. census: op.SetInterruptible -/
theorem ensure_setInterruptible_substitutes (cause : Cause ε δ ι α)
    (fiber : FrameFiber ν σ β ε δ ι α) (h : fiber.interruptedCause = some cause) :
    (setInterruptible true : Prim ν σ β ε δ ι α).ensure fiber =
      (FrameFiber.mk fiber.current fiber.stack true fiber.interruptedCause
        fiber.deferredInterrupt, some (failure cause)) := by
  simp [ensure, h]

/-- Only `setInterruptible true` can substitute, because only it can leave the
fiber interruptible. census: op.SetInterruptible -/
theorem ensure_setInterruptible_false_no_replacement (fiber : FrameFiber ν σ β ε δ ι α) :
    ((setInterruptible false : Prim ν σ β ε δ ι α).ensure fiber).snd = none := by
  cases hcause : fiber.interruptedCause with
  | none => simp [ensure, hcause]
  | some cause => simp [ensure, hcause]

/-- With no cause pending the mask frame only restores the flag.
census: op.SetInterruptible -/
theorem ensure_setInterruptible_no_pending (flag : Bool) (fiber : FrameFiber ν σ β ε δ ι α)
    (h : fiber.interruptedCause = none) :
    (setInterruptible flag : Prim ν σ β ε δ ι α).ensure fiber =
      (FrameFiber.mk fiber.current fiber.stack flag fiber.interruptedCause
        fiber.deferredInterrupt, none) := by
  simp [ensure, h]

/-- A returned replacement answers whatever arm was demanded.
census: rule.frames-are-primitives -/
theorem answerOf_replacement (frame next : Prim ν σ β ε δ ι α) (demand : Arm) :
    frame.answerOf demand (some next) = some (ContAnswer.replacement next) := rfl

/-- A frame declaring the demanded arm answers with itself.
census: rule.frames-are-primitives -/
theorem answerOf_arm (frame : Prim ν σ β ε δ ι α) (demand : Arm)
    (h : frame.hasArm demand = true) :
    frame.answerOf demand none = some (ContAnswer.frame frame) := by
  simp [answerOf, h]

/-- A frame lacking the demanded arm answers nothing.
census: rule.frames-are-primitives -/
theorem answerOf_missing (frame : Prim ν σ β ε δ ι α) (demand : Arm)
    (h : frame.hasArm demand = false) : frame.answerOf demand none = none := by
  simp [answerOf, h]

/-- A frame answer is the frame itself, and it declares the demanded arm.
census: rule.frames-are-primitives -/
theorem answerOf_frame_eq (frame answering : Prim ν σ β ε δ ι α) (demand : Arm)
    (replacement : Option (Prim ν σ β ε δ ι α))
    (h : frame.answerOf demand replacement = some (ContAnswer.frame answering)) :
    answering = frame ∧ frame.hasArm demand = true := by
  cases replacement with
  | some next => simp [answerOf] at h
  | none =>
    cases hd : frame.hasArm demand with
    | false => simp [answerOf, hd] at h
    | true =>
      simp [answerOf, hd] at h
      exact ⟨h.symm, rfl⟩

/-- rc.112's `cont[contA](value, fiber, exit?)`, per frame. The `List` is what
the arm itself pushes; the `Option (Exit …)` is rc.112's third continuation
argument, supplied by `Success` and `Failure` and withheld by `Sync`.
census: rule.frames-are-primitives -/
def armA [DecidableEq ε] [DecidableEq δ] [DecidableEq ι] [DecidableEq α]
    (interp : PrimInterp ν σ β ε δ ι α) :
    Prim ν σ β ε δ ι α -> β -> Option (Exit β ε δ ι α) ->
      Option (Prim ν σ β ε δ ι α × List (Prim ν σ β ε δ ι α))
  | onSuccess _ onValue, value, _ => some (interp.contA onValue value, [])
  | onSuccessAndFailure _ onValue _, value, _ => some (interp.contA onValue value, [])
  | exitFrame _, value, provided =>
    some (success (interp.reifyExit (provided.getD (Exit.success value))), [])
  | onExit _ finalizer _, value, provided =>
    some (ofExit (Exit.restoreAfterFinalizer (provided.getD (Exit.success value))
      (interp.finalizerExit finalizer (provided.getD (Exit.success value)))), [])
  | whileLoop loop _, value, _ =>
    if interp.loopTest loop (interp.loopStep loop value) then
      some (interp.loopBody loop (interp.loopStep loop value),
        [whileLoop loop (interp.loopStep loop value)])
    else some (success (interp.loopDone loop), [])
  | iterator generator cursor, value, _ =>
    match (interp.iterNext generator value).snd with
    | IterStep.done result => some (success result, [])
    | IterStep.halt cause => some (failure cause, [])
    | IterStep.resume next => some (next, [iterator generator cursor])
  | success _, _, _ => none
  | failure _, _, _ => none
  | sync _, _, _ => none
  | suspend _, _, _ => none
  | withFiber _, _, _ => none
  | yieldableError _, _, _ => none
  | onFailure _ _, _, _ => none
  | setInterruptible _, _, _ => none

/-- rc.112's `cont[contE](cause, fiber, exit?)`, per frame.
census: rule.frames-are-primitives -/
def armE [DecidableEq ε] [DecidableEq δ] [DecidableEq ι] [DecidableEq α]
    (interp : PrimInterp ν σ β ε δ ι α) :
    Prim ν σ β ε δ ι α -> Cause ε δ ι α -> Option (Exit β ε δ ι α) ->
      Option (Prim ν σ β ε δ ι α × List (Prim ν σ β ε δ ι α))
  | onFailure _ onCause, cause, _ => some (interp.contE onCause cause, [])
  | onSuccessAndFailure _ _ onCause, cause, _ => some (interp.contE onCause cause, [])
  | exitFrame _, cause, provided =>
    some (success (interp.reifyExit (provided.getD (Exit.failure cause))), [])
  | onExit _ finalizer _, cause, provided =>
    some (ofExit (Exit.restoreAfterFinalizer (provided.getD (Exit.failure cause))
      (interp.finalizerExit finalizer (provided.getD (Exit.failure cause)))), [])
  | success _, _, _ => none
  | failure _, _, _ => none
  | sync _, _, _ => none
  | suspend _, _, _ => none
  | withFiber _, _, _ => none
  | yieldableError _, _, _ => none
  | iterator _ _, _, _ => none
  | onSuccess _ _, _, _ => none
  | setInterruptible _, _, _ => none
  | whileLoop _ _, _, _ => none

/-- The trace an answering arm leaves: only `onExit` runs a finalizer.
census: op.OnExit -/
def finalizerEvents : Prim ν σ β ε δ ι α -> Exit β ε δ ι α -> List (FrameEvent ν σ β ε δ ι α)
  | onExit _ finalizer _, exit => [FrameEvent.ranFinalizer finalizer exit]
  | success _, _ => []
  | failure _, _ => []
  | sync _, _ => []
  | suspend _, _ => []
  | withFiber _, _ => []
  | yieldableError _, _ => []
  | iterator _ _, _ => []
  | onSuccess _ _, _ => []
  | onFailure _ _, _ => []
  | onSuccessAndFailure _ _ _, _ => []
  | exitFrame _, _ => []
  | setInterruptible _, _ => []
  | whileLoop _ _, _ => []

/-- The values a generator folds inline before it stops. census: op.Iterator -/
def iteratorFolded (interp : PrimInterp ν σ β ε δ ι α) :
    Prim ν σ β ε δ ι α -> β -> List β
  | iterator generator _, value => (interp.iterNext generator value).fst
  | success _, _ => []
  | failure _, _ => []
  | sync _, _ => []
  | suspend _, _ => []
  | withFiber _, _ => []
  | yieldableError _, _ => []
  | onSuccess _ _, _ => []
  | onFailure _ _, _ => []
  | onSuccessAndFailure _ _ _, _ => []
  | exitFrame _, _ => []
  | onExit _ _ _, _ => []
  | setInterruptible _, _ => []
  | whileLoop _ _, _ => []

/-- The value arm is defined exactly on the frames that declare it.
census: rule.frames-are-primitives -/
theorem armA_isSome [DecidableEq ε] [DecidableEq δ] [DecidableEq ι] [DecidableEq α]
    (interp : PrimInterp ν σ β ε δ ι α) (frame : Prim ν σ β ε δ ι α) (value : β)
    (provided : Option (Exit β ε δ ι α)) :
    (frame.armA interp value provided).isSome = frame.hasArm Arm.contA := by
  cases frame with
  | success _ => rfl
  | failure _ => rfl
  | sync _ => rfl
  | suspend _ => rfl
  | withFiber _ => rfl
  | yieldableError _ => rfl
  | iterator generator cursor =>
    show (armA interp (iterator generator cursor) value provided).isSome = true
    cases hiter : (interp.iterNext generator value).snd <;> simp [armA, hiter]
  | onSuccess _ _ => rfl
  | onFailure _ _ => rfl
  | onSuccessAndFailure _ _ _ => rfl
  | exitFrame _ => rfl
  | onExit _ _ _ => rfl
  | setInterruptible _ => rfl
  | whileLoop loop cursor =>
    show (armA interp (whileLoop loop cursor) value provided).isSome = true
    cases hloop : interp.loopTest loop (interp.loopStep loop value) <;> simp [armA, hloop]

/-- The cause arm is defined exactly on the frames that declare it.
census: rule.frames-are-primitives -/
theorem armE_isSome [DecidableEq ε] [DecidableEq δ] [DecidableEq ι] [DecidableEq α]
    (interp : PrimInterp ν σ β ε δ ι α) (frame : Prim ν σ β ε δ ι α) (cause : Cause ε δ ι α)
    (provided : Option (Exit β ε δ ι α)) :
    (frame.armE interp cause provided).isSome = frame.hasArm Arm.contE := by
  cases frame <;> rfl

/-- `flatMap` assigns the value continuation on the instance.
census: op.OnSuccess -/
theorem armA_onSuccess [DecidableEq ε] [DecidableEq δ] [DecidableEq ι] [DecidableEq α]
    (interp : PrimInterp ν σ β ε δ ι α) (body : Prim ν σ β ε δ ι α) (onValue : ν) (value : β)
    (provided : Option (Exit β ε δ ι α)) :
    (onSuccess body onValue).armA interp value provided =
      some (interp.contA onValue value, []) := rfl

/-- `matchCauseEffect` assigns the value arm on the instance.
census: op.OnSuccessAndFailure -/
theorem armA_onSuccessAndFailure [DecidableEq ε] [DecidableEq δ] [DecidableEq ι]
    [DecidableEq α] (interp : PrimInterp ν σ β ε δ ι α) (body : Prim ν σ β ε δ ι α)
    (onValue onCause : ν) (value : β) (provided : Option (Exit β ε δ ι α)) :
    (onSuccessAndFailure body onValue onCause).armA interp value provided =
      some (interp.contA onValue value, []) := rfl

/-- `catchCause` assigns the cause continuation on the instance.
census: op.OnFailure -/
theorem armE_onFailure [DecidableEq ε] [DecidableEq δ] [DecidableEq ι] [DecidableEq α]
    (interp : PrimInterp ν σ β ε δ ι α) (body : Prim ν σ β ε δ ι α) (onCause : ν)
    (cause : Cause ε δ ι α) (provided : Option (Exit β ε δ ι α)) :
    (onFailure body onCause).armE interp cause provided =
      some (interp.contE onCause cause, []) := rfl

/-- `matchCauseEffect` assigns the cause arm on the instance.
census: op.OnSuccessAndFailure -/
theorem armE_onSuccessAndFailure [DecidableEq ε] [DecidableEq δ] [DecidableEq ι]
    [DecidableEq α] (interp : PrimInterp ν σ β ε δ ι α) (body : Prim ν σ β ε δ ι α)
    (onValue onCause : ν) (cause : Cause ε δ ι α) (provided : Option (Exit β ε δ ι α)) :
    (onSuccessAndFailure body onValue onCause).armE interp cause provided =
      some (interp.contE onCause cause, []) := rfl

/-- `onSuccess` declares no cause arm. census: frame-arm.OnSuccess -/
theorem armE_onSuccess_none [DecidableEq ε] [DecidableEq δ] [DecidableEq ι] [DecidableEq α]
    (interp : PrimInterp ν σ β ε δ ι α) (body : Prim ν σ β ε δ ι α) (onValue : ν)
    (cause : Cause ε δ ι α) (provided : Option (Exit β ε δ ι α)) :
    (onSuccess body onValue).armE interp cause provided = none := rfl

/-- `onFailure` declares no value arm. census: frame-arm.OnFailure -/
theorem armA_onFailure_none [DecidableEq ε] [DecidableEq δ] [DecidableEq ι] [DecidableEq α]
    (interp : PrimInterp ν σ β ε δ ι α) (body : Prim ν σ β ε δ ι α) (onCause : ν) (value : β)
    (provided : Option (Exit β ε δ ι α)) :
    (onFailure body onCause).armA interp value provided = none := rfl

/-- The mask frame declares no value arm. census: frame-arm.SetInterruptible -/
theorem armA_setInterruptible_none [DecidableEq ε] [DecidableEq δ] [DecidableEq ι]
    [DecidableEq α] (interp : PrimInterp ν σ β ε δ ι α) (flag : Bool) (value : β)
    (provided : Option (Exit β ε δ ι α)) :
    (setInterruptible flag : Prim ν σ β ε δ ι α).armA interp value provided = none := rfl

/-- The mask frame declares no cause arm. census: frame-arm.SetInterruptible -/
theorem armE_setInterruptible_none [DecidableEq ε] [DecidableEq δ] [DecidableEq ι]
    [DecidableEq α] (interp : PrimInterp ν σ β ε δ ι α) (flag : Bool) (cause : Cause ε δ ι α)
    (provided : Option (Exit β ε δ ι α)) :
    (setInterruptible flag : Prim ν σ β ε δ ι α).armE interp cause provided = none := rfl

/-- `whileLoop` declares no cause arm. census: frame-arm.While -/
theorem armE_whileLoop_none [DecidableEq ε] [DecidableEq δ] [DecidableEq ι] [DecidableEq α]
    (interp : PrimInterp ν σ β ε δ ι α) (loop : ν) (cursor : β) (cause : Cause ε δ ι α)
    (provided : Option (Exit β ε δ ι α)) :
    (whileLoop loop cursor : Prim ν σ β ε δ ι α).armE interp cause provided = none := rfl

/-- `iterator` declares no cause arm. census: frame-arm.Iterator -/
theorem armE_iterator_none [DecidableEq ε] [DecidableEq δ] [DecidableEq ι] [DecidableEq α]
    (interp : PrimInterp ν σ β ε δ ι α) (generator : ν) (cursor : β) (cause : Cause ε δ ι α)
    (provided : Option (Exit β ε δ ι α)) :
    (iterator generator cursor : Prim ν σ β ε δ ι α).armE interp cause provided = none := rfl

/-- The `Exit` frame reuses the exit the pop supplied. census: op.Exit -/
theorem armA_exitFrame_provided [DecidableEq ε] [DecidableEq δ] [DecidableEq ι]
    [DecidableEq α] (interp : PrimInterp ν σ β ε δ ι α) (body : Prim ν σ β ε δ ι α) (value : β)
    (exit : Exit β ε δ ι α) :
    (exitFrame body).armA interp value (some exit) =
      some (success (interp.reifyExit exit), []) := rfl

/-- Without a supplied exit the `Exit` frame reifies the produced value.
census: op.Exit -/
theorem armA_exitFrame_none [DecidableEq ε] [DecidableEq δ] [DecidableEq ι] [DecidableEq α]
    (interp : PrimInterp ν σ β ε δ ι α) (body : Prim ν σ β ε δ ι α) (value : β) :
    (exitFrame body).armA interp value none =
      some (success (interp.reifyExit (Exit.success value)), []) := rfl

/-- The `Exit` frame reuses the supplied exit on the cause arm too.
census: op.Exit -/
theorem armE_exitFrame_provided [DecidableEq ε] [DecidableEq δ] [DecidableEq ι]
    [DecidableEq α] (interp : PrimInterp ν σ β ε δ ι α) (body : Prim ν σ β ε δ ι α)
    (cause : Cause ε δ ι α) (exit : Exit β ε δ ι α) :
    (exitFrame body).armE interp cause (some exit) =
      some (success (interp.reifyExit exit), []) := rfl

/-- Without a supplied exit the `Exit` frame reifies the produced cause.
census: op.Exit -/
theorem armE_exitFrame_none [DecidableEq ε] [DecidableEq δ] [DecidableEq ι] [DecidableEq α]
    (interp : PrimInterp ν σ β ε δ ι α) (body : Prim ν σ β ε δ ι α) (cause : Cause ε δ ι α) :
    (exitFrame body).armE interp cause none =
      some (success (interp.reifyExit (Exit.failure cause)), []) := rfl

/-- The `onExit` value arm runs the finalizer and restores the original exit.
census: op.OnExit -/
theorem armA_onExit [DecidableEq ε] [DecidableEq δ] [DecidableEq ι] [DecidableEq α]
    (interp : PrimInterp ν σ β ε δ ι α) (body : Prim ν σ β ε δ ι α) (finalizer : ν)
    (flag : Bool) (value : β) (exit : Exit β ε δ ι α) :
    (onExit body finalizer flag).armA interp value (some exit) =
      some (ofExit (Exit.restoreAfterFinalizer exit (interp.finalizerExit finalizer exit)),
        []) := rfl

/-- The `onExit` cause arm runs the finalizer and restores the original exit.
census: op.OnExit -/
theorem armE_onExit [DecidableEq ε] [DecidableEq δ] [DecidableEq ι] [DecidableEq α]
    (interp : PrimInterp ν σ β ε δ ι α) (body : Prim ν σ β ε δ ι α) (finalizer : ν)
    (flag : Bool) (cause : Cause ε δ ι α) (exit : Exit β ε δ ι α) :
    (onExit body finalizer flag).armE interp cause (some exit) =
      some (ofExit (Exit.restoreAfterFinalizer exit (interp.finalizerExit finalizer exit)),
        []) := rfl

/-- A successful finalizer leaves the exit it was bracketing unchanged.
census: op.OnExit -/
theorem onExit_finalizer_success_restores [DecidableEq ε] [DecidableEq δ] [DecidableEq ι]
    [DecidableEq α] (interp : PrimInterp ν σ β ε δ ι α) (body : Prim ν σ β ε δ ι α)
    (finalizer : ν) (flag : Bool) (value : β) (exit : Exit β ε δ ι α)
    (h : interp.finalizerExit finalizer exit = Exit.success ()) :
    (onExit body finalizer flag).armA interp value (some exit) = some (ofExit exit, []) := by
  rw [armA_onExit, h, Exit.restoreAfterFinalizer_success_finalizer]

/-- A failing finalizer under a failed exit merges both causes.
census: op.OnExit -/
theorem onExit_finalizer_failure_merges [DecidableEq ε] [DecidableEq δ] [DecidableEq ι]
    [DecidableEq α] (interp : PrimInterp ν σ β ε δ ι α) (body : Prim ν σ β ε δ ι α)
    (finalizer : ν) (flag : Bool) (cause finalizerCause : Cause ε δ ι α)
    (h : interp.finalizerExit finalizer (Exit.failure cause) = Exit.failure finalizerCause) :
    (onExit body finalizer flag).armE interp cause (some (Exit.failure cause)) =
      some (failure (Cause.combine cause finalizerCause), []) := by
  rw [armE_onExit, h, Exit.restoreAfterFinalizer_failure_failure]
  rfl

/-- A failing finalizer under a successful exit stands alone.
census: op.OnExit -/
theorem onExit_success_finalizer_failure [DecidableEq ε] [DecidableEq δ] [DecidableEq ι]
    [DecidableEq α] (interp : PrimInterp ν σ β ε δ ι α) (body : Prim ν σ β ε δ ι α)
    (finalizer : ν) (flag : Bool) (value produced : β) (finalizerCause : Cause ε δ ι α)
    (h : interp.finalizerExit finalizer (Exit.success produced) =
      Exit.failure finalizerCause) :
    (onExit body finalizer flag).armA interp value (some (Exit.success produced)) =
      some (failure finalizerCause, []) := by
  rw [armA_onExit, h, Exit.restoreAfterFinalizer_success_failure]
  rfl

/-- The `onExit` arm depends on the stored finalizer name and on nothing else
about the frame. census: frame-arm.OnExit -/
theorem onExit_arm_is_per_frame [DecidableEq ε] [DecidableEq δ] [DecidableEq ι]
    [DecidableEq α] (interp : PrimInterp ν σ β ε δ ι α) (body other : Prim ν σ β ε δ ι α)
    (finalizer : ν) (flag otherFlag : Bool) (value : β)
    (provided : Option (Exit β ε δ ι α)) :
    (onExit body finalizer flag).armA interp value provided =
      (onExit other finalizer otherFlag).armA interp value provided := rfl

/-- The value arm is assigned per instance, not by the op prototype.
census: op.OnSuccess -/
theorem onSuccess_arm_is_per_instance [DecidableEq ε] [DecidableEq δ] [DecidableEq ι]
    [DecidableEq α] (interp : PrimInterp ν σ β ε δ ι α) (body : Prim ν σ β ε δ ι α)
    (left right : ν) (value : β) (provided : Option (Exit β ε δ ι α))
    (h : interp.contA left value ≠ interp.contA right value) :
    (onSuccess body left).armA interp value provided ≠
      (onSuccess body right).armA interp value provided := by
  intro harm
  rw [armA_onSuccess, armA_onSuccess] at harm
  exact h (congrArg Prod.fst (Option.some.inj harm))

/-- The cause arm is assigned per instance, not by the op prototype.
census: op.OnFailure -/
theorem onFailure_arm_is_per_instance [DecidableEq ε] [DecidableEq δ] [DecidableEq ι]
    [DecidableEq α] (interp : PrimInterp ν σ β ε δ ι α) (body : Prim ν σ β ε δ ι α)
    (left right : ν) (cause : Cause ε δ ι α) (provided : Option (Exit β ε δ ι α))
    (h : interp.contE left cause ≠ interp.contE right cause) :
    (onFailure body left).armE interp cause provided ≠
      (onFailure body right).armE interp cause provided := by
  intro harm
  rw [armE_onFailure, armE_onFailure] at harm
  exact h (congrArg Prod.fst (Option.some.inj harm))

/-- Both arms of `matchCauseEffect` are assigned per instance.
census: op.OnSuccessAndFailure -/
theorem onSuccessAndFailure_arms_are_per_instance [DecidableEq ε] [DecidableEq δ]
    [DecidableEq ι] [DecidableEq α] (interp : PrimInterp ν σ β ε δ ι α)
    (body : Prim ν σ β ε δ ι α) (onValue onCause : ν) (value : β) (cause : Cause ε δ ι α)
    (provided : Option (Exit β ε δ ι α)) :
    (onSuccessAndFailure body onValue onCause).armA interp value provided =
        some (interp.contA onValue value, []) ∧
      (onSuccessAndFailure body onValue onCause).armE interp cause provided =
        some (interp.contE onCause cause, []) := ⟨rfl, rfl⟩

/-- The loop steps the cursor, re-tests, and only then pushes and runs the body.
census: op.While -/
theorem armA_whileLoop_continue [DecidableEq ε] [DecidableEq δ] [DecidableEq ι]
    [DecidableEq α] (interp : PrimInterp ν σ β ε δ ι α) (loop : ν) (cursor value : β)
    (provided : Option (Exit β ε δ ι α))
    (h : interp.loopTest loop (interp.loopStep loop value) = true) :
    (whileLoop loop cursor : Prim ν σ β ε δ ι α).armA interp value provided =
      some (interp.loopBody loop (interp.loopStep loop value),
        [whileLoop loop (interp.loopStep loop value)]) := by
  simp [armA, h]

/-- A loop whose re-test fails finishes with the supplied terminal value.
census: op.While -/
theorem armA_whileLoop_stop [DecidableEq ε] [DecidableEq δ] [DecidableEq ι] [DecidableEq α]
    (interp : PrimInterp ν σ β ε δ ι α) (loop : ν) (cursor value : β)
    (provided : Option (Exit β ε δ ι α))
    (h : interp.loopTest loop (interp.loopStep loop value) = false) :
    (whileLoop loop cursor : Prim ν σ β ε δ ι α).armA interp value provided =
      some (success (interp.loopDone loop), []) := by
  simp [armA, h]

/-- A generator that returned finishes with its value. census: op.Iterator -/
theorem armA_iterator_done [DecidableEq ε] [DecidableEq δ] [DecidableEq ι] [DecidableEq α]
    (interp : PrimInterp ν σ β ε δ ι α) (generator : ν) (cursor value result : β)
    (provided : Option (Exit β ε δ ι α))
    (h : (interp.iterNext generator value).snd = IterStep.done result) :
    (iterator generator cursor : Prim ν σ β ε δ ι α).armA interp value provided =
      some (success result, []) := by
  simp [armA, h]

/-- A generator that yielded a failed exit fails. census: op.Iterator -/
theorem armA_iterator_halt [DecidableEq ε] [DecidableEq δ] [DecidableEq ι] [DecidableEq α]
    (interp : PrimInterp ν σ β ε δ ι α) (generator : ν) (cursor value : β)
    (cause : Cause ε δ ι α) (provided : Option (Exit β ε δ ι α))
    (h : (interp.iterNext generator value).snd = IterStep.halt cause) :
    (iterator generator cursor : Prim ν σ β ε δ ι α).armA interp value provided =
      some (failure cause, []) := by
  simp [armA, h]

/-- A generator that yielded a non-exit effect pushes this frame under it.
census: op.Iterator -/
theorem armA_iterator_resume [DecidableEq ε] [DecidableEq δ] [DecidableEq ι] [DecidableEq α]
    (interp : PrimInterp ν σ β ε δ ι α) (generator : ν) (cursor value : β)
    (next : Prim ν σ β ε δ ι α) (provided : Option (Exit β ε δ ι α))
    (h : (interp.iterNext generator value).snd = IterStep.resume next) :
    (iterator generator cursor : Prim ν σ β ε δ ι α).armA interp value provided =
      some (next, [iterator generator cursor]) := by
  simp [armA, h]

/-- The inline run is exactly the supplied prefix. census: op.Iterator -/
theorem iteratorFolded_eq [DecidableEq ε] [DecidableEq δ] [DecidableEq ι] [DecidableEq α]
    (interp : PrimInterp ν σ β ε δ ι α) (generator : ν) (cursor value : β) :
    (iterator generator cursor : Prim ν σ β ε δ ι α).iteratorFolded interp value =
      (interp.iterNext generator value).fst := rfl

/-- The arm depends only on the outcome that stopped the generator, never on
the values folded before it: that is what "folded inline" means, and it is why
no `getCont` checkpoint sits between them. census: op.Iterator -/
theorem iterator_folds_inline [DecidableEq ε] [DecidableEq δ] [DecidableEq ι] [DecidableEq α]
    (left right : PrimInterp ν σ β ε δ ι α) (generator : ν) (cursor value : β)
    (provided : Option (Exit β ε δ ι α))
    (h : (left.iterNext generator value).snd = (right.iterNext generator value).snd) :
    (iterator generator cursor : Prim ν σ β ε δ ι α).armA left value provided =
      (iterator generator cursor).armA right value provided := by
  cases hright : (right.iterNext generator value).snd with
  | done result =>
    rw [armA_iterator_done left generator cursor value result provided (h.trans hright),
      armA_iterator_done right generator cursor value result provided hright]
  | halt cause =>
    rw [armA_iterator_halt left generator cursor value cause provided (h.trans hright),
      armA_iterator_halt right generator cursor value cause provided hright]
  | resume next =>
    rw [armA_iterator_resume left generator cursor value next provided (h.trans hright),
      armA_iterator_resume right generator cursor value next provided hright]

/-- An `onExit` arm records the finalizer it ran. census: op.OnExit -/
theorem finalizerEvents_onExit (body : Prim ν σ β ε δ ι α) (finalizer : ν) (flag : Bool)
    (exit : Exit β ε δ ι α) :
    (onExit body finalizer flag).finalizerEvents exit =
      [FrameEvent.ranFinalizer finalizer exit] := rfl

/-- An `onSuccess` arm runs no finalizer. census: op.OnExit -/
theorem finalizerEvents_onSuccess (body : Prim ν σ β ε δ ι α) (onValue : ν)
    (exit : Exit β ε δ ι α) : (onSuccess body onValue).finalizerEvents exit = [] := rfl

/-- An `onFailure` arm runs no finalizer. census: op.OnExit -/
theorem finalizerEvents_onFailure (body : Prim ν σ β ε δ ι α) (onCause : ν)
    (exit : Exit β ε δ ι α) : (onFailure body onCause).finalizerEvents exit = [] := rfl

end Prim

namespace FrameFiber

/-- One pass leaves exactly one popped frame in the trace.
census: rule.frames-are-primitives -/
theorem passEvents_poppedFrames (frame : Prim ν σ β ε δ ι α)
    (replacement : Option (Prim ν σ β ε δ ι α)) :
    FrameEvent.poppedFrames (frame.passEvents replacement) = [frame] := by
  cases hcontAll : frame.hasArm Arm.contAll with
  | false => simp [Prim.passEvents, hcontAll, FrameEvent.poppedFrames, FrameEvent.poppedFrame?]
  | true =>
    cases replacement with
    | none => simp [Prim.passEvents, hcontAll, FrameEvent.poppedFrames, FrameEvent.poppedFrame?]
    | some next =>
      cases next <;> simp [Prim.passEvents, hcontAll, FrameEvent.poppedFrames, FrameEvent.poppedFrame?]

/-- The hook runs on every frame a pop passes, not only on the frame that
answers. `E4-RUN-CE-010` is the attack. census: rule.frames-are-primitives -/
theorem passEvents_ranContAll (frame : Prim ν σ β ε δ ι α)
    (replacement : Option (Prim ν σ β ε δ ι α)) (h : frame.hasArm Arm.contAll = true) :
    FrameEvent.ranContAll frame ∈ frame.passEvents replacement := by
  cases replacement with
  | none => simp [Prim.passEvents, h]
  | some next => cases next <;> simp [Prim.passEvents, h]

/-- rc.112's `getCont` pop loop fused with the handler-skipping loop of
`exitFailCause`, as one structural recursion over the frame list. It recurses
on the list and never on `fiber.stack`, because `contAll` can push.
`docs/FRAMES-DAG.md` "Where the fusion could diverge" owns the justification
and names `AsyncFinalizer` as the one shape a later packet must re-derive.
census: rule.frames-are-primitives -/
def popFrom (demand : Arm) (skip : Bool) :
    List (Prim ν σ β ε δ ι α) -> FrameFiber ν σ β ε δ ι α -> FramePop ν σ β ε δ ι α
  | [], fiber => FramePop.mk ContAnswer.empty [] [] fiber
  | frame :: rest, fiber =>
    match Prim.answerOf frame demand (frame.ensure fiber).snd with
    | some answer =>
      if skip && (frame.ensure fiber).fst.interrupted then
        FramePop.mk (popFrom demand skip rest (frame.ensure fiber).fst).answer
          (frame :: (popFrom demand skip rest (frame.ensure fiber).fst).popped)
          (frame.passEvents (frame.ensure fiber).snd ++
            (popFrom demand skip rest (frame.ensure fiber).fst).events)
          (popFrom demand skip rest (frame.ensure fiber).fst).fiber
      else
        FramePop.mk answer [frame] (frame.passEvents (frame.ensure fiber).snd)
          { (frame.ensure fiber).fst with
            stack := (frame.ensure fiber).fst.stack ++ rest }
    | none =>
      FramePop.mk (popFrom demand skip rest (frame.ensure fiber).fst).answer
        (frame :: (popFrom demand skip rest (frame.ensure fiber).fst).popped)
        (frame.passEvents (frame.ensure fiber).snd ++
          (popFrom demand skip rest (frame.ensure fiber).fst).events)
        (popFrom demand skip rest (frame.ensure fiber).fst).fiber

/-- rc.112's `getCont`: answer a deferred interrupt before touching the stack,
then run the pop loop with the stack detached so whatever `contAll` pushes
lands on top of the frames that are left.
census: checkpoint.getcont-deferred -/
def getCont (self : FrameFiber ν σ β ε δ ι α) (demand : Arm) (skipInterrupted : Bool) :
    FramePop ν σ β ε δ ι α :=
  if self.deferredInterrupt && !skipInterrupted then
    FramePop.mk (ContAnswer.deferred self.pendingCause) []
      [FrameEvent.deferred self.pendingCause]
      { self with deferredInterrupt := false }
  else
    popFrom demand skipInterrupted self.stack
      { self with stack := [], deferredInterrupt := false }

/-- A deferred interrupt is answered before the stack is touched.
census: checkpoint.getcont-deferred -/
theorem getCont_deferred (self : FrameFiber ν σ β ε δ ι α) (demand : Arm)
    (h : self.deferredInterrupt = true) :
    self.getCont demand false =
      FramePop.mk (ContAnswer.deferred self.pendingCause) []
        [FrameEvent.deferred self.pendingCause]
        (FrameFiber.mk self.current self.stack self.interruptible self.interruptedCause
          false) := by
  simp [getCont, h]

/-- The deferred answer pops nothing. census: checkpoint.getcont-deferred -/
theorem getCont_deferred_pops_nothing (self : FrameFiber ν σ β ε δ ι α) (demand : Arm)
    (h : self.deferredInterrupt = true) : (self.getCont demand false).popped = [] := by
  rw [getCont_deferred self demand h]

/-- Without a deferred interrupt `getCont` is the pop loop over the detached
stack. census: rule.frames-are-primitives -/
theorem getCont_eq_popFrom (self : FrameFiber ν σ β ε δ ι α) (demand : Arm) (skip : Bool)
    (h : self.deferredInterrupt = false) :
    self.getCont demand skip =
      popFrom demand skip self.stack
        (FrameFiber.mk self.current [] self.interruptible self.interruptedCause false) := by
  simp [getCont, h]

/-- With skipping on, the fused loop clears the deferred flag and proceeds
straight into the pop: rc.112 answers `deferredInterruptCont`, the outer loop
discards it, and the next `getCont` finds the flag already cleared.
census: checkpoint.getcont-deferred -/
theorem getCont_skip_clears_deferred (self : FrameFiber ν σ β ε δ ι α) (demand : Arm) :
    self.getCont demand true =
      popFrom demand true self.stack
        (FrameFiber.mk self.current [] self.interruptible self.interruptedCause false) := by
  simp [getCont]

/-- An empty stack answers nothing. census: rule.frames-are-primitives -/
theorem getCont_empty_stack (self : FrameFiber ν σ β ε δ ι α) (demand : Arm) (skip : Bool)
    (hdeferred : self.deferredInterrupt = false) (hstack : self.stack = []) :
    self.getCont demand skip =
      FramePop.mk ContAnswer.empty [] []
        (FrameFiber.mk self.current [] self.interruptible self.interruptedCause false) := by
  rw [getCont_eq_popFrom self demand skip hdeferred, hstack]
  rfl

/-- The exhausted stack answers nothing. census: rule.frames-are-primitives -/
theorem popFrom_nil (demand : Arm) (skip : Bool) (fiber : FrameFiber ν σ β ε δ ι α) :
    popFrom demand skip [] fiber = FramePop.mk ContAnswer.empty [] [] fiber := rfl

/-- An answering frame supplies the answer. census: rule.frames-are-primitives -/
theorem popFrom_answer_answer (demand : Arm) (skip : Bool) (frame : Prim ν σ β ε δ ι α)
    (rest : List (Prim ν σ β ε δ ι α)) (fiber : FrameFiber ν σ β ε δ ι α)
    (answer : ContAnswer ν σ β ε δ ι α)
    (hanswer : frame.answerOf demand (frame.ensure fiber).snd = some answer)
    (hskip : (skip && (frame.ensure fiber).fst.interrupted) = false) :
    (popFrom demand skip (frame :: rest) fiber).answer = answer := by
  simp [popFrom, hanswer, hskip]

/-- An answering frame is the only frame popped.
census: rule.frames-are-primitives -/
theorem popFrom_answer_popped (demand : Arm) (skip : Bool) (frame : Prim ν σ β ε δ ι α)
    (rest : List (Prim ν σ β ε δ ι α)) (fiber : FrameFiber ν σ β ε δ ι α)
    (answer : ContAnswer ν σ β ε δ ι α)
    (hanswer : frame.answerOf demand (frame.ensure fiber).snd = some answer)
    (hskip : (skip && (frame.ensure fiber).fst.interrupted) = false) :
    (popFrom demand skip (frame :: rest) fiber).popped = [frame] := by
  simp [popFrom, hanswer, hskip]

/-- An answering frame leaves exactly its own pass trace.
census: rule.frames-are-primitives -/
theorem popFrom_answer_events (demand : Arm) (skip : Bool) (frame : Prim ν σ β ε δ ι α)
    (rest : List (Prim ν σ β ε δ ι α)) (fiber : FrameFiber ν σ β ε δ ι α)
    (answer : ContAnswer ν σ β ε δ ι α)
    (hanswer : frame.answerOf demand (frame.ensure fiber).snd = some answer)
    (hskip : (skip && (frame.ensure fiber).fst.interrupted) = false) :
    (popFrom demand skip (frame :: rest) fiber).events =
      frame.passEvents (frame.ensure fiber).snd := by
  simp [popFrom, hanswer, hskip]

/-- The frames left under an answering frame are restored beneath whatever its
hook pushed. census: rule.frames-are-primitives -/
theorem popFrom_answer_fiber (demand : Arm) (skip : Bool) (frame : Prim ν σ β ε δ ι α)
    (rest : List (Prim ν σ β ε δ ι α)) (fiber : FrameFiber ν σ β ε δ ι α)
    (answer : ContAnswer ν σ β ε δ ι α)
    (hanswer : frame.answerOf demand (frame.ensure fiber).snd = some answer)
    (hskip : (skip && (frame.ensure fiber).fst.interrupted) = false) :
    (popFrom demand skip (frame :: rest) fiber).fiber =
      { (frame.ensure fiber).fst with
        stack := (frame.ensure fiber).fst.stack ++ rest } := by
  simp [popFrom, hanswer, hskip]

/-- A frame that does not answer, or whose answer the skip discards, passes the
answer through. census: rule.frames-are-primitives -/
theorem popFrom_continue_answer (demand : Arm) (skip : Bool) (frame : Prim ν σ β ε δ ι α)
    (rest : List (Prim ν σ β ε δ ι α)) (fiber : FrameFiber ν σ β ε δ ι α)
    (h : frame.answerOf demand (frame.ensure fiber).snd = none ∨
      (skip && (frame.ensure fiber).fst.interrupted) = true) :
    (popFrom demand skip (frame :: rest) fiber).answer =
      (popFrom demand skip rest (frame.ensure fiber).fst).answer := by
  rcases h with hnone | hskip
  · simp [popFrom, hnone]
  · cases hanswer : frame.answerOf demand (frame.ensure fiber).snd with
    | none => simp [popFrom, hanswer]
    | some answer => simp [popFrom, hanswer, hskip]

/-- A passed frame is popped and the traversal continues.
census: rule.frames-are-primitives -/
theorem popFrom_continue_popped (demand : Arm) (skip : Bool) (frame : Prim ν σ β ε δ ι α)
    (rest : List (Prim ν σ β ε δ ι α)) (fiber : FrameFiber ν σ β ε δ ι α)
    (h : frame.answerOf demand (frame.ensure fiber).snd = none ∨
      (skip && (frame.ensure fiber).fst.interrupted) = true) :
    (popFrom demand skip (frame :: rest) fiber).popped =
      frame :: (popFrom demand skip rest (frame.ensure fiber).fst).popped := by
  rcases h with hnone | hskip
  · simp [popFrom, hnone]
  · cases hanswer : frame.answerOf demand (frame.ensure fiber).snd with
    | none => simp [popFrom, hanswer]
    | some answer => simp [popFrom, hanswer, hskip]

/-- A passed frame's trace precedes the rest of the traversal's.
census: rule.frames-are-primitives -/
theorem popFrom_continue_events (demand : Arm) (skip : Bool) (frame : Prim ν σ β ε δ ι α)
    (rest : List (Prim ν σ β ε δ ι α)) (fiber : FrameFiber ν σ β ε δ ι α)
    (h : frame.answerOf demand (frame.ensure fiber).snd = none ∨
      (skip && (frame.ensure fiber).fst.interrupted) = true) :
    (popFrom demand skip (frame :: rest) fiber).events =
      frame.passEvents (frame.ensure fiber).snd ++
        (popFrom demand skip rest (frame.ensure fiber).fst).events := by
  rcases h with hnone | hskip
  · simp [popFrom, hnone]
  · cases hanswer : frame.answerOf demand (frame.ensure fiber).snd with
    | none => simp [popFrom, hanswer]
    | some answer => simp [popFrom, hanswer, hskip]

/-- A passed frame's hook is threaded into the rest of the traversal.
census: rule.frames-are-primitives -/
theorem popFrom_continue_fiber (demand : Arm) (skip : Bool) (frame : Prim ν σ β ε δ ι α)
    (rest : List (Prim ν σ β ε δ ι α)) (fiber : FrameFiber ν σ β ε δ ι α)
    (h : frame.answerOf demand (frame.ensure fiber).snd = none ∨
      (skip && (frame.ensure fiber).fst.interrupted) = true) :
    (popFrom demand skip (frame :: rest) fiber).fiber =
      (popFrom demand skip rest (frame.ensure fiber).fst).fiber := by
  rcases h with hnone | hskip
  · simp [popFrom, hnone]
  · cases hanswer : frame.answerOf demand (frame.ensure fiber).snd with
    | none => simp [popFrom, hanswer]
    | some answer => simp [popFrom, hanswer, hskip]

private theorem popFrom_answer_hasArm_aux (demand : Arm) (skip : Bool)
    (frame : Prim ν σ β ε δ ι α) :
    forall (frames : List (Prim ν σ β ε δ ι α)) (fiber : FrameFiber ν σ β ε δ ι α),
      (popFrom demand skip frames fiber).answer = ContAnswer.frame frame ->
        frame.hasArm demand = true := by
  intro frames
  induction frames with
  | nil =>
    intro fiber h
    simp [popFrom] at h
  | cons head rest ih =>
    intro fiber h
    cases hanswer : head.answerOf demand (head.ensure fiber).snd with
    | none =>
      rw [popFrom_continue_answer demand skip head rest fiber (Or.inl hanswer)] at h
      exact ih (head.ensure fiber).fst h
    | some answer =>
      cases hskip : (skip && (head.ensure fiber).fst.interrupted) with
      | true =>
        rw [popFrom_continue_answer demand skip head rest fiber (Or.inr hskip)] at h
        exact ih (head.ensure fiber).fst h
      | false =>
        rw [popFrom_answer_answer demand skip head rest fiber answer hanswer hskip] at h
        have hframe := Prim.answerOf_frame_eq head frame demand (head.ensure fiber).snd
          (by rw [hanswer, h])
        rw [hframe.1]
        exact hframe.2

/-- A frame answer declares the demanded arm.
census: rule.frames-are-primitives -/
theorem popFrom_answer_hasArm (demand : Arm) (skip : Bool)
    (frames : List (Prim ν σ β ε δ ι α)) (fiber : FrameFiber ν σ β ε δ ι α)
    (frame : Prim ν σ β ε δ ι α)
    (h : (popFrom demand skip frames fiber).answer = ContAnswer.frame frame) :
    frame.hasArm demand = true :=
  popFrom_answer_hasArm_aux demand skip frame frames fiber h

/-- A `getCont` answer declares the demanded arm.
census: rule.frames-are-primitives -/
theorem getCont_answer_hasArm (self : FrameFiber ν σ β ε δ ι α) (demand : Arm) (skip : Bool)
    (frame : Prim ν σ β ε δ ι α)
    (h : (self.getCont demand skip).answer = ContAnswer.frame frame) :
    frame.hasArm demand = true := by
  simp only [getCont] at h
  split at h
  · simp at h
  · exact popFrom_answer_hasArm demand skip self.stack _ frame h

private theorem poppedFrames_append (left right : List (FrameEvent ν σ β ε δ ι α)) :
    FrameEvent.poppedFrames (left ++ right) =
      FrameEvent.poppedFrames left ++ FrameEvent.poppedFrames right :=
  List.filterMap_append

private theorem popFrom_popped_eq_events_aux (demand : Arm) (skip : Bool) :
    forall (frames : List (Prim ν σ β ε δ ι α)) (fiber : FrameFiber ν σ β ε δ ι α),
      (popFrom demand skip frames fiber).popped =
        FrameEvent.poppedFrames (popFrom demand skip frames fiber).events := by
  intro frames
  induction frames with
  | nil => intro fiber; rfl
  | cons head rest ih =>
    intro fiber
    cases hanswer : head.answerOf demand (head.ensure fiber).snd with
    | none =>
      rw [popFrom_continue_popped demand skip head rest fiber (Or.inl hanswer),
        popFrom_continue_events demand skip head rest fiber (Or.inl hanswer),
        poppedFrames_append, passEvents_poppedFrames, ih (head.ensure fiber).fst]
      rfl
    | some answer =>
      cases hskip : (skip && (head.ensure fiber).fst.interrupted) with
      | true =>
        rw [popFrom_continue_popped demand skip head rest fiber (Or.inr hskip),
          popFrom_continue_events demand skip head rest fiber (Or.inr hskip),
          poppedFrames_append, passEvents_poppedFrames, ih (head.ensure fiber).fst]
        rfl
      | false =>
        rw [popFrom_answer_popped demand skip head rest fiber answer hanswer hskip,
          popFrom_answer_events demand skip head rest fiber answer hanswer hskip,
          passEvents_poppedFrames]

/-- The popped frames are exactly the trace's pop events.
census: rule.frames-are-primitives -/
theorem popFrom_popped_eq_events (demand : Arm) (skip : Bool)
    (frames : List (Prim ν σ β ε δ ι α)) (fiber : FrameFiber ν σ β ε δ ι α) :
    (popFrom demand skip frames fiber).popped =
      FrameEvent.poppedFrames (popFrom demand skip frames fiber).events :=
  popFrom_popped_eq_events_aux demand skip frames fiber

private theorem popFrom_ranContAll_aux (demand : Arm) (skip : Bool)
    (frame : Prim ν σ β ε δ ι α) (hcontAll : frame.hasArm Arm.contAll = true) :
    forall (frames : List (Prim ν σ β ε δ ι α)) (fiber : FrameFiber ν σ β ε δ ι α),
      frame ∈ (popFrom demand skip frames fiber).popped ->
        FrameEvent.ranContAll frame ∈ (popFrom demand skip frames fiber).events := by
  intro frames
  induction frames with
  | nil =>
    intro fiber hmem
    simp [popFrom] at hmem
  | cons head rest ih =>
    intro fiber hmem
    cases hanswer : head.answerOf demand (head.ensure fiber).snd with
    | none =>
      rw [popFrom_continue_popped demand skip head rest fiber (Or.inl hanswer)] at hmem
      rw [popFrom_continue_events demand skip head rest fiber (Or.inl hanswer)]
      rcases List.mem_cons.mp hmem with hhead | htail
      · subst hhead
        exact List.mem_append_left _ (passEvents_ranContAll frame _ hcontAll)
      · exact List.mem_append_right _ (ih (head.ensure fiber).fst htail)
    | some answer =>
      cases hskip : (skip && (head.ensure fiber).fst.interrupted) with
      | true =>
        rw [popFrom_continue_popped demand skip head rest fiber (Or.inr hskip)] at hmem
        rw [popFrom_continue_events demand skip head rest fiber (Or.inr hskip)]
        rcases List.mem_cons.mp hmem with hhead | htail
        · subst hhead
          exact List.mem_append_left _ (passEvents_ranContAll frame _ hcontAll)
        · exact List.mem_append_right _ (ih (head.ensure fiber).fst htail)
      | false =>
        rw [popFrom_answer_popped demand skip head rest fiber answer hanswer hskip] at hmem
        rw [popFrom_answer_events demand skip head rest fiber answer hanswer hskip]
        rw [List.mem_singleton.mp hmem]
        exact passEvents_ranContAll head _ (by rw [← List.mem_singleton.mp hmem]; exact hcontAll)

/-- The hook ran on every popped frame that declares it: a pop that ran it only
on the answering frame would never clear the flag on the way past a mask frame.
`E4-RUN-CE-010` is the attack. census: rule.frames-are-primitives -/
theorem popFrom_ranContAll (demand : Arm) (skip : Bool)
    (frames : List (Prim ν σ β ε δ ι α)) (fiber : FrameFiber ν σ β ε δ ι α)
    (frame : Prim ν σ β ε δ ι α) (hcontAll : frame.hasArm Arm.contAll = true)
    (hmem : frame ∈ (popFrom demand skip frames fiber).popped) :
    FrameEvent.ranContAll frame ∈ (popFrom demand skip frames fiber).events :=
  popFrom_ranContAll_aux demand skip frame hcontAll frames fiber hmem

/-- The same, through `getCont`. census: rule.frames-are-primitives -/
theorem getCont_ranContAll (self : FrameFiber ν σ β ε δ ι α) (demand : Arm) (skip : Bool)
    (frame : Prim ν σ β ε δ ι α) (hdeferred : self.deferredInterrupt = false)
    (hcontAll : frame.hasArm Arm.contAll = true)
    (hmem : frame ∈ (self.getCont demand skip).popped) :
    FrameEvent.ranContAll frame ∈ (self.getCont demand skip).events := by
  rw [getCont_eq_popFrom self demand skip hdeferred] at hmem ⊢
  exact popFrom_ranContAll demand skip self.stack _ frame hcontAll hmem

private theorem ensure_interruptedCause (frame : Prim ν σ β ε δ ι α)
    (fiber : FrameFiber ν σ β ε δ ι α) :
    (frame.ensure fiber).fst.interruptedCause = fiber.interruptedCause := by
  cases frame with
  | onExit _ _ _ =>
    simp only [Prim.ensure]
    split <;> rfl
  | setInterruptible _ =>
    simp only [Prim.ensure]
    split
    · split <;> rfl
    · rfl
  | success _ => rfl
  | failure _ => rfl
  | sync _ => rfl
  | suspend _ => rfl
  | withFiber _ => rfl
  | yieldableError _ => rfl
  | iterator _ _ => rfl
  | onSuccess _ _ => rfl
  | onFailure _ _ => rfl
  | onSuccessAndFailure _ _ _ => rfl
  | exitFrame _ => rfl
  | whileLoop _ _ => rfl

private theorem popFrom_skip_eq_of_no_cause (demand : Arm) :
    forall (frames : List (Prim ν σ β ε δ ι α)) (fiber : FrameFiber ν σ β ε δ ι α),
      fiber.interruptedCause = none ->
        popFrom demand true frames fiber = popFrom demand false frames fiber := by
  intro frames
  induction frames with
  | nil => intro fiber _; rfl
  | cons head rest ih =>
    intro fiber hcause
    have hinner : (head.ensure fiber).fst.interruptedCause = none := by
      rw [ensure_interruptedCause, hcause]
    have hint : (head.ensure fiber).fst.interrupted = false := by
      rw [interrupted_eq, hinner]
      simp
    cases hanswer : head.answerOf demand (head.ensure fiber).snd with
    | none =>
      simp only [popFrom, hanswer]
      rw [ih (head.ensure fiber).fst hinner]
    | some answer => simp [popFrom, hanswer, hint]

/-- With no interruption recorded the skip flag changes nothing at all.
census: checkpoint.exit-failcause-skip -/
theorem getCont_skip_of_no_pending_cause (self : FrameFiber ν σ β ε δ ι α) (demand : Arm)
    (hdeferred : self.deferredInterrupt = false) (hcause : self.interruptedCause = none) :
    self.getCont demand true = self.getCont demand false := by
  rw [getCont_eq_popFrom self demand true hdeferred,
    getCont_eq_popFrom self demand false hdeferred]
  exact popFrom_skip_eq_of_no_cause demand self.stack _ hcause

private theorem popFrom_skip_all (demand : Arm) :
    forall (frames : List (Prim ν σ β ε δ ι α)) (fiber : FrameFiber ν σ β ε δ ι α),
      fiber.interrupted = true ->
        (forall frame, frame ∈ frames -> frame.hasArm Arm.contAll = false) ->
          (popFrom demand true frames fiber).answer = ContAnswer.empty := by
  intro frames
  induction frames with
  | nil => intro fiber _ _; rfl
  | cons head rest ih =>
    intro fiber hint hno
    have hens : head.ensure fiber = (fiber, none) :=
      Prim.ensure_of_no_contAll head fiber (hno head List.mem_cons_self)
    have hcont : head.answerOf demand (head.ensure fiber).snd = none ∨
        (true && (head.ensure fiber).fst.interrupted) = true := by
      rw [hens]
      cases hdemand : head.hasArm demand with
      | false => exact Or.inl (Prim.answerOf_missing head demand hdemand)
      | true => exact Or.inr (by simpa using hint)
    rw [popFrom_continue_answer demand true head rest fiber hcont, hens]
    exact ih fiber hint (fun frame hmem => hno frame (List.mem_cons_of_mem head hmem))

/-- Once interrupted and interruptible, the pop discards every answering `contE`
frame, so with no frame able to flip the flag the stack simply empties and no
user error handler ever sees the interruption. `E4-RUN-CE-011` is the attack.
census: checkpoint.exit-failcause-skip -/
theorem interrupt_skips_every_handler (self : FrameFiber ν σ β ε δ ι α) (demand : Arm)
    (cause : Cause ε δ ι α) (hflag : self.interruptible = true)
    (hcause : self.interruptedCause = some cause)
    (hno : forall frame, frame ∈ self.stack -> frame.hasArm Arm.contAll = false) :
    (self.getCont demand true).answer = ContAnswer.empty := by
  rw [getCont_skip_clears_deferred]
  exact popFrom_skip_all demand self.stack _ (by simp [interrupted, hflag, hcause]) hno

private theorem ensure_setInterruptible_fst (flag : Bool) (fiber : FrameFiber ν σ β ε δ ι α) :
    ((Prim.setInterruptible flag : Prim ν σ β ε δ ι α).ensure fiber).fst =
      FrameFiber.mk fiber.current fiber.stack flag fiber.interruptedCause
        fiber.deferredInterrupt := by
  cases hcause : fiber.interruptedCause with
  | none => simp [Prim.ensure, hcause]
  | some cause => cases flag <;> simp [Prim.ensure, hcause]

/-- A mask frame stops the skip: the flag is re-read after every hook, so the
handler inside the uninterruptible region does run. `E4-RUN-CE-012` is the
attack. census: rule.interrupt-bypasses-handlers -/
theorem getCont_mask_stops_skip (self : FrameFiber ν σ β ε δ ι α) (skip : Bool)
    (rest : List (Prim ν σ β ε δ ι α)) (hdeferred : self.deferredInterrupt = false)
    (hstack : self.stack = Prim.setInterruptible false :: rest) :
    (self.getCont Arm.contE skip).answer =
      ((FrameFiber.mk self.current rest false self.interruptedCause false).getCont
        Arm.contE skip).answer := by
  rw [getCont_eq_popFrom self Arm.contE skip hdeferred, hstack,
    getCont_eq_popFrom _ Arm.contE skip rfl]
  rw [popFrom_continue_answer Arm.contE skip (Prim.setInterruptible false) rest _
    (Or.inl (by
      rw [Prim.ensure_setInterruptible_false_no_replacement]
      exact Prim.answerOf_missing _ _ rfl))]
  rw [ensure_setInterruptible_fst]

/-- rc.112's `exitSucceed[evaluate]`: pop the value slot and resume. The pop
does not skip, because only the failure path skips.
census: op.Success -/
def resumeValue [DecidableEq ε] [DecidableEq δ] [DecidableEq ι] [DecidableEq α]
    (interp : PrimInterp ν σ β ε δ ι α) (self : FrameFiber ν σ β ε δ ι α) (value : β)
    (provided : Option (Exit β ε δ ι α)) :
    FrameStep ν σ β ε δ ι α × List (FrameEvent ν σ β ε δ ι α) :=
  match (self.getCont Arm.contA false).answer with
  | ContAnswer.empty =>
    (FrameStep.finished (provided.getD (Exit.success value)),
      (self.getCont Arm.contA false).events ++
        [FrameEvent.yielded (provided.getD (Exit.success value))])
  | ContAnswer.deferred cause =>
    (FrameStep.running
      { (self.getCont Arm.contA false).fiber with current := Prim.failure cause },
      (self.getCont Arm.contA false).events)
  | ContAnswer.replacement next =>
    (FrameStep.running { (self.getCont Arm.contA false).fiber with current := next },
      (self.getCont Arm.contA false).events)
  | ContAnswer.frame frame =>
    match frame.armA interp value provided with
    | some (next, pushed) =>
      (FrameStep.running
        { (self.getCont Arm.contA false).fiber with
          current := next,
          stack := pushed ++ (self.getCont Arm.contA false).fiber.stack },
        (self.getCont Arm.contA false).events ++
          frame.finalizerEvents (provided.getD (Exit.success value)) ++
          pushed.map FrameEvent.pushed)
    | none =>
      (FrameStep.finished (provided.getD (Exit.success value)),
        (self.getCont Arm.contA false).events ++
          [FrameEvent.yielded (provided.getD (Exit.success value))])

/-- rc.112's `exitFailCause[evaluate]`: pop the cause slot, skipping every
handler while the fiber is interrupted and interruptible.
census: op.Failure -/
def resumeCause [DecidableEq ε] [DecidableEq δ] [DecidableEq ι] [DecidableEq α]
    (interp : PrimInterp ν σ β ε δ ι α) (self : FrameFiber ν σ β ε δ ι α)
    (cause : Cause ε δ ι α) (provided : Option (Exit β ε δ ι α)) :
    FrameStep ν σ β ε δ ι α × List (FrameEvent ν σ β ε δ ι α) :=
  match (self.getCont Arm.contE true).answer with
  | ContAnswer.empty =>
    (FrameStep.finished (provided.getD (Exit.failure cause)),
      (self.getCont Arm.contE true).events ++
        [FrameEvent.yielded (provided.getD (Exit.failure cause))])
  | ContAnswer.deferred deferredCause =>
    (FrameStep.running
      { (self.getCont Arm.contE true).fiber with current := Prim.failure deferredCause },
      (self.getCont Arm.contE true).events)
  | ContAnswer.replacement next =>
    (FrameStep.running { (self.getCont Arm.contE true).fiber with current := next },
      (self.getCont Arm.contE true).events)
  | ContAnswer.frame frame =>
    match frame.armE interp cause provided with
    | some (next, pushed) =>
      (FrameStep.running
        { (self.getCont Arm.contE true).fiber with
          current := next,
          stack := pushed ++ (self.getCont Arm.contE true).fiber.stack },
        (self.getCont Arm.contE true).events ++
          frame.finalizerEvents (provided.getD (Exit.failure cause)) ++
          pushed.map FrameEvent.pushed)
    | none =>
      (FrameStep.finished (provided.getD (Exit.failure cause)),
        (self.getCont Arm.contE true).events ++
          [FrameEvent.yielded (provided.getD (Exit.failure cause))])

/-- One machine step, one equation per pinned op. A total function, not a
relation: this model has no decision source, so `docs/DESIGN-BASIS.md` DB-03's
relational requirement does not bite here. census: rule.frames-are-primitives -/
def step [DecidableEq ε] [DecidableEq δ] [DecidableEq ι] [DecidableEq α]
    (interp : PrimInterp ν σ β ε δ ι α) (self : FrameFiber ν σ β ε δ ι α) :
    FrameStep ν σ β ε δ ι α × List (FrameEvent ν σ β ε δ ι α) :=
  match self.current with
  | Prim.success value => self.resumeValue interp value (some (Exit.success value))
  | Prim.failure cause => self.resumeCause interp cause (some (Exit.failure cause))
  | Prim.sync thunk => self.resumeValue interp (interp.syncValue thunk) none
  | Prim.suspend thunk =>
    (FrameStep.running { self with current := interp.suspendBody thunk }, [])
  | Prim.withFiber thunk =>
    (FrameStep.running { self with current := interp.suspendBody thunk }, [])
  | Prim.yieldableError error =>
    (FrameStep.running { self with current := Prim.failure (Cause.fail error) }, [])
  | Prim.iterator generator cursor =>
    match (Prim.iterator generator cursor : Prim ν σ β ε δ ι α).armA interp cursor none with
    | some (next, pushed) =>
      (FrameStep.running { self with current := next, stack := pushed ++ self.stack },
        pushed.map FrameEvent.pushed)
    | none => (FrameStep.running self, [])
  | Prim.onSuccess body onValue =>
    (FrameStep.running
      { self with current := body, stack := Prim.onSuccess body onValue :: self.stack },
      [FrameEvent.pushed (Prim.onSuccess body onValue)])
  | Prim.onFailure body onCause =>
    (FrameStep.running
      { self with current := body, stack := Prim.onFailure body onCause :: self.stack },
      [FrameEvent.pushed (Prim.onFailure body onCause)])
  | Prim.onSuccessAndFailure body onValue onCause =>
    (FrameStep.running
      { self with
        current := body,
        stack := Prim.onSuccessAndFailure body onValue onCause :: self.stack },
      [FrameEvent.pushed (Prim.onSuccessAndFailure body onValue onCause)])
  | Prim.exitFrame body =>
    (FrameStep.running
      { self with current := body, stack := Prim.exitFrame body :: self.stack },
      [FrameEvent.pushed (Prim.exitFrame body)])
  | Prim.onExit body finalizer flag =>
    (FrameStep.running
      { self with
        current := body,
        stack := Prim.onExit body finalizer flag :: self.stack },
      [FrameEvent.pushed (Prim.onExit body finalizer flag)])
  | Prim.setInterruptible _ =>
    (FrameStep.running
      { self with current := Prim.failure (Cause.die interp.notImplemented) }, [])
  | Prim.whileLoop loop cursor =>
    if interp.loopTest loop cursor then
      (FrameStep.running
        { self with
          current := interp.loopBody loop cursor,
          stack := Prim.whileLoop loop cursor :: self.stack },
        [FrameEvent.pushed (Prim.whileLoop loop cursor)])
    else
      (FrameStep.running { self with current := Prim.success (interp.loopDone loop) }, [])

/-- The bounded runner. `FrameStep.running` at exhausted fuel is a live
frontier under `docs/DESIGN-BASIS.md` DB-04: never a failure, never a defect,
never an interruption and never a refusal. It exists so that which frames were
popped and which finalizers ran is statable across more than one step.
census: exit.success-failure -/
def run [DecidableEq ε] [DecidableEq δ] [DecidableEq ι] [DecidableEq α]
    (interp : PrimInterp ν σ β ε δ ι α) :
    Nat -> FrameFiber ν σ β ε δ ι α ->
      FrameStep ν σ β ε δ ι α × List (FrameEvent ν σ β ε δ ι α)
  | 0, self => (FrameStep.running self, [])
  | fuel + 1, self =>
    match step interp self with
    | (FrameStep.finished exit, events) => (FrameStep.finished exit, events)
    | (FrameStep.running next, events) =>
      ((run interp fuel next).fst, events ++ (run interp fuel next).snd)

/-- With an empty stack the fiber yields the exit it produced.
`E4-RUN-CE-020` is the attack. census: op.Success -/
theorem resumeValue_empty [DecidableEq ε] [DecidableEq δ] [DecidableEq ι] [DecidableEq α]
    (interp : PrimInterp ν σ β ε δ ι α) (self : FrameFiber ν σ β ε δ ι α) (value : β)
    (provided : Option (Exit β ε δ ι α))
    (h : (self.getCont Arm.contA false).answer = ContAnswer.empty) :
    self.resumeValue interp value provided =
      (FrameStep.finished (provided.getD (Exit.success value)),
        (self.getCont Arm.contA false).events ++
          [FrameEvent.yielded (provided.getD (Exit.success value))]) := by
  simp [resumeValue, h]

/-- A deferred interrupt fails the fiber with the accumulated cause.
census: checkpoint.getcont-deferred -/
theorem resumeValue_deferred [DecidableEq ε] [DecidableEq δ] [DecidableEq ι] [DecidableEq α]
    (interp : PrimInterp ν σ β ε δ ι α) (self : FrameFiber ν σ β ε δ ι α) (value : β)
    (provided : Option (Exit β ε δ ι α)) (cause : Cause ε δ ι α)
    (h : (self.getCont Arm.contA false).answer = ContAnswer.deferred cause) :
    self.resumeValue interp value provided =
      (FrameStep.running
        { (self.getCont Arm.contA false).fiber with current := Prim.failure cause },
        (self.getCont Arm.contA false).events) := by
  simp [resumeValue, h]

/-- A substituted continuation is used for the value arm.
census: checkpoint.set-interruptible-contall -/
theorem resumeValue_replacement [DecidableEq ε] [DecidableEq δ] [DecidableEq ι]
    [DecidableEq α] (interp : PrimInterp ν σ β ε δ ι α) (self : FrameFiber ν σ β ε δ ι α)
    (value : β) (provided : Option (Exit β ε δ ι α)) (next : Prim ν σ β ε δ ι α)
    (h : (self.getCont Arm.contA false).answer = ContAnswer.replacement next) :
    self.resumeValue interp value provided =
      (FrameStep.running { (self.getCont Arm.contA false).fiber with current := next },
        (self.getCont Arm.contA false).events) := by
  simp [resumeValue, h]

/-- An answering frame runs its value arm and pushes what the arm pushes.
census: op.Success -/
theorem resumeValue_frame [DecidableEq ε] [DecidableEq δ] [DecidableEq ι] [DecidableEq α]
    (interp : PrimInterp ν σ β ε δ ι α) (self : FrameFiber ν σ β ε δ ι α) (value : β)
    (provided : Option (Exit β ε δ ι α)) (frame next : Prim ν σ β ε δ ι α)
    (pushed : List (Prim ν σ β ε δ ι α))
    (hanswer : (self.getCont Arm.contA false).answer = ContAnswer.frame frame)
    (harm : frame.armA interp value provided = some (next, pushed)) :
    self.resumeValue interp value provided =
      (FrameStep.running
        { (self.getCont Arm.contA false).fiber with
          current := next,
          stack := pushed ++ (self.getCont Arm.contA false).fiber.stack },
        (self.getCont Arm.contA false).events ++
          frame.finalizerEvents (provided.getD (Exit.success value)) ++
          pushed.map FrameEvent.pushed) := by
  simp [resumeValue, hanswer, harm]

/-- With no handler left the fiber yields the failed exit.
census: op.Failure -/
theorem resumeCause_empty [DecidableEq ε] [DecidableEq δ] [DecidableEq ι] [DecidableEq α]
    (interp : PrimInterp ν σ β ε δ ι α) (self : FrameFiber ν σ β ε δ ι α)
    (cause : Cause ε δ ι α) (provided : Option (Exit β ε δ ι α))
    (h : (self.getCont Arm.contE true).answer = ContAnswer.empty) :
    self.resumeCause interp cause provided =
      (FrameStep.finished (provided.getD (Exit.failure cause)),
        (self.getCont Arm.contE true).events ++
          [FrameEvent.yielded (provided.getD (Exit.failure cause))]) := by
  simp [resumeCause, h]

/-- A deferred interrupt fails the fiber with the accumulated cause on the
failure path too. census: checkpoint.getcont-deferred -/
theorem resumeCause_deferred [DecidableEq ε] [DecidableEq δ] [DecidableEq ι] [DecidableEq α]
    (interp : PrimInterp ν σ β ε δ ι α) (self : FrameFiber ν σ β ε δ ι α)
    (cause deferredCause : Cause ε δ ι α) (provided : Option (Exit β ε δ ι α))
    (h : (self.getCont Arm.contE true).answer = ContAnswer.deferred deferredCause) :
    self.resumeCause interp cause provided =
      (FrameStep.running
        { (self.getCont Arm.contE true).fiber with
          current := Prim.failure deferredCause },
        (self.getCont Arm.contE true).events) := by
  simp [resumeCause, h]

/-- A substituted continuation is used for the cause arm as well.
census: checkpoint.set-interruptible-contall -/
theorem resumeCause_replacement [DecidableEq ε] [DecidableEq δ] [DecidableEq ι]
    [DecidableEq α] (interp : PrimInterp ν σ β ε δ ι α) (self : FrameFiber ν σ β ε δ ι α)
    (cause : Cause ε δ ι α) (provided : Option (Exit β ε δ ι α)) (next : Prim ν σ β ε δ ι α)
    (h : (self.getCont Arm.contE true).answer = ContAnswer.replacement next) :
    self.resumeCause interp cause provided =
      (FrameStep.running { (self.getCont Arm.contE true).fiber with current := next },
        (self.getCont Arm.contE true).events) := by
  simp [resumeCause, h]

/-- An answering frame runs its cause arm and pushes what the arm pushes.
census: op.Failure -/
theorem resumeCause_frame [DecidableEq ε] [DecidableEq δ] [DecidableEq ι] [DecidableEq α]
    (interp : PrimInterp ν σ β ε δ ι α) (self : FrameFiber ν σ β ε δ ι α)
    (cause : Cause ε δ ι α) (provided : Option (Exit β ε δ ι α))
    (frame next : Prim ν σ β ε δ ι α) (pushed : List (Prim ν σ β ε δ ι α))
    (hanswer : (self.getCont Arm.contE true).answer = ContAnswer.frame frame)
    (harm : frame.armE interp cause provided = some (next, pushed)) :
    self.resumeCause interp cause provided =
      (FrameStep.running
        { (self.getCont Arm.contE true).fiber with
          current := next,
          stack := pushed ++ (self.getCont Arm.contE true).fiber.stack },
        (self.getCont Arm.contE true).events ++
          frame.finalizerEvents (provided.getD (Exit.failure cause)) ++
          pushed.map FrameEvent.pushed) := by
  simp [resumeCause, hanswer, harm]

/-- `Success` pops the value slot and supplies itself as the pop's exit.
census: op.Success -/
theorem step_success [DecidableEq ε] [DecidableEq δ] [DecidableEq ι] [DecidableEq α]
    (interp : PrimInterp ν σ β ε δ ι α) (self : FrameFiber ν σ β ε δ ι α) (value : β) :
    (FrameFiber.mk (Prim.success value) self.stack self.interruptible self.interruptedCause
        self.deferredInterrupt).step interp =
      (FrameFiber.mk (Prim.success value) self.stack self.interruptible self.interruptedCause
        self.deferredInterrupt).resumeValue interp value (some (Exit.success value)) := rfl

/-- `Failure` pops the cause slot and supplies itself as the pop's exit. The
stack-frame cause annotation is refused as `FRAME-FB-STACK-ANNOTATION`, which
is why `op.Failure` stays partial. census: op.Failure -/
theorem step_failure [DecidableEq ε] [DecidableEq δ] [DecidableEq ι] [DecidableEq α]
    (interp : PrimInterp ν σ β ε δ ι α) (self : FrameFiber ν σ β ε δ ι α)
    (cause : Cause ε δ ι α) :
    (FrameFiber.mk (Prim.failure cause) self.stack self.interruptible self.interruptedCause
        self.deferredInterrupt).step interp =
      (FrameFiber.mk (Prim.failure cause) self.stack self.interruptible self.interruptedCause
        self.deferredInterrupt).resumeCause interp cause (some (Exit.failure cause)) := rfl

/-- `Sync` runs the thunk and then behaves like `Success`, but supplies no
exit: rc.112 calls `cont[contA](value, fiber)` and not
`cont[contA](this[args], fiber, this)`. census: op.Sync -/
theorem step_sync [DecidableEq ε] [DecidableEq δ] [DecidableEq ι] [DecidableEq α]
    (interp : PrimInterp ν σ β ε δ ι α) (self : FrameFiber ν σ β ε δ ι α) (thunk : σ) :
    (FrameFiber.mk (Prim.sync thunk) self.stack self.interruptible self.interruptedCause
        self.deferredInterrupt).step interp =
      (FrameFiber.mk (Prim.sync thunk) self.stack self.interruptible self.interruptedCause
        self.deferredInterrupt).resumeValue interp (interp.syncValue thunk) none := rfl

/-- `Suspend` returns the primitive the thunk names, with no stack interaction.
census: op.Suspend -/
theorem step_suspend [DecidableEq ε] [DecidableEq δ] [DecidableEq ι] [DecidableEq α]
    (interp : PrimInterp ν σ β ε δ ι α) (self : FrameFiber ν σ β ε δ ι α) (thunk : σ) :
    (FrameFiber.mk (Prim.suspend thunk) self.stack self.interruptible self.interruptedCause
        self.deferredInterrupt).step interp =
      (FrameStep.running
        (FrameFiber.mk (interp.suspendBody thunk) self.stack self.interruptible
          self.interruptedCause self.deferredInterrupt), []) := rfl

/-- `WithFiber` is modelled by the effect it returns; the raw `FiberImpl`
handover is refused as `FRAME-FB-RAW-FIBER`. census: op.WithFiber -/
theorem step_withFiber [DecidableEq ε] [DecidableEq δ] [DecidableEq ι] [DecidableEq α]
    (interp : PrimInterp ν σ β ε δ ι α) (self : FrameFiber ν σ β ε δ ι α) (thunk : σ) :
    (FrameFiber.mk (Prim.withFiber thunk) self.stack self.interruptible self.interruptedCause
        self.deferredInterrupt).step interp =
      (FrameStep.running
        (FrameFiber.mk (interp.suspendBody thunk) self.stack self.interruptible
          self.interruptedCause self.deferredInterrupt), []) := rfl

/-- `YieldableError`'s `evaluate` is `exitFail(this)`; the host `Error` class
identity is refused as `FRAME-FB-HOST-ERROR`. census: op.YieldableError -/
theorem step_yieldableError [DecidableEq ε] [DecidableEq δ] [DecidableEq ι] [DecidableEq α]
    (interp : PrimInterp ν σ β ε δ ι α) (self : FrameFiber ν σ β ε δ ι α) (error : ε) :
    (FrameFiber.mk (Prim.yieldableError error) self.stack self.interruptible
        self.interruptedCause self.deferredInterrupt).step interp =
      (FrameStep.running
        (FrameFiber.mk (Prim.failure (Cause.fail error)) self.stack self.interruptible
          self.interruptedCause self.deferredInterrupt), []) := rfl

/-- `OnSuccess` pushes itself and continues with its body.
census: op.OnSuccess -/
theorem step_onSuccess [DecidableEq ε] [DecidableEq δ] [DecidableEq ι] [DecidableEq α]
    (interp : PrimInterp ν σ β ε δ ι α) (self : FrameFiber ν σ β ε δ ι α)
    (body : Prim ν σ β ε δ ι α) (onValue : ν) :
    (FrameFiber.mk (Prim.onSuccess body onValue) self.stack self.interruptible
        self.interruptedCause self.deferredInterrupt).step interp =
      (FrameStep.running
        (FrameFiber.mk body (Prim.onSuccess body onValue :: self.stack) self.interruptible
          self.interruptedCause self.deferredInterrupt),
        [FrameEvent.pushed (Prim.onSuccess body onValue)]) := rfl

/-- `OnFailure` pushes itself and continues with its body.
census: op.OnFailure -/
theorem step_onFailure [DecidableEq ε] [DecidableEq δ] [DecidableEq ι] [DecidableEq α]
    (interp : PrimInterp ν σ β ε δ ι α) (self : FrameFiber ν σ β ε δ ι α)
    (body : Prim ν σ β ε δ ι α) (onCause : ν) :
    (FrameFiber.mk (Prim.onFailure body onCause) self.stack self.interruptible
        self.interruptedCause self.deferredInterrupt).step interp =
      (FrameStep.running
        (FrameFiber.mk body (Prim.onFailure body onCause :: self.stack) self.interruptible
          self.interruptedCause self.deferredInterrupt),
        [FrameEvent.pushed (Prim.onFailure body onCause)]) := rfl

/-- `OnSuccessAndFailure` pushes itself and continues with its body.
census: op.OnSuccessAndFailure -/
theorem step_onSuccessAndFailure [DecidableEq ε] [DecidableEq δ] [DecidableEq ι]
    [DecidableEq α] (interp : PrimInterp ν σ β ε δ ι α) (self : FrameFiber ν σ β ε δ ι α)
    (body : Prim ν σ β ε δ ι α) (onValue onCause : ν) :
    (FrameFiber.mk (Prim.onSuccessAndFailure body onValue onCause) self.stack
        self.interruptible self.interruptedCause self.deferredInterrupt).step interp =
      (FrameStep.running
        (FrameFiber.mk body (Prim.onSuccessAndFailure body onValue onCause :: self.stack)
          self.interruptible self.interruptedCause self.deferredInterrupt),
        [FrameEvent.pushed (Prim.onSuccessAndFailure body onValue onCause)]) := rfl

/-- The `Exit` frame pushes itself and continues with its body.
census: op.Exit -/
theorem step_exitFrame [DecidableEq ε] [DecidableEq δ] [DecidableEq ι] [DecidableEq α]
    (interp : PrimInterp ν σ β ε δ ι α) (self : FrameFiber ν σ β ε δ ι α)
    (body : Prim ν σ β ε δ ι α) :
    (FrameFiber.mk (Prim.exitFrame body) self.stack self.interruptible self.interruptedCause
        self.deferredInterrupt).step interp =
      (FrameStep.running
        (FrameFiber.mk body (Prim.exitFrame body :: self.stack) self.interruptible
          self.interruptedCause self.deferredInterrupt),
        [FrameEvent.pushed (Prim.exitFrame body)]) := rfl

/-- `OnExit` pushes itself and continues with its body. census: op.OnExit -/
theorem step_onExit [DecidableEq ε] [DecidableEq δ] [DecidableEq ι] [DecidableEq α]
    (interp : PrimInterp ν σ β ε δ ι α) (self : FrameFiber ν σ β ε δ ι α)
    (body : Prim ν σ β ε δ ι α) (finalizer : ν) (flag : Bool) :
    (FrameFiber.mk (Prim.onExit body finalizer flag) self.stack self.interruptible
        self.interruptedCause self.deferredInterrupt).step interp =
      (FrameStep.running
        (FrameFiber.mk body (Prim.onExit body finalizer flag :: self.stack)
          self.interruptible self.interruptedCause self.deferredInterrupt),
        [FrameEvent.pushed (Prim.onExit body finalizer flag)]) := rfl

/-- rc.112 gives `setInterruptible` no `evaluate`, and `defaultEvaluate`
returns `exitDie("Effect.evaluate: Not implemented")`: a mask frame stepped as
the current effect is a defect. census: op.SetInterruptible -/
theorem step_setInterruptible_not_evaluable [DecidableEq ε] [DecidableEq δ] [DecidableEq ι]
    [DecidableEq α] (interp : PrimInterp ν σ β ε δ ι α) (self : FrameFiber ν σ β ε δ ι α)
    (flag : Bool) :
    (FrameFiber.mk (Prim.setInterruptible flag) self.stack self.interruptible
        self.interruptedCause self.deferredInterrupt).step interp =
      (FrameStep.running
        (FrameFiber.mk (Prim.failure (Cause.die interp.notImplemented)) self.stack
          self.interruptible self.interruptedCause self.deferredInterrupt), []) := rfl

/-- A loop whose test passes pushes itself and runs its body.
census: op.While -/
theorem step_whileLoop_true [DecidableEq ε] [DecidableEq δ] [DecidableEq ι] [DecidableEq α]
    (interp : PrimInterp ν σ β ε δ ι α) (self : FrameFiber ν σ β ε δ ι α) (loop : ν)
    (cursor : β) (h : interp.loopTest loop cursor = true) :
    (FrameFiber.mk (Prim.whileLoop loop cursor) self.stack self.interruptible
        self.interruptedCause self.deferredInterrupt).step interp =
      (FrameStep.running
        (FrameFiber.mk (interp.loopBody loop cursor)
          (Prim.whileLoop loop cursor :: self.stack) self.interruptible
          self.interruptedCause self.deferredInterrupt),
        [FrameEvent.pushed (Prim.whileLoop loop cursor)]) := by
  simp [step, h]

/-- A loop whose test fails finishes with the supplied terminal value.
census: op.While -/
theorem step_whileLoop_false [DecidableEq ε] [DecidableEq δ] [DecidableEq ι] [DecidableEq α]
    (interp : PrimInterp ν σ β ε δ ι α) (self : FrameFiber ν σ β ε δ ι α) (loop : ν)
    (cursor : β) (h : interp.loopTest loop cursor = false) :
    (FrameFiber.mk (Prim.whileLoop loop cursor) self.stack self.interruptible
        self.interruptedCause self.deferredInterrupt).step interp =
      (FrameStep.running
        (FrameFiber.mk (Prim.success (interp.loopDone loop)) self.stack self.interruptible
          self.interruptedCause self.deferredInterrupt), []) := by
  simp [step, h]

/-- The `Iterator` frame's `evaluate` delegates to its own value arm, so the
inline fold happens without a `getCont` checkpoint. census: op.Iterator -/
theorem step_iterator [DecidableEq ε] [DecidableEq δ] [DecidableEq ι] [DecidableEq α]
    (interp : PrimInterp ν σ β ε δ ι α) (self : FrameFiber ν σ β ε δ ι α) (generator : ν)
    (cursor : β) (next : Prim ν σ β ε δ ι α) (pushed : List (Prim ν σ β ε δ ι α))
    (h : (Prim.iterator generator cursor : Prim ν σ β ε δ ι α).armA interp cursor none =
      some (next, pushed)) :
    (FrameFiber.mk (Prim.iterator generator cursor) self.stack self.interruptible
        self.interruptedCause self.deferredInterrupt).step interp =
      (FrameStep.running
        (FrameFiber.mk next (pushed ++ self.stack) self.interruptible self.interruptedCause
          self.deferredInterrupt), pushed.map FrameEvent.pushed) := by
  simp [step, h]

/-- A bare exit with an empty stack finishes with that exit.
census: exit.success-failure -/
theorem step_ofExit_finishes [DecidableEq ε] [DecidableEq δ] [DecidableEq ι] [DecidableEq α]
    (interp : PrimInterp ν σ β ε δ ι α) (exit : Exit β ε δ ι α) :
    (start (Prim.ofExit exit : Prim ν σ β ε δ ι α)).step interp =
      (FrameStep.finished exit, [FrameEvent.yielded exit]) := by
  cases exit <;> rfl

/-- No fuel is no step. census: exit.success-failure -/
theorem run_zero [DecidableEq ε] [DecidableEq δ] [DecidableEq ι] [DecidableEq α]
    (interp : PrimInterp ν σ β ε δ ι α) (self : FrameFiber ν σ β ε δ ι α) :
    self.run interp 0 = (FrameStep.running self, []) := rfl

/-- A finished step ends the run. census: exit.success-failure -/
theorem run_succ_finished [DecidableEq ε] [DecidableEq δ] [DecidableEq ι] [DecidableEq α]
    (interp : PrimInterp ν σ β ε δ ι α) (self : FrameFiber ν σ β ε δ ι α) (fuel : Nat)
    (exit : Exit β ε δ ι α) (events : List (FrameEvent ν σ β ε δ ι α))
    (h : self.step interp = (FrameStep.finished exit, events)) :
    self.run interp (fuel + 1) = (FrameStep.finished exit, events) := by
  simp [run, h]

/-- A running step spends one unit of fuel and concatenates the traces.
census: exit.success-failure -/
theorem run_succ_running [DecidableEq ε] [DecidableEq δ] [DecidableEq ι] [DecidableEq α]
    (interp : PrimInterp ν σ β ε δ ι α) (self next : FrameFiber ν σ β ε δ ι α) (fuel : Nat)
    (events : List (FrameEvent ν σ β ε δ ι α))
    (h : self.step interp = (FrameStep.running next, events)) :
    self.run interp (fuel + 1) =
      ((next.run interp fuel).fst, events ++ (next.run interp fuel).snd) := by
  simp [run, h]

/-- rc.112's `uninterruptible`: mask the fiber and push the restoring frame. -/
def uninterruptible (self : FrameFiber ν σ β ε δ ι α) : FrameFiber ν σ β ε δ ι α :=
  if self.interruptible then
    { self with
      stack := Prim.setInterruptible true :: self.stack,
      interruptible := false }
  else self

/-- rc.112's `setFiberInterruptible`: restore interruptibility, push the
re-masking frame, and fail now if a cause is already pending. -/
def setFiberInterruptible (self : FrameFiber ν σ β ε δ ι α) :
    FrameFiber ν σ β ε δ ι α × Option (Prim ν σ β ε δ ι α) :=
  ({ self with
      stack := Prim.setInterruptible false :: self.stack,
      interruptible := true },
    match self.interruptedCause with
    | some cause => some (Prim.failure cause)
    | none => none)

/-- rc.112's `interruptible` combinator; the rename is forced because
`FrameFiber.interruptible` is already the field name. -/
def interruptibleRegion (self : FrameFiber ν σ β ε δ ι α) :
    FrameFiber ν σ β ε δ ι α × Option (Prim ν σ β ε δ ι α) :=
  if self.interruptible then (self, none) else self.setFiberInterruptible

/-- rc.112's `uninterruptibleMask`, whose fiber side is `uninterruptible`. -/
def uninterruptibleMask (self : FrameFiber ν σ β ε δ ι α) : FrameFiber ν σ β ε δ ι α :=
  self.uninterruptible

/-- The `restore` an `uninterruptibleMask` hands its body, applied only when
`acquireRelease` asked for an interruptible acquire. -/
def restoreAcquire (self : FrameFiber ν σ β ε δ ι α) (asked : Bool) :
    FrameFiber ν σ β ε δ ι α × Option (Prim ν σ β ε δ ι α) :=
  match asked with
  | true => self.interruptibleRegion
  | false => (self, none)

/-- An uninterruptible region inside an uninterruptible region pushes no second
restoring frame: the mask is not a counter. census: scope.acquire-release -/
theorem uninterruptible_already_masked (self : FrameFiber ν σ β ε δ ι α)
    (h : self.interruptible = false) : self.uninterruptible = self := by
  simp [uninterruptible, h]

/-- Masking an interruptible fiber pushes the restoring frame.
census: scope.acquire-release -/
theorem uninterruptible_masks (self : FrameFiber ν σ β ε δ ι α)
    (h : self.interruptible = true) :
    self.uninterruptible =
      FrameFiber.mk self.current (Prim.setInterruptible true :: self.stack) false
        self.interruptedCause self.deferredInterrupt := by
  simp [uninterruptible, h]

/-- The mask combinator's fiber side is exactly `uninterruptible`.
census: scope.acquire-release -/
theorem uninterruptibleMask_eq (self : FrameFiber ν σ β ε δ ι α) :
    self.uninterruptibleMask = self.uninterruptible := rfl

/-- Restoring interruptibility sets the flag.
census: checkpoint.set-fiber-interruptible -/
theorem setFiberInterruptible_flag (self : FrameFiber ν σ β ε δ ι α) :
    self.setFiberInterruptible.fst.interruptible = true := rfl

/-- Restoring interruptibility pushes the re-masking frame.
census: checkpoint.set-fiber-interruptible -/
theorem setFiberInterruptible_pushes (self : FrameFiber ν σ β ε δ ι α) :
    self.setFiberInterruptible.fst.stack = Prim.setInterruptible false :: self.stack := rfl

/-- Restoring interruptibility with a cause already pending fails now, before
the body runs. census: checkpoint.set-fiber-interruptible -/
theorem setFiberInterruptible_immediate_failure (self : FrameFiber ν σ β ε δ ι α)
    (cause : Cause ε δ ι α) (h : self.interruptedCause = some cause) :
    self.setFiberInterruptible.snd = some (Prim.failure cause) := by
  simp [setFiberInterruptible, h]

/-- With no cause pending nothing fails immediately.
census: checkpoint.set-fiber-interruptible -/
theorem setFiberInterruptible_no_pending (self : FrameFiber ν σ β ε δ ι α)
    (h : self.interruptedCause = none) : self.setFiberInterruptible.snd = none := by
  simp [setFiberInterruptible, h]

/-- An already interruptible fiber is left alone.
census: checkpoint.set-fiber-interruptible -/
theorem interruptibleRegion_already (self : FrameFiber ν σ β ε δ ι α)
    (h : self.interruptible = true) : self.interruptibleRegion = (self, none) := by
  simp [interruptibleRegion, h]

/-- A masked fiber goes through `setFiberInterruptible`.
census: checkpoint.set-fiber-interruptible -/
theorem interruptibleRegion_masked (self : FrameFiber ν σ β ε δ ι α)
    (h : self.interruptible = false) :
    self.interruptibleRegion = self.setFiberInterruptible := by
  simp [interruptibleRegion, h]

/-- `options?.interruptible ? restore(acquire) : acquire`, asked.
census: scope.acquire-release -/
theorem restoreAcquire_asked (self : FrameFiber ν σ β ε δ ι α) :
    self.restoreAcquire true = self.interruptibleRegion := rfl

/-- `options?.interruptible ? restore(acquire) : acquire`, not asked.
census: scope.acquire-release -/
theorem restoreAcquire_not_asked (self : FrameFiber ν σ β ε δ ι α) :
    self.restoreAcquire false = (self, none) := rfl

end FrameFiber

namespace Prim

/-- rc.112's `scoped`, stack side only: the body under one `OnExit` frame whose
finalizer name stands for `exit => { restore context; scopeCloseUnsafe(scope,
exit) }`. The scope side of the same census row is `Effect4.Scope.runScoped`,
which this module neither imports nor duplicates, and no relation between the
two is claimed here. census: scope.scoped -/
def scopedFrame (body : Prim ν σ β ε δ ι α) (closeScope : ν) : Prim ν σ β ε δ ι α :=
  onExit body closeScope false

/-- `scoped` is one `OnExit` frame, masked because `onExitPrimitive` is called
with no third argument. census: scope.scoped -/
theorem scopedFrame_eq [DecidableEq ε] [DecidableEq δ] [DecidableEq ι] [DecidableEq α]
    (body : Prim ν σ β ε δ ι α) (closeScope : ν) :
    scopedFrame body closeScope = onExit body closeScope false := rfl

/-- The scope-closing finalizer runs masked. census: scope.scoped -/
theorem scopedFrame_finalizer_masked [DecidableEq ε] [DecidableEq δ] [DecidableEq ι]
    [DecidableEq α] (body : Prim ν σ β ε δ ι α) (closeScope : ν)
    (fiber : FrameFiber ν σ β ε δ ι α) (h : fiber.interruptible = true) :
    (scopedFrame body closeScope).ensure fiber =
      (FrameFiber.mk fiber.current (setInterruptible true :: fiber.stack) false
        fiber.interruptedCause fiber.deferredInterrupt, none) :=
  ensure_onExit_masks body closeScope fiber h

/-- Any Effect4 interpretation of a `WithFiber` body is a function of the five
modelled fields, so two fibers agreeing on them get the same effect and the
host object distinction is not representable. This is a theorem-shaped refusal,
not a model of object identity: `FRAME-FB-RAW-FIBER` names what is refused and
`E4-RUN-CE-021` exhibits the pair. census: op.WithFiber -/
theorem withFiber_refused [DecidableEq ε] [DecidableEq δ] [DecidableEq ι] [DecidableEq α]
    {ϑ : Type u} (resolve : FrameFiber ν σ β ε δ ι α -> ϑ)
    (left right : FrameFiber ν σ β ε δ ι α) (h : left = right) :
    resolve left = resolve right :=
  congrArg resolve h

/-- Any Effect4 rendering of a `YieldableError` is a function of the admitted
error payload, so two host errors with equal payloads and different messages or
stacks are one Effect4 cause. `FRAME-FB-HOST-ERROR` names what is refused and
`E4-RUN-CE-021` exhibits the pair; the behaviour itself is modelled by
`Effect4.FrameFiber.step_yieldableError`. census: op.YieldableError -/
theorem yieldableError_host_class_refused [DecidableEq ε] {ϑ : Type u} (host : ε -> ϑ)
    (left right : ε) (h : left = right) : host left = host right :=
  congrArg host h

end Prim

namespace FrameFiber

/-- The stack side of `scoped` steps exactly as its `OnExit` frame does.
census: scope.scoped -/
theorem step_scopedFrame [DecidableEq ε] [DecidableEq δ] [DecidableEq ι] [DecidableEq α]
    (interp : PrimInterp ν σ β ε δ ι α) (self : FrameFiber ν σ β ε δ ι α)
    (body : Prim ν σ β ε δ ι α) (closeScope : ν) :
    (FrameFiber.mk (Prim.scopedFrame body closeScope) self.stack self.interruptible
        self.interruptedCause self.deferredInterrupt).step interp =
      (FrameStep.running
        (FrameFiber.mk body (Prim.onExit body closeScope false :: self.stack)
          self.interruptible self.interruptedCause self.deferredInterrupt),
        [FrameEvent.pushed (Prim.onExit body closeScope false)]) := rfl

end FrameFiber


/-! ## The uninterrupted fragment, and fuel additivity

Fence A of packet D4 (`docs/research/2026-09-03-frame-simulation.md` section 1.3
and "Fuel adequacy"). Nothing in this module ever *writes* `interruptedCause`:
`FrameFiber.start` sets it to `none`, `Prim.ensure` only reads it, and
`getCont` only clears the deferred flag. So
`interruptedCause = none /\ deferredInterrupt = false` is an invariant of
`step`, and under it the whole interrupt half of the machine is inert: an
answering frame is never skipped by `popFrom`, and `getCont` never answers the
deferred interrupt.

`FRAME-FB-NONNULL` (`docs/FRAMES-DAG.md`) becomes **vacuous on that fragment**:
the state in which `pendingCause` answers `Cause.empty` where rc.112 asserts
`_interruptedCause!` is not reachable from `start` by `step`. The row is *not*
retired. The invariant is a fragment fact, not a model fact: the supervision
packet that records an interrupt breaks the hypothesis, and that row is exactly
what states what happens then.

`run_add` and `run_mono` are the fuel laws the module lacked. DB-04 forbids the
`forall fuel` form -- exhausted fuel is a live frontier, never a result -- so
every downstream statement is `forall fuel >= bound`, and that shape needs
these two.
-/

namespace FrameFiber

private theorem ensure_deferredInterrupt (frame : Prim ν σ β ε δ ι α)
    (fiber : FrameFiber ν σ β ε δ ι α) :
    (frame.ensure fiber).fst.deferredInterrupt = fiber.deferredInterrupt := by
  cases frame with
  | onExit _ _ _ =>
    simp only [Prim.ensure]
    split <;> rfl
  | setInterruptible _ =>
    simp only [Prim.ensure]
    split
    · split <;> rfl
    · rfl
  | success _ => rfl
  | failure _ => rfl
  | sync _ => rfl
  | suspend _ => rfl
  | withFiber _ => rfl
  | yieldableError _ => rfl
  | iterator _ _ => rfl
  | onSuccess _ _ => rfl
  | onFailure _ _ => rfl
  | onSuccessAndFailure _ _ _ => rfl
  | exitFrame _ => rfl
  | whileLoop _ _ => rfl

/-- A pop never records an interruption: whatever hooks it runs, the
accumulated cause it leaves is the one it found.
census: checkpoint.getcont-deferred -/
theorem popFrom_interruptedCause (demand : Arm) (skip : Bool) :
    forall (frames : List (Prim ν σ β ε δ ι α)) (fiber : FrameFiber ν σ β ε δ ι α),
      (popFrom demand skip frames fiber).fiber.interruptedCause = fiber.interruptedCause := by
  intro frames
  induction frames with
  | nil => intro fiber; rfl
  | cons head rest ih =>
    intro fiber
    cases hanswer : head.answerOf demand (head.ensure fiber).snd with
    | none =>
      rw [popFrom_continue_fiber demand skip head rest fiber (Or.inl hanswer), ih,
        ensure_interruptedCause]
    | some answer =>
      cases hskip : (skip && (head.ensure fiber).fst.interrupted) with
      | true =>
        rw [popFrom_continue_fiber demand skip head rest fiber (Or.inr hskip), ih,
          ensure_interruptedCause]
      | false =>
        rw [popFrom_answer_fiber demand skip head rest fiber answer hanswer hskip]
        exact ensure_interruptedCause head fiber

/-- A pop never defers an interruption either: `getCont` detaches the stack
with the flag already cleared, and no hook sets it.
census: checkpoint.getcont-deferred -/
theorem popFrom_deferredInterrupt (demand : Arm) (skip : Bool) :
    forall (frames : List (Prim ν σ β ε δ ι α)) (fiber : FrameFiber ν σ β ε δ ι α),
      (popFrom demand skip frames fiber).fiber.deferredInterrupt = fiber.deferredInterrupt := by
  intro frames
  induction frames with
  | nil => intro fiber; rfl
  | cons head rest ih =>
    intro fiber
    cases hanswer : head.answerOf demand (head.ensure fiber).snd with
    | none =>
      rw [popFrom_continue_fiber demand skip head rest fiber (Or.inl hanswer), ih,
        ensure_deferredInterrupt]
    | some answer =>
      cases hskip : (skip && (head.ensure fiber).fst.interrupted) with
      | true =>
        rw [popFrom_continue_fiber demand skip head rest fiber (Or.inr hskip), ih,
          ensure_deferredInterrupt]
      | false =>
        rw [popFrom_answer_fiber demand skip head rest fiber answer hanswer hskip]
        exact ensure_deferredInterrupt head fiber

/-- With nothing recorded and nothing deferred, a pop leaves the fiber in the
same uninterrupted state. census: checkpoint.getcont-deferred -/
theorem getCont_fiber_uninterrupted (self : FrameFiber ν σ β ε δ ι α) (demand : Arm)
    (skip : Bool) (hcause : self.interruptedCause = none)
    (hdeferred : self.deferredInterrupt = false) :
    (self.getCont demand skip).fiber.interruptedCause = none /\
      (self.getCont demand skip).fiber.deferredInterrupt = false := by
  rw [getCont_eq_popFrom self demand skip hdeferred]
  exact ⟨(popFrom_interruptedCause demand skip _ _).trans hcause,
    popFrom_deferredInterrupt demand skip _ _⟩

/-- On the uninterrupted fragment the skip guard never fires: a frame that
declares the demanded arm answers, whatever the skip flag says. This is the
precise sense in which `FRAME-FB-NONNULL` is harmless here.
census: checkpoint.exit-failcause-skip -/
theorem popFrom_never_skips (demand : Arm) (skip : Bool) (frame : Prim ν σ β ε δ ι α)
    (rest : List (Prim ν σ β ε δ ι α)) (fiber : FrameFiber ν σ β ε δ ι α)
    (answer : ContAnswer ν σ β ε δ ι α) (hcause : fiber.interruptedCause = none)
    (hanswer : frame.answerOf demand (frame.ensure fiber).snd = some answer) :
    popFrom demand skip (frame :: rest) fiber =
      FramePop.mk answer [frame] (frame.passEvents (frame.ensure fiber).snd)
        { (frame.ensure fiber).fst with
          stack := (frame.ensure fiber).fst.stack ++ rest } := by
  have hint : (skip && (frame.ensure fiber).fst.interrupted) = false := by
    rw [interrupted_eq, ensure_interruptedCause, hcause]
    simp
  simp [popFrom, hanswer, hint]

private theorem answerOf_ne_deferred (frame : Prim ν σ β ε δ ι α) (demand : Arm)
    (replacement : Option (Prim ν σ β ε δ ι α)) (answer : ContAnswer ν σ β ε δ ι α)
    (cause : Cause ε δ ι α)
    (h : frame.answerOf demand replacement = some answer) :
    answer ≠ ContAnswer.deferred cause := by
  cases replacement with
  | some next =>
    rw [Prim.answerOf_replacement] at h
    cases Option.some.inj h
    exact by simp
  | none =>
    cases hd : frame.hasArm demand with
    | false =>
      rw [Prim.answerOf_missing frame demand hd] at h
      exact absurd h (by simp)
    | true =>
      rw [Prim.answerOf_arm frame demand hd] at h
      cases Option.some.inj h
      exact by simp

/-- Only `getCont`'s pre-stack branch can answer a deferred interrupt; the pop
loop itself never produces that answer. census: checkpoint.getcont-deferred -/
theorem popFrom_answer_ne_deferred (demand : Arm) (skip : Bool) (cause : Cause ε δ ι α) :
    forall (frames : List (Prim ν σ β ε δ ι α)) (fiber : FrameFiber ν σ β ε δ ι α),
      (popFrom demand skip frames fiber).answer ≠ ContAnswer.deferred cause := by
  intro frames
  induction frames with
  | nil => intro fiber; simp [popFrom]
  | cons head rest ih =>
    intro fiber
    cases hanswer : head.answerOf demand (head.ensure fiber).snd with
    | none =>
      rw [popFrom_continue_answer demand skip head rest fiber (Or.inl hanswer)]
      exact ih (head.ensure fiber).fst
    | some answer =>
      cases hskip : (skip && (head.ensure fiber).fst.interrupted) with
      | true =>
        rw [popFrom_continue_answer demand skip head rest fiber (Or.inr hskip)]
        exact ih (head.ensure fiber).fst
      | false =>
        rw [popFrom_answer_answer demand skip head rest fiber answer hanswer hskip]
        exact answerOf_ne_deferred head demand _ answer cause hanswer

/-- With nothing deferred, `getCont` never answers the deferred interrupt, so
`pendingCause` is never read on this fragment.
census: checkpoint.getcont-deferred -/
theorem getCont_never_defers (self : FrameFiber ν σ β ε δ ι α) (demand : Arm) (skip : Bool)
    (cause : Cause ε δ ι α) (hdeferred : self.deferredInterrupt = false) :
    (self.getCont demand skip).answer ≠ ContAnswer.deferred cause := by
  rw [getCont_eq_popFrom self demand skip hdeferred]
  exact popFrom_answer_ne_deferred demand skip cause _ _

private theorem resumeValue_uninterrupted [DecidableEq ε] [DecidableEq δ] [DecidableEq ι]
    [DecidableEq α] (interp : PrimInterp ν σ β ε δ ι α) (self next : FrameFiber ν σ β ε δ ι α)
    (value : β) (provided : Option (Exit β ε δ ι α))
    (hcause : self.interruptedCause = none) (hdeferred : self.deferredInterrupt = false)
    (h : (self.resumeValue interp value provided).fst = FrameStep.running next) :
    next.interruptedCause = none /\ next.deferredInterrupt = false := by
  obtain ⟨hc, hd⟩ := getCont_fiber_uninterrupted self Arm.contA false hcause hdeferred
  unfold resumeValue at h
  split at h
  · exact absurd h (by simp)
  · injection h with h'
    subst h'
    exact ⟨hc, hd⟩
  · injection h with h'
    subst h'
    exact ⟨hc, hd⟩
  · split at h
    · injection h with h'
      subst h'
      exact ⟨hc, hd⟩
    · exact absurd h (by simp)

private theorem resumeCause_uninterrupted [DecidableEq ε] [DecidableEq δ] [DecidableEq ι]
    [DecidableEq α] (interp : PrimInterp ν σ β ε δ ι α) (self next : FrameFiber ν σ β ε δ ι α)
    (cause : Cause ε δ ι α) (provided : Option (Exit β ε δ ι α))
    (hcause : self.interruptedCause = none) (hdeferred : self.deferredInterrupt = false)
    (h : (self.resumeCause interp cause provided).fst = FrameStep.running next) :
    next.interruptedCause = none /\ next.deferredInterrupt = false := by
  obtain ⟨hc, hd⟩ := getCont_fiber_uninterrupted self Arm.contE true hcause hdeferred
  unfold resumeCause at h
  split at h
  · exact absurd h (by simp)
  · injection h with h'
    subst h'
    exact ⟨hc, hd⟩
  · injection h with h'
    subst h'
    exact ⟨hc, hd⟩
  · split at h
    · injection h with h'
      subst h'
      exact ⟨hc, hd⟩
    · exact absurd h (by simp)

/-- The uninterrupted state is a `step` invariant. Nothing in this module
writes `interruptedCause`, and `getCont` clears the deferred flag, so a fiber
started by `FrameFiber.start` never reaches a state in which the interrupt half
of the machine does anything. census: checkpoint.getcont-deferred -/
theorem step_preserves_uninterrupted [DecidableEq ε] [DecidableEq δ] [DecidableEq ι]
    [DecidableEq α] (interp : PrimInterp ν σ β ε δ ι α) (self next : FrameFiber ν σ β ε δ ι α)
    (hcause : self.interruptedCause = none) (hdeferred : self.deferredInterrupt = false)
    (h : (self.step interp).fst = FrameStep.running next) :
    next.interruptedCause = none /\ next.deferredInterrupt = false := by
  unfold step at h
  split at h
  all_goals
    first
      | exact resumeValue_uninterrupted interp self next _ _ hcause hdeferred h
      | exact resumeCause_uninterrupted interp self next _ _ hcause hdeferred h
      | (injection h with h'; subst h'; exact ⟨hcause, hdeferred⟩)
      | (split at h <;> (injection h with h'; subst h'; exact ⟨hcause, hdeferred⟩))

/-- A bounded run started uninterrupted stays uninterrupted.
census: checkpoint.getcont-deferred -/
theorem run_preserves_uninterrupted [DecidableEq ε] [DecidableEq δ] [DecidableEq ι]
    [DecidableEq α] (interp : PrimInterp ν σ β ε δ ι α) (fuel : Nat) :
    forall (self next : FrameFiber ν σ β ε δ ι α),
      self.interruptedCause = none -> self.deferredInterrupt = false ->
        (self.run interp fuel).fst = FrameStep.running next ->
          next.interruptedCause = none /\ next.deferredInterrupt = false := by
  induction fuel with
  | zero =>
    intro self next hcause hdeferred h
    rw [run_zero] at h
    injection h with h'
    subst h'
    exact ⟨hcause, hdeferred⟩
  | succ fuel ih =>
    intro self next hcause hdeferred h
    cases hstep : self.step interp with
    | mk result events =>
      cases result with
      | finished exit =>
        rw [run_succ_finished interp self fuel exit events hstep] at h
        exact absurd h (by simp)
      | running mid =>
        have hmid : mid.interruptedCause = none /\ mid.deferredInterrupt = false :=
          step_preserves_uninterrupted interp self mid hcause hdeferred (by rw [hstep])
        rw [run_succ_running interp self mid fuel events hstep] at h
        exact ih mid next hmid.1 hmid.2 h

/-- Fuel splits: running `m + n` units is running `m` and, if that has not
finished, resuming the rest. The module had `run_zero`, `run_succ_finished` and
`run_succ_running` and no way to compose two runs.
census: exit.success-failure -/
theorem run_add [DecidableEq ε] [DecidableEq δ] [DecidableEq ι] [DecidableEq α]
    (interp : PrimInterp ν σ β ε δ ι α) (m n : Nat) :
    forall (self : FrameFiber ν σ β ε δ ι α),
      self.run interp (m + n) =
        (match self.run interp m with
          | (FrameStep.finished exit, events) => (FrameStep.finished exit, events)
          | (FrameStep.running mid, events) =>
            ((mid.run interp n).fst, events ++ (mid.run interp n).snd)) := by
  induction m with
  | zero =>
    intro self
    rw [Nat.zero_add, run_zero]
    simp
  | succ m ih =>
    intro self
    have harith : m + 1 + n = (m + n) + 1 := by omega
    cases hstep : self.step interp with
    | mk result events =>
      cases result with
      | finished exit =>
        rw [harith, run_succ_finished interp self (m + n) exit events hstep,
          run_succ_finished interp self m exit events hstep]
      | running mid =>
        rw [harith, run_succ_running interp self mid (m + n) events hstep,
          run_succ_running interp self mid m events hstep, ih mid]
        cases hrun : mid.run interp m with
        | mk innerResult innerEvents =>
          cases innerResult with
          | finished exit => simp
          | running deep => simp [List.append_assoc]

/-- A finished run is stable: extra fuel changes neither the exit nor the
trace. census: exit.success-failure -/
theorem run_add_finished [DecidableEq ε] [DecidableEq δ] [DecidableEq ι] [DecidableEq α]
    (interp : PrimInterp ν σ β ε δ ι α) (self : FrameFiber ν σ β ε δ ι α) (m n : Nat)
    (exit : Exit β ε δ ι α) (events : List (FrameEvent ν σ β ε δ ι α))
    (h : self.run interp m = (FrameStep.finished exit, events)) :
    self.run interp (m + n) = (FrameStep.finished exit, events) := by
  rw [run_add interp m n self, h]

/-- An unfinished run resumes from the state it stopped in.
census: exit.success-failure -/
theorem run_add_running [DecidableEq ε] [DecidableEq δ] [DecidableEq ι] [DecidableEq α]
    (interp : PrimInterp ν σ β ε δ ι α) (self mid : FrameFiber ν σ β ε δ ι α) (m n : Nat)
    (events : List (FrameEvent ν σ β ε δ ι α))
    (h : self.run interp m = (FrameStep.running mid, events)) :
    self.run interp (m + n) = ((mid.run interp n).fst, events ++ (mid.run interp n).snd) := by
  rw [run_add interp m n self, h]

/-- Fuel monotonicity for a finished run. `FrameStep.running` at exhausted fuel
stays a live frontier under DB-04; this says nothing about it.
census: exit.success-failure -/
theorem run_mono [DecidableEq ε] [DecidableEq δ] [DecidableEq ι] [DecidableEq α]
    (interp : PrimInterp ν σ β ε δ ι α) (self : FrameFiber ν σ β ε δ ι α) (m n : Nat)
    (exit : Exit β ε δ ι α) (events : List (FrameEvent ν σ β ε δ ι α)) (hle : m <= n)
    (h : self.run interp m = (FrameStep.finished exit, events)) :
    self.run interp n = (FrameStep.finished exit, events) := by
  obtain ⟨k, hk⟩ := Nat.le.dest hle
  rw [← hk]
  exact run_add_finished interp self m k exit events h

end FrameFiber
end Effect4
