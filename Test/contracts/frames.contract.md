# Frame-machine runtime first-order contract

Status: FROZEN / RED, breaker-authored 2026-09-02

Implementation fence:
`src/Effect4/Machine/Frames.lean`

Lean battery:
`Test/Machine/Runtime/FramesContract.lean`

Axiom report:
`Test/Machine/Runtime/FramesAxiomReport.lean`

Counterexamples: `E4-RUN-CE-010` through `E4-RUN-CE-021` in
`Test/Counterexamples/REGISTER.md`; witnesses in
`Test/Counterexamples/Machine/Runtime/Frames.lean`; attack shapes in
`git:c407ab7:test/counterexamples/runtime/ATTACKS.md`

Proof graph: `FRAME-PG-STACK` in `docs/research/FRAMES-DAG.md`

Pinned source: `effect@4.0.0-rc.112` under `vendor/effect-4.0.0-rc.112/src/`.
Reading: `docs/effect-rc112-fiber-runtime.html` sections 1-4.

## Claim boundary

This packet freezes one bounded model: Effect v4's continuation-stack machine as
first-order data over two externally admitted alphabets — the continuation name
`ν` and the thunk name `σ` — together with an externally supplied interpretation
record `PrimInterp`, and the already-canonical `Effect4.Exit` and `Effect4.Cause`
carriers, which it reuses unchanged.

It does not implement the model. It does not model the run loop, the op budget,
parking, `Yield`, `Async`, `AsyncFinalizer`, the dispatcher, the scheduler,
observers, children, the fiber `Context`, the stack-frame cause annotation, or
any fiber other than the one whose stack it is. It makes no Effect TypeScript
compatibility claim and no code-generation claim.

It does **not** claim that `Effect4.Prim` is equivalent to rc.112's `Primitive`
or that `Effect4.FrameFiber` is equivalent to `FiberImpl`. It claims that each
named clause of each named census row in the per-row table of
`docs/research/FRAMES-DAG.md` has an exact theorem over the Effect4 model, and it names,
in six `FRAME-FB-*` rows of that document, exactly what was dropped or deferred:
the raw fiber handover, the host `Error` class identity, the finalizer's own
frame activity, the stack-frame cause annotation, the `AsyncFinalizer` pop
shape, and the `InterruptMask` carrier correspondence. Three of the thirty-one
assigned census rows are declared **partial**; see the per-row table.

## CATEGORIES

- `inductive-data` — primitives, frames, answers, events and fiber states are
  first-order data parameterized by externally owned alphabets;
- `total-functions` — every operation is a total, kernel-reducible function of
  its arguments and of one supplied record of total functions; there is no
  relation and no decision source, and therefore no determinism theorem to
  state;
- `interpreter` — `step` is a one-step interpreter over first-order syntax,
  which is why the assurance route is a graph and not a leaf;
- `protocol-state` — the interruptible flag, the deferred flag and the stack
  discipline are protocol invariants;
- `algebraic-laws` — the frame-arm matrix, the ensure hook, the answer
  selection, the pop, the skip, the arms and the two brackets;
- `counterexamples` — twelve registered attacks with twenty-three finite proved
  witnesses force the representation;
- `claim-scope` — the pinned host boundary is named, not silently modelled, and
  three rows are declared partial rather than green.

## REQUIRES

1. Lean core and Std at the repository's pinned toolchain. No Mathlib.
2. `src/Effect4/Machine/Frames.lean` imports `Effect4.Semantics.Exit` and nothing
   else from Effect4. It must not import `Effect4/Concurrency/` — including
   `src/Effect4/Machine/Supervision.lean` and, emphatically,
   `src/Effect4/Machine/Fibers.lean` — nor `Effect4/Layer/`,
   `Effect4/Channel/`, `Effect4/Context/`, or `src/Effect4/Machine/Scope.lean`.
   `docs/ARCHITECTURE.md` "Dependency direction" and `docs/research/FRAMES-DAG.md`
   separations 1-3 own the reasons.
3. `ν`, `σ`, and the four cause alphabets `ε`, `δ`, `ι`, `α`, plus the value
   alphabet `β`, are opaque parameters. No constructor, decidable equality,
   order or default value of any of them is assumed beyond the instance binders
   written in the frozen signatures. `[DecidableEq ε] [DecidableEq δ]
   [DecidableEq ι] [DecidableEq α]` appear exactly on the operations that reach
   `Effect4.Cause.combine` through `Effect4.Exit.restoreAfterFinalizer`:
   `Prim.armA`, `Prim.armE`, `FrameFiber.resumeValue`, `FrameFiber.resumeCause`,
   `FrameFiber.step` and `FrameFiber.run`. They appear nowhere else.
4. `Effect4.Exit`, `Effect4.Cause`, `Effect4.Reason` and
   `Effect4.ReasonAnnotations` are consumed exactly as
   `Test/contracts/cause-exit.contract.md` froze them. This packet declares no
   new exit or cause carrier, adds no arm to either, and claims exactly one
   adapter, `Prim.ofExit`/`Prim.asExit?`.
5. `DecidableEq` is derived, never classical. `Classical.choice`,
   `native_decide`, `sorry`, `admit`, `partial`, `unsafe` and new axioms are not
   allowed in the packet or the implementation. The axiom ceiling for every
   public theorem is `propext` and `Quot.sound`.
6. Universe policy: `ν`, `σ`, `ε`, `δ`, `ι`, `α` live in one explicit `Type u`;
   the value alphabet `β` lives in `Type v`, and every carrier lands in
   `Type (max u v)`. This is exactly the shape `src/Effect4/Machine/Exit.lean`
   already uses for `Exit (β : Type v) (ε δ ι α : Type u)`, and the two universes
   are inherited from it rather than chosen here.
7. Every recursive definition is structurally recursive. `FrameFiber.popFrom`
   recurses on the frame list, `FrameFiber.run` on its fuel; neither needs a
   termination argument, and `decreasing_by` must not appear.
8. Auxiliary lemmas beyond the list below are permitted but must be `private`,
   so the generated declaration snapshot has no unannotated public export.

## Public declarations

Binder names may differ. Public names, constructor order and fields, argument
roles, result types and theorem propositions are frozen by the Lean battery's
`#check (@name : proposition)` ascriptions. **The battery is the authority**; the
Lean shown here is a reading aid. Every theorem in the battery also carries a
`census:` tag naming the census rows it witnesses; the builder carries that tag
into the declaration's docstring, as
`docs/RUNTIME-COVERAGE.md` and `AGENTS.md` require.

### Existing-type and duplicate-prevention rows

The twelve rows — nine native, two reuse, one named-not-imported — with their
owners, relationships, pins and assurance routes are in `docs/research/FRAMES-DAG.md`
"Existing-type rows", together with the per-declaration records for every
definition. They are not restated here.

### D0 — the three continuation slots

```lean
inductive Arm
  | contA
  | contE
  | contAll
deriving DecidableEq, Repr

Arm.all        : List Arm
Arm.demandable : List Arm
```

rc.112's `[contA]`, `[contE]` and `[contAll]` slots. `getCont` is typed
`getCont<S extends contA | contE>`, so only two of the three can ever be
demanded; `Arm.demandable` is that restriction as first-order data and
`Arm.contAll_not_demandable` is its receipt.

### D1 — the primitive syntax

```lean
inductive Prim (ν σ : Type u) (β : Type v) (ε δ ι α : Type u) : Type (max u v)
  | success (value : β)
  | failure (cause : Cause ε δ ι α)
  | sync (thunk : σ)
  | suspend (thunk : σ)
  | withFiber (thunk : σ)
  | yieldableError (error : ε)
  | iterator (generator : ν) (cursor : β)
  | onSuccess (body : Prim …) (onValue : ν)
  | onFailure (body : Prim …) (onCause : ν)
  | onSuccessAndFailure (body : Prim …) (onValue : ν) (onCause : ν)
  | exitFrame (body : Prim …)
  | onExit (body : Prim …) (finalizer : ν) (finalizerInterruptible : Bool)
  | setInterruptible (flag : Bool)
  | whileLoop (loop : ν) (cursor : β)
deriving DecidableEq
```

One constructor per pinned op in this packet's scope. Three deliberate absences:
`Yield`, `Async` and `AsyncFinalizer` belong to the later run-loop and parking
packet, and adding them is an additive change to this inductive that that packet
must make consciously — together with the `popFrom` obligation recorded as
`FRAME-FB-ASYNC-FINALIZER`.

`success` and `failure` are the two rc.112 `Exit` ops; they *are* primitives, and
`Prim.ofExit` / `Prim.asExit?` are the embedding and its partial inverse that
close `exit.success-failure`'s open clause.

A continuation slot stores a nominal `ν`. A nested body stores a `Prim` subterm,
because rc.112's `onSuccess[args]` holds the inner *effect* and a subterm is
first-order, inspectable and decidable where a closure is none of those.
`docs/research/FRAMES-DAG.md` separation 5 owns that distinction.

`exitFrame` carries rc.112's op name `Exit`; the Lean spelling avoids colliding
with `Effect4.Exit`. `whileLoop` carries rc.112's constructor name.

### D2 — the generator outcome and the supplied interpretation

```lean
inductive IterStep (ν σ : Type u) (β : Type v) (ε δ ι α : Type u)
  | done (value : β)
  | halt (cause : Cause ε δ ι α)
  | resume (next : Prim …)
deriving DecidableEq

structure PrimInterp (ν σ : Type u) (β : Type v) (ε δ ι α : Type u) where
  contA         : ν -> β -> Prim …
  contE         : ν -> Cause ε δ ι α -> Prim …
  syncValue     : σ -> β
  suspendBody   : σ -> Prim …
  finalizerExit : ν -> Exit β ε δ ι α -> Exit Unit ε δ ι α
  reifyExit     : Exit β ε δ ι α -> β
  iterNext      : ν -> β -> List β × IterStep …
  loopTest      : ν -> β -> Bool
  loopBody      : ν -> β -> Prim …
  loopStep      : ν -> β -> β
  loopDone      : ν -> β
  notImplemented : δ
```

`PrimInterp` is a **parameter**, never canonical program content. It carries no
`DecidableEq` and never enters `Prim` or `FrameFiber`, which is what keeps both
first-order. `docs/research/FRAMES-DAG.md` "Scope" justifies the record over stored
closures, a relation, and loose function arguments, and justifies `iterNext`'s
`List β` prefix and the `notImplemented` defect individually.

`finalizerExit` returns an `Exit Unit`, matching rc.112's
`(exit) => Effect<void>`. rc.112 also allows `undefined` — no finalizer effect at
all — which is `Exit.void` here, sound because
`Effect4.Exit.restoreAfterFinalizer_success_finalizer` already proves a
successful finalizer leaves the exit unchanged.

`reifyExit` is how an `Exit` becomes a value of the one value alphabet, which is
what rc.112's `succeed(exit)` does for free because its values are `unknown`.

### D3 — the fiber state, the pop result, and the trace

```lean
structure FrameFiber (ν σ : Type u) (β : Type v) (ε δ ι α : Type u) where
  current : Prim …
  stack : List (Prim …)
  interruptible : Bool
  interruptedCause : Option (Cause ε δ ι α)
  deferredInterrupt : Bool
deriving DecidableEq

inductive ContAnswer …
  | deferred (cause : Cause ε δ ι α)
  | replacement (next : Prim …)
  | frame (frame : Prim …)
  | empty
deriving DecidableEq

inductive FrameEvent …
  | popped (frame : Prim …)
  | ranContAll (frame : Prim …)
  | pushed (frame : Prim …)
  | ranFinalizer (finalizer : ν) (exit : Exit β ε δ ι α)
  | substituted (cause : Cause ε δ ι α)
  | deferred (cause : Cause ε δ ι α)
  | yielded (exit : Exit β ε δ ι α)
deriving DecidableEq

structure FramePop … where
  answer : ContAnswer …
  popped : List (Prim …)
  events : List (FrameEvent …)
  fiber : FrameFiber …
deriving DecidableEq

inductive FrameStep …
  | running (fiber : FrameFiber …)
  | finished (exit : Exit β ε δ ι α)
deriving DecidableEq

FrameFiber.start        : Prim … -> FrameFiber …
FrameFiber.pendingCause : FrameFiber … -> Cause ε δ ι α
FrameFiber.masked       : FrameFiber … -> Bool
FrameFiber.interrupted  : FrameFiber … -> Bool

FrameEvent.poppedFrame?  : FrameEvent … -> Option (Prim …)
FrameEvent.finalizer?    : FrameEvent … -> Option ν
FrameEvent.poppedFrames  : List (FrameEvent …) -> List (Prim …)
FrameEvent.finalizersRun : List (FrameEvent …) -> List ν
```

The five fields are exactly the five rc.112 `FiberImpl` fields this packet
models: `interruptible`, `_stack`, `_interruptedCause`, `_deferredInterrupt`, and
the current primitive the run loop threads. `_running`, `_yielded`, `_observers`,
`_children`, `_exit`, `currentOpCount`, `_dispatcher` and the `Context` cache are
absent by construction, not by omission: no theorem here mentions them, and the
later run-loop, supervision and context packets own them.

`FrameEvent.poppedFrames` and `FrameEvent.finalizersRun` are the two trace
projections the packet promises: what frames were popped and which finalizers
ran. They are what makes order statable across a bounded `run`.

`pendingCause` is total and answers `Cause.empty` where rc.112 asserts
`_interruptedCause!`; `FRAME-FB-NONNULL` records that reading. `masked` is the
shared mask word; `FRAME-FB-MASK-CARRIER` records that the correspondence to
`Effect4.InterruptMask` is a later bridge, because the dependency direction
forbids importing it.

### D4 — the frame-arm matrix

```lean
Prim.arms    : Prim … -> List Arm
Prim.hasArm  : Prim … -> Arm -> Bool
Prim.isFrame : Prim … -> Bool
```

Frozen exactly as `docs/effect-rc112-fiber-runtime.html` section 3 states it:

| Frame | `contA` | `contE` | `contAll` |
| --- | --- | --- | --- |
| `onSuccess` | yes | — | — |
| `onFailure` | — | yes | — |
| `onSuccessAndFailure` | yes | yes | — |
| `exitFrame` | yes | yes | — |
| `whileLoop` | yes | — | — |
| `iterator` | yes | — | — |
| `onExit` | yes | yes | yes |
| `setInterruptible` | — | — | yes |

`success`, `failure`, `sync`, `suspend`, `withFiber` and `yieldableError` declare
no arm and are never pushed. `Prim.isFrame` is exactly "declares at least one
arm", which is the first half of `rule.frames-are-primitives`.

### D5 — the ensure hook and the answer selection

```lean
Prim.ensure    : Prim … -> FrameFiber … -> FrameFiber … × Option (Prim …)
Prim.answerOf  : Prim … -> Arm -> Option (Prim …) -> Option (ContAnswer …)
Prim.passEvents : Prim … -> Option (Prim …) -> List (FrameEvent …)
```

`ensure` is `[contAll](fiber)`:

```lean
Prim.ensure (onExit _ _ finalizerInterruptible) fiber =
  if fiber.interruptible = true && finalizerInterruptible = false then
    ({ fiber with interruptible := false,
        stack := setInterruptible true :: fiber.stack }, none)
  else (fiber, none)

Prim.ensure (setInterruptible flag) fiber =
  match fiber.interruptedCause with
  | some cause =>
    if flag = true then ({ fiber with interruptible := true }, some (failure cause))
    else ({ fiber with interruptible := flag }, none)
  | none => ({ fiber with interruptible := flag }, none)

Prim.ensure _ fiber = (fiber, none)
```

`answerOf` is the decision rc.112 makes after `contAll` returns:

```lean
Prim.answerOf frame demand replacement =
  match replacement with
  | some next => some (ContAnswer.replacement next)
  | none => if frame.hasArm demand = true then some (ContAnswer.frame frame) else none
```

A replacement wins for **either** arm — that is `frame-arm.SetInterruptible`'s
"can return a replacement continuation used for either arm" — and a frame lacking
the demanded arm is skipped. `answerOf` is public and not inlined so that "a
frame is selected by which arms it defines" is a statement rather than a comment.

### D6 — the arms

```lean
Prim.armA : [DecidableEq ε δ ι α] -> PrimInterp … -> Prim … -> β ->
  Option (Exit β ε δ ι α) -> Option (Prim … × List (Prim …))
Prim.armE : [DecidableEq ε δ ι α] -> PrimInterp … -> Prim … -> Cause ε δ ι α ->
  Option (Exit β ε δ ι α) -> Option (Prim … × List (Prim …))
Prim.finalizerEvents : Prim … -> Exit β ε δ ι α -> List (FrameEvent …)
Prim.iteratorFolded  : PrimInterp … -> Prim … -> β -> List β
```

`none` exactly when the frame does not declare the arm — `armA_isSome` and
`armE_isSome` tie the behaviour to the matrix. The `List (Prim …)` is what the
arm itself pushes: `whileLoop` and `iterator` push themselves, every other arm
pushes nothing. The `Option (Exit …)` is rc.112's third continuation argument,
supplied by `Success` and `Failure` and withheld by `Sync`.

The two arms an implementer is most likely to get wrong:

```lean
Prim.armA (exitFrame _) value provided =
  some (success (interp.reifyExit (provided.getD (Exit.success value))), [])

Prim.armA (onExit _ finalizer _) value provided =
  let closing := provided.getD (Exit.success value)
  some (ofExit (Exit.restoreAfterFinalizer closing
    (interp.finalizerExit finalizer closing)), [])
```

and the same two on `armE` with `Exit.failure cause` as the default. Both `OnExit`
arms go through `Effect4.Exit.restoreAfterFinalizer`, which is already owned and
already proved, and which is exactly rc.112's pair: `flatMap(eff, _ => exit)` on
the success arm and `flatMap(combineFinalizerCause(exit, eff), _ => exit)` on the
failure arm. `onExit_finalizer_success_restores`,
`onExit_finalizer_failure_merges` and `onExit_success_finalizer_failure` are the
three consequences, and `E4-RUN-CE-015` and `E4-RUN-CE-016` are the attacks.

`iteratorFolded` exposes the inline run, and `iterator_folds_inline` states that
the arm does not depend on it: that is what "folded inline" means, and
`E4-RUN-CE-018` is the attack.

### D7 — the pop

```lean
FrameFiber.popFrom : Arm -> Bool -> List (Prim …) -> FrameFiber … -> FramePop …
FrameFiber.getCont : FrameFiber … -> Arm -> Bool -> FramePop …
```

`getCont` answers a deferred interrupt before touching the stack, then runs the
loop with the stack detached so that whatever `contAll` pushes lands on top of
the frames that are left:

```lean
FrameFiber.getCont self demand skipInterrupted =
  if self.deferredInterrupt = true && skipInterrupted = false then
    { answer := .deferred self.pendingCause, popped := [],
      events := [FrameEvent.deferred self.pendingCause],
      fiber := { self with deferredInterrupt := false } }
  else
    popFrom demand skipInterrupted self.stack
      { self with stack := [], deferredInterrupt := false }

FrameFiber.popFrom demand skip [] fiber =
  { answer := .empty, popped := [], events := [], fiber := fiber }

FrameFiber.popFrom demand skip (frame :: rest) fiber =
  let after := frame.ensure fiber
  let passed := frame.passEvents after.snd
  match frame.answerOf demand after.snd with
  | some answer =>
    if skip = true && after.fst.interrupted = true then
      -- keep popping: the handler is skipped
      … popFrom demand skip rest after.fst …
    else
      { answer := answer, popped := [frame], events := passed,
        fiber := { after.fst with stack := after.fst.stack ++ rest } }
  | none => … popFrom demand skip rest after.fst …
```

`skipInterrupted` is `true` on the failure path only. The loop is rc.112's two
nested loops fused into one structural recursion; `docs/research/FRAMES-DAG.md` "Where the
fusion could diverge" owns the justification, the deferred-interrupt equivalence,
and the one frame shape — `AsyncFinalizer` — that the next packet must re-derive.

### D8 — resuming, stepping, running

```lean
FrameFiber.resumeValue : [DecidableEq ε δ ι α] -> PrimInterp … -> FrameFiber … ->
  β -> Option (Exit β ε δ ι α) -> FrameStep … × List (FrameEvent …)
FrameFiber.resumeCause : [DecidableEq ε δ ι α] -> PrimInterp … -> FrameFiber … ->
  Cause ε δ ι α -> Option (Exit β ε δ ι α) -> FrameStep … × List (FrameEvent …)
FrameFiber.step : [DecidableEq ε δ ι α] -> PrimInterp … -> FrameFiber … ->
  FrameStep … × List (FrameEvent …)
FrameFiber.run : [DecidableEq ε δ ι α] -> PrimInterp … -> Nat -> FrameFiber … ->
  FrameStep … × List (FrameEvent …)
```

`resumeValue` demands `contA` with `skipInterrupted := false`; `resumeCause`
demands `contE` with `skipInterrupted := true`. That asymmetry is
`rule.interrupt-bypasses-handlers` in one line: only the failure path skips.

The fourteen `step` equations are one per constructor.
`Success` supplies itself as the pop's exit argument, `Sync` supplies nothing,
`Failure` supplies itself. The five pushing frames push themselves and continue
with their body. `setInterruptible` as a *current* primitive is a defect, because
rc.112 gives it no `evaluate` and `defaultEvaluate` returns
`exitDie("Effect.evaluate: Not implemented")`.

`run` is a bounded runner. `FrameStep.running` at exhausted fuel is a live
frontier under DB-04: never a failure, never a defect, never a refusal. It exists
so that "which frames were popped and which finalizers ran" is statable across
more than one step, and for no other reason.

### D9 — masks and the stack side of the two brackets

```lean
FrameFiber.uninterruptible       : FrameFiber … -> FrameFiber …
FrameFiber.setFiberInterruptible : FrameFiber … -> FrameFiber … × Option (Prim …)
FrameFiber.interruptibleRegion   : FrameFiber … -> FrameFiber … × Option (Prim …)
FrameFiber.uninterruptibleMask   : FrameFiber … -> FrameFiber …
FrameFiber.restoreAcquire        : FrameFiber … -> Bool -> FrameFiber … × Option (Prim …)
Prim.scopedFrame                 : Prim … -> ν -> Prim …
```

`interruptibleRegion` carries rc.112's `interruptible` combinator; the rename is
forced because `FrameFiber.interruptible` is already the field.
`restoreAcquire` is the `restore` an `uninterruptibleMask` hands to its body,
applied only when `acquireRelease` was asked for an interruptible acquire —
`options?.interruptible ? restore(acquire) : acquire`.

`Prim.scopedFrame body closeScope = Prim.onExit body closeScope false` is rc.112's
`scoped`, stack side only: the body under one `OnExit` frame whose finalizer name
stands for `exit => { restore context; scopeCloseUnsafe(scope, exit) }`, masked
because `onExitPrimitive` is called with no third argument. The *scope* side of
the same census row is `Effect4.Scope.runScoped`, owned by
`Test/contracts/scope.contract.md`; this packet does not import it, does not
duplicate it, and claims no relation between the two.

## ENSURES — public theorem spine

Every proposition is frozen in the Lean battery by exact ascription. A weaker
statement does not satisfy this contract. One hundred and forty-nine theorems, in
battery order. The battery groups them F0 through F9 and tags each with its
census rows.

### F0 — the slot alphabet (census: rule.frames-are-primitives)

```lean
Arm.all_nodup, Arm.mem_all, Arm.cases_receipt
Arm.demandable_eq          : Arm.demandable = [Arm.contA, Arm.contE]
Arm.contAll_not_demandable : Arm.contAll ∉ Arm.demandable
```

### F1 — the syntax (census: op.Success .. op.While)

`Prim.cases_receipt` is the fourteen-way exhaustive receipt. There is no
fifteenth op in this packet, and `Yield`, `Async` and `AsyncFinalizer` are
deliberately not among the fourteen.

### F2 — the fiber state (census: rule.frames-are-primitives)

```lean
FrameFiber.start_eq  : start current =
  { current := current, stack := [], interruptible := true,
    interruptedCause := none, deferredInterrupt := false }
FrameFiber.pendingCause_some / pendingCause_none
FrameFiber.masked_eq      : self.masked = !self.interruptible
FrameFiber.interrupted_eq : self.interrupted =
  (self.interruptible && self.interruptedCause.isSome)
```

`start` is `new FiberImpl(context, interruptible = true)` restricted to the five
modelled fields. `interrupted` is the exact skip condition of
`internal/core.ts:540`.

### F3 — the frame-arm matrix (census: frame-arm.*)

```lean
Prim.hasArm_eq, Prim.isFrame_eq, Prim.isFrame_iff
Prim.arms_onSuccess = [Arm.contA]
Prim.arms_onFailure = [Arm.contE]
Prim.arms_onSuccessAndFailure = [Arm.contA, Arm.contE]
Prim.arms_exitFrame = [Arm.contA, Arm.contE]
Prim.arms_onExit = [Arm.contA, Arm.contE, Arm.contAll]
Prim.arms_setInterruptible = [Arm.contAll]
Prim.arms_whileLoop = [Arm.contA]
Prim.arms_iterator = [Arm.contA]
Prim.non_frames_have_no_arms   -- all six at once
```

The order of the arm lists is frozen: `[contA, contE, contAll]`, the order the
reference page's table uses. An implementation that returns the same set in a
different order fails the ascription.

### F3b — an Exit is a steppable primitive (census: exit.success-failure)

```lean
Prim.ofExit_asExit? : (ofExit exit).asExit? = some exit
Prim.asExit?_success, Prim.asExit?_failure
Prim.asExit?_eq_some : self.asExit? = some exit -> self = ofExit exit
Prim.ofExit_isFrame  : (ofExit exit).isFrame = false
```

An `Exit` is a primitive and is never a frame: `makeExit` gives it an `evaluate`
and no continuation slot.

### F4 — the ensure hook (census: frame-arm.OnExit, frame-arm.SetInterruptible,
op.SetInterruptible, checkpoint.set-interruptible-contall)

```lean
Prim.ensure_of_no_contAll : frame.hasArm Arm.contAll = false ->
  frame.ensure fiber = (fiber, none)
Prim.ensure_onExit_masks : fiber.interruptible = true ->
  (onExit body finalizer false).ensure fiber =
    ({ fiber with interruptible := false,
        stack := setInterruptible true :: fiber.stack }, none)
Prim.ensure_onExit_told_not_to     : (onExit body finalizer true).ensure fiber = (fiber, none)
Prim.ensure_onExit_already_masked  : fiber.interruptible = false -> … = (fiber, none)
Prim.ensure_onExit_no_replacement  : ((onExit …).ensure fiber).snd = none
Prim.ensure_setInterruptible_flag / _stack
Prim.ensure_setInterruptible_substitutes : fiber.interruptedCause = some cause ->
  (setInterruptible true).ensure fiber =
    ({ fiber with interruptible := true }, some (failure cause))
Prim.ensure_setInterruptible_false_no_replacement
Prim.ensure_setInterruptible_no_pending
Prim.answerOf_replacement, answerOf_arm, answerOf_missing, answerOf_frame_eq
```

`ensure_onExit_no_replacement` is the half a builder forgets: `OnExit`'s
`contAll` pushes and flips but never *returns* a continuation, so it never
short-circuits the arm selection. `ensure_setInterruptible_false_no_replacement`
is the other half: only `SetInterruptible(true)` can substitute, because only it
can leave the fiber interruptible.

### F5 — the arms (census: op.OnSuccess .. op.While)

```lean
Prim.armA_isSome : (frame.armA interp value provided).isSome = frame.hasArm Arm.contA
Prim.armE_isSome : (frame.armE interp cause provided).isSome = frame.hasArm Arm.contE
```

These two are the load-bearing pair: they make the matrix a statement about
behaviour and not a lookup table beside it. The per-frame equations follow, then
the four `Exit`-frame arms, the two `OnExit` arms and their three restore laws,
the three per-instance laws, the two `While` arms, the three `Iterator` arms, and
the inline-fold independence law.

```lean
Prim.onSuccess_arm_is_per_instance :
  interp.contA left value ≠ interp.contA right value ->
    (onSuccess body left).armA interp value provided ≠
      (onSuccess body right).armA interp value provided
```

with the same shape for `onFailure`, and a conjunction for
`onSuccessAndFailure`. These are `op.OnSuccess`'s "assigned per instance by
`flatMap`, not by the prototype" made falsifiable: `E4-RUN-CE-017` is the attack.

```lean
Prim.onExit_arm_is_per_frame :
  (onExit body finalizer flag).armA interp value provided =
    (onExit other finalizer otherFlag).armA interp value provided
```

is the complementary statement for `OnExit`: the arm depends on the stored
finalizer name and on nothing else about the frame — not the body, not the
interruptible flag, which only `contAll` reads.

```lean
Prim.iterator_folds_inline :
  (left.iterNext generator value).snd = (right.iterNext generator value).snd ->
    (iterator generator cursor).armA left value provided =
      (iterator generator cursor).armA right value provided
```

Two interpretations that agree on what stopped the generator agree on the arm,
however much they disagree on the inline run. That is "folded inline": the folded
values never reach the stack and never become a current primitive, so no
`getCont` checkpoint sits between them.

### F6 — the pop (census: checkpoint.getcont-deferred,
checkpoint.exit-failcause-skip, rule.frames-are-primitives,
rule.interrupt-bypasses-handlers)

```lean
FrameFiber.getCont_deferred : self.deferredInterrupt = true ->
  self.getCont demand false =
    { answer := .deferred self.pendingCause, popped := [],
      events := [FrameEvent.deferred self.pendingCause],
      fiber := { self with deferredInterrupt := false } }
FrameFiber.getCont_deferred_pops_nothing
FrameFiber.getCont_eq_popFrom, getCont_skip_clears_deferred, getCont_empty_stack
FrameFiber.popFrom_nil
FrameFiber.popFrom_answer_answer / _popped / _events / _fiber
FrameFiber.popFrom_continue_answer / _popped / _events / _fiber
FrameFiber.popFrom_answer_hasArm, getCont_answer_hasArm
FrameFiber.passEvents_ranContAll, passEvents_poppedFrames
FrameFiber.popFrom_popped_eq_events
FrameFiber.popFrom_ranContAll, getCont_ranContAll
FrameFiber.getCont_skip_of_no_pending_cause
FrameFiber.interrupt_skips_every_handler
FrameFiber.getCont_mask_stops_skip
```

**`contAll` runs on every frame passed.**

```lean
FrameFiber.popFrom_ranContAll :
  frame.hasArm Arm.contAll = true ->
    frame ∈ (popFrom demand skip frames fiber).popped ->
      FrameEvent.ranContAll frame ∈ (popFrom demand skip frames fiber).events
```

is the second half of `rule.frames-are-primitives`, and `E4-RUN-CE-010` is the
attack: a pop that runs the hook only on the answering frame never clears the
interruptible flag on the way past a mask frame.

**The skip.**

```lean
FrameFiber.interrupt_skips_every_handler :
  self.interruptible = true -> self.interruptedCause = some cause ->
    (forall frame, frame ∈ self.stack -> frame.hasArm Arm.contAll = false) ->
      (self.getCont demand true).answer = ContAnswer.empty
```

is the general form of "every user error handler is skipped": with no frame able
to flip the flag, the stack simply empties.

```lean
FrameFiber.getCont_mask_stops_skip :
  self.deferredInterrupt = false ->
    self.stack = Prim.setInterruptible false :: rest ->
      (self.getCont Arm.contE skip).answer =
        ({ self with interruptible := false, stack := rest,
            deferredInterrupt := false }.getCont Arm.contE skip).answer
```

is the "until a mask frame flips the flag" half. The two together are
`rule.interrupt-bypasses-handlers`, and `E4-RUN-CE-011` and `E4-RUN-CE-012` are
the attacks. `getCont_skip_of_no_pending_cause` is the third leg: with no
interruption recorded, the skip flag changes nothing at all.

### F7 — resuming and stepping (census: op.Success .. op.While,
exit.success-failure)

```lean
FrameFiber.resumeValue_empty / _deferred / _replacement / _frame
FrameFiber.resumeCause_empty / _deferred / _replacement / _frame
FrameFiber.step_success   : { self with current := success value }.step interp =
  { self with current := success value }.resumeValue interp value (some (Exit.success value))
FrameFiber.step_failure   : … .resumeCause interp cause (some (Exit.failure cause))
FrameFiber.step_sync      : … .resumeValue interp (interp.syncValue thunk) none
FrameFiber.step_suspend, step_withFiber, step_yieldableError
FrameFiber.step_onSuccess, step_onFailure, step_onSuccessAndFailure,
  step_exitFrame, step_onExit
FrameFiber.step_setInterruptible_not_evaluable
FrameFiber.step_whileLoop_true / _false, step_iterator
FrameFiber.step_ofExit_finishes :
  (start (Prim.ofExit exit)).step interp = (FrameStep.finished exit,
    [FrameEvent.yielded exit])
FrameFiber.run_zero, run_succ_finished, run_succ_running
```

`resumeValue_deferred` and `resumeCause_deferred` are together
`checkpoint.getcont-deferred`'s "whose both arms fail with the accumulated
cause"; `resumeValue_replacement` and `resumeCause_replacement` are together
`checkpoint.set-interruptible-contall`'s "for both arms".

The `some`/`none` third argument is not decoration: `step_success` supplies the
Exit and `step_sync` does not, which is exactly rc.112's
`cont[contA](this[args], fiber, this)` against `cont[contA](value, fiber)`. An
implementation that supplies the exit in both cases fails `step_sync`, and an
`Exit` frame under it would then reify the wrong exit.

`step_ofExit_finishes` is `exit.success-failure`'s open clause and
`E4-RUN-CE-020`'s repair in one line.

### F8 — masks and the two brackets (census: checkpoint.set-fiber-interruptible,
scope.scoped, scope.acquire-release)

```lean
FrameFiber.uninterruptible_already_masked : self.interruptible = false ->
  self.uninterruptible = self
FrameFiber.uninterruptible_masks : self.interruptible = true ->
  self.uninterruptible = { self with interruptible := false,
    stack := Prim.setInterruptible true :: self.stack }
FrameFiber.uninterruptibleMask_eq : self.uninterruptibleMask = self.uninterruptible
FrameFiber.setFiberInterruptible_flag / _pushes / _immediate_failure / _no_pending
FrameFiber.interruptibleRegion_already / _masked
FrameFiber.restoreAcquire_asked / _not_asked
Prim.scopedFrame_eq : scopedFrame body closeScope = onExit body closeScope false
Prim.scopedFrame_finalizer_masked
FrameFiber.step_scopedFrame
```

`uninterruptible_already_masked` is rc.112's `if (!fiber.interruptible) return self`:
an uninterruptible region inside an uninterruptible region pushes no second
restoring frame, so the mask is not a counter.
`setFiberInterruptible_immediate_failure` is `checkpoint.set-fiber-interruptible`'s
third clause: restoring interruptibility with a cause already pending fails now,
before the body runs.

### F9 — the two foreign boundaries (census: op.WithFiber, op.YieldableError)

```lean
Prim.withFiber_refused :
  forall {ϑ : Type u} (resolve : FrameFiber … -> ϑ) (left right : FrameFiber …),
    left = right -> resolve left = resolve right
Prim.yieldableError_host_class_refused :
  forall {ϑ : Type u} (host : ε -> ϑ) (left right : ε),
    left = right -> host left = host right
```

Both are the shape of `Effect4.Scope.key_freshness_refused` and
`Effect4.Reason.host_memory_refused`: an Effect4 interpretation is a function of
what Effect4 admits, so a host distinction outside that data is not
representable. `E4-RUN-CE-021` exhibits both pairs. The *behaviours* stay
modelled — `step_withFiber` and `step_yieldableError` — and only the object and
class identities are refused.

## Census row to obligation map

The clause-by-clause table, including which clauses are left to the run-loop,
context and supervision packets and the expected coverage state of each of the
thirty-one rows after the join, is in `docs/research/FRAMES-DAG.md` "Census rows this
packet targets". It is not duplicated here, because two copies of a clause map is
exactly the ownership error `AGENTS.md` forbids.

Summary: twenty-eight rows are green-able (`op.Success`, `op.Sync`,
`op.Suspend`, `op.WithFiber`, `op.YieldableError`, `op.Iterator`, `op.OnSuccess`,
`op.OnFailure`, `op.OnSuccessAndFailure`, `op.Exit`, `op.OnExit`,
`op.SetInterruptible`, `op.While`, the eight `frame-arm.*` rows in this packet,
`checkpoint.getcont-deferred`, `checkpoint.exit-failcause-skip`,
`checkpoint.set-interruptible-contall`, `checkpoint.set-fiber-interruptible`,
`rule.frames-are-primitives`, `rule.interrupt-bypasses-handlers`,
`exit.success-failure`); and three stay `partial` (`op.Failure`, `scope.scoped`,
`scope.acquire-release`). `op.Yield`, `op.Async`, `op.AsyncFinalizer`,
`checkpoint.runloop-top`, `checkpoint.post-yield-cancel`,
`rule.yield-is-overloaded` and `rule.budget-per-runloop-entry` are **not** in
this packet.

## Counterexample obligations

| ID | Frozen attack | Forced repair |
| --- | --- | --- |
| `E4-RUN-CE-010` | `contAll` runs only on the frame that answers the demanded arm | run it on every frame passed; a mask frame that answers no `contE` still clears the flag on the way past |
| `E4-RUN-CE-011` | a user `contE` handler catches an interruption | while interruptible with a pending cause the pop discards every answering `contE` frame, so `catchCause` never sees an interrupt |
| `E4-RUN-CE-012` | the skip is decided once, before the loop | re-read the flag after every `contAll`, so a mask frame stops the skip and the handler inside the uninterruptible region does run |
| `E4-RUN-CE-013` | `SetInterruptible(true)` only restores the flag | with a pending cause its `contAll` returns `failCause(cause)` as the continuation for either arm |
| `E4-RUN-CE-014` | the `OnExit` finalizer runs with the flag as it stands | `contAll` pushes `SetInterruptible(true)` and clears the flag, unless `args[2]` is `true` |
| `E4-RUN-CE-015` | the `OnExit` arm returns the finalizer's exit | run the finalizer, then restore the original exit |
| `E4-RUN-CE-016` | a failing finalizer under a failed exit keeps one cause | merge both by `causeCombine`; under a *successful* exit the finalizer's failure stands alone |
| `E4-RUN-CE-017` | the arms are fixed by the op prototype | `flatMap`, `catchCause` and `matchCauseEffect` assign them on the instance |
| `E4-RUN-CE-018` | an Exit yielded by a generator travels through the stack | fold it inline inside `contA`, so no `getCont` checkpoint sits between the folded values |
| `E4-RUN-CE-019` | `While`'s `contA` runs the body again without re-testing | step the cursor, re-test, and only then push and run the body |
| `E4-RUN-CE-020` | an empty stack is a defect, or the produced value is dropped | yield the Exit the fiber produced |
| `E4-RUN-CE-021` | the raw `FiberImpl` and the host `Error` class can be modelled | refuse both by theorem; model the effect each produces and nothing about the host object |

The twenty-three witnesses are finite self-contained breaker models in
`Test/Counterexamples/Machine/Runtime/Frames.lean`. They prove the attacks, not
the production laws, and they remain executable after the repair lands.

## Trust and acceptance

The checker is Lean's kernel at the pinned toolchain. `decide` is allowed for
finite propositions. `native_decide`, `sorry`, `admit`, `Classical.choice` and
new axioms are not allowed in the packet or the implementation.

Known traps for this packet, in addition to those `COORDINATION.md` already
records for Scope and Cause:

- A structure instance whose fields are split across lines must have every field
  at the same column. `{ self with current := x,` followed by a differently
  indented `stack := y }` is a parse error, not a layout preference.
- `Effect4.Exit.restoreAfterFinalizer` carries four `DecidableEq` instances
  because `Cause.combine` deduplicates. They propagate to `armA`, `armE`, both
  `resume` functions, `step` and `run`, and to nothing else.
- The pop must recurse on the frame list, never on `fiber.stack`, because
  `contAll` can push and the stack therefore does not decrease.

The breaker phase is accepted when

```sh
lake build Effect4Test.Counterexamples.Runtime.Frames
```

exits zero, while

```sh
lake env lean -DmaxErrors=10000 Test/Machine/Runtime/FramesContract.lean
lake env lean -DmaxErrors=10000 Test/Machine/Runtime/FramesAxiomReport.lean
```

both exit nonzero with *only* unknown-identifier and unknown-constant
diagnostics for the fenced `Effect4.Prim*`, `Effect4.Arm*`, `Effect4.IterStep*`,
`Effect4.PrimInterp*`, `Effect4.FrameFiber*`, `Effect4.ContAnswer*`,
`Effect4.FrameEvent*`, `Effect4.FramePop*` and `Effect4.FrameStep*` names. A
parse error, an import error, or a failure in the battery's own helper code is
not a clean red result. Both red modules are declared in
`test/fixtures/trust-gate/known-red.txt`, which is self-checking in both
directions: they must be removed the moment they go green.

The builder phase requires all three files plus the complete project test suite
to exit zero, with `#print axioms` receipts inside `propext`/`Quot.sound` for
every one of the one hundred and forty-nine public theorems. It does not
authorize any coverage-number change: the runtime-coverage join in
`Test/Audit/RuntimeCoverage.lean` is a separate packet with a separate
claim, as recorded in `docs/research/FRAMES-DAG.md`.

## Open questions

**Whether `popFrom` should be public.** It is, because every pop law is stated
over it, because the fusion of rc.112's two loops has to be inspectable rather
than buried, and because `FRAME-FB-ASYNC-FINALIZER` makes it the exact
declaration a later packet must revisit. The alternative — `private`, with the
laws restated over `getCont` — hides the one design decision most likely to be
wrong. Recommendation: keep it public.

**One interpretation record, or one per operation.** `PrimInterp` is threaded
through `armA`, `armE`, both `resume` functions, `step` and `run`. A later packet
that models the run loop will want the same record available to `Yield` and
`Async`, at which point it grows fields. That is an additive change: every
theorem above is universally quantified over `interp`, so a wider record
satisfies each one unchanged. Adding a *constructor* to `Prim` is not additive in
the same way, and the run-loop packet must say so.

**Whether `While`'s terminal value should be a `PrimInterp` field.** rc.112
finishes the loop with `exitVoid`, and the abstract value alphabet `β` has no
distinguished inhabitant. `loopDone : ν -> β` supplies one per loop. The
alternatives were a `Unit`-valued second machine (two value alphabets, and every
frame law doubled) and storing the terminal value in the `whileLoop` constructor
(first-order but not what rc.112 stores). Recommendation: keep `loopDone`; no
census clause observes the terminal value, and a later `Unit`-aware packet can
pin it.

**Whether the fiber should carry a `Context`.** Three clauses are `partial`
for want of one: the stack-frame cause annotation of `op.Failure`, and the
context save/restore of `scope.scoped` and `scope.acquire-release`. A `Context`
carrier is `Effect4/Context/`'s to own, and importing it here would put Runtime
above Context in the dependency order, which `docs/ARCHITECTURE.md` does allow.
Recommendation: leave it to the context packet and keep the three rows honestly
`partial`, rather than minting a fourth alphabet for a field this model never
reads.
