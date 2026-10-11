# Masked context provider entry

The coordinator approves this internal compiler repair of the providing-region contract.
The physical-only wrapper remains rejected because it restores before installation at some cuts.
No production compiler change lands in this note.
The current R2 runtime still needs the retained paired controls.

## Placement

Concept: scope-lifetime-finalization; requirement R11; role: preservation.
Consumer: the existing provider source arm and shared MaskBracket and StackRegionRun instances.
Concept: residual-program-typing; requirements R4 and R9; role: preservation dependency.
Consumer: the existing ambient M5 denotation and closed Assembly claims.
Rows 117 and 349 and the approved success/failure service guarantees bound the typing work.
The original closed claim headers remain unchanged.

## Data and entry order

The compiler keeps the existing Region data and existing machine actions.
It adds no program representation, action constructor or private evaluator.
It does not reuse acquireMasked or releaseMasked source roles.

| Sort | Payload |
| --- | --- |
| EffThunk.captureMask | none |
| EffName.provideMask | update : ContextUpdate; body : Region |
| EffThunk.provideMasked | update : ContextUpdate; body : Region; previousFlag : Bool |
| EffName.updateThen | update : ContextUpdate; body : Region; previousFlag : Bool |
| EffName.bodyThen | body : Region; previousContext : Ctx; previousFlag : Bool |
| EffThunk.restoreRegion | body : Region; previousFlag : Bool |

The previous context stays used by bodyThen when it installs the restoring finalizer.
The captured flag belongs to the body restoration action, not to a source service value.

```mermaid
flowchart LR
  A[Capture entry mask] --> B[Pop capture restoring slot]
  B --> C[Enter masked provider]
  C --> D[Read context]
  D --> E[Set updated context]
  E --> F[Install context finalizer]
  F --> G[Restore body mask]
  G --> H[Run body]
  H --> I[Restore context on exit]
  I --> J[Pop provider mask slot]
```

getInterruptible has its own restoring slot.
Its successful answer restores the prior flag before provideMask enters the masked provider.
A pending failure intercepted there never reaches the context getter or setter.
The second mask protects installation and finalizer placement together.
The body restoration action may deliver pending interruption after the context finalizer exists.
The outer mask slot restores the caller's flag after context cleanup.

## Compiler equations

These equations specify the new constructor domain.
They remain proposed equations until the temporary paired compiler probe checks them.

```lean
updateContextAt update body =
  .onSuccess (.withFiber .captureMask) (.provideMask update body)

interp.withFiberOf .captureMask = some .getInterruptible

contAOf root (.provideMask update body) (Val.savedMask flag) =
  .withFiber (.provideMasked update body flag)

interp.withFiberOf (.provideMasked update body flag) =
  some (.setInterruptible
    (.onSuccess (.withFiber .getCtx) (.updateThen update body flag)) false)

updateThenK root update body flag (Val.context previous) =
  if updateKeepsIdentity update previous.services then
    .withFiber (.restoreRegion body flag)
  else
    .onSuccess (.withFiber (.setCtx next)) (.bodyThen body previous flag)

contAOf root (.bodyThen body previous flag) value =
  .onExit (.withFiber (.restoreRegion body flag)) (.restoreCtx previous) false

interp.withFiberOf (.restoreRegion body flag) =
  some (.setInterruptible (regionCode root body) flag)
```

Here next is Ctx.withServices (update.apply previous.services).
The existing context and saved-mask readers retain their located bad-shape behavior.
The identity branch restores the body mask without setting or restoring the context.
The setter and bodyThen execute under the provider mask.
The onExit frame therefore exists before interruption becomes effective again.

## Paired reference equations

FiberOp.mask already carries first-order Sched.Body data.
Its Body cannot store an RProgram or a function.
Two body names expose the same Region and provider-entry payloads:

| Sort | Payload |
| --- | --- |
| Body.region | body : Region |
| Body.contextEntry | update : ContextUpdate; body : Region; previousFlag : Bool |

updateContextR changes its internal body parameter from RProgram to Region.
The source callers pass their actual existing program, build, buildAdding or construct Region.
The outward closed source claims retain their original scope.
The previous arbitrary-program helper reach changes explicitly; it is not retained by a hidden ambient premise.

```lean
updateContextR update body =
  (guardR .onSuccess (fiberValR .getInterruptible rfl)).bind
    (seqR fun value =>
      match Val.savedMask? value with
      | some flag => .vis (.inr (.mask false (.contextEntry update body flag))) .pure
      | none => .pure badShapeExit)

contextEntryR update body flag =
  (guardR .onSuccess (fiberValR .getContext rfl)).bind
    (seqR fun value =>
      match Val.context? value with
      | some previous =>
        if updateKeepsIdentity update previous.services then restoreRegionR body flag
        else
          (guardR .onSuccess (fiberValR (.setContext next) rfl)).bind
            (seqR fun _ =>
              onExitR (restoreRegionR body flag)
                (fun _ => fiberValR (.setContext previous) rfl))
      | none => .pure badShapeExit)

restoreRegionR body flag = .vis (.inr (.mask flag (.region body))) .pure
```

The reference body interpreter uses its existing addressed-body and layer-build hooks.
A generated Region fold supplies the four leaf clauses once.
Its program clause uses suspendBody (.body point), without executing another Suspend checkpoint.
Its build clause uses the existing forkLayer body hook.
Its buildAdding and construct clauses reuse addCurrentMemoMapR and bindServiceR.
InterpR.denoteBody and EvaluateR.bodyR instantiate that shared fold through existing interpreters.
No new recursive source resolution pass enters the tree.

The existing Fold producer reads Region's declared constructor signature.
A RegionFold manifest entry imports Program.Compile and emits Program.RegionFold.
The coordinator owns its Makefile output and root hook.
The native regionCode traversal remains its existing census exemption.
The new reference interpretation consumes the generated fold instead of adding another hand traversal.

## Required controls and observation

The observation includes physical context, context-write events and the saved interruptible flag.
An admitted pre-entry interruption performs zero installation writes and zero restoration writes.
A post-install interruption records one installation followed by one restoration.
Both initial flag settings return to their prior setting after body and cleanup.
The getInterruptible restoring-slot interception remains a separate pre-entry control.
The identity branch performs no context write.
Fuel eight remains an explicit retained control, with its result recomputed at the current R2 pin.
Old finite cut numbers establish nothing about the current R2 runtime.
Public HistoryOf exposure and outside runtime comparison remain separate obligations.

## Exact migration fence

Compile owns the new names, payloads, withFiberOf cases and continuation equations.
Sched owns the two Body names; DenoteR owns the named provider reference equations.
InterpR and EvaluateR own the existing body interpreter clauses through the Region fold.
Agreement and Intro.Region own the paired existing CodeMeans producers.
Typed.Body, Typed.Residual, Typed.Context and Typed.Denotation retain actual body entry coverage.
Handles, NativeCallbacks and support/weight folds require exhaustive new-constructor coverage.
The native source files remain coordinated with host_timeout before edits.
Machine.Fibers stays unchanged and belongs to the machine seat.
The coordinator owns roots, Makefile, lakefile and registries.

## Status

The paired equations and payloads are recorded, not compiled by this note.
The resource hold prevents a new Lean run until the coordinator opens a slot.
The full M5 Denotation migration remains open.
The checked ambient entry checkpoint remains 1b66ff6a4.
The retained old-runtime pin correction remains f836b384f.
