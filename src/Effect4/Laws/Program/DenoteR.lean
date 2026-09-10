import Effect4.Laws.Program.Sched
import Effect4.Laws.Program.Agreement

/-!
# Structural denotation over stores and fibers (R2, restated by P2)

Contract: `Test/contracts/program-denote-r.contract.md`. Design and authorized
corrections: `docs/research/2026-09-06-w3-r2-continuation.md`,
`docs/research/2026-09-06-r3-r4-implementation.md` and the P2 phase model of
`docs/research/2026-09-06-p0-fable-record.md` §4.

`denoteR root e p` is structural on the existing `Eff` at a `Point`; `p.fuel` is
the only budget and is spent as `compileEff` spends it. A frontier carries the
residual point, never a failed exit. Loops and generators are not unfolded here:
they are the runtime operations `FiberOp.loop` and `FiberOp.gen`, whose later
iterations the evaluator runs inside the body's delivery through its saved slots,
with the compile's own navigation (`InterpR.walkR`). `inlineYield` records exactly
which yielded source forms expose an immediate exit before the iterator resumes.

The counted checkpoints the host spends where the term has no work of its own are
explicit: `suspend` in front of a suspension, a decided branch, a yieldable error's
failure and the generator and loop entries, and `sync` for a pure thunk's value.
Control erasure removes them with the boundary markers, so after erasure the
straight fragment restricts to `Denote.denote` when the compile budget covers its
depth. The raw terms retain handler and cleanup boundaries (`E4-SCHED-CE-004`).
Fiber nodes are the term scheduler's interface, not a handler semantics or a
simulation theorem. In particular the placeholder `rHandler` must not be used to
interpret a frontier as a finished result (`RDEN-FB-HANDLER`). Mask nodes carry
addressed or synthesized bodies; their execution and interruption rules live in the
evaluator (`RDEN-FB-SCHEDULER`). Program rows remain unsupported frontiers, as in
`compileEff` (`RDEN-FB-UNSUPPORTED`); `acquireRelease` denotes step by step as the compile
names it (V1, 2026-09-07): the context read, then its masked half as a `Body`.
-/

set_option autoImplicit false

namespace Effect4.Program.Sched

open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Denote

/-- A live frontier at a point. -/
def pending (reason : FrontierReason) (at_ : Point) : RProgram :=
  .vis (.inr (.frontier reason at_)) Effects.Program.pure

/-- Value continuations short-circuit on a failed exit. -/
def seqR (k : Val → RProgram) : ExitV → RProgram
  | .success v => k v
  | .failure c => .pure (.failure c)

/-- Invoke a source callback against the completed exits visible at invocation.
The query is administrative and is consumed by `prepareR`, not the run loop. -/
def constructR (k : List (FiberId × ExitV) → RProgram) : RProgram :=
  .vis (.inr .construction) k

/-- Resolve construction queries in freshly built code, including the eager body
of a guard. Its saved exit callback is constructed only when that callback runs.
Counted operations retain their continuations untouched. -/
def prepareR (completed : List (FiberId × ExitV)) : RProgram → RProgram
  | .pure ex => .pure ex
  | .vis (.inr .construction) k => prepareR completed (k completed)
  | .vis (.inr (.guard_ kind)) k => .vis (.inr (.guard_ kind)) fun
    | none => prepareR completed (k none)
    | some ex => k (some ex)
  | .vis op k => .vis op k

/-- Retain a continuation boundary. The normal branch closes it explicitly;
an interrupted body resumes through the saved exit branch instead. -/
def guardR (kind : GuardKind) (body : RProgram) : RProgram :=
  .vis (.inr (.guard_ kind)) fun
    | none => body.bind fun ex => .vis (.inr (.unguard ex)) Effects.Program.pure
    | some ex => .pure ex

/-- The optional cleanup effect returned by an OnExit callback follows the
same ordinary handlers as `Machine.finalizerCode` (`internal/effect.ts:4021-4029`). -/
def finalizerR (ex : ExitV) (cleanup : RProgram) : RProgram :=
    (guardR .onSuccess
      (match ex with
       | .success _ => cleanup
       | .failure _ => (guardR .onFailure cleanup).bind fun
           | .success v => .pure (.success v)
           | .failure c => .pure (Exit.restoreAfterFinalizer ex (.failure c)))).bind (seqR fun _ =>
      .vis (.inr (.finishFinalizer ex)) Effects.Program.pure)

/-- An exit finalizer has its own boundary, then restores the body's exit and mask.
The runtime implements the mask; erasure below removes only these control markers. -/
def onExitR (body : RProgram) (fin : ExitV → RProgram)
    (interruptible : Bool := false) : RProgram :=
  (guardR (.onExit interruptible) body).bind fun ex => finalizerR ex (fin ex)

/-- The counted checkpoint that returns code: `Suspend` at `p`. -/
def suspendR (p : Point) (body : RProgram) : RProgram :=
  .vis (.inr (.suspend p)) fun _ => body

/-- A store operation answering its value. -/
def storeR (op : SyncOp) : RProgram :=
  .vis (.inl op) fun v => .pure (.success v)

/-- A value-answering fiber operation answering its value. -/
def fiberValR (op : FiberOp) (h : op.answer = Val) : RProgram :=
  .vis (.inr op) fun v => .pure (.success (h ▸ v))

/-- Forget control boundaries and checkpoints for the store meaning, retaining every
other operation. This is an erasure, not a scheduler or a handler for interruption. -/
def controlErasure : Effects.Handler RSig (Effects.Program RSig) where
  handle
    | .inr .construction => .pure []
    | .inr (.guard_ _) => .pure none
    | .inr (.unguard ex) | .inr (.finishFinalizer ex) => .pure ex
    | .inr (.suspend _) => .pure Val.unit
    | .inr (.sync v) => .pure v
    | op => .vis op Effects.Program.pure

def eraseControl {A : Type} (program : Effects.Program RSig A) : Effects.Program RSig A :=
  Effects.interpret controlErasure program

theorem eraseControl_pure {A : Type} (a : A) :
    eraseControl (Effects.Program.pure a) = .pure a := rfl

theorem eraseControl_bind {A B : Type} (p : Effects.Program RSig A)
    (k : A → Effects.Program RSig B) :
    eraseControl (p.bind k) = (eraseControl p).bind (fun a => eraseControl (k a)) :=
  Effects.interpret_bind controlErasure p k

theorem eraseControl_guardR (kind : GuardKind) (body : RProgram) :
    eraseControl (guardR kind body) = eraseControl body := by
  change eraseControl (body.bind fun ex => .vis (.inr (.unguard ex)) Effects.Program.pure) = _
  rw [eraseControl_bind]
  exact Effects.Program.bind_pure_right _

theorem eraseControl_onExitR (body : RProgram) (fin : ExitV → RProgram) (flag : Bool) :
    eraseControl (onExitR body fin flag) =
      (eraseControl body).bind fun ex => (eraseControl (fin ex)).bind fun fex =>
        .pure (Exit.restoreAfterFinalizer ex (finVoid fex)) := by
  simp only [onExitR, finalizerR, eraseControl_bind, eraseControl_guardR]
  congr 1
  funext ex
  cases ex with
  | success v =>
    congr 1
    funext fex
    cases fex <;> rfl
  | failure cause =>
    simp only [eraseControl_bind, eraseControl_guardR, Effects.Program.bind_assoc]
    congr 1
    funext fex
    cases fex <;> rfl

theorem eraseControl_suspendR (p : Point) (body : RProgram) :
    eraseControl (suspendR p body) = eraseControl body := rfl

theorem eraseControl_sync (v : Val) (k : Val → RProgram) :
    eraseControl (.vis (.inr (.sync v)) k) = eraseControl (k v) := rfl

theorem eraseControl_constructR (k : List (FiberId × ExitV) → RProgram) :
    eraseControl (constructR k) = eraseControl (k []) := rfl

/-- Race entrants use the same list-node addresses as `actionAt.entrants`. -/
def entrantPoints : Effs NativeOp → Point → List Point
  | .nil, _ => []
  | .cons _ rest, p => p.child 0 :: entrantPoints rest (p.child 1)

def racePoints (root : NativeEff) (p : Point) : List Point :=
  match Node.at_ (.eff root) p.path with
  | some (.eff (.withFiber (.raceAll es))) => entrantPoints es ((p.child 0).child 0)
  | _ => []

/-- The term of the fiber action `actionAt` answers at a point. Program-valued fields of
the action are represented by their source addresses, never stored as `Prim`. -/
def denoteFiberAction (root : NativeEff) (p : Point) : NAction → RProgram
  | .fork _ options =>
    .vis (.inr (.fork (.at_ ((p.child 0).child 0)) options)) fun v => .pure (.success v)
  | .forkIn _ options scope =>
    .vis (.inr (.forkIn ((p.child 0).child 0) options scope)) fun v => .pure (.success v)
  | .forkScoped _ options =>
    .vis (.inr (.forkScoped ((p.child 0).child 0) options)) Effects.Program.pure
  | .runIn target scope =>
    .vis (.inr (.runIn target scope)) fun v => .pure (.success v)
  | .interrupt target => .vis (.inr (.interrupt target)) fun v => .pure (.success v)
  | .interruptAs target who => .vis (.inr (.interruptAs target who)) fun v => .pure (.success v)
  | .interruptScoped target =>
    .vis (.inr (.interruptScoped target)) fun v => .pure (.success v)
  | .interruptAll targets who =>
    .vis (.inr (.interruptAll targets who)) fun v => .pure (.success v)
  | .awaitAll targets => .vis (.inr (.awaitAll targets)) fun v => .pure (.success v)
  | .awaitAllFailFast targets =>
    .vis (.inr (.awaitAllFailFast targets)) fun v => .pure (.success v)
  | .snapshotChildren => .vis (.inr .snapshotChildren) fun v => .pure (.success v)
  | .awaitNewChildren snapshot =>
    .vis (.inr (.awaitNewChildren snapshot)) fun v => .pure (.success v)
  | .raceAll _ => .vis (.inr (.raceAll (racePoints root p))) Effects.Program.pure
  | .setInterruptible _ flag =>
    .vis (.inr (.mask flag (.at_ (p.child 0)))) Effects.Program.pure
  | .setContext ctx => .vis (.inr (.setContext ctx)) fun v => .pure (.success v)
  | .getContext => .vis (.inr .getContext) fun v => .pure (.success v)
  | .getId => .vis (.inr .getId) fun v => .pure (.success v)
  | .closeScope scope ex => .vis (.inr (.closeScope scope ex)) Effects.Program.pure
  | .refuse cause => .vis (.inr (.refuse cause)) fun v => .pure (.success v)
  | .dropObservers token => .vis (.inr (.dropObservers token)) fun v => .pure (.success v)
  | .cancelRace race => .vis (.inr (.cancelRace race)) fun v => .pure (.success v)
  -- `forkScoped` is `flatMap(scope, scope => forkIn(self, scope, options))` (`:5381-5406`,
  -- §20): the counted service read, then `forkIn` on the handle it answered
  | .ambientScope =>
    match Node.at_ (.eff root) p.path with
    | some (.eff (.withFiber (.forkScoped _ options))) =>
      (guardR .onSuccess (fiberValR .ambientScope rfl)).bind (seqR fun
        | .scopeHandle s =>
          .vis (.inr (.forkIn ((p.child 0).child 0) options s)) fun v => .pure (.success v)
        | _ => .pure badShapeExit)
    | _ => .pure badShapeExit
  -- the parallel close's step is a store program, never a source node
  | .closePar _ => .pure badShapeExit

/-- The fiber action selected by the actual point lookup. A point that names no action is
the frame machine's `suspendBody` refusal after its counted step. -/
def denoteAction (root : NativeEff) (p : Point) : RProgram :=
  match actionAt root p with
  | none => suspendR p (.pure outsideExit)
  | some action => denoteFiberAction root p action

/-- Async registration answers with an exit; failure is not a successful error value.
The request and registration name retain the exact `Deferred.await` decoding. -/
def denoteAsync (request : Term) (p : Point) : RProgram :=
  match evalTerm p.env request with
  | none => .pure badShapeExit
  | some value =>
    match NativeOp.awaitCellOf value with
    | none => .pure badShapeExit
    | some cell => .vis (.inr (.async (.registerAwait cell) value)) Effects.Program.pure

/-- An external callback retains its row and request until it receives an exit. -/
def denoteForeign (op : NativeOp) (request : Term) (p : Point) : RProgram :=
  match evalTerm p.env request with
  | none => .pure badShapeExit
  | some value => .vis (.inr (.async (.external op value) value)) Effects.Program.pure

/-- `Effect.sleep(d)` on the term route (the timer, A4): `d = 0` is the counted yield, the rest
the registration on the logical clock by the machine's name. -/
def denoteSleep (request : Term) (p : Point) : RProgram :=
  match (evalTerm p.env request).bind NativeOp.sleepMillisOf with
  | none => .pure badShapeExit
  | some 0 => .vis (.inr (.yieldNow 0)) fun v => .pure (.success v)
  | some (n + 1) =>
    .vis (.inr (.async (.store (.registerSleep (n + 1))) (Val.nat (n + 1)))) Effects.Program.pure

/-- The scope's finalizer shapes (`Stores.finProgram`). -/
def denoteFin : FinName → ExitV → RProgram
  | .interruptFiber fiber true, _ => fiberValR (.interruptScoped fiber) rfl
  | .interruptFiber fiber false, _ => fiberValR (.interrupt fiber) rfl
  | .closeChildScope scope, ex => .vis (.inr (.closeScope scope ex)) Effects.Program.pure
  | .detachFromParent parent key, _ => storeR (.scopeRemove parent key)
  | .release label fails, _ =>
    .pure (if fails then .failure (Cause.fail (.tag label)) else .success .unit)
  | .parkThen slot, _ => .vis (.inr (.async (.store (.externalRegister slot)) .unit)) Effects.Program.pure
  | .awaitNewChildren snapshot, _ => fiberValR (.awaitNewChildren snapshot) rfl
  -- a capture's release (V1): the counted suspend, then `provideContext(release(a, exit),
  -- context)` (`internal/effect.ts:3983`, `:2180-2199`): the current context read, the captured
  -- one set, the release at the capture's point over the exit under the finalizer restoring
  -- the previous context — constructed with the view at its invocation (`constructR`), as the
  -- frame's `interpAt` refreshes the release's name
  | .foreign c, ex => .vis (.inr (.foreignRelease c ex)) fun _ =>
      (guardR .onSuccess (fiberValR .getContext rfl)).bind (seqR fun v =>
        match Val.context? v with
        | some previous =>
          (guardR .onSuccess (fiberValR (.setContext c.ctx) rfl)).bind (seqR fun _ =>
            constructR fun completed =>
              .vis (.inr (.mask false
                (.release ((Point.ofCapture c completed).childWith 1 (reifyExitVal ex)) previous)))
                Effects.Program.pure)
        | none => .pure badShapeExit)
  -- `fromBuild`'s `onExit` (`Layer.ts:343`, the join): close the layer scope on failure only
  | .closeChildOnFailure scope, .failure cause =>
    .vis (.inr (.closeScope scope (.failure cause))) Effects.Program.pure
  | .closeChildOnFailure _, .success _ => .pure (.success .unit)
  -- the memo entry finalizer (`Layer.ts:401-410`, the join): `observers--`; the last
  -- observer's release answers the layer scope, closed with the exit
  | .memoEntry layer memoMap, ex =>
    (guardR .onSuccess (storeR (.memoRelease layer memoMap))).bind (seqR fun v =>
      match Val.scope? v with
      | some s => .vis (.inr (.closeScope s ex)) Effects.Program.pure
      | none => .pure (.success .unit))
  -- `memoMapBuild`'s `onExit` (`:414-417`): the exit stored, the Deferred completed
  | .memoDone layer memoMap, ex => storeR (.memoComplete layer memoMap ex)

/-! ## The join: `Effect.provide`, `Effect.service`, `Effect.provideService`, `Layer.build`

The term follows the compile's names step by step, as `acquireRelease` does (V1): every frame
continuation of `Compile.lean`'s join arms is a `seqR` continuation here, and a layer's build
(`compileLayer`, `innerLayerAt`, `constructionAt`) is `denoteLayer` below, structural in the
layer term, in the mutual block with `denoteR` — a leaf's body is a subterm. What the frame
resolves by a lookup at a point (`resolve`, `resolveLayer`, `regionCode`) the term has in hand. -/

/-- `updateContext(self, f)` (`internal/effect.ts:2087-2096`): the context read; the same object
runs the body as is (`:2090`, `updateKeepsIdentity`); else the next context set and the body
under the finalizer restoring the previous one (`:2091-2095`). -/
def updateContextR (update : Env.ContextUpdate) (body : RProgram) : RProgram :=
  (guardR .onSuccess (fiberValR .getContext rfl)).bind (seqR fun v =>
    match Val.context? v with
    | some prev =>
      if updateKeepsIdentity update prev.services then body
      else
        (guardR .onSuccess
          (fiberValR (.setContext (Ctx.withServices (update.apply prev.services))) rfl)).bind
          (seqR fun _ => onExitR body fun _ => fiberValR (.setContext prev) rfl)
    | none => .pure badShapeExit)

/-- `scopeAddFinalizerExit(scope, fin)` (`internal/effect.ts:3847-3858`): unit when the
registration took; else the closing exit read back and the finalizer run now, then unit. -/
def scopeAddR (scope : Nat) (fin : FinName) : RProgram :=
  (guardR .onSuccess (storeR (.scopeAdd scope fin))).bind (seqR fun w =>
    if w = Val.unit then .pure (.success .unit)
    else
      match exitOfVal w with
      | some ex => (guardR .onSuccess (denoteFin fin ex)).bind (seqR fun _ => .pure (.success .unit))
      | none => .pure badShapeExit)

/-- `Context.make(key, value)` (`Layer.ts:1440`), or `Context.empty()` (`:1515`), over a leaf's
answer. -/
def bindServiceR (key : Option ServiceKey) (v : Val) : RProgram :=
  match key with
  | some key => .pure (.success (Env.encode (Env.Context.empty.addV key v)))
  | none => .pure (.success (Env.encode Env.Context.empty))

/-- `map(_, Context.add(CurrentMemoMap, memoMap))` (`Layer.ts:762`) on the built context. -/
def addCurrentMemoMapR (m : MemoMapId) (v : Val) : RProgram :=
  match Env.decode v with
  | some ctx => .pure (.success (Env.encode (ctx.addV Env.currentMemoMapKey (Val.memoMap m))))
  | none => .pure badShapeExit

/-- `f(merged, context)` (`Layer.ts:1923`) on the dependent's context. -/
def combineWithR (mode : CombineMode) (that : Env.Ctx) (v : Val) : RProgram :=
  match Env.decode v with
  | some merged =>
    match mode with
    | .provide => .pure (.success (Env.encode merged))
    | .provideMerge => .pure (.success (Env.encode (that.merge merged)))
  | none => .pure badShapeExit

/-- `Context.mergeAll(...contexts)` (`Layer.ts:1600`) over the awaited exits. -/
def mergeContextsR (v : Val) : RProgram :=
  match contextsOf v with
  | some ctxs => .pure (.success (Env.encode (Env.Context.mergeAll ctxs)))
  | none =>
    match reasonsOfVal v with
    | [] => .pure badShapeExit
    | reason :: rest => .pure (.failure ⟨reason :: rest⟩)

/-- `Effect.service(key)` on the context value: the lookup, or the host throw as a defect. -/
def serviceLookupR (key : ServiceKey) (v : Val) : RProgram :=
  match Val.context? v with
  | some ctx =>
    match ctx.services.getV key with
    | some value => .pure (.success value)
    | none => .pure (.failure (Cause.die Defect.missingService))
  | none => .pure badShapeExit

/-- `buildWithMemoMap` (`Layer.ts:756-765`): `provideService(CurrentMemoMap)` around the build
through the map, `Context.add(CurrentMemoMap, _)` mapped over its answer. -/
def buildWithMemoMapR (build : MemoMapId → RProgram) (m : MemoMapId) : RProgram :=
  updateContextR (.provideService Env.currentMemoMapKey (Val.memoMap m))
    ((guardR .onSuccess (build m)).bind (seqR fun v => addCurrentMemoMapR m v))

/-- `fromBuild` (`Layer.ts:333-345`): the layer scope forked from the caller's, the inner build
inside it under the finalizer that closes it on failure. -/
def fromBuildR (scope : Nat) (inner : Nat → RProgram) : RProgram :=
  (guardR .onSuccess (storeR (.scopeFork scope .sequential))).bind (seqR fun v =>
    match Val.scope? v with
    | some child => onExitR (inner child) fun ex => denoteFin (.closeChildOnFailure child) ex
    | none => .pure badShapeExit)

/-- `getOrElseMemoize` (`Layer.ts:445-457`): the counted suspend, the lookup; a hit registers
the entry finalizer on the caller's scope and awaits the entry's deferred (`:439-440`,
`:400`); a miss is `memoMapBuild` (`:390-419`) — the allocation, the registration, and the
construction into the layer scope under the `onExit` that completes the entry. -/
def memoizeR (q : Point) (m : MemoMapId) (scope : Nat) (construction : Nat → RProgram) :
    RProgram :=
  suspendR q ((guardR .onSuccess (storeR (.memoGet q.path m))).bind (seqR fun v =>
    match Val.memoHit? v with
    | some (cell, owner) =>
      (guardR .onSuccess (scopeAddR scope (.memoEntry q.path owner))).bind (seqR fun _ =>
        .vis (.inr (.async (.registerAwait cell) (Val.promise cell))) Effects.Program.pure)
    | none =>
      if v = Val.unit then
        (guardR .onSuccess (storeR (.memoBuild q.path m))).bind (seqR fun w =>
          match Val.scope? w with
          | some layerScope =>
            (guardR .onSuccess (scopeAddR scope (.memoEntry q.path m))).bind (seqR fun _ =>
              onExitR (construction layerScope) fun ex => denoteFin (.memoDone q.path m) ex)
          | none => .pure badShapeExit)
      else .pure badShapeExit))

/-- `provideWith` (`Layer.ts:1915-1923`): the dependency built, the dependent under
`provideContext(context)`, the combiner. -/
def provideWithR (dependency dependent : RProgram) (mode : CombineMode) : RProgram :=
  (guardR .onSuccess dependency).bind (seqR fun v =>
    match Env.decode v with
    | some ctx =>
      (guardR .onSuccess (updateContextR (.provide ctx) dependent)).bind (seqR fun w =>
        combineWithR mode ctx w)
    | none => .pure badShapeExit)

/-- One sibling's build forked as an immediate daemon (`Layer.ts:1597`; `forEach`'s
concurrency, `internal/effect.ts:4851`). -/
def forkLayerR (q : Point) (m : MemoMapId) (scope : Nat) : RProgram :=
  .vis (.inr (.fork (.layerBuild q m scope) ⟨true, true, .inherit⟩)) fun v => .pure (.success v)

/-- `mergeAllEffect`'s fork loop for two siblings (`Layer.ts:1597-1600`): a sequential child of
the parallel parent per sibling, the sibling's build forked into it, then the await and the
merge. -/
def mergeForkR (q : Point) (m : MemoMapId) (parent : Nat) : RProgram :=
  (guardR .onSuccess (storeR (.scopeFork parent .sequential))).bind (seqR fun v =>
    match Val.scope? v with
    | some c0 =>
      (guardR .onSuccess (forkLayerR (q.child 0) m c0)).bind (seqR fun f0 =>
        match Val.fiber? f0 with
        | some id0 =>
          (guardR .onSuccess (storeR (.scopeFork parent .sequential))).bind (seqR fun w =>
            match Val.scope? w with
            | some c1 =>
              (guardR .onSuccess (forkLayerR (q.child 1) m c1)).bind (seqR fun f1 =>
                match Val.fiber? f1 with
                | some id1 =>
                  (guardR .onSuccess (fiberValR (.awaitAllFailFast [id0, id1]) rfl)).bind
                    (seqR fun ex => mergeContextsR ex)
                | none => .pure badShapeExit)
            | none => .pure badShapeExit)
        | none => .pure badShapeExit)
    | none => .pure badShapeExit)

/-- `mergeAllEffect` (`Layer.ts:1587-1602`): the parallel parent forked from the layer scope,
then the siblings. -/
def mergeTwoR (q : Point) (m : MemoMapId) (child : Nat) : RProgram :=
  (guardR .onSuccess (storeR (.scopeFork child .parallel))).bind (seqR fun v =>
    match Val.scope? v with
    | some parent => mergeForkR q m parent
    | none => .pure badShapeExit)

/-- `mergeAllEffect`'s fork loop for the layers of a `mergeAll` (`Layer.ts:1597-1600`, the host
rows slice), from layer `i` with `remaining` layers left and the fibers forked so far: a
sequential child of the parallel parent per layer, the layer's build forked into it
(`Point.spineChild`), then the await of every fiber and the merge. What `contAOf` does for
`mergeAllForkOne`/`mergeAllForkNext` (`Compile.lean`), the count read off the node. -/
def mergeAllForkR (q : Point) (m : MemoMapId) (parent : Nat) :
    Nat → Nat → List FiberId → RProgram
  | 0, _, forked =>
    (guardR .onSuccess (fiberValR (.awaitAllFailFast forked) rfl)).bind
      (seqR fun ex => mergeContextsR ex)
  | remaining + 1, i, forked =>
    (guardR .onSuccess (storeR (.scopeFork parent .sequential))).bind (seqR fun v =>
      match Val.scope? v with
      | some c =>
        (guardR .onSuccess (forkLayerR (q.spineChild i) m c)).bind (seqR fun f =>
          match Val.fiber? f with
          | some id => mergeAllForkR q m parent remaining (i + 1) (forked ++ [id])
          | none => .pure badShapeExit)
      | none => .pure badShapeExit)

/-- `mergeAllEffect` for a `mergeAll` of `count` layers (`Layer.ts:1587-1602`): the parallel
parent forked from the layer scope, then the fork loop from layer `0`. -/
def mergeAllR (q : Point) (m : MemoMapId) (child : Nat) (count : Nat) : RProgram :=
  (guardR .onSuccess (storeR (.scopeFork child .parallel))).bind (seqR fun v =>
    match Val.scope? v with
    | some parent => mergeAllForkR q m parent count 0 []
    | none => .pure badShapeExit)

/-- DI-61: the semantic counterpart of `asyncRoute`, shared by both invocation forms.
External registration is selected before the placeholder's row kind. -/
def denoteAsyncRoute (op : NativeOp) (request : Term) (p : Point) : RProgram :=
  match op with
  | .external _ => denoteForeign op request p
  | .sleep => denoteSleep request p
  | _ => match (NativeOp.row op).kind with
    | .async => denoteAsync request p
    | _ => .pure badShapeExit

/-- Immediate-exit classification for the shared asynchronous route. -/
def inlineAsyncYield (op : NativeOp) (request : Term) (p : Point) : Option ExitV :=
  match op with
  | .external _ => match evalTerm p.env request with
    | some _ => none | none => some badShapeExit
  | .sleep => match (evalTerm p.env request).bind NativeOp.sleepMillisOf with
    | some _ => none | none => some badShapeExit
  | _ => match (NativeOp.row op).kind with
    | .async => match (evalTerm p.env request).bind NativeOp.awaitCellOf with
      | some _ => none | none => some badShapeExit
    | _ => some badShapeExit

/-- A yielded source form with an immediate `Prim.success` or `Prim.failure` head.
`sync`, `yieldError` with a valid argument, and compound frames are not inline exits;
`exit` of an immediate exit is that exit's success (`internal/effect.ts:3621-3622`), and
a loop never is (its compile is a `Suspend`). The definition inspects source data and the point's captured completed exits;
its compiler-head equation is checked below. -/
def inlineYield : NativeEff → Point → Option ExitV
  | e, p =>
    if p.fuel = 0 then none else
    match e with
    | .succeed t => some (match evalTerm p.env t with
      | some v => .success v | none => badShapeExit)
    | .fail t => some (match evalTerm p.env t with
      | some v => .failure (Cause.fail (errOf v)) | none => badShapeExit)
    | .failCause t => some (match causeOf p.env t with
      | some c => .failure c | none => badShapeExit)
    | .yieldError t => match evalTerm p.env t with
      | some _ => none | none => some badShapeExit
    | .perform op request =>
      match op with
      | .external _ => inlineAsyncYield op request p
      | _ => match (NativeOp.row op).kind with
        | .sync => match (evalTerm p.env request).bind (NativeOp.syncOpOf op) with
          | some _ => none | none => some badShapeExit
        | .async => inlineAsyncYield op request p
        | .program => none
    | .callback op request => inlineAsyncYield op request p
    | .awaitFiber target mode => match evalTerm p.env target with
      | some (Val.fiber ⟨id⟩) => p.awaitExit ⟨id⟩ mode | _ => some badShapeExit
    | .exit b => (inlineYield b (p.child 0)).map fun ex => .success (reifyExitVal ex)
    -- `provideService` of a value that does not evaluate is the wrong-shape refusal
    | .provideService _ value _ => match evalTerm p.env value with
      | some _ => none | none => some badShapeExit
    | _ => none

/-- `Effect.provide`'s protocol after the counted step, at the point that carries the view
(`scopedWith`, `internal/effect.ts:3966-3967`; `internal/layer.ts:15-21`): the scope made, the
layer built into it (`buildAt`, the layer's `denoteLayer`) — off the fiber context's memo map,
or a private one when `local` — the body (`bodyAt`, its `denoteR`; `bodyExit` its
`inlineYield`) under `provideContext(built)`, the scope closed with the exit. The three
programs are passed in so that this stays outside the mutual block. -/
def provideLayerR (buildAt : Point → MemoMapId → Nat → RProgram) (bodyAt : Point → RProgram)
    (bodyExit : Point → Option ExitV) (isLocal : Bool) (p : Point) : RProgram :=
  (guardR .onSuccess (storeR (.scopeMake .sequential))).bind (seqR fun v =>
    match Val.scope? v with
    | some scope =>
      onExitR
        ((guardR .onSuccess
          (if isLocal then
            (guardR .onSuccess (storeR (.memoFork none))).bind (seqR fun w =>
              match Val.memoMap? w with
              | some id => buildWithMemoMapR (fun m => buildAt (p.child 0) m scope) id
              | none => .pure badShapeExit)
          else
            (guardR .onSuccess (fiberValR .getContext rfl)).bind (seqR fun w =>
              match Val.context? w with
              | some ctx =>
                (guardR .onSuccess (storeR (.memoFork (currentMemoMapOf ctx.services)))).bind
                  (seqR fun u =>
                    match Val.memoMap? u with
                    | some id => buildWithMemoMapR (fun m => buildAt (p.child 0) m scope) id
                    | none => .pure badShapeExit)
              | none => .pure badShapeExit))).bind (seqR fun built =>
          match Env.decode built with
          | some ctx =>
            -- `provideContext` of an exit is that exit (`internal/effect.ts:2196`)
            match bodyExit (p.child 1) with
            | some exit => .pure exit
            | none => updateContextR (.provide ctx) (bodyAt (p.child 1))
          | none => .pure badShapeExit))
        (fun ex => .vis (.inr (.closeScope scope ex)) Effects.Program.pure)
    | none => .pure badShapeExit)

/-! The two denotations below carry the point's fuel as an explicit budget (`f`, always the
point's own fuel: `denoteR` and `denoteLayer` pass it in, and every child call passes the
child's). It is the recursion: a layer reference (`LayerTerm.ref`, the host rows slice) hops
to its target's term, which is no subterm, one fuel down, so the block is structural on the
budget, its arms at a positive budget in two bodies that take the predecessor budget's two
denotations as arguments (`denoteEffBody`, `denoteLayerBody`), and only
a layer at no fuel, whose children have none either, descends in its term
(`denoteLayerZero`). Structural recursion keeps every finite run reducible by `rfl`, which the
batteries pin (`Test/Program/RuntimeRContract.lean`); the equations below are the only
interface the proofs use. -/

/-- Whether a layer term is a reference. `compileLayer` compiles the inner term of `orDie`
directly (`Prim.onFailure (compileLayer inner …)`), never through `resolveLayer`, so a
reference there is the wrong shape it is at that table; the `orDie` arm of the build mirrors
that. -/
def _root_.Effect4.Program.LayerTerm.isRef {Op : Type} : LayerTerm Op → Bool
  | .ref _ => true
  | _ => false

/-- The arms of the denotation at a positive budget, every child at the predecessor budget
through `rec` (a program at its point) and `recL` (a layer at its point). Every arm names the `compileEff` arm it
mirrors; the counted checkpoints are where the frame machine spends a primitive that the term
would otherwise elide. -/
def denoteEffBody (root : NativeEff) (rec : NativeEff → Point → RProgram)
    (recL : LayerTerm NativeOp → Point → MemoMapId → Nat → RProgram) :
    NativeEff → Point → RProgram
  | .succeed t, p => .pure (match evalTerm p.env t with
      | some v => .success v | none => badShapeExit)
  | .fail t, p => .pure (match evalTerm p.env t with
      | some v => .failure (Cause.fail (errOf v)) | none => badShapeExit)
  | .failCause t, p => .pure (match causeOf p.env t with
      | some c => .failure c | none => badShapeExit)
  -- `Prim.yieldableError`: one counted step, then the failure.
  | .yieldError t, p => match evalTerm p.env t with
      | some v => suspendR p (.pure (.failure (Cause.fail (errOf v))))
      | none => .pure badShapeExit
  -- `Prim.sync (pure p)`: the value through the `answered` phase.
  | .sync t, p => .vis (.inr (.sync ((evalTerm p.env t).getD Val.unit))) fun v => .pure (.success v)
  -- `Prim.suspend (body child)`: the counted step, then the body.
  | .suspend b, p => suspendR p (constructR fun completed =>
      rec b ({ p with completed }.child 0))
  | .perform op request, p =>
    match op with
    | .external _ => denoteAsyncRoute op request p
    | _ => match (NativeOp.row op).kind with
      | .sync =>
        match (evalTerm p.env request).bind (NativeOp.syncOpOf op) with
        | some operation => .vis (.inl operation) fun v => .pure (.success v)
        | none => .pure badShapeExit
      | .async => denoteAsyncRoute op request p
      | .program => pending .unsupported p
  | .bind a b, p => (guardR .onSuccess (rec a (p.child 0))).bind
      (seqR fun v => constructR fun completed =>
        rec b ({ p with completed }.childWith 1 v))
  -- `Prim.suspend (body p)`, decided by `suspendBodyAt`: the counted step, then the branch.
  | .branch test a b, p => suspendR p (constructR fun completed => match evalTerm p.env test with
      | some (.bool true) => rec a ({ p with completed }.child 0)
      | some (.bool false) => rec b ({ p with completed }.child 1)
      | _ => .pure badShapeExit)
  -- `Effect.exit` folds an immediate exit; otherwise the both-arm boundary.
  | .exit b, p =>
    match inlineYield b (p.child 0) with
    | some ex => .pure (.success (reifyExitVal ex))
    | none => (guardR .all (rec b (p.child 0))).bind fun ex =>
        .pure (.success (reifyExitVal ex))
  | .catchCause b h, p => (guardR .onFailure (rec b (p.child 0))).bind fun
    | .success v => .pure (.success v)
    | .failure c => constructR fun completed =>
        rec h ({ p with completed }.childWith 1 (.exitErr c))
  | .catchIf test b h, p => (guardR .onFailure (rec b (p.child 0))).bind fun
    | .success v => .pure (.success v)
    | .failure cause => constructR fun completed =>
      match caughtErrorValue? p.env test cause with
      | some value => rec h ({ p with completed }.childWith 1 value)
      | none => .pure (.failure cause)
  | .matchCause b v c, p => (guardR .all (rec b (p.child 0))).bind fun
    | .success x => constructR fun completed =>
        rec v ({ p with completed }.childWith 1 x)
    | .failure cause => constructR fun completed =>
        rec c ({ p with completed }.childWith 2 (.exitErr cause))
  | .onExit b fin, p => onExitR (rec b (p.child 0)) fun ex =>
      constructR fun completed =>
        rec fin ({ p with completed }.childWith 1 (reifyExitVal ex))
  -- `Prim.suspend (body p)` then `Prim.iterator (gen p [] false) unit`: the entry.
  | .gen _, p => suspendR p (.vis (.inr (.gen p)) Effects.Program.pure)
  -- `Prim.suspend (body p)` then `Prim.whileLoop (loop p) cursor`: the entry.
  | .whileLoop initial _ _ _, p => suspendR p (match evalTerm p.env initial with
      | some cursor => .vis (.inr (.loop p cursor)) Effects.Program.pure
      | none => .pure badShapeExit)
  -- `Prim.yieldNowWith`: the park answers the void value, which the continuation passes
  -- on (the frame resumes with `success void`; an answer is never discarded)
  | .yieldNow priority, _ => .vis (.inr (.yieldNow priority)) fun v => .pure (.success v)
  | .callback op request, p => denoteAsyncRoute op request p
  | .awaitFiber target mode, p =>
    match evalTerm p.env target with
    | some (Val.fiber ⟨id⟩) =>
      match p.awaitExit ⟨id⟩ mode with
      | some exit => .pure exit
      | none => match mode with
        | .joinEffect => .vis (.inr (.await ⟨id⟩ .joinEffect)) Effects.Program.pure
        | .awaitValue => .vis (.inr (.await ⟨id⟩ .awaitValue)) fun v => .pure (.success v)
    | _ => .pure badShapeExit
  | .uninterruptible _, p | .interruptible _, p | .withFiber _, p => denoteAction root p
  -- `scoped` is one WithFiber whose eager body is child 0
  -- (`internal/effect.ts:3938-3948`). Context restoration is callback glue.
  | .scoped _, p => .vis (.inr (.scoped (p.child 0))) Effects.Program.pure
  -- `acquireRelease` (`internal/effect.ts:3971-3987`, V1): the context read, then the
  -- masked half (`Body.acquireIn`) under it, as `compileEff` names it step by step
  | .acquireRelease _ _, p =>
    (guardR .onSuccess (fiberValR .getContext rfl)).bind (seqR fun v =>
      match Val.context? v with
      | some ctx => .vis (.inr (.mask false (.acquireIn p ctx))) Effects.Program.pure
      | none => .pure badShapeExit)
  -- the join. `Effect.provide(self, layer)`: `Prim.suspend (body p)`, the counted step
  -- (`scopedWith`, `internal/effect.ts:3966`), then the scope made, the layer built into it
  -- (`buildWithScope` off the context's memo map, or a private map when `local`), the body
  -- under `provideContext(built)` (`internal/layer.ts:15-21`), the scope closed with the exit
  | .provideLayer layer isLocal body, p => suspendR p (constructR fun completed =>
      provideLayerR (fun q m s => recL layer q m s) (fun q => rec body q)
        (fun q => inlineYield body q) isLocal { p with completed })
  -- `Effect.service(key)` (`internal/effect.ts:2059`): the context read, then the lookup
  | .service key, _ =>
    (guardR .onSuccess (fiberValR .getContext rfl)).bind (seqR fun v => serviceLookupR key v)
  -- `Effect.provideService(self, key, value)` (`:2232`): a `Context.add` region
  | .provideService key value body, p =>
    match evalTerm p.env value with
    | some v => updateContextR (.provideService key v) (rec body (p.child 0))
    | none => .pure badShapeExit

/-- `self.build(memoMap, scope)` at the term (`compileLayer`, `innerLayerAt`, `constructionAt`),
the arms at a positive budget, every child at the predecessor budget through `recL`, a leaf's
body through `rec`: `Layer.succeed` answers its context (`Layer.ts:1129`); `fresh` builds the
inner layer through a brand-new map (`:3851`); `orDie` turns the inner build's typed error into
a defect (`:3327`), its inner term compiled directly as `compileLayer` compiles it, so a
reference there is the wrong shape; every other constructor is a `fromBuild` wrapper
(`:333-345`) — a memoized leaf's construction under `Scope.provide` (`:386`, `:1482`),
`provideWith` (`:1915`), or `mergeAllEffect` (`:1587`, binary and n-ary). A reference hops to
its target's term at the target's path one fuel down (`resolveLayer.resolveLayerTerm`, the
predecessor budget); a hop to a reference or to no layer is the wrong shape. -/
def denoteLayerBody (root : NativeEff) (rec : NativeEff → Point → RProgram)
    (recL : LayerTerm NativeOp → Point → MemoMapId → Nat → RProgram) :
    LayerTerm NativeOp → Point → MemoMapId → Nat → RProgram
  | .succeed key value, _, _, _ =>
    match Lit.toVal value with
    | some v => .pure (.success (Env.encode (Env.Context.empty.addV key v)))
    | none => .pure badShapeExit
  | .fresh inner, q, _, scope =>
    (guardR .onSuccess (storeR (.memoFork none))).bind (seqR fun v =>
      match Val.memoMap? v with
      | some id => recL inner (q.child 0) id scope
      | none => .pure badShapeExit)
  -- the inner term is compiled at the table directly (`compileLayer`'s `orDie` arm), never
  -- resolved: a reference there is the wrong shape
  | .orDie inner, q, m, scope =>
    (guardR .onFailure
      (if inner.isRef then .pure badShapeExit else recL inner (q.child 0) m scope)).bind fun
      | .success v => .pure (.success v)
      | .failure c => .pure (.failure (orDieCause c))
  | .effect key body, q, m, scope =>
    fromBuildR scope fun child => memoizeR q m child fun layerScope =>
      updateContextR (.provideService Env.scopeKey (Val.scopeHandle layerScope))
        ((guardR .onSuccess (rec body (q.child 0))).bind (seqR fun v =>
          bindServiceR (some key) v))
  | .effectDiscard body, q, m, scope =>
    fromBuildR scope fun child => memoizeR q m child fun layerScope =>
      updateContextR (.provideService Env.scopeKey (Val.scopeHandle layerScope))
        ((guardR .onSuccess (rec body (q.child 0))).bind (seqR fun v =>
          bindServiceR none v))
  | .provide self that, q, m, scope =>
    fromBuildR scope fun child =>
      provideWithR (recL that (q.child 1) m child) (recL self (q.child 0) m child) .provide
  | .provideMerge self that, q, m, scope =>
    fromBuildR scope fun child =>
      provideWithR (recL that (q.child 1) m child) (recL self (q.child 0) m child) .provideMerge
  | .merge _ _, q, m, scope => fromBuildR scope fun child => mergeTwoR q m child
  | .mergeAll layers, q, m, scope =>
    fromBuildR scope fun child => mergeAllR q m child layers.length
  | .ref target, q, m, scope =>
    match Node.at_ (Node.eff root) target with
    | some (Node.layer (.ref _)) => .pure badShapeExit
    | some (Node.layer l) => recL l (q.redirect target) m scope
    | _ => .pure badShapeExit

/-- A layer's build with no fuel: the arms of `denoteLayerBody`, every child at no fuel either
(a `Point.child` of a point without fuel has none), a leaf's body the frontier at its point,
and a reference the frontier at its own point (no fuel for the hop; DB-04: fuel exhaustion is
never an error). Structural in the term, which is the descent the budget cannot make. -/
def denoteLayerZero (root : NativeEff) : LayerTerm NativeOp → Point → MemoMapId → Nat → RProgram
  | .succeed key value, _, _, _ =>
    match Lit.toVal value with
    | some v => .pure (.success (Env.encode (Env.Context.empty.addV key v)))
    | none => .pure badShapeExit
  | .fresh inner, q, _, scope =>
    (guardR .onSuccess (storeR (.memoFork none))).bind (seqR fun v =>
      match Val.memoMap? v with
      | some id => denoteLayerZero root inner (q.child 0) id scope
      | none => .pure badShapeExit)
  | .orDie inner, q, m, scope =>
    (guardR .onFailure
      (if inner.isRef then .pure badShapeExit
       else denoteLayerZero root inner (q.child 0) m scope)).bind fun
      | .success v => .pure (.success v)
      | .failure c => .pure (.failure (orDieCause c))
  | .effect key body, q, m, scope =>
    fromBuildR scope fun child => memoizeR q m child fun layerScope =>
      updateContextR (.provideService Env.scopeKey (Val.scopeHandle layerScope))
        ((guardR .onSuccess (pending .compileFuel (q.child 0))).bind (seqR fun v =>
          bindServiceR (some key) v))
  | .effectDiscard body, q, m, scope =>
    fromBuildR scope fun child => memoizeR q m child fun layerScope =>
      updateContextR (.provideService Env.scopeKey (Val.scopeHandle layerScope))
        ((guardR .onSuccess (pending .compileFuel (q.child 0))).bind (seqR fun v =>
          bindServiceR none v))
  | .provide self that, q, m, scope =>
    fromBuildR scope fun child =>
      provideWithR (denoteLayerZero root that (q.child 1) m child)
        (denoteLayerZero root self (q.child 0) m child) .provide
  | .provideMerge self that, q, m, scope =>
    fromBuildR scope fun child =>
      provideWithR (denoteLayerZero root that (q.child 1) m child)
        (denoteLayerZero root self (q.child 0) m child) .provideMerge
  | .merge _ _, q, m, scope => fromBuildR scope fun child => mergeTwoR q m child
  | .mergeAll layers, q, m, scope =>
    fromBuildR scope fun child => mergeAllR q m child layers.length
  | .ref _, q, _, _ => pending .compileFuel q

mutual
/-- The structural denotation at an address, at the point's fuel as its budget: the frontier
with none, else the arms at the predecessor budget's denotations. -/
def denoteRWith (root : NativeEff) : Nat → NativeEff → Point → RProgram
  | 0, _, p => pending .compileFuel p
  | f + 1, e, p => denoteEffBody root (denoteRWith root f) (denoteLayerWith root f) e p

/-- A layer's build at its point, at the point's fuel as its budget: the build with no fuel,
else the arms at the predecessor budget's denotations (a reference's hop lands there). -/
def denoteLayerWith (root : NativeEff) :
    Nat → LayerTerm NativeOp → Point → MemoMapId → Nat → RProgram
  | 0, l, q, m, scope => denoteLayerZero root l q m scope
  | f + 1, l, q, m, scope =>
    denoteLayerBody root (denoteRWith root f) (denoteLayerWith root f) l q m scope
end

/-- The structural denotation at an address: `denoteRWith` at the point's fuel. -/
def denoteR (root : NativeEff) (e : NativeEff) (p : Point) : RProgram := denoteRWith root p.fuel e p

/-- The build of a layer term at its point: `denoteLayerWith` at the point's fuel. -/
def denoteLayer (root : NativeEff) (l : LayerTerm NativeOp) (q : Point) (m : MemoMapId)
    (scope : Nat) : RProgram :=
  denoteLayerWith root q.fuel l q m scope

/-- A child point's fuel is one less: the budget of every child call. -/
theorem Point.child_fuel (p : Point) (i : Nat) : (p.child i).fuel = p.fuel - 1 := rfl
theorem Point.childWith_fuel (p : Point) (i : Nat) (v : Val) : (p.childWith i v).fuel = p.fuel - 1 := rfl
theorem Point.redirect_fuel (p : Point) (target : List Nat) : (p.redirect target).fuel = p.fuel - 1 := rfl
theorem Point.completed_fuel (p : Point) (completed : List (FiberId × ExitV)) :
    ({ p with completed } : Point).fuel = p.fuel := rfl

/-! ## The address and frontier equations -/

/-- The one budget arithmetic every equation below needs: a child's budget is the parent's
predecessor, which at a positive fuel `f + 1` is `f`. -/
local macro "budget" hf:ident : tactic => `(tactic|
  simp only [denoteR, denoteLayer, $hf:ident, Point.child_fuel, Point.childWith_fuel,
    Point.completed_fuel, Point.redirect_fuel, Nat.add_sub_cancel, denoteRWith, denoteEffBody])

theorem denoteR_zero (root e : NativeEff) (p : Point) (h : p.fuel = 0) :
    denoteR root e p = pending .compileFuel p := by
  simp only [denoteR, h, denoteRWith]

theorem denoteR_bind (root : NativeEff) (a b : NativeEff) (p : Point) (h : p.fuel ≠ 0) :
    denoteR root (.bind a b) p =
      (guardR .onSuccess (denoteR root a (p.child 0))).bind
        (seqR fun v => constructR fun completed =>
          denoteR root b ({ p with completed }.childWith 1 v)) := by
  cases hf : p.fuel with
  | zero => exact (h hf).elim
  | succ f => budget hf

theorem denoteR_suspend (root : NativeEff) (b : NativeEff) (p : Point) (h : p.fuel ≠ 0) :
    denoteR root (.suspend b) p = suspendR p (constructR fun completed =>
      denoteR root b ({ p with completed }.child 0)) := by
  cases hf : p.fuel with
  | zero => exact (h hf).elim
  | succ f => budget hf

theorem denoteR_branch (root : NativeEff) (t : Term) (a b : NativeEff) (p : Point)
    (h : p.fuel ≠ 0) :
    denoteR root (.branch t a b) p =
      suspendR p (constructR fun completed => match evalTerm p.env t with
        | some (.bool true) => denoteR root a ({ p with completed }.child 0)
        | some (.bool false) => denoteR root b ({ p with completed }.child 1)
        | _ => .pure badShapeExit) := by
  cases hf : p.fuel with
  | zero => exact (h hf).elim
  | succ f => budget hf

/-- The exit arm: an immediate exit folds (row D1 of the P0 record); otherwise the body
runs inside a both-arm boundary and its exit is reified. -/
theorem denoteR_exit (root : NativeEff) (b : NativeEff) (p : Point) (h : p.fuel ≠ 0) :
    denoteR root (.exit b) p =
      match inlineYield b (p.child 0) with
      | some ex => .pure (.success (reifyExitVal ex))
      | none => (guardR .all (denoteR root b (p.child 0))).bind fun ex =>
          .pure (.success (reifyExitVal ex)) := by
  cases hf : p.fuel with
  | zero => exact (h hf).elim
  | succ f => budget hf

theorem denoteR_withFiber (root : NativeEff) (action : ActionTerm NativeOp) (p : Point)
    (h : p.fuel ≠ 0) :
    denoteR root (.withFiber action) p = denoteAction root p := by
  cases hf : p.fuel with
  | zero => exact (h hf).elim
  | succ f => budget hf

theorem denoteR_gen (root : NativeEff) (body : Stmts NativeOp) (p : Point) (h : p.fuel ≠ 0) :
    denoteR root (.gen body) p = suspendR p (.vis (.inr (.gen p)) Effects.Program.pure) := by
  cases hf : p.fuel with
  | zero => exact (h hf).elim
  | succ f => budget hf

theorem denoteR_whileLoop (root : NativeEff) (initial test step : Term) (body : NativeEff)
    (p : Point) (h : p.fuel ≠ 0) :
    denoteR root (.whileLoop initial test step body) p =
      suspendR p (match evalTerm p.env initial with
        | some cursor => .vis (.inr (.loop p cursor)) Effects.Program.pure
        | none => .pure badShapeExit) := by
  cases hf : p.fuel with
  | zero => exact (h hf).elim
  | succ f => budget hf

/-! ## The denotation, one arm at a time, at positive fuel

Every arm of `denoteRWith` as an equation of `denoteR` at the point's own fuel, the child
calls spelled with `denoteR` at the child points; nothing downstream unfolds the block. -/

section denoteEqs

variable (root : NativeEff) {p : Point}

theorem denoteR_succeed (t : Term) (h : p.fuel ≠ 0) :
    denoteR root (.succeed t) p =
      .pure (match evalTerm p.env t with | some v => .success v | none => badShapeExit) := by
  cases hf : p.fuel with
  | zero => exact (h hf).elim
  | succ f => budget hf; try rfl

theorem denoteR_fail (t : Term) (h : p.fuel ≠ 0) :
    denoteR root (.fail t) p =
      .pure (match evalTerm p.env t with
        | some v => .failure (Cause.fail (errOf v)) | none => badShapeExit) := by
  cases hf : p.fuel with
  | zero => exact (h hf).elim
  | succ f => budget hf; try rfl

theorem denoteR_failCause (c : CauseTerm) (h : p.fuel ≠ 0) :
    denoteR root (.failCause c) p =
      .pure (match causeOf p.env c with | some cause => .failure cause | none => badShapeExit) := by
  cases hf : p.fuel with
  | zero => exact (h hf).elim
  | succ f => budget hf; try rfl

theorem denoteR_yieldError (t : Term) (h : p.fuel ≠ 0) :
    denoteR root (.yieldError t) p =
      (match evalTerm p.env t with
       | some v => suspendR p (.pure (.failure (Cause.fail (errOf v))))
       | none => .pure badShapeExit) := by
  cases hf : p.fuel with
  | zero => exact (h hf).elim
  | succ f => budget hf; try rfl

theorem denoteR_sync (t : Term) (h : p.fuel ≠ 0) :
    denoteR root (.sync t) p =
      .vis (.inr (.sync ((evalTerm p.env t).getD Val.unit))) fun v => .pure (.success v) := by
  cases hf : p.fuel with
  | zero => exact (h hf).elim
  | succ f => budget hf; try rfl

theorem denoteR_perform (op : NativeOp) (r : Term) (h : p.fuel ≠ 0) :
    denoteR root (.perform op r) p =
      (match op with
       | .external _ => denoteAsyncRoute op r p
       | _ => match (NativeOp.row op).kind with
         | .sync =>
           match (evalTerm p.env r).bind (NativeOp.syncOpOf op) with
           | some operation => .vis (.inl operation) fun v => .pure (.success v)
           | none => .pure badShapeExit
         | .async => denoteAsyncRoute op r p
         | .program => pending .unsupported p) := by
  cases hf : p.fuel with
  | zero => exact (h hf).elim
  | succ f => budget hf; try rfl

/-- The synchronous fragment retains its old semantic head under external-first routing. -/
theorem denoteR_perform_sync (op : NativeOp) (r : Term) (h : p.fuel ≠ 0)
    (hk : (NativeOp.row op).kind = .sync) :
    denoteR root (.perform op r) p =
      (match (evalTerm p.env r).bind (NativeOp.syncOpOf op) with
       | some operation => .vis (.inl operation) fun v => .pure (.success v)
       | none => .pure badShapeExit) := by
  rw [denoteR_perform root op r h]
  cases op with
  | scopeMake strategy => cases strategy <;> rfl
  | external _ => cases hk
  | _ => simp_all [NativeOp.row] <;> rfl

theorem denoteR_catchCause (b hd : NativeEff) (h : p.fuel ≠ 0) :
    denoteR root (.catchCause b hd) p =
      (guardR .onFailure (denoteR root b (p.child 0))).bind fun
        | .success v => .pure (.success v)
        | .failure c => constructR fun completed =>
            denoteR root hd ({ p with completed }.childWith 1 (.exitErr c)) := by
  cases hf : p.fuel with
  | zero => exact (h hf).elim
  | succ f => budget hf; try rfl

theorem denoteR_catchIf (test : Term) (b hd : NativeEff) (h : p.fuel ≠ 0) :
    denoteR root (.catchIf test b hd) p =
      (guardR .onFailure (denoteR root b (p.child 0))).bind fun
        | .success v => .pure (.success v)
        | .failure cause => constructR fun completed =>
          match caughtErrorValue? p.env test cause with
          | some value => denoteR root hd ({ p with completed }.childWith 1 value)
          | none => .pure (.failure cause) := by
  cases hf : p.fuel with
  | zero => exact (h hf).elim
  | succ f => budget hf; try rfl

theorem denoteR_matchCause (b v c : NativeEff) (h : p.fuel ≠ 0) :
    denoteR root (.matchCause b v c) p =
      (guardR .all (denoteR root b (p.child 0))).bind fun
        | .success x => constructR fun completed =>
            denoteR root v ({ p with completed }.childWith 1 x)
        | .failure cause => constructR fun completed =>
            denoteR root c ({ p with completed }.childWith 2 (.exitErr cause)) := by
  cases hf : p.fuel with
  | zero => exact (h hf).elim
  | succ f => budget hf; try rfl

theorem denoteR_onExit (b f : NativeEff) (h : p.fuel ≠ 0) :
    denoteR root (.onExit b f) p =
      onExitR (denoteR root b (p.child 0)) fun ex =>
        constructR fun completed => denoteR root f ({ p with completed }.childWith 1 (reifyExitVal ex)) := by
  cases hf : p.fuel with
  | zero => exact (h hf).elim
  | succ f => budget hf; try rfl

theorem denoteR_yieldNow (priority : Nat) (h : p.fuel ≠ 0) :
    denoteR root (.yieldNow priority) p =
      .vis (.inr (.yieldNow priority)) fun v => .pure (.success v) := by
  cases hf : p.fuel with
  | zero => exact (h hf).elim
  | succ f => budget hf; try rfl

theorem denoteR_callback (op : NativeOp) (r : Term) (h : p.fuel ≠ 0) :
    denoteR root (.callback op r) p =
      (match op with
       | .external _ => denoteForeign op r p
       | .sleep => denoteSleep r p
       | _ => match (NativeOp.row op).kind with
         | .async => denoteAsync r p
         | _ => .pure badShapeExit) := by
  cases hf : p.fuel with
  | zero => exact (h hf).elim
  | succ f => cases op <;> (budget hf; try rfl)

theorem denoteR_awaitFiber (t : Term) (mode : Supervision.ObserverMode) (h : p.fuel ≠ 0) :
    denoteR root (.awaitFiber t mode) p =
      (match evalTerm p.env t with
       | some (Val.fiber ⟨id⟩) =>
         match p.awaitExit ⟨id⟩ mode with
         | some exit => .pure exit
         | none => match mode with
           | .joinEffect => .vis (.inr (.await ⟨id⟩ .joinEffect)) Effects.Program.pure
           | .awaitValue => .vis (.inr (.await ⟨id⟩ .awaitValue)) fun v => .pure (.success v)
       | _ => .pure badShapeExit) := by
  cases hf : p.fuel with
  | zero => exact (h hf).elim
  | succ f => budget hf; try rfl

theorem denoteR_uninterruptible (b : NativeEff) (h : p.fuel ≠ 0) :
    denoteR root (.uninterruptible b) p = denoteAction root p := by
  cases hf : p.fuel with
  | zero => exact (h hf).elim
  | succ f => budget hf; try rfl

theorem denoteR_interruptible (b : NativeEff) (h : p.fuel ≠ 0) :
    denoteR root (.interruptible b) p = denoteAction root p := by
  cases hf : p.fuel with
  | zero => exact (h hf).elim
  | succ f => budget hf; try rfl

theorem denoteR_scoped (b : NativeEff) (h : p.fuel ≠ 0) :
    denoteR root (.scoped b) p = .vis (.inr (.scoped (p.child 0))) Effects.Program.pure := by
  cases hf : p.fuel with
  | zero => exact (h hf).elim
  | succ f => budget hf; try rfl

theorem denoteR_acquireRelease (a r : NativeEff) (h : p.fuel ≠ 0) :
    denoteR root (.acquireRelease a r) p =
      (guardR .onSuccess (fiberValR .getContext rfl)).bind (seqR fun v =>
        match Val.context? v with
        | some ctx => .vis (.inr (.mask false (.acquireIn p ctx))) Effects.Program.pure
        | none => .pure badShapeExit) := by
  cases hf : p.fuel with
  | zero => exact (h hf).elim
  | succ f => budget hf; try rfl

-- the join's three constructors. The layer's build and the body are the term's own at their
-- points: `provideLayerR` applies them at the children of the counted point, whose fuel is
-- the budget the block passes, so the equation holds after unfolding the protocol.
theorem denoteR_provideLayer (l : LayerTerm NativeOp) (i : Bool) (b : NativeEff) (h : p.fuel ≠ 0) :
    denoteR root (.provideLayer l i b) p =
      suspendR p (constructR fun completed =>
        provideLayerR (fun q m s => denoteLayer root l q m s) (fun q => denoteR root b q)
          (fun q => inlineYield b q) i { p with completed }) := by
  cases hf : p.fuel with
  | zero => exact (h hf).elim
  | succ f =>
    simp only [denoteR, denoteLayer, hf, Point.child_fuel, Nat.add_sub_cancel, denoteRWith,
      denoteEffBody, provideLayerR]
    try rfl

theorem denoteR_service (key : ServiceKey) (h : p.fuel ≠ 0) :
    denoteR root (.service key) p =
      (guardR .onSuccess (fiberValR .getContext rfl)).bind (seqR fun v => serviceLookupR key v) := by
  cases hf : p.fuel with
  | zero => exact (h hf).elim
  | succ f => budget hf; try rfl

theorem denoteR_provideService (key : ServiceKey) (value : Term) (b : NativeEff)
    (h : p.fuel ≠ 0) :
    denoteR root (.provideService key value b) p =
      (match evalTerm p.env value with
       | some v => updateContextR (.provideService key v) (denoteR root b (p.child 0))
       | none => .pure badShapeExit) := by
  cases hf : p.fuel with
  | zero => exact (h hf).elim
  | succ f => budget hf; try rfl

end denoteEqs

/-! ## The build, one constructor at a time

Every arm of `denoteLayerWith` as an equation of `denoteLayer` at the point's own fuel, the
child calls spelled with `denoteLayer` (and `denoteR`) at the child points. A reference's two
arms are the frontier at fuel zero and the hop to the target's term at `Point.redirect`. -/

/-- The layer equations' budget split: with no fuel the build is `denoteLayerZero`, with
`f + 1` the body at budget `f`; on either side the children's spelling meets the child
points' fuel (`0 - 1 = 0`, `f + 1 - 1 = f`). -/
local macro "layerBudget" q:ident : tactic => `(tactic|
  (cases hf : ($q).fuel with
   | zero =>
     simp only [denoteLayer, denoteR, hf, Point.child_fuel, Point.redirect_fuel, Nat.zero_sub,
       denoteLayerWith, denoteRWith, denoteLayerZero]
   | succ f =>
     simp only [denoteLayer, denoteR, hf, Point.child_fuel, Point.redirect_fuel,
       Nat.add_sub_cancel, denoteLayerWith, denoteRWith, denoteLayerBody]))

section denoteLayerEqs

variable (root : NativeEff)

theorem denoteLayer_succeed (key : ServiceKey) (value : Lit) (q : Point) (m : MemoMapId)
    (scope : Nat) :
    denoteLayer root (.succeed key value) q m scope =
      (match Lit.toVal value with
       | some v => .pure (.success (Env.encode (Env.Context.empty.addV key v)))
       | none => .pure badShapeExit) := by
  layerBudget q

theorem denoteLayer_fresh (inner : LayerTerm NativeOp) (q : Point) (m : MemoMapId) (scope : Nat) :
    denoteLayer root (.fresh inner) q m scope =
      (guardR .onSuccess (storeR (.memoFork none))).bind (seqR fun v =>
        match Val.memoMap? v with
        | some id => denoteLayer root inner (q.child 0) id scope
        | none => .pure badShapeExit) := by
  layerBudget q

theorem denoteLayer_orDie (inner : LayerTerm NativeOp) (q : Point) (m : MemoMapId) (scope : Nat) :
    denoteLayer root (.orDie inner) q m scope =
      (guardR .onFailure
        (if inner.isRef then .pure badShapeExit
         else denoteLayer root inner (q.child 0) m scope)).bind fun
        | .success v => .pure (.success v)
        | .failure c => .pure (.failure (orDieCause c)) := by
  layerBudget q

theorem denoteLayer_effect (key : ServiceKey) (body : NativeEff) (q : Point) (m : MemoMapId)
    (scope : Nat) :
    denoteLayer root (.effect key body) q m scope =
      fromBuildR scope fun child => memoizeR q m child fun layerScope =>
        updateContextR (.provideService Env.scopeKey (Val.scopeHandle layerScope))
          ((guardR .onSuccess (denoteR root body (q.child 0))).bind (seqR fun v =>
            bindServiceR (some key) v)) := by
  layerBudget q

theorem denoteLayer_effectDiscard (body : NativeEff) (q : Point) (m : MemoMapId) (scope : Nat) :
    denoteLayer root (.effectDiscard body) q m scope =
      fromBuildR scope fun child => memoizeR q m child fun layerScope =>
        updateContextR (.provideService Env.scopeKey (Val.scopeHandle layerScope))
          ((guardR .onSuccess (denoteR root body (q.child 0))).bind (seqR fun v =>
            bindServiceR none v)) := by
  layerBudget q

theorem denoteLayer_provide (self that : LayerTerm NativeOp) (q : Point) (m : MemoMapId)
    (scope : Nat) :
    denoteLayer root (.provide self that) q m scope =
      fromBuildR scope fun child =>
        provideWithR (denoteLayer root that (q.child 1) m child)
          (denoteLayer root self (q.child 0) m child) .provide := by
  layerBudget q

theorem denoteLayer_provideMerge (self that : LayerTerm NativeOp) (q : Point) (m : MemoMapId)
    (scope : Nat) :
    denoteLayer root (.provideMerge self that) q m scope =
      fromBuildR scope fun child =>
        provideWithR (denoteLayer root that (q.child 1) m child)
          (denoteLayer root self (q.child 0) m child) .provideMerge := by
  layerBudget q

theorem denoteLayer_merge (left right : LayerTerm NativeOp) (q : Point) (m : MemoMapId)
    (scope : Nat) :
    denoteLayer root (.merge left right) q m scope =
      fromBuildR scope fun child => mergeTwoR q m child := by
  layerBudget q

theorem denoteLayer_mergeAll (layers : LayerTerms NativeOp) (q : Point) (m : MemoMapId)
    (scope : Nat) :
    denoteLayer root (.mergeAll layers) q m scope =
      fromBuildR scope fun child => mergeAllR q m child layers.length := by
  layerBudget q

/-- A reference with no fuel for its hop: the live frontier at the reference's own point. -/
theorem denoteLayer_ref_zero (target : List Nat) (q : Point) (m : MemoMapId) (scope : Nat)
    (hf : q.fuel = 0) :
    denoteLayer root (.ref target) q m scope = pending .compileFuel q := by
  simp only [denoteLayer, hf, denoteLayerWith, denoteLayerZero]

/-- A reference with fuel hops to its target's term at the target's path, one fuel down; a
target that is a reference itself, or no layer, is the wrong shape. -/
theorem denoteLayer_ref_succ (target : List Nat) (q : Point) (m : MemoMapId) (scope : Nat)
    {k : Nat} (hf : q.fuel = k + 1) :
    denoteLayer root (.ref target) q m scope =
      (match Node.at_ (Node.eff root) target with
       | some (Node.layer (.ref _)) => .pure badShapeExit
       | some (Node.layer l) => denoteLayer root l (q.redirect target) m scope
       | _ => .pure badShapeExit) := by
  simp only [denoteLayer, hf, Point.redirect_fuel, Nat.add_sub_cancel, denoteLayerWith,
    denoteLayerBody]; try rfl

end denoteLayerEqs

/-- Only the two immediate exit constructors; all other heads require a machine step. -/
def headExit : NCode → Option ExitV
  | .success v => some (.success v)
  | .failure c => some (.failure c)
  | _ => none

theorem headExit_eq_asExit? (c : NCode) : headExit c = c.asExit? := by
  cases c <;> rfl

/-- The synchronous classifier and code use the same request/operation decoding. -/
theorem inlineSyncYield_eq_headExit (op : NativeOp) (request : Term) (p : Point) :
    (match (evalTerm p.env request).bind (NativeOp.syncOpOf op) with
     | some _ => none | none => some badShapeExit) =
      headExit (match evalTerm p.env request with
        | some value => match NativeOp.syncOpOf op value with
          | some operation => Prim.sync (EffThunk.op operation)
          | none => badShape
        | none => badShape) := by
  cases hv : evalTerm p.env request with
  | none => rfl
  | some value =>
    dsimp only [Option.bind]
    cases NativeOp.syncOpOf op value <;> rfl

/-- The shared route's source classifier agrees with its immediate compiled exit. -/
theorem inlineAsyncYield_eq_headExit (op : NativeOp) (request : Term) (p : Point) :
    inlineAsyncYield op request p = headExit (asyncRoute op request p) := by
  cases op
  all_goals simp only [inlineAsyncYield, asyncRoute]
  case external i => cases evalTerm p.env request <;> rfl
  case sleep =>
    cases (evalTerm p.env request).bind NativeOp.sleepMillisOf with
    | none => rfl
    | some n => cases n <;> rfl
  all_goals first
    | rfl
    | (cases (evalTerm p.env request).bind NativeOp.awaitCellOf <;> rfl)
    | (rename_i strategy; cases strategy <;> rfl)

theorem inlineYield_eq_headExit (e : NativeEff) (p : Point) :
    inlineYield e p = headExit (compileEff e p) := by
  cases hf : p.fuel with
  | zero =>
    have hc : ∀ e, compileEff e p = frontier p := fun e => by unfold compileEff; rw [hf]
    cases e <;> simp only [inlineYield, hf, ↓reduceIte, hc, frontier, headExit]
  | succ f =>
    cases e with
    | exit b =>
      simp only [inlineYield, compileEff, hf, Nat.succ_ne_zero, ↓reduceIte]
      rw [inlineYield_eq_headExit b (p.child 0), headExit_eq_asExit? (compileEff b (p.child 0))]
      cases hx : (compileEff b (p.child 0)).asExit? <;> rfl
    | perform op request =>
      cases op
      all_goals unfold compileEff; rw [hf]
      all_goals simp only [inlineYield, hf, Nat.succ_ne_zero, ↓reduceIte]
      case external i => exact inlineAsyncYield_eq_headExit (.external i) request p
      case sleep => exact inlineAsyncYield_eq_headExit .sleep request p
      case deferredAwait => exact inlineAsyncYield_eq_headExit .deferredAwait request p
      all_goals first
        | exact inlineSyncYield_eq_headExit _ request p
        | (rename_i strategy; cases strategy <;> exact inlineSyncYield_eq_headExit _ request p)
    | callback op request =>
      simp only [inlineYield, compileEff, hf, Nat.succ_ne_zero, ↓reduceIte]
      exact inlineAsyncYield_eq_headExit op request p
    | succeed t | fail t | yieldError t =>
      simp only [inlineYield, compileEff, hf, Nat.succ_ne_zero, ↓reduceIte]
      cases evalTerm p.env t <;> rfl
    | failCause c =>
      simp only [inlineYield, compileEff, hf, Nat.succ_ne_zero, ↓reduceIte]
      cases causeOf p.env c <;> rfl
    | awaitFiber target mode =>
      simp only [inlineYield, compileEff, hf, Nat.succ_ne_zero, ↓reduceIte]
      cases evalTerm p.env target with
      | none => rfl
      | some v =>
        -- the value is a fiber handle (kind byte 1) or it is not, decided by `Val.fiber?`;
        -- both sides match on that
        cases hfib : Val.fiber? v with
        | some id =>
          obtain ⟨id⟩ := id
          have hv := Val.fiber?_exact hfib
          subst hv
          simp only
          cases hx : p.awaitExit ⟨id⟩ mode with
          | none => rfl
          | some ex => cases ex <;> rfl
        | none =>
          have hb : ∀ id, v ≠ Val.fiber ⟨id⟩ := fun id => Val.fiber?_none hfib ⟨id⟩
          split
          · next id heq => exact absurd (Option.some.inj heq) (hb id)
          · split
            · next id heq => exact absurd (Option.some.inj heq) (hb id)
            · rfl
    -- a `forkScoped` node compiles to its wrapper's `OnSuccess` (§20); every other action
    -- to the `WithFiber`; neither is an immediate exit
    | withFiber a =>
      cases a <;> simp only [inlineYield, compileEff, hf, Nat.succ_ne_zero, ↓reduceIte, headExit]
    | provideService key value body =>
      simp only [inlineYield, compileEff, hf, Nat.succ_ne_zero, ↓reduceIte]
      cases evalTerm p.env value <;> rfl
    | sync _ | suspend _ | bind _ _ | gen _ | catchCause _ _ | catchIf _ _ _ | matchCause _ _ _
    | onExit _ _ | uninterruptible _ | interruptible _ | branch _ _ _ | whileLoop _ _ _ _
    | yieldNow _ | «scoped» _ | acquireRelease _ _ | provideLayer _ _ _ | service _ =>
      simp only [inlineYield, compileEff, hf, Nat.succ_ne_zero, ↓reduceIte, headExit, frontier]
termination_by structural e

/-- The synchronous classifier is unchanged by the shared async route. -/
theorem inlineYield_perform_sync (op : NativeOp) (r : Term) (q : Point)
    (hk : (NativeOp.row op).kind = .sync) :
    inlineYield (.perform op r) q =
      if q.fuel = 0 then none else
        match (evalTerm q.env r).bind (NativeOp.syncOpOf op) with
        | some _ => none | none => some badShapeExit := by
  cases op with
  | scopeMake strategy => cases strategy <;> rfl
  | external _ => cases hk
  | _ => simp_all [NativeOp.row, inlineYield] <;> rfl

/-- A straight source form that `inlineYield` classifies as an immediate exit denotes to
exactly that exit: the fold of `denoteR`'s `exit` arm is the body's straight meaning. -/
theorem denote_of_inlineYield : ∀ (b : NativeEff) (q : Point) {exit : ExitV},
    Straight b = true → inlineYield b q = some exit → denote b q.env = Effects.Program.pure exit
  | .succeed t, q, exit, _, h => by
    simp only [inlineYield] at h
    split at h
    · cases h
    · simp only [Option.some.injEq] at h
      subst h
      rfl
  | .fail t, q, exit, _, h => by
    simp only [inlineYield] at h
    split at h
    · cases h
    · simp only [Option.some.injEq] at h
      subst h
      rfl
  | .failCause c, q, exit, _, h => by
    simp only [inlineYield] at h
    split at h
    · cases h
    · simp only [Option.some.injEq] at h
      subst h
      rfl
  | .yieldError t, q, exit, _, h => by
    simp only [inlineYield] at h
    split at h
    · cases h
    · rcases hx : evalTerm q.env t with _ | x
      · simp only [hx, Option.some.injEq] at h
        subst h
        simp only [denote, hx]
        rfl
      · simp [hx] at h
  | .perform op r, q, exit, hs, h => by
    have hk := Straight.perform_sync hs
    rw [inlineYield_perform_sync op r q hk] at h
    split at h
    · cases h
    · rcases hx : evalTerm q.env r with _ | x
      · simp only [hx, Option.bind, Option.some.injEq] at h
        subst h
        simp only [denote, hk, hx, Option.bind]
        rfl
      · rcases ho : NativeOp.syncOpOf op x with _ | o
        · simp only [hx, ho, Option.bind, Option.some.injEq] at h
          subst h
          simp only [denote, hk, hx, ho, Option.bind]
          rfl
        · simp [hx, ho] at h
  | .exit b, q, exit, hs, h => by
    simp only [inlineYield] at h
    split at h
    · cases h
    · rcases hy : inlineYield b (q.child 0) with _ | inner
      · simp [hy] at h
      · simp only [hy, Option.map, Option.some.injEq] at h
        subst h
        have hd : denote b q.env = Effects.Program.pure inner :=
          denote_of_inlineYield b (q.child 0) hs hy
        rw [denote, hd]
        rfl
  | .sync _, q, exit, _, h | .suspend _, q, exit, _, h | .bind _ _, q, exit, _, h
  | .branch _ _ _, q, exit, _, h | .catchCause _ _, q, exit, _, h
  | .matchCause _ _ _, q, exit, _, h | .onExit _ _, q, exit, _, h => by
    simp [inlineYield] at h
  | .gen _, _, _, hs, _ | .uninterruptible _, _, _, hs, _ | .interruptible _, _, _, hs, _
  | .whileLoop _ _ _ _, _, _, hs, _ | .yieldNow _, _, _, hs, _ | .callback _ _, _, _, hs, _
  | .awaitFiber _ _, _, _, hs, _ | .withFiber _, _, _, hs, _ | .«scoped» _, _, _, hs, _
  | .acquireRelease _ _, _, _, hs, _
  | .provideLayer _ _ _, _, _, hs, _ | .service _, _, _, hs, _
  | .provideService _ _ _, _, _, hs, _
  | .catchIf _ _ _, _, _, hs, _ => by
    simp [Straight] at hs

/-! ## Restriction to the existing straight denotation -/

/-- The compile budget of a straight program is positive: its depth is. -/
theorem fuel_ne_zero_of_depth {e : NativeEff} {p : Point} (hp : Agreement.depth e ≤ p.fuel) :
    p.fuel ≠ 0 := by
  have := Agreement.depth_pos e
  omega

/-- After erasing the control markers and checkpoints, the straight fragment is the
store denotation whenever the compile budget covers its depth. -/
theorem denoteR_straight (root : NativeEff) : ∀ (e : NativeEff) (p : Point),
    Straight e = true → Agreement.depth e ≤ p.fuel →
    eraseControl (denoteR root e p) = Effects.Program.inl (denote e p.env)
  | .succeed t, p, _, hp => by
    cases hf : p.fuel with
    | zero => exact (fuel_ne_zero_of_depth hp hf).elim
    | succ f => simp only [denoteR, hf, denoteRWith, denoteEffBody]; rw [denote]; rfl
  | .fail t, p, _, hp => by
    cases hf : p.fuel with
    | zero => exact (fuel_ne_zero_of_depth hp hf).elim
    | succ f => simp only [denoteR, hf, denoteRWith, denoteEffBody]; rw [denote]; rfl
  | .failCause t, p, _, hp => by
    cases hf : p.fuel with
    | zero => exact (fuel_ne_zero_of_depth hp hf).elim
    | succ f => simp only [denoteR, hf, denoteRWith, denoteEffBody]; rw [denote]; rfl
  | .yieldError t, p, _, hp => by
    cases hf : p.fuel with
    | zero => exact (fuel_ne_zero_of_depth hp hf).elim
    | succ f =>
      simp only [denoteR, hf, denoteRWith, denoteEffBody]
      rw [denote]
      cases hx : evalTerm p.env t <;> rfl
  | .sync t, p, _, hp => by
    cases hf : p.fuel with
    | zero => exact (fuel_ne_zero_of_depth hp hf).elim
    | succ f => simp only [denoteR, hf, denoteRWith, denoteEffBody]; rw [denote]; rfl
  | .suspend b, p, hs, hp => by
    cases hf : p.fuel with
    | zero => exact (fuel_ne_zero_of_depth hp hf).elim
    | succ f =>
      have ih := denoteR_straight root b ({ p with fuel := f + 1, completed := [] }.child 0) hs
        (by simp only [Agreement.depth] at hp; simp only [Point.child]; omega)
      simp only [denoteR, Point.child_fuel, Nat.add_sub_cancel] at ih
      simp only [denoteR, hf, denoteRWith, denoteEffBody]
      rw [eraseControl_suspendR, eraseControl_constructR, denote]
      exact ih
  | .perform op request, p, hs, hp => by
    cases hf : p.fuel with
    | zero => exact (fuel_ne_zero_of_depth hp hf).elim
    | succ f =>
      have hk := Straight.perform_sync hs
      rw [denoteR_perform_sync root op request (by rw [hf]; exact Nat.succ_ne_zero f) hk]
      simp only [denote, hk]
      cases (evalTerm p.env request).bind (NativeOp.syncOpOf op) <;> rfl
  | .bind a b, p, hs, hp => by
    have hpos : p.fuel ≠ 0 := by have := Agreement.depth_pos (.bind a b); omega
    have hab := Straight.bind hs
    have ha := denoteR_straight root a (p.child 0) hab.1
      (by simp only [Agreement.depth] at hp; simp only [Point.child]; omega)
    rw [denoteR_bind root a b p hpos, eraseControl_bind, eraseControl_guardR,
      ha, denote, Effects.Program.inl_bind]
    congr 1
    funext ex
    cases ex with
    | failure c => rfl
    | success v =>
      exact denoteR_straight root b ({ p with completed := [] }.childWith 1 v) hab.2
        (by simp only [Agreement.depth] at hp; simp only [Point.childWith]; omega)
  | .branch test a b, p, hs, hp => by
    have hpos : p.fuel ≠ 0 := by have := Agreement.depth_pos (.branch test a b); omega
    have hab := Straight.branch hs
    rw [denoteR_branch root test a b p hpos, eraseControl_suspendR, eraseControl_constructR, denote]
    split
    · rename_i ht
      rw [ht]
      exact denoteR_straight root a ({ p with completed := [] }.child 0) hab.1
        (by simp only [Agreement.depth] at hp; simp only [Point.child]; omega)
    · rename_i ht
      rw [ht]
      exact denoteR_straight root b ({ p with completed := [] }.child 1) hab.2
        (by simp only [Agreement.depth] at hp; simp only [Point.child]; omega)
    · split
      · contradiction
      · contradiction
      · rfl
  | .exit b, p, hs, hp => by
    have hpos : p.fuel ≠ 0 := by have := Agreement.depth_pos (.exit b); omega
    have hb := denoteR_straight root b (p.child 0) hs
      (by simp only [Agreement.depth] at hp; simp only [Point.child]; omega)
    rw [denoteR_exit root b p hpos]
    cases hy : inlineYield b (p.child 0) with
    | none =>
      dsimp only
      rw [eraseControl_bind, eraseControl_guardR, hb, denote, Effects.Program.inl_bind]
      rfl
    | some ex =>
      dsimp only
      have hd : denote b p.env = Effects.Program.pure ex :=
        denote_of_inlineYield b (p.child 0) hs hy
      rw [eraseControl_pure, denote, hd]
      rfl
  | .catchCause b h, p, hs, hp => by
    cases hf : p.fuel with
    | zero => exact (fuel_ne_zero_of_depth hp hf).elim
    | succ f =>
      have hbh := Straight.catchCause hs
      have hb := denoteR_straight root b (p.child 0) hbh.1
        (by simp only [Agreement.depth] at hp; simp only [Point.child]; omega)
      simp only [denoteR, Point.child_fuel, hf, Nat.add_sub_cancel] at hb
      simp only [denoteR, hf, denoteRWith, denoteEffBody]
      rw [eraseControl_bind, eraseControl_guardR, hb, denote, Effects.Program.inl_bind]
      congr 1
      funext ex
      cases ex with
      | success v => rfl
      | failure c =>
        have ih := denoteR_straight root h
          ({ p with fuel := f + 1, completed := [] }.childWith 1 (.exitErr c)) hbh.2
          (by simp only [Agreement.depth] at hp; simp only [Point.childWith]; omega)
        simp only [denoteR, Point.childWith_fuel, Nat.add_sub_cancel] at ih
        exact ih
  | .matchCause b v c, p, hs, hp => by
    cases hf : p.fuel with
    | zero => exact (fuel_ne_zero_of_depth hp hf).elim
    | succ f =>
      have hparts := Straight.matchCause hs
      have hb := denoteR_straight root b (p.child 0) hparts.1
        (by simp only [Agreement.depth] at hp; simp only [Point.child]; omega)
      simp only [denoteR, Point.child_fuel, hf, Nat.add_sub_cancel] at hb
      simp only [denoteR, hf, denoteRWith, denoteEffBody]
      rw [eraseControl_bind, eraseControl_guardR, hb, denote, Effects.Program.inl_bind]
      congr 1
      funext ex
      cases ex with
      | success value =>
        have ih := denoteR_straight root v
          ({ p with fuel := f + 1, completed := [] }.childWith 1 value) hparts.2.1
          (by simp only [Agreement.depth] at hp; simp only [Point.childWith]; omega)
        simp only [denoteR, Point.childWith_fuel, Nat.add_sub_cancel] at ih
        exact ih
      | failure cause =>
        have ih := denoteR_straight root c
          ({ p with fuel := f + 1, completed := [] }.childWith 2 (.exitErr cause)) hparts.2.2
          (by simp only [Agreement.depth] at hp; simp only [Point.childWith]; omega)
        simp only [denoteR, Point.childWith_fuel, Nat.add_sub_cancel] at ih
        exact ih
  | .onExit b fin, p, hs, hp => by
    cases hf : p.fuel with
    | zero => exact (fuel_ne_zero_of_depth hp hf).elim
    | succ f =>
      have hparts := Straight.onExit hs
      have hb := denoteR_straight root b (p.child 0) hparts.1
        (by simp only [Agreement.depth] at hp; simp only [Point.child]; omega)
      simp only [denoteR, Point.child_fuel, hf, Nat.add_sub_cancel] at hb
      simp only [denoteR, hf, denoteRWith, denoteEffBody]
      rw [eraseControl_onExitR, hb, denote, Effects.Program.inl_bind]
      congr 1
      funext ex
      have hfin := denoteR_straight root fin
        ({ p with completed := [] }.childWith 1 (reifyExitVal ex)) hparts.2
        (by simp only [Agreement.depth] at hp; simp only [Point.childWith]; omega)
      simp only [denoteR, Point.childWith_fuel, Point.completed_fuel, hf, Nat.add_sub_cancel] at hfin
      rw [eraseControl_constructR, hfin, Effects.Program.inl_bind]
      rfl
  | .gen _, _, hs, _ | .uninterruptible _, _, hs, _ | .interruptible _, _, hs, _
  | .whileLoop _ _ _ _, _, hs, _ | .yieldNow _, _, hs, _ | .callback _ _, _, hs, _
  | .awaitFiber _ _, _, hs, _ | .withFiber _, _, hs, _ | .«scoped» _, _, hs, _
  | .acquireRelease _ _, _, hs, _
  | .provideLayer _ _ _, _, hs, _ | .service _, _, hs, _
  | .provideService _ _ _, _, hs, _
  | .catchIf _ _ _, _, hs, _ => by
    simp only [Straight, Bool.false_eq_true] at hs

theorem meaning_denoteR_straight (root : NativeEff) (e : NativeEff) (p : Point)
    (hs : Straight e = true) (hp : Agreement.depth e ≤ p.fuel) (stores : Stores) :
    (Effects.interpret rHandler (eraseControl (denoteR root e p))).run stores =
      meaning e p.env stores := by
  rw [denoteR_straight root e p hs hp]
  exact meaning_via_rsig e p.env stores

end Effect4.Program.Sched
