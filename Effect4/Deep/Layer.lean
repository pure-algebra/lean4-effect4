import Effect4.Deep.Context
import Effect4.Runtime.Scope
import Effect4.Layer.LayerFamily

/-!
# Deep spike S5, part 2: the Layer store, and the machine instantiated at `Ctx`

Status: design spike, 2026-09-03. Module `Deep.Layer` of the non-default `Deep` library
(`lakefile.toml`, `srcDir = "workshop"`); built with `lake build Deep.Layer`. Plan:
`docs/research/2026-09-03-deep-plan.md` row S5, rows M5 and M6 of §2. Model reading:
`docs/research/2026-09-03-deep-state-models.md` §2.3 and §3.3. Report:
`docs/research/2026-09-03-spike-s5-context-layer.md`.

This file is **the one instantiation** of `Deep.Fibers`' alphabets `ν σ St` over the `χ := Ctx` of
`Deep.Context`. It carries its own `Name`/`Thunk`/`SyncOp`/`FinName`/`ProgName` alphabets and its
own scope and Deferred stores because the S2 alphabets in `Deep.Stores` are closed inductives
with derived `DecidableEq`: a memo-entry finalizer name, a memo operation, a context-carrying
action and a context spine cannot be added to them from outside, and this spike may not edit
`Stores.lean`. Every shape duplicated from S2 is marked `-- SHIM:` with the S2 name the landing
merges it into.

Every arm names the rc.112 line it transcribes (`vendor/effect-4.0.0-rc.112/src/Layer.ts` unless
another file is named; `internal/effect.ts` for the context and scope sites). Names are data;
`progOf`, `contAOf` and `finProgram` are the only places a program is built. Where rc.113 takes a
function (`updateContext`'s `f`, `fromBuildUnsafe`'s `build`, the memo entry finalizer closure)
the model takes a *name* with the data the closure captured (`ContextUpdate`, `Construction`,
`FinName.memoEntry layer memoMap`), exactly as `PrimInterp` names continuations (DB-02).

The error channel is `Cause`/`Exit` everywhere: a failing build closes its `fromBuild` child scope
with the failing exit (`Layer.ts:343`), a memo entry's Deferred completes with the build's exit as
`Prim.ofExit exit` (`:415-416`), a missing ambient `Scope` is `Cause.die (serviceNotFound
scopeKey)` (`:807` through `internal/effect.ts:670-674`), never a typed error.

**What the store cannot hold.** rc.112 keys the memo `Map` on the layer *object* (`:411`, `:438`);
`LayerId` into a declared `LayerTable` is the model's stand-in: identity is allocation identity, two
declared ids are two objects even when their descriptions agree, and the model cannot stop a
program from forging an id. That is the `LAYER-FB-LAYER-IDENTITY` refusal of the
`SCOPE-FB-KEY-IDENTITY` shape (`Effect4/Runtime/Scope.lean:314-320`), stated as
`layerId_identity_not_structural` below. `forEach` with `concurrency: layers.length`
(`:1597-1598`) is `mergeForkAll` over `ActionName.awaitAllFailFast`: the machine interrupts the
outstanding siblings with the awaiter's id on the first failing exit and still awaits them.
-/

set_option autoImplicit false

namespace Effect4.Deep.Layers

open Effect4 Effect4.Deep Effect4.Deep.Env

/-! ## Layer identifiers and descriptions (state note §3.3) -/

/-- A layer object, by declaration index. -/
structure LayerId where
  index : Nat
deriving DecidableEq, Repr

/-- A `MemoMapImpl` (`:421-432`), by allocation order. -/
structure MemoMapId where
  index : Nat
deriving DecidableEq, Repr

/-- A cell of the Deferred store (`Deferred.ts:140-145`). -/
structure DeferredKey where
  index : Nat
deriving DecidableEq, Repr

/-- `provideWith`'s combiner (`:1907-1926`): `identity` for `provide` (`:2348`), `(self, that) =>
Context.merge(that, self)` for `provideMerge`. -/
inductive CombineMode
  | provide
  | provideMerge
deriving DecidableEq, Repr

/-- The build function of `fromBuildUnsafe` (`:289-298`), as a name plus the data it needs. The
interpretation is `constructionProgram`. -/
inductive Construction
  /-- `Layer.succeedContext(ctx)` / `Layer.effect` over `succeed` (`:1129`, `:1435-1439`). -/
  | succeedContext (services : List (ServiceKey × Val))
  /-- A build that fails with a typed error. -/
  | failWith (error : Err)
  /-- A build that acquires: registers `release label` on the layer scope, then succeeds
  (`Layer.effect(tag, acquireRelease(...))`'s shape, `internal/effect.ts:3971-3987`). -/
  | acquire (services : List (ServiceKey × Val)) (release : Nat)
  /-- A build that reads service `input` from the fiber context and binds it under `output`:
  `Layer.effect(Out, Effect.map(In, f))`, the dependent half of `provide`. -/
  | fromService (input output : ServiceKey)
deriving DecidableEq

/-- A layer, by its construction (`Layer.ts`). `mergeAll` carries `List LayerId`
(plan §5 decision 2). A nested layer is named by its id, never inlined: the memo map keys on
layer identity (`:411`). -/
inductive LayerDesc
  /-- `fromBuildUnsafe(build)` (`:289-298`). -/
  | atom (construction : Construction)
  /-- `fromBuildMemo(build)` (`:380-388`): `fromBuild((m, s) => m.getOrElseMemoize(self, s, build))`. -/
  | memoized (construction : Construction)
  /-- `fromBuild(inner.build)` (`:333-345`). -/
  | childScope (inner : LayerId)
  /-- `fresh(inner)` (`:3850-3851`). -/
  | fresh (inner : LayerId)
  /-- `provideWith(self, that, f)` (`:1907-1926`), `f` by `CombineMode`. -/
  | provideWith (self that : LayerId) (mode : CombineMode)
  /-- `mergeAll(...layers)` (`:1652-1658`). -/
  | mergeAll (layers : List LayerId)
deriving DecidableEq

/-- The declared layers; `LayerId.index` indexes it. Static: rc.112 mints layer objects at call
time, the model declares them. -/
abbrev LayerTable := List LayerDesc

/-! ## The finalizer name alphabet -/

/-- Scope finalizer *names* (`Effect4.Scope`'s `φ`). Each is a closure in rc.112; here the data
it captured. -/
inductive FinName
  /-- `scopeForkUnsafe`'s parent side (`internal/effect.ts:3841`): `scopeClose(child, exit)`. -/
  | closeChildScope (scope : Nat)
  /-- Its child side (`:3842`): `scopeRemoveFinalizerUnsafe(parent, key)`. -/
  | detachFromParent (parent key : Nat)
  /-- `fromBuild`'s `onExit` (`Layer.ts:343`): close the layer scope only on `Failure`. -/
  | closeChildOnFailure (scope : Nat)
  /-- The memo entry finalizer (`Layer.ts:401-410`), registered on every observer's caller scope. -/
  | memoEntry (layer : LayerId) (memoMap : MemoMapId)
  /-- `memoMapBuild`'s `onExit` (`Layer.ts:414-417`): store the exit, complete the Deferred. -/
  | memoDone (layer : LayerId) (memoMap : MemoMapId)
  /-- `updateContext`'s `onExitPrimitive` (`internal/effect.ts:2092-2095`): `fiber.setContext(prev)`. -/
  | restoreContext (prev : Ctx)
  /-- `scoped`'s `onExitPrimitive` (`:3943-3946`): restore the context, then close the scope. -/
  | scopedExit (prev : Ctx) (scope : Nat)
  /-- `scopedWith`'s / `scopeUse`'s `onExit` (`:3958`, `:3967`): `scopeCloseUnsafe(scope, exit)`. -/
  | closeScopeWith (scope : Nat)
  /-- An ordinary release, observable through its label and its exit. -/
  | release (label : Nat) (fails : Bool)
  /-- `acquireRelease`'s release (`:3983`): `provideContext(release(a, exit), context)` with the
  context captured by `contextWith` at `:3976`. -/
  | releaseWith (label : Nat) (captured : Ctx)
  /-- `forkIn`'s keyed fiber finalizer (`:5369-5371`); `skipSelf = false` is `fiberRunIn`. -/
  | interruptFiber (fiber : FiberId) (skipSelf : Bool)
deriving DecidableEq

/-! ## The `sync` operations that touch the store -/

/-- Every `sync` thunk over the store, one arm per rc.112 site. -/
inductive SyncOp
  /-- `scopeMakeUnsafe(strategy)` (`internal/effect.ts:3915-3920`). -/
  | scopeMake (strategy : FinalizerStrategy)
  /-- `scopeForkUnsafe(parent, strategy)` (`:3834-3844`): answers the child handle. -/
  | scopeFork (parent : Nat) (strategy : FinalizerStrategy)
  /-- `scopeAddFinalizerExit(scope, f)` (`:3847-3858`): registered while open, answers the
  closing exit (reified) when closed, so the caller runs the finalizer now. -/
  | scopeAdd (scope : Nat) (finalizer : FinName)
  /-- `scopeRemoveFinalizerUnsafe(scope, key)` (`:3891-3904`). -/
  | scopeRemove (scope : Nat) (key : Nat)
  /-- `makeMemoMapUnsafe()` (`Layer.ts:492`) with `none`; `forkMemoMapUnsafe(parent)` (`:511`). -/
  | memoFork (parent : Option MemoMapId)
  /-- `MemoMapImpl.get(layer, scope)` (`:434-443`): own map, then the parent chain; a hit bumps
  the owning entry's observer count (`:245`) and answers the entry's Deferred and owner. -/
  | memoGet (layer : LayerId) (memoMap : MemoMapId)
  /-- `memoMapBuild`'s synchronous half (`:396-411`): a layer scope, a Deferred, the entry with
  one observer, `map.set`. -/
  | memoBuild (layer : LayerId) (memoMap : MemoMapId)
  /-- `memoMapBuild`'s `onExit` (`:414-417`): `entry.effect = exit; Deferred.done(deferred, exit)`. -/
  | memoComplete (layer : LayerId) (memoMap : MemoMapId) (exit : ExitV)
  /-- The entry finalizer's `suspend` body (`:402-408`): `observers--`; at zero delete the entry
  and answer the layer scope to close. -/
  | memoRelease (layer : LayerId) (memoMap : MemoMapId)
  /-- `_await`'s cleanup (`Deferred.ts:178-185`). -/
  | deferredAwaitCleanup (cell : DeferredKey) (waiter : FiberId) (token : Nat)
deriving DecidableEq

/-! ## Program names -/

/-- The declared programs. `progOf` interprets them; `WithFiberAction.fork` carries one. -/
inductive ProgName
  | value (v : Val)
  | failCause (cause : CauseV)
  /-- `context()` (`internal/effect.ts:2152-2153`). -/
  | getContext
  /-- `Effect.service(key)` / a `Context.Tag` as an effect (`:2069-2070`), unchecked: a missing
  key is the host throw, `Cause.die`. -/
  | service (key : ServiceKey)
  /-- `setContext(self, context)` (`:2161-2177`). -/
  | setContextTo (context : Ctx) (body : ProgName)
  /-- `provideContext(self, context)` (`:2180-2199`). -/
  | provideContext (context : Ctx) (body : ProgName)
  /-- `provideService(self, key, value)` (`:2202-2232`). -/
  | provideService (key : ServiceKey) (value : Val) (body : ProgName)
  /-- `scoped(self)` (`:3938-3947`). -/
  | scoped (body : ProgName)
  /-- `acquireRelease(acquire, release, { interruptible })` (`:3971-3987`). -/
  | acquireRelease (acquire : ProgName) (release : Nat) (interruptible : Bool)
  /-- `acquireRelease`'s masked body: `flatMap(scope, scope => tap(acquire', register))`. -/
  | acquireMasked (acquire : ProgName) (release : Nat) (captured : Ctx) (interruptible : Bool)
  /-- `addFinalizer(finalizer)` (`:3990-3999`). -/
  | addFinalizer (label : Nat)
  /-- `flatMap(first, () => second)`. -/
  | seq (first second : ProgName)
  /-- `never = callback(constVoid)` (`:1172`). -/
  | never
  /-- `scopeClose(scope, exit)` from the fiber (`:3775-3776`). -/
  | closeScope (scope : Nat) (exit : ExitV)
  /-- `Layer.build(layer)` (`Layer.ts:800-809`). -/
  | build (layer : LayerId)
  /-- `Layer.buildWithScope(layer, scope)` (`:970-980`). -/
  | buildWithScope (layer : LayerId) (scope : Nat)
  /-- `Layer.buildWithMemoMap(layer, memoMap, scope)` (`:756-765`). -/
  | buildWithMemoMap (layer : LayerId) (memoMap : MemoMapId) (scope : Nat)
  /-- `layer.build(memoMap, scope)`, the raw field (`:54-60`). -/
  | layerBuild (layer : LayerId) (memoMap : MemoMapId) (scope : Nat)
  /-- `map(self.build(memoMap, scope), Context.add(CurrentMemoMap, memoMap))` (`:762`). -/
  | buildAdding (layer : LayerId) (memoMap : MemoMapId) (scope : Nat)
  /-- `andThen(build(self), never)` (`:3898`). -/
  | buildThenNever (layer : LayerId)
  /-- `Layer.launch(layer)` (`:3897-3898`). -/
  | launch (layer : LayerId)
  /-- `Effect.provide(self, layer, { local })` (`internal/layer.ts:8-22`). -/
  | provideLayer (layer : LayerId) (isLocal : Bool) (body : ProgName)
  /-- `scopedWith`'s `suspend` body (`internal/effect.ts:3965-3967`) for `provideLayer`. -/
  | scopedWithAlloc (layer : LayerId) (isLocal : Bool) (body : ProgName)
  /-- `getOrElseMemoize`'s `suspend` body (`Layer.ts:450-456`). -/
  | memoLookup (layer : LayerId) (memoMap : MemoMapId) (scope : Nat) (construction : Construction)
  /-- The program a scope finalizer name runs, as a forkable program (`internal/effect.ts:3820`). -/
  | finalizerOf (fin : FinName) (exit : ExitV)
  /-- The entry finalizer's `suspend` body (`Layer.ts:402-408`). -/
  | memoReleaseOf (layer : LayerId) (memoMap : MemoMapId) (exit : ExitV)
  /-- `release(a, exit)`'s body: succeeds. -/
  | releaseOf (label : Nat)
deriving DecidableEq

/-! ## Continuation, registration and finalizer names (`ν`) -/

/-- One alphabet for rc.112's three function slots, as in S2. -/
inductive Name
  /-- `Exit.restoreAfterFinalizer`'s caller side (`RunInterp.restoreName`). -/
  | restore (exit : ExitV)
  /-- `Exit.mergeFinalizer` (`RunInterp.mergeName`, `internal/effect.ts:3800-3804`). -/
  | merge (exit : ExitV)
  /-- contA: discard the value, continue with the named program. -/
  | seq (next : ProgName)
  /-- contA: answer a constant. -/
  | constant (value : Val)
  /-- `Deferred.await`'s registration (`Deferred.ts:173-177`). -/
  | registerAwait (cell : DeferredKey)
  /-- `_await`'s cleanup name (`Deferred.ts:178-185`). -/
  | cancelAwait (cell : DeferredKey)
  /-- `never`'s registration (`internal/effect.ts:1172`): `constVoid`, never resumes. -/
  | neverRegister
  /-- `RunInterp.abortName`. -/
  | abortController
  /-- `RunInterp.cancelName base waiter token` (M3). -/
  | withWaiter (base : Name) (waiter : FiberId) (token : Nat)
  /-- `PrimInterp.cancelThenFail`'s tail (`:1157`). -/
  | reFail (cause : CauseV)
  /-- A scope finalizer name carried by an `OnExit` frame. -/
  | finalizerName (fin : FinName)
  /-- The sequential close chain (`:3817-3818`). -/
  | closeSeq (remaining : List FinName) (exit : ExitV)
      (captured : List (Reason Err Defect FiberId Ann))
  /-- The parallel close chain (`:3819-3821`). -/
  | closePar (remaining : List FinName) (exit : ExitV) (forked : List FiberId)
      (closerInterruptible : Bool)
  /-- `exitAsVoidAll` of the awaited exits (`:3826`, M6). -/
  | mergeAwaitedExits
  /-- `scopeAddFinalizerExit`'s answer (`:3851-3857`): registered, or run the finalizer now. -/
  | afterScopeAdd (fin : FinName)
  /-- `updateContext` (`:2087-2096`), on the previous context value. -/
  | updateThen (update : ContextUpdate) (body : ProgName)
  /-- `updateContext` after `setContext`: `onExitPrimitive(self, () => setContext(prev))`. -/
  | bodyThen (body : ProgName) (prev : Ctx)
  /-- `scoped` (`:3939-3941`), on the previous context value: allocate the scope. -/
  | scopedThen (body : ProgName)
  /-- `scoped` (`:3942`), on the scope handle: install it in the context. -/
  | scopedInstall (body : ProgName) (prev : Ctx)
  /-- `scoped` (`:3943`): push the `OnExit` frame around the body. -/
  | scopedBody (body : ProgName) (prev : Ctx) (scope : Nat)
  /-- `scoped`'s finalizer, second half (`:3945`): close the scope with the exit. -/
  | thenClose (scope : Nat) (exit : ExitV)
  /-- `Effect.service(key)` on the context value (`:2070`). -/
  | serviceLookup (key : ServiceKey)
  /-- `Context.make(output, value)` (`Layer.ts:1439`), on the value a construction read. -/
  | bindService (output : ServiceKey)
  /-- `acquireRelease`'s `contextWith` (`:3976`): the captured context. -/
  | acquireWith (acquire : ProgName) (release : Nat) (interruptible : Bool)
  /-- `acquireRelease`'s `flatMap(scope, …)` (`:3979-3980`), on the ambient scope handle. -/
  | acquireInScope (acquire : ProgName) (release : Nat) (captured : Ctx) (interruptible : Bool)
  /-- `tap(acquire, a => scopeAddFinalizerExit(scope, …))` (`:3981-3983`), on the acquired value. -/
  | registerRelease (scope : Nat) (release : Nat) (captured : Ctx)
  /-- `addFinalizer` (`:3993-3996`), on the ambient scope handle. -/
  | addFinalizerOn (label : Nat)
  /-- `addFinalizer`'s `contextWith` (`:3996-3997`), on the context value. -/
  | addFinalizerCaptured (scope : Nat) (label : Nat)
  /-- `Layer.build` (`Layer.ts:803-808`), on the fiber context value. -/
  | buildFromContext (layer : LayerId)
  /-- `Layer.buildWithScope` (`:974-979`), on the fiber context value. -/
  | buildWithScopeFromContext (layer : LayerId) (scope : Nat)
  /-- On the forked-or-created memo map: `buildWithMemoMap`, or the host throw when no scope. -/
  | withMemoMapThen (layer : LayerId) (scope : Option Nat)
  /-- `map(_, Context.add(CurrentMemoMap, memoMap))` (`:762`), on the built context value. -/
  | addCurrentMemoMap (memoMap : MemoMapId)
  /-- `getOrElseMemoize` after `get` (`:451-455`): reuse on a hit, `memoMapBuild` on a miss. -/
  | memoize (layer : LayerId) (memoMap : MemoMapId) (scope : Nat) (construction : Construction)
  /-- `entry.effect` on a hit: `Deferred.await(deferred)` (`:400`, `:248`). -/
  | awaitPromise (cell : DeferredKey)
  /-- `memoMapBuild` after the allocations (`:412`): register the entry finalizer on the caller. -/
  | buildIntoLayerScope (layer : LayerId) (memoMap : MemoMapId) (scope : Nat)
      (construction : Construction)
  /-- `memoMapBuild` (`:413-417`): build into the layer scope under the completing `onExit`. -/
  | thenBuildInto (layer : LayerId) (memoMap : MemoMapId) (construction : Construction)
      (layerScope : Nat)
  /-- The entry finalizer (`:404-408`): close the layer scope only when the count hit zero. -/
  | closeIfLast (exit : ExitV)
  /-- `fromBuild` (`:339-344`), on the forked child handle: build inside the closing `onExit`. -/
  | fromBuildThen (desc : LayerDesc) (self : LayerId) (memoMap : MemoMapId)
  /-- `fresh` (`:3851`), on the brand-new memo map: build the inner layer on the same scope. -/
  | freshThen (inner : LayerId) (scope : Nat)
  /-- `provideWith` (`:1920-1923`), on the dependency's context value. -/
  | provideThen (self : LayerId) (memoMap : MemoMapId) (scope : Nat) (mode : CombineMode)
  /-- `map(merged => f(merged, context))` (`:1923`), on the dependent's context value. -/
  | combineWith (mode : CombineMode) (thatContext : Ctx)
  /-- `mergeAllEffect` (`:1596`), on the parallel parent scope handle. -/
  | mergeChildren (layers : List LayerId) (memoMap : MemoMapId)
  /-- `mergeAllEffect` (`:1597`), on one sequential child handle: fork that layer's build. -/
  | mergeForkOne (layer : LayerId) (rest : List LayerId) (memoMap : MemoMapId) (parent : Nat)
      (forked : List FiberId)
  /-- On the forked fiber handle: the next layer. -/
  | mergeForkNext (rest : List LayerId) (memoMap : MemoMapId) (parent : Nat)
      (forked : List FiberId)
  /-- `map(context => Context.mergeAll(...context))` (`:1600`), on the awaited exits. -/
  | mergeContexts
  /-- `provideLayer`'s `scopedWith` body (`internal/layer.ts:15-21`), on the fresh scope handle. -/
  | provideLayerWith (layer : LayerId) (isLocal : Bool) (body : ProgName)
  /-- `flatMap(build, context => provideContext(self, context))` (`internal/layer.ts:20`). -/
  | provideLayerBody (body : ProgName)
deriving DecidableEq

/-- What a `withFiber` thunk names; `actionOf` expands the program names. -/
inductive ActionName
  | fork (program : ProgName) (options : Supervision.ForkOptions)
  | forkScoped (program : ProgName) (options : Supervision.ForkOptions) (key : Nat)
  | interrupt (target : FiberId)
  | interruptScoped (target : FiberId)
  | awaitAll (targets : List FiberId)
  /-- `forEach` with `concurrency: layers.length` (`Layer.ts:1597-1598`): the first failing
  sibling interrupts the outstanding ones. -/
  | awaitAllFailFast (targets : List FiberId)
  | setContext (context : Ctx)
  | getContext
  | getId
  | closeScope (scope : Nat) (exit : ExitV)
  | setInterruptible (body : ProgName) (flag : Bool)
  | refuse (cause : CauseV)
deriving DecidableEq

/-- Every thunk name. -/
inductive Thunk
  | act (action : ActionName)
  | op (operation : SyncOp)
  | body (program : ProgName)
deriving DecidableEq

/-- The program carrier at this instantiation. -/
abbrev Program := Prim Name Thunk Val Err Defect FiberId Ann

/-- The reason carrier. -/
abbrev ReasonV := Reason Err Defect FiberId Ann

/-! ## The Deferred store

-- SHIM: `Deep.Stores.DeferredStore`, re-declared at this `Program`; the landing keeps one. -/

/-- One `Deferred` (`Deferred.ts:58-61`). -/
structure DeferredCell where
  completion : Option Program
  waiters : List (FiberId × Nat)
deriving DecidableEq

/-- The cells and the resumes a completion owes (`Deferred.ts:1655-1659`). -/
structure DeferredStore where
  cells : List DeferredCell
  due : List (FiberId × Nat × Program)
deriving DecidableEq

namespace DeferredStore

/-- `Deferred.makeUnsafe` (`Deferred.ts:140-145`). -/
def make (self : DeferredStore) : DeferredKey × DeferredStore :=
  (⟨self.cells.length⟩, { self with cells := self.cells ++ [⟨none, []⟩] })

def cellAt (self : DeferredStore) (cell : DeferredKey) : Option DeferredCell :=
  self.cells[cell.index]?

def setCell (self : DeferredStore) (cell : DeferredKey) (value : DeferredCell) : DeferredStore :=
  { self with cells := self.cells.set cell.index value }

/-- `_await` (`Deferred.ts:173-177`): resume at once when done, else append the waiter. -/
def register (self : DeferredStore) (cell : DeferredKey) (waiter : FiberId) (token : Nat) :
    DeferredStore × Option Program :=
  match self.cellAt cell with
  | none => (self, none)
  | some c =>
    match c.completion with
    | some effect => (self, some effect)
    | none => (self.setCell cell { c with waiters := c.waiters ++ [(waiter, token)] }, none)

/-- `_await`'s cleanup (`Deferred.ts:178-185`). -/
def cancel (self : DeferredStore) (cell : DeferredKey) (waiter : FiberId) (token : Nat) :
    DeferredStore :=
  match self.cellAt cell with
  | none => self
  | some c =>
    self.setCell cell
      { c with waiters := c.waiters.filter fun w => !(decide (w.1 = waiter) && decide (w.2 = token)) }

/-- `doneUnsafe` (`Deferred.ts:1648-1662`). -/
def complete (self : DeferredStore) (cell : DeferredKey) (effect : Program) :
    DeferredStore × Bool :=
  match self.cellAt cell with
  | none => (self, false)
  | some c =>
    match c.completion with
    | some _ => (self, false)
    | none =>
      ({ self.setCell cell ⟨some effect, []⟩ with
          due := self.due ++ c.waiters.map fun w => (w.1, w.2, effect) }, true)

def drainDue (self : DeferredStore) : List (FiberId × Nat × Program) × DeferredStore :=
  (self.due, { self with due := [] })

end DeferredStore

/-! ## The scope store

-- SHIM: `Deep.Stores.ScopeStore`, re-declared at this `FinName`; `Effect4.Scope` itself is
reused unchanged. -/

/-- One keyed `Effect4.Scope`. -/
abbrev ScopeV := Effect4.Scope Nat FinName Val Err Defect FiberId Ann

structure ScopeEntry where
  key : Nat
  scope : ScopeV
deriving DecidableEq

structure ScopeStore where
  entries : List ScopeEntry
deriving DecidableEq

namespace ScopeStore

def entryAt (self : ScopeStore) (key : Nat) : Option ScopeEntry :=
  self.entries.find? fun e => e.key = key

def setEntry (self : ScopeStore) (entry : ScopeEntry) : ScopeStore :=
  { entries := self.entries.map fun e => if e.key = entry.key then entry else e }

/-- `scopeMakeUnsafe` (`internal/effect.ts:3915-3920`). -/
def make (self : ScopeStore) (key : Nat) (strategy : FinalizerStrategy) : ScopeStore :=
  { entries := self.entries ++ [⟨key, Effect4.Scope.make strategy⟩] }

/-- `scopeRemoveFinalizerUnsafe` (`:3891-3904`). -/
def removeFinalizer (self : ScopeStore) (key finalizerKey : Nat) : ScopeStore :=
  match self.entryAt key with
  | none => self
  | some entry => self.setEntry { entry with scope := entry.scope.removeUnsafe finalizerKey }

/-- `scopeForkUnsafe` (`:3834-3844`): one shared key links the parent's `scopeClose(child)` to
the child's `scopeRemoveFinalizerUnsafe(parent, key)`; a closed parent's child is born closed. -/
def forkChild (self : ScopeStore) (parentKey childKey sharedKey : Nat)
    (strategy : FinalizerStrategy) : ScopeStore :=
  match self.entryAt parentKey with
  | none => self
  | some parent =>
    let (parentScope, childScope) :=
      Effect4.Scope.fork parent.scope strategy sharedKey
        (FinName.closeChildScope childKey) (FinName.detachFromParent parentKey sharedKey)
    { entries := (self.setEntry { parent with scope := parentScope }).entries ++ [⟨childKey, childScope⟩] }

/-- `RunInterp.scopeStatus`'s view. -/
def status (self : ScopeStore) (key : Nat) : Option (Option ExitV) :=
  (self.entryAt key).map fun e => e.scope.closingExit?

end ScopeStore

/-! ## The memo world (`Layer.ts:235-239`, `:421-458`) -/

/-- `MemoMapEntry` (`:235-239`) plus the two objects the closure captured (`:396-397`). -/
structure MemoEntry where
  /-- `observers` (`:236`). -/
  observers : Nat
  /-- `effect` (`:237`): `Deferred.await(deferred)` until the build exits, then the exit. -/
  effect : Program
  /-- The layer scope `memoMapBuild` allocated (`:396`). -/
  layerScope : Nat
  /-- The Deferred (`:397`). -/
  deferred : DeferredKey
  /-- `finalizer` (`:238`): the one name every observer registers. -/
  finalizer : FinName
deriving DecidableEq

/-- `MemoMapImpl` (`:421-432`): `parent` and `map`, insertion-ordered. -/
structure MemoMap where
  id : MemoMapId
  parent : Option MemoMapId
  entries : List (LayerId × MemoEntry)
deriving DecidableEq

/-- Every memo map ever made. -/
abbrev MemoWorld := List MemoMap

namespace MemoWorld

def mapAt (w : MemoWorld) (id : MemoMapId) : Option MemoMap :=
  w.find? fun m => m.id = id

def setMap (w : MemoWorld) (m : MemoMap) : MemoWorld :=
  w.map fun n => if n.id = m.id then m else n

/-- `this.map.get(layer)` (`:438`), own map only. -/
def entryAt (w : MemoWorld) (id : MemoMapId) (layer : LayerId) : Option MemoEntry :=
  (w.mapAt id).bind fun m => (m.entries.find? fun e => e.1 = layer).map Prod.snd

def updateEntry (w : MemoWorld) (id : MemoMapId) (layer : LayerId) (f : MemoEntry → MemoEntry) :
    MemoWorld :=
  match w.mapAt id with
  | none => w
  | some m => w.setMap { m with entries := m.entries.map fun e => if e.1 = layer then (e.1, f e.2) else e }

/-- `map.set(layer, entry)` (`:411`) on a fresh key: appended. -/
def insertEntry (w : MemoWorld) (id : MemoMapId) (layer : LayerId) (entry : MemoEntry) :
    MemoWorld :=
  match w.mapAt id with
  | none => w
  | some m => w.setMap { m with entries := m.entries ++ [(layer, entry)] }

/-- `map.delete(layer)` (`:405`). -/
def deleteEntry (w : MemoWorld) (id : MemoMapId) (layer : LayerId) : MemoWorld :=
  match w.mapAt id with
  | none => w
  | some m => w.setMap { m with entries := m.entries.filter fun e => !(decide (e.1 = layer)) }

/-- `MemoMapImpl.get` (`:434-443`) without the reuse side effect: own map first, else the parent
chain. Fuel-bounded by the number of maps, which bounds the chain. -/
def lookup (w : MemoWorld) (layer : LayerId) : Nat → MemoMapId → Option (MemoMapId × MemoEntry)
  | 0, _ => none
  | fuel + 1, id =>
    match w.entryAt id layer with
    | some entry => some (id, entry)
    | none =>
      match w.mapAt id with
      | none => none
      | some m =>
        match m.parent with
        | none => none
        | some parent => lookup w layer fuel parent

def get (w : MemoWorld) (layer : LayerId) (id : MemoMapId) : Option (MemoMapId × MemoEntry) :=
  lookup w layer (w.length + 1) id

/-- `LAYER-FB-LAYER-IDENTITY`, the `SCOPE-FB-KEY-IDENTITY` shape (`Effect4/Runtime/Scope.lean:314-320`):
the memo map is keyed by `LayerId`, which is allocation identity, never by the layer's
description. Inserting under one id leaves every other id's entry untouched, however the
`LayerTable` describes the two — rc.112 keys on the layer object (`Layer.ts:411`, `:438`). The
model cannot stop a program from forging an id; that boundary is the refusal row. -/
theorem find?_append_other_key (entries : List (LayerId × MemoEntry)) (layer other : LayerId)
    (entry : MemoEntry) (hne : other ≠ layer) :
    (entries ++ [(layer, entry)]).find? (fun e => e.1 = other) =
      entries.find? (fun e => e.1 = other) := by
  rw [List.find?_append]
  have hlast : ([(layer, entry)].find? fun e : LayerId × MemoEntry => e.1 = other) = none := by
    have hne' : layer ≠ other := fun h => hne h.symm
    simp [List.find?, hne']
  rw [hlast, Option.or_none]

/-- The same fact at the world level, for a world whose maps carry distinct ids (every world
the store builds does: `memoFork` mints a fresh id). -/
theorem insertEntry_other (w : MemoWorld) (id : MemoMapId) (layer other : LayerId)
    (entry : MemoEntry) (hne : other ≠ layer) :
    (w.insertEntry id layer entry).entryAt id other = w.entryAt id other := by
  unfold insertEntry
  cases hmap : w.mapAt id with
  | none => rfl
  | some m =>
    have hid : m.id = id := by
      have := List.find?_some hmap
      simpa using this
    have hmem : m ∈ w := List.mem_of_find?_eq_some hmap
    -- `setMap` replaces exactly the map with `m.id`; with distinct ids, `mapAt` finds the
    -- replacement, whose entries are `m.entries ++ [(layer, entry)]`.
    have hset : (w.setMap { m with entries := m.entries ++ [(layer, entry)] }).mapAt id =
        some { m with entries := m.entries ++ [(layer, entry)] } := by
      unfold setMap mapAt
      rw [List.find?_map]
      have hpred : (fun n : MemoMap =>
          decide ((if n.id = m.id then { m with entries := m.entries ++ [(layer, entry)] } else n).id = id)) =
          fun n : MemoMap => decide (n.id = id) := by
        funext n
        by_cases hn : n.id = m.id
        · simp [hn, hid]
        · simp [hn]
      simp only [Function.comp_def]
      rw [hpred]
      unfold mapAt at hmap
      rw [hmap]
      simp [hid]
    unfold entryAt
    rw [hset, hmap]
    simp only [Option.bind_some]
    rw [find?_append_other_key _ _ _ _ hne]

end MemoWorld

/-! ## The service state `St` -/

/-- The store the machine carries: the memo world, the scopes, the Deferreds, one fresh-name
counter for scope keys, finalizer keys and memo-map ids.

One counter is the faithful choice, not a shortcut. In rc.112 a scope, a memo map and a finalizer
key are each an *object* — `finalizerKey: {} | undefined`, `finalizers: Map<{}, …>`
(`Scope.ts:154-156`), `MemoMapImpl` (`Layer.ts:421`), `ScopeImpl` — and the only fact the runtime
ever reads off one is identity. A single counter mints every such identity distinct, which is
exactly the relation those objects stand in; separate counters would add numeric coincidences
(scope `2` and memo map `2`) that name nothing in rc.112 and that no clause here could read
without inventing a comparison the runtime never makes. -/
structure St where
  memo : MemoWorld
  scopes : ScopeStore
  deferreds : DeferredStore
  nextName : Nat
deriving DecidableEq

namespace St

def empty : St := ⟨[], ⟨[]⟩, ⟨[], []⟩, 0⟩

/-- A store with one open sequential scope `0` and one root memo map `⟨1⟩`, for the witnesses that
name an explicit memo map and scope (`buildWithMemoMap`, `buildWithScope`). -/
def seeded : St :=
  ⟨[⟨⟨1⟩, none, []⟩], ⟨[⟨0, Effect4.Scope.make FinalizerStrategy.sequential⟩]⟩, ⟨[], []⟩, 2⟩

end St

/-! ## Values -/

/-- `reifyExit`. -/
def reifyExitVal : ExitV → Val
  | Exit.success value => Val.exitOk value
  | Exit.failure cause => Val.exitErr cause

/-- `RunInterp.exitsValue` (M6). -/
def exitsVal : List ExitV → Val
  | [] => Val.exitNil
  | exit :: rest => Val.exitCons (reifyExitVal exit) (exitsVal rest)

/-- The exits read back off an exits value. -/
def exitsOfVal : Val → List ExitV
  | Val.exitCons (Val.exitOk value) rest => Exit.success value :: exitsOfVal rest
  | Val.exitCons (Val.exitErr cause) rest => Exit.failure cause :: exitsOfVal rest
  | _ => []

/-- The reasons carried by an exits value, in order. -/
def reasonsOfVal : Val → List ReasonV
  | Val.exitErr cause => cause.reasons
  | Val.exitCons head tail => reasonsOfVal head ++ reasonsOfVal tail
  | _ => []

/-- `exitAsVoidAll` at the value alphabet (`internal/effect.ts:2024-2038`). -/
def voidAllOf (reasons : List ReasonV) : ExitV :=
  match reasons with
  | [] => Exit.success Val.unit
  | reason :: rest => Exit.failure ⟨reason :: rest⟩

theorem exitsOfVal_exitsVal : ∀ exits : List ExitV, exitsOfVal (exitsVal exits) = exits
  | [] => rfl
  | Exit.success value :: rest => by
    show Exit.success value :: exitsOfVal (exitsVal rest) = _
    rw [exitsOfVal_exitsVal rest]
  | Exit.failure cause :: rest => by
    show Exit.failure cause :: exitsOfVal (exitsVal rest) = _
    rw [exitsOfVal_exitsVal rest]

/-- A context from a service list, by `addV` in order. -/
def ctxOfList : List (ServiceKey × Val) → Ctx
  | [] => Context.empty
  | (key, value) :: rest => (ctxOfList rest).addV key value

/-- A memo-map handle read off an optional value. -/
def memoMapOfVal : Option Val → Option MemoMapId
  | some (Val.memoMap id) => some ⟨id⟩
  | _ => none

/-- The memo map `forkOrCreate` reads (`Layer.ts:586`): the `CurrentMemoMap` service, if bound to
a memo-map handle. -/
def currentMemoMapOf (c : Ctx) : Option MemoMapId := memoMapOfVal (c.getV currentMemoMapKey)

/-! ## The store step under `Prim.sync` -/

/-- Every `sync` thunk over the store. `none` is a frontier: a key no allocation minted (M7). -/
def syncStep : SyncOp → St → Option (St × Val)
  | SyncOp.scopeMake strategy, st =>
    some ({ st with scopes := st.scopes.make st.nextName strategy, nextName := st.nextName + 1 },
      Val.scopeHandle st.nextName)
  | SyncOp.scopeFork parent strategy, st =>
    match st.scopes.entryAt parent with
    | none => none
    | some _ =>
      some ({ st with
          scopes := st.scopes.forkChild parent st.nextName (st.nextName + 1) strategy
          nextName := st.nextName + 2 },
        Val.scopeHandle st.nextName)
  | SyncOp.scopeAdd scope fin, st =>
    match st.scopes.entryAt scope with
    | none => none
    | some entry =>
      match entry.scope.closingExit? with
      | some exit => some (st, reifyExitVal exit)                        -- :3852-3853
      | none =>
        some ({ st with
            scopes := st.scopes.setEntry { entry with scope := entry.scope.addUnsafe st.nextName fin }
            nextName := st.nextName + 1 },
          Val.unit)                                                     -- :3855-3856
  | SyncOp.scopeRemove scope key, st =>
    some ({ st with scopes := st.scopes.removeFinalizer scope key }, Val.unit)
  | SyncOp.memoFork parent, st =>
    some ({ st with memo := st.memo ++ [⟨⟨st.nextName⟩, parent, []⟩], nextName := st.nextName + 1 },
      Val.memoMap st.nextName)
  | SyncOp.memoGet layer memoMap, st =>
    match st.memo.get layer memoMap with
    | none => some (st, Val.unit)
    | some (owner, entry) =>                                            -- :245, :438-442
      some ({ st with memo := st.memo.updateEntry owner layer fun e => { e with observers := e.observers + 1 } },
        Val.pair (Val.promise entry.deferred.index) (Val.memoMap owner.index))
  | SyncOp.memoBuild layer memoMap, st =>                               -- :396-411
    let layerScope := st.nextName
    let (deferred, deferreds) := st.deferreds.make
    let entry : MemoEntry :=
      ⟨1, Prim.async (Name.registerAwait deferred) true (some (Name.cancelAwait deferred)),
        layerScope, deferred, FinName.memoEntry layer memoMap⟩
    some ({ st with
        scopes := st.scopes.make layerScope FinalizerStrategy.sequential
        deferreds := deferreds
        memo := st.memo.insertEntry memoMap layer entry
        nextName := st.nextName + 1 },
      Val.scopeHandle layerScope)
  | SyncOp.memoComplete layer memoMap exit, st =>                       -- :415-416
    match st.memo.entryAt memoMap layer with
    | none => some (st, Val.unit)
    | some entry =>
      let (deferreds, _) := st.deferreds.complete entry.deferred (Prim.ofExit exit)
      some ({ st with
          memo := st.memo.updateEntry memoMap layer fun e => { e with effect := Prim.ofExit exit }
          deferreds := deferreds },
        Val.unit)
  | SyncOp.memoRelease layer memoMap, st =>                             -- :403-408
    match st.memo.entryAt memoMap layer with
    | none => some (st, Val.unit)
    | some entry =>
      if entry.observers ≤ 1 then
        some ({ st with memo := st.memo.deleteEntry memoMap layer }, Val.scopeHandle entry.layerScope)
      else
        some ({ st with memo := st.memo.updateEntry memoMap layer fun e => { e with observers := e.observers - 1 } },
          Val.unit)
  | SyncOp.deferredAwaitCleanup cell waiter token, st =>
    some ({ st with deferreds := st.deferreds.cancel cell waiter token }, Val.unit)

/-! ## Programs

Every program is built here, from names. Context programs first (M4b's machine half, M5, M6),
then the layer programs, then the close chains. -/

/-- `sync(op)`. -/
def syncOp (op : SyncOp) : Program := Prim.sync (Thunk.op op)

/-- `withFiber(action)`. -/
def act (action : ActionName) : Program := Prim.withFiber (Thunk.act action)

/-- `scopeAddFinalizerExit(scope, fin)` (`internal/effect.ts:3847-3858`): the `sync` half and the
continuation that runs the finalizer now when the scope was already closed. -/
def scopeAddProgram (scope : Nat) (fin : FinName) : Program :=
  Prim.onSuccess (syncOp (SyncOp.scopeAdd scope fin)) (Name.afterScopeAdd fin)

/-- `updateContext(self, f)` (`internal/effect.ts:2087-2096`): read the context, apply the named
update, `setContext`, and run the body under an `onExitPrimitive` that restores the previous
context. -/
def updateContextProgram (update : ContextUpdate) (body : ProgName) : Program :=
  Prim.onSuccess (act ActionName.getContext) (Name.updateThen update body)

/-- `scoped(self)` (`:3938-3947`): read the context, allocate a scope, install it, and run the
body under the `OnExit` frame that restores the context and closes the scope. -/
def scopedProgram (body : ProgName) : Program :=
  Prim.onSuccess (act ActionName.getContext) (Name.scopedThen body)

/-- `Effect.service(key)` (`:2069-2070`): the context, then the lookup. -/
def serviceProgram (key : ServiceKey) : Program :=
  Prim.onSuccess (act ActionName.getContext) (Name.serviceLookup key)

/-- `acquireRelease(acquire, release, options)` (`:3971-3987`): `contextWith` first. -/
def acquireReleaseProgram (acquire : ProgName) (release : Nat) (interruptible : Bool) : Program :=
  Prim.onSuccess (act ActionName.getContext) (Name.acquireWith acquire release interruptible)

/-- `Layer.buildWithMemoMap(self, memoMap, scope)` (`Layer.ts:756-765`): `provideService(map(
self.build(memoMap, scope), Context.add(CurrentMemoMap, memoMap)), CurrentMemoMap, memoMap)`. -/
def buildWithMemoMapProgram (layer : LayerId) (memoMap : MemoMapId) (scope : Nat) : Program :=
  updateContextProgram (ContextUpdate.provideService currentMemoMapKey (Val.memoMap memoMap.index))
    (ProgName.buildAdding layer memoMap scope)

/-- `getOrElseMemoize(self, scope, build)` (`:445-457`): a `suspend`, so the lookup is at run time. -/
def getOrElseMemoizeProgram (layer : LayerId) (memoMap : MemoMapId) (scope : Nat)
    (construction : Construction) : Program :=
  Prim.suspend (Thunk.body (ProgName.memoLookup layer memoMap scope construction))

/-- `memoMapBuild(memoMap, layer, scope, build)` (`:390-419`): the allocations, then the
registration on the caller scope, then the build into the layer scope under the completing
`onExit`. -/
def memoBuildProgram (layer : LayerId) (memoMap : MemoMapId) (scope : Nat)
    (construction : Construction) : Program :=
  Prim.onSuccess (syncOp (SyncOp.memoBuild layer memoMap))
    (Name.buildIntoLayerScope layer memoMap scope construction)

/-- What a `fromBuildUnsafe` build does at a scope (`:289-298`): no scope handling of its own. -/
def constructionProgram (construction : Construction) (scope : Nat) : Program :=
  match construction with
  | Construction.succeedContext services => Prim.success (encode (ctxOfList services))
  | Construction.failWith error => Prim.failure (Cause.fail error)
  | Construction.acquire services label =>
    Prim.onSuccess (scopeAddProgram scope (FinName.release label false))
      (Name.constant (encode (ctxOfList services)))
  | Construction.fromService input output =>
    Prim.onSuccess (serviceProgram input) (Name.bindService output)

/-- `mergeAllEffect(layers, memoMap, scope)`'s fork loop (`:1597`): one sequential child of the
parallel parent per layer, each layer's build forked as a tracked child fiber; then all awaited. -/
def mergeForkAll (memoMap : MemoMapId) (parent : Nat) :
    List LayerId → List FiberId → Program
  | [], forked => Prim.onSuccess (act (ActionName.awaitAllFailFast forked)) Name.mergeContexts
  | layer :: rest, forked =>
    Prim.onSuccess (syncOp (SyncOp.scopeFork parent FinalizerStrategy.sequential))
      (Name.mergeForkOne layer rest memoMap parent forked)

/-- `mergeAllEffect` (`:1587-1602`): one `"parallel"` scope forked from the caller scope first. -/
def mergeAllEffectProgram (layers : List LayerId) (memoMap : MemoMapId) (scope : Nat) : Program :=
  Prim.onSuccess (syncOp (SyncOp.scopeFork scope FinalizerStrategy.parallel))
    (Name.mergeChildren layers memoMap)

/-- `self.build(memoMap, scope)` by the declared description (`Layer.ts`, one arm per constructor
site). `atom` builds directly (`:296`); `fresh` calls the inner build with a brand-new map on the
same scope (`:3851`); every other description is a `fromBuild` wrapper (`:339-344`, `:386`,
`:1915`, `:1658`) that forks a child of the caller scope first. -/
def layerBuildProgram (table : LayerTable) (layer : LayerId) (memoMap : MemoMapId) (scope : Nat) :
    Program :=
  match table[layer.index]? with
  | none => Prim.failure (Cause.die (Defect.unknownLayer layer.index))
  | some (LayerDesc.atom construction) => constructionProgram construction scope
  | some (LayerDesc.fresh inner) =>
    Prim.onSuccess (syncOp (SyncOp.memoFork none)) (Name.freshThen inner scope)
  | some desc =>
    Prim.onSuccess (syncOp (SyncOp.scopeFork scope FinalizerStrategy.sequential))
      (Name.fromBuildThen desc layer memoMap)

/-- What runs inside a `fromBuild` wrapper, on the forked child scope. -/
def innerBuildProgram (table : LayerTable) (desc : LayerDesc) (self : LayerId)
    (memoMap : MemoMapId) (child : Nat) : Program :=
  match desc with
  | LayerDesc.memoized construction => getOrElseMemoizeProgram self memoMap child construction  -- :386
  | LayerDesc.childScope inner => layerBuildProgram table inner memoMap child                    -- :342
  | LayerDesc.provideWith self' that mode =>                                                    -- :1916-1919
    Prim.onSuccess (layerBuildProgram table that memoMap child)
      (Name.provideThen self' memoMap child mode)
  | LayerDesc.mergeAll layers => mergeAllEffectProgram layers memoMap child                       -- :1658
  | LayerDesc.atom construction => constructionProgram construction child
  | LayerDesc.fresh inner => layerBuildProgram table inner memoMap child

/-- The program a scope finalizer *name* runs (`internal/effect.ts:4021`: an `OnExit` finalizer is
a program, run as one). -/
def finProgram : FinName → ExitV → Program
  | FinName.closeChildScope scope, exit => act (ActionName.closeScope scope exit)          -- :3841
  | FinName.detachFromParent parent key, _ => syncOp (SyncOp.scopeRemove parent key)       -- :3842
  | FinName.closeChildOnFailure scope, Exit.failure cause =>                              -- Layer.ts:343
    act (ActionName.closeScope scope (Exit.failure cause))
  | FinName.closeChildOnFailure _, Exit.success _ => Prim.success Val.unit
  | FinName.memoEntry layer memoMap, exit =>                                               -- Layer.ts:402
    Prim.suspend (Thunk.body (ProgName.memoReleaseOf layer memoMap exit))
  | FinName.memoDone layer memoMap, exit => syncOp (SyncOp.memoComplete layer memoMap exit) -- :414-417
  | FinName.restoreContext prev, _ => act (ActionName.setContext prev)                     -- :2093
  | FinName.scopedExit prev scope, exit =>                                                 -- :3944-3945
    Prim.onSuccess (act (ActionName.setContext prev)) (Name.thenClose scope exit)
  | FinName.closeScopeWith scope, exit => act (ActionName.closeScope scope exit)          -- :3958, :3967
  | FinName.release label fails, _ =>
    if fails then Prim.failure (Cause.fail (Err.tag label)) else Prim.success Val.unit
  | FinName.releaseWith label captured, _ =>                                               -- :3983
    updateContextProgram (ContextUpdate.provide captured) (ProgName.releaseOf label)
  | FinName.interruptFiber fiber true, _ => act (ActionName.interruptScoped fiber)         -- :5369-5371
  | FinName.interruptFiber fiber false, _ => act (ActionName.interrupt fiber)              -- :5458

/-- The sequential close chain (`internal/effect.ts:3813-3818`).
-- SHIM: `Deep.Stores.closeSeqChain`. -/
def closeSeqChain : List FinName → ExitV → List ReasonV → Program
  | [], _, captured => Prim.ofExit (voidAllOf captured)
  | fin :: rest, exit, captured =>
    Prim.onSuccessAndFailure (finProgram fin exit) (Name.closeSeq rest exit captured)
      (Name.closeSeq rest exit captured)

/-- The parallel close chain (`:3819-3826`): every finalizer an immediate daemon with the closer's
mask, then all awaited and merged.
-- SHIM: `Deep.Stores.closeParChain`. -/
def closeParChain (closerInterruptible : Bool) : List FinName → ExitV → List FiberId → Program
  | [], _, forked => Prim.onSuccess (act (ActionName.awaitAll forked)) Name.mergeAwaitedExits
  | fin :: rest, exit, forked =>
    Prim.onSuccess
      (act (ActionName.fork (ProgName.finalizerOf fin exit)
        ⟨true, true,
          if closerInterruptible then Supervision.MaskMode.interruptible
          else Supervision.MaskMode.uninterruptible⟩))
      (Name.closePar rest exit forked closerInterruptible)

/-- The close program of a scope (`internal/effect.ts:3779-3798` and `:3806-3827`): state first.
-- SHIM: `Deep.Stores.storesCloseScope`. -/
def closeScopeProgram (scope : Nat) (exit : ExitV) (closerInterruptible : Bool) (st : St) :
    Option (St × Program) :=
  match st.scopes.entryAt scope with
  | none => none
  | some entry =>
    if entry.scope.isClosed then some (st, Prim.success Val.unit)
    else
      let order := entry.scope.closeOrder
      let st := { st with scopes := st.scopes.setEntry { entry with scope := entry.scope.closeState exit } }
      match entry.scope.strategy with
      | FinalizerStrategy.sequential => some (st, closeSeqChain order exit [])
      | FinalizerStrategy.parallel => some (st, closeParChain closerInterruptible order exit [])

/-- The declared programs. -/
def progOf (table : LayerTable) : ProgName → Program
  | ProgName.value v => Prim.success v
  | ProgName.failCause cause => Prim.failure cause
  | ProgName.getContext => act ActionName.getContext                                    -- :2153
  | ProgName.service key => serviceProgram key
  | ProgName.setContextTo context body => updateContextProgram (ContextUpdate.setTo context) body
  | ProgName.provideContext context body =>                                              -- :2196-2197
    match progOf table body with
    | Prim.success v => Prim.success v
    | Prim.failure cause => Prim.failure cause
    | _ => updateContextProgram (ContextUpdate.provide context) body
  | ProgName.provideService key value body =>                                            -- :2232
    updateContextProgram (ContextUpdate.provideService key value) body
  | ProgName.scoped body => scopedProgram body
  | ProgName.acquireRelease acquire release interruptible =>
    acquireReleaseProgram acquire release interruptible
  | ProgName.acquireMasked acquire release captured interruptible =>                     -- :3978-3985
    Prim.onSuccess (serviceProgram scopeKey)
      (Name.acquireInScope acquire release captured interruptible)
  | ProgName.addFinalizer label =>                                                       -- :3993-3998
    Prim.onSuccess (serviceProgram scopeKey) (Name.addFinalizerOn label)
  | ProgName.seq first second => Prim.onSuccess (progOf table first) (Name.seq second)
  | ProgName.never => Prim.async Name.neverRegister false none                           -- :1172
  | ProgName.closeScope scope exit => act (ActionName.closeScope scope exit)
  | ProgName.build layer =>                                                              -- Layer.ts:803
    Prim.onSuccess (act ActionName.getContext) (Name.buildFromContext layer)
  | ProgName.buildWithScope layer scope =>                                               -- :974
    Prim.onSuccess (act ActionName.getContext) (Name.buildWithScopeFromContext layer scope)
  | ProgName.buildWithMemoMap layer memoMap scope => buildWithMemoMapProgram layer memoMap scope
  | ProgName.layerBuild layer memoMap scope => layerBuildProgram table layer memoMap scope
  | ProgName.buildAdding layer memoMap scope =>                                          -- :762
    Prim.onSuccess (layerBuildProgram table layer memoMap scope) (Name.addCurrentMemoMap memoMap)
  | ProgName.buildThenNever layer =>                                                     -- :3898
    Prim.onSuccess (Prim.onSuccess (act ActionName.getContext) (Name.buildFromContext layer))
      (Name.seq ProgName.never)
  | ProgName.launch layer => scopedProgram (ProgName.buildThenNever layer)               -- :3898
  | ProgName.provideLayer layer isLocal body =>                                          -- internal/layer.ts:15
    Prim.suspend (Thunk.body (ProgName.scopedWithAlloc layer isLocal body))
  | ProgName.scopedWithAlloc layer isLocal body =>                                       -- internal/effect.ts:3966
    Prim.onSuccess (syncOp (SyncOp.scopeMake FinalizerStrategy.sequential))
      (Name.provideLayerWith layer isLocal body)
  | ProgName.memoLookup layer memoMap scope construction =>                              -- Layer.ts:451
    Prim.onSuccess (syncOp (SyncOp.memoGet layer memoMap))
      (Name.memoize layer memoMap scope construction)
  | ProgName.finalizerOf fin exit => finProgram fin exit
  | ProgName.memoReleaseOf layer memoMap exit =>                                         -- :403-408
    Prim.onSuccess (syncOp (SyncOp.memoRelease layer memoMap)) (Name.closeIfLast exit)
  | ProgName.releaseOf _ => Prim.success Val.unit

/-! ### The continuations that read a context value

Each is a function of `Option Ctx`, so that a theorem about it can rewrite `decode (encode c)`
by `decode_encode` and never has to match a compiled `match`. -/

/-- `updateContext` on the previous context (`:2088-2095`): `f(prev)`; if unchanged the body
runs as is (`:2090`, object identity there, data equality here); else `setContext(next)` and the
restoring frame. -/
def updateThenK (table : LayerTable) (update : ContextUpdate) (body : ProgName) :
    Option Ctx → Program
  | none => Prim.failure (Cause.die Defect.badName)
  | some prev =>
    let next := update.apply prev
    if next = prev then progOf table body
    else Prim.onSuccess (act (ActionName.setContext next)) (Name.bodyThen body prev)

/-- `scoped` on the previous context (`:3940-3941`): allocate the fresh default scope. -/
def scopedThenK (body : ProgName) : Option Ctx → Program
  | none => Prim.failure (Cause.die Defect.badName)
  | some prev =>
    Prim.onSuccess (syncOp (SyncOp.scopeMake FinalizerStrategy.sequential))
      (Name.scopedInstall body prev)

/-- `Effect.service(key)` on the context: the value, or the host throw as a defect. -/
def serviceLookupK (key : ServiceKey) : Option Ctx → Program
  | none => Prim.failure (Cause.die Defect.badName)
  | some ctx =>
    match ctx.getV key with
    | some value => Prim.success value
    | none => Prim.failure (Cause.die (Defect.serviceNotFound key))

/-- `acquireRelease`'s `contextWith` (`:3976-3977`): capture, then `uninterruptibleMask`. -/
def acquireWithK (acquire : ProgName) (release : Nat) (interruptible : Bool) :
    Option Ctx → Program
  | none => Prim.failure (Cause.die Defect.badName)
  | some captured =>
    act (ActionName.setInterruptible
      (ProgName.acquireMasked acquire release captured interruptible) false)

/-- `addFinalizer`'s `contextWith` (`:3996-3997`): register the release with the captured context. -/
def addFinalizerCapturedK (scope : Nat) (label : Nat) : Option Ctx → Program
  | none => Prim.failure (Cause.die Defect.badName)
  | some captured => scopeAddProgram scope (FinName.releaseWith label captured)

/-- `Layer.build` on the fiber context (`Layer.ts:803-808`): `forkOrCreate` first, then the
unchecked `Scope` lookup, carried to the continuation. -/
def buildFromContextK (layer : LayerId) : Option Ctx → Program
  | none => Prim.failure (Cause.die Defect.badName)
  | some ctx =>
    Prim.onSuccess (syncOp (SyncOp.memoFork (currentMemoMapOf ctx)))
      (Name.withMemoMapThen layer (ambientScope ctx))

/-- `Layer.buildWithScope` on the fiber context (`:974-979`): the memo map is still forked. -/
def buildWithScopeFromContextK (layer : LayerId) (scope : Nat) : Option Ctx → Program
  | none => Prim.failure (Cause.die Defect.badName)
  | some ctx =>
    Prim.onSuccess (syncOp (SyncOp.memoFork (currentMemoMapOf ctx)))
      (Name.withMemoMapThen layer (some scope))

/-- `Context.add(CurrentMemoMap, memoMap)` over the built context (`:762`). -/
def addCurrentMemoMapK (memoMap : MemoMapId) : Option Ctx → Program
  | none => Prim.failure (Cause.die Defect.badName)
  | some ctx => Prim.success (encode (ctx.addV currentMemoMapKey (Val.memoMap memoMap.index)))

/-- `provideWith` on the dependency's context (`:1920-1923`): the dependent's build under
`provideContext(context)`, then the combiner. -/
def provideThenK (self : LayerId) (memoMap : MemoMapId) (scope : Nat) (mode : CombineMode) :
    Option Ctx → Program
  | none => Prim.failure (Cause.die Defect.badName)
  | some ctx =>
    Prim.onSuccess (updateContextProgram (ContextUpdate.provide ctx)
      (ProgName.layerBuild self memoMap scope)) (Name.combineWith mode ctx)

/-- `f(merged, context)` (`:1923`): `identity` for `provide` (`:2348`),
`Context.merge(that, self)` for `provideMerge`. -/
def combineWithK (mode : CombineMode) (thatContext : Ctx) : Option Ctx → Program
  | none => Prim.failure (Cause.die Defect.badName)
  | some merged =>
    match mode with
    | CombineMode.provide => Prim.success (encode merged)
    | CombineMode.provideMerge => Prim.success (encode (thatContext.merge merged))

/-- `flatMap(build, context => provideContext(self, context))` (`internal/layer.ts:20`). -/
def provideLayerBodyK (body : ProgName) : Option Ctx → Program
  | none => Prim.failure (Cause.die Defect.badName)
  | some ctx => updateContextProgram (ContextUpdate.provide ctx) body

/-- The contexts of a list of exits, when every one succeeded with a context. -/
def contextsOf : List ExitV → Option (List Ctx)
  | [] => some []
  | Exit.success value :: rest =>
    match decode value, contextsOf rest with
    | some ctx, some ctxs => some (ctx :: ctxs)
    | _, _ => none
  | Exit.failure _ :: _ => none

/-- `Context.mergeAll(...contexts)` (`Layer.ts:1600`) over the awaited exits; a failed build fails
the merge with every failure's reasons. -/
def mergeExitContexts (exits : List ExitV) : Program :=
  match contextsOf exits with
  | some ctxs => Prim.success (encode (Context.mergeAll ctxs))
  | none =>
    match exits.flatMap Exit.causeReasons with
    | [] => Prim.failure (Cause.die Defect.badName)
    | reason :: rest => Prim.failure ⟨reason :: rest⟩

/-- `cont[contA](value, fiber)`. -/
def contAOf (table : LayerTable) : Name → Val → Program
  | Name.restore exit, _ => Prim.ofExit exit
  | Name.merge exit, _ => Prim.ofExit exit
  | Name.seq next, _ => progOf table next
  | Name.constant value, _ => Prim.success value
  | Name.closeSeq rest exit captured, _ => closeSeqChain rest exit captured
  | Name.closePar rest exit forked masked, Val.fiber id => closeParChain masked rest exit (forked ++ [id])
  | Name.closePar rest exit forked masked, _ => closeParChain masked rest exit forked
  | Name.mergeAwaitedExits, value => Prim.ofExit (voidAllOf (reasonsOfVal value))
  | Name.afterScopeAdd _, Val.unit => Prim.success Val.unit                              -- :3856
  | Name.afterScopeAdd fin, Val.exitOk value => finProgram fin (Exit.success value)        -- :3853
  | Name.afterScopeAdd fin, Val.exitErr cause => finProgram fin (Exit.failure cause)
  | Name.afterScopeAdd _, _ => Prim.failure (Cause.die Defect.badName)
  | Name.updateThen update body, value => updateThenK table update body (decode value)
  | Name.bodyThen body prev, _ =>                                                        -- :2092
    Prim.onExit (progOf table body) (Name.finalizerName (FinName.restoreContext prev)) false
  | Name.scopedThen body, value => scopedThenK body (decode value)
  | Name.scopedInstall body prev, Val.scopeHandle scope =>                                -- :3942
    Prim.onSuccess (act (ActionName.setContext (prev.addV scopeKey (Val.scopeHandle scope))))
      (Name.scopedBody body prev scope)
  | Name.scopedInstall _ _, _ => Prim.failure (Cause.die Defect.badName)
  | Name.scopedBody body prev scope, _ =>                                                 -- :3943
    Prim.scopedFrame (progOf table body) (Name.finalizerName (FinName.scopedExit prev scope))
  | Name.thenClose scope exit, _ => act (ActionName.closeScope scope exit)                -- :3945
  | Name.serviceLookup key, value => serviceLookupK key (decode value)
  | Name.bindService output, value => Prim.success (encode (Context.empty.addV output value))
  | Name.acquireWith acquire release interruptible, value =>
    acquireWithK acquire release interruptible (decode value)
  | Name.acquireInScope acquire release captured interruptible, Val.scopeHandle scope =>   -- :3981-3982
    Prim.onSuccess
      (if interruptible then act (ActionName.setInterruptible acquire true)
        else progOf table acquire)
      (Name.registerRelease scope release captured)
  | Name.acquireInScope _ _ _ _, _ => Prim.failure (Cause.die Defect.badName)
  | Name.registerRelease scope release captured, value =>                                 -- :3983
    Prim.onSuccess (scopeAddProgram scope (FinName.releaseWith release captured)) (Name.constant value)
  | Name.addFinalizerOn label, Val.scopeHandle scope =>
    Prim.onSuccess (act ActionName.getContext) (Name.addFinalizerCaptured scope label)
  | Name.addFinalizerOn _, _ => Prim.failure (Cause.die Defect.badName)
  | Name.addFinalizerCaptured scope label, value => addFinalizerCapturedK scope label (decode value)
  | Name.buildFromContext layer, value => buildFromContextK layer (decode value)
  | Name.buildWithScopeFromContext layer scope, value =>
    buildWithScopeFromContextK layer scope (decode value)
  | Name.withMemoMapThen layer (some scope), Val.memoMap id => buildWithMemoMapProgram layer ⟨id⟩ scope
  | Name.withMemoMapThen _ none, Val.memoMap _ =>                                          -- Layer.ts:807
    Prim.failure (Cause.die (Defect.serviceNotFound scopeKey))
  | Name.withMemoMapThen _ _, _ => Prim.failure (Cause.die Defect.badName)
  | Name.addCurrentMemoMap memoMap, value => addCurrentMemoMapK memoMap (decode value)
  | Name.memoize layer _ scope _, Val.pair (Val.promise cell) (Val.memoMap owner) =>       -- :439-440, :246-249
    Prim.onSuccess (scopeAddProgram scope (FinName.memoEntry layer ⟨owner⟩)) (Name.awaitPromise ⟨cell⟩)
  | Name.memoize layer memoMap scope construction, Val.unit =>                              -- :455
    memoBuildProgram layer memoMap scope construction
  | Name.memoize _ _ _ _, _ => Prim.failure (Cause.die Defect.badName)
  | Name.awaitPromise cell, _ =>                                                            -- :400
    Prim.async (Name.registerAwait cell) true (some (Name.cancelAwait cell))
  | Name.buildIntoLayerScope layer memoMap scope construction, Val.scopeHandle layerScope => -- :412
    Prim.onSuccess (scopeAddProgram scope (FinName.memoEntry layer memoMap))
      (Name.thenBuildInto layer memoMap construction layerScope)
  | Name.buildIntoLayerScope _ _ _ _, _ => Prim.failure (Cause.die Defect.badName)
  | Name.thenBuildInto layer memoMap construction layerScope, _ =>                          -- :413-414
    Prim.onExit (constructionProgram construction layerScope)
      (Name.finalizerName (FinName.memoDone layer memoMap)) false
  | Name.closeIfLast exit, Val.scopeHandle scope => act (ActionName.closeScope scope exit) -- :406
  | Name.closeIfLast _, _ => Prim.success Val.unit                                          -- :408
  | Name.fromBuildThen desc self memoMap, Val.scopeHandle child =>                           -- :341-344
    Prim.onExit (innerBuildProgram table desc self memoMap child)
      (Name.finalizerName (FinName.closeChildOnFailure child)) false
  | Name.fromBuildThen _ _ _, _ => Prim.failure (Cause.die Defect.badName)
  | Name.freshThen inner scope, Val.memoMap id => layerBuildProgram table inner ⟨id⟩ scope   -- :3851
  | Name.freshThen _ _, _ => Prim.failure (Cause.die Defect.badName)
  | Name.provideThen self memoMap scope mode, value => provideThenK self memoMap scope mode (decode value)
  | Name.combineWith mode thatContext, value => combineWithK mode thatContext (decode value)
  | Name.mergeChildren layers memoMap, Val.scopeHandle parent => mergeForkAll memoMap parent layers []
  | Name.mergeChildren _ _, _ => Prim.failure (Cause.die Defect.badName)
  | Name.mergeForkOne layer rest memoMap parent forked, Val.scopeHandle child =>              -- :1597
    Prim.onSuccess
      (act (ActionName.fork (ProgName.layerBuild layer memoMap child)
        ⟨true, false, Supervision.MaskMode.inherit⟩))
      (Name.mergeForkNext rest memoMap parent forked)
  | Name.mergeForkOne _ _ _ _ _, _ => Prim.failure (Cause.die Defect.badName)
  | Name.mergeForkNext rest memoMap parent forked, Val.fiber id =>
    mergeForkAll memoMap parent rest (forked ++ [id])
  | Name.mergeForkNext _ _ _ _, _ => Prim.failure (Cause.die Defect.badName)
  | Name.mergeContexts, value => mergeExitContexts (exitsOfVal value)
  | Name.provideLayerWith layer isLocal body, Val.scopeHandle scope =>                       -- internal/layer.ts:15-21
    Prim.onExit
      (Prim.onSuccess
        (if isLocal then
          Prim.onSuccess (syncOp (SyncOp.memoFork none)) (Name.withMemoMapThen layer (some scope))
        else Prim.onSuccess (act ActionName.getContext) (Name.buildWithScopeFromContext layer scope))
        (Name.provideLayerBody body))
      (Name.finalizerName (FinName.closeScopeWith scope)) false
  | Name.provideLayerWith _ _ _, _ => Prim.failure (Cause.die Defect.badName)
  | Name.provideLayerBody body, value => provideLayerBodyK body (decode value)
  | _, value => Prim.success value

/-- `cont[contE](cause, fiber)`. -/
def contEOf : Name → CauseV → Program
  | Name.restore exit, cause => Prim.ofExit (Exit.restoreAfterFinalizer exit (Exit.failure cause))
  | Name.merge exit, cause => Prim.ofExit (Exit.restoreAfterFinalizer exit (Exit.failure cause))
  | Name.closeSeq rest exit captured, cause => closeSeqChain rest exit (captured ++ cause.reasons)
  | _, cause => Prim.failure cause

/-- The cancel effect a cancel name runs (M3). -/
def cancelProgram : Name → Program
  | Name.withWaiter (Name.cancelAwait cell) waiter token =>
    syncOp (SyncOp.deferredAwaitCleanup cell waiter token)
  | _ => Prim.success Val.unit

/-- `WithFiberAction` from a name. -/
def actionOf (table : LayerTable) : ActionName → WithFiberAction Name Thunk Val Err Defect FiberId Ann Ctx
  | ActionName.fork program options => WithFiberAction.fork (progOf table program) options
  | ActionName.forkScoped program options key =>
    WithFiberAction.forkScoped (progOf table program) options key
  | ActionName.interrupt target => WithFiberAction.interrupt target
  | ActionName.interruptScoped target => WithFiberAction.interruptScoped target
  | ActionName.awaitAll targets => WithFiberAction.awaitAll targets
  | ActionName.awaitAllFailFast targets => WithFiberAction.awaitAllFailFast targets
  | ActionName.setContext context => WithFiberAction.setContext context
  | ActionName.getContext => WithFiberAction.getContext
  | ActionName.getId => WithFiberAction.getId
  | ActionName.closeScope scope exit => WithFiberAction.closeScope scope exit
  | ActionName.setInterruptible body flag => WithFiberAction.setInterruptible (progOf table body) flag
  | ActionName.refuse cause => WithFiberAction.refuse cause

/-! ## The interp -/

/-- The `RunInterp` of this instantiation, over a declared layer table. DB-07 as in S2: every arm
threads the store out; none restores a snapshot. -/
def interp (table : LayerTable) : RunInterp Name Thunk Val Err Defect FiberId Ann Ctx St where
  contA := contAOf table
  contE := contEOf
  syncValue := fun _ => Val.unit
  suspendBody := fun
    | Thunk.body program => progOf table program
    | _ => Prim.failure (Cause.die Defect.notImplemented)
  finalizerExit := fun _ _ => Exit.void
  reifyExit := reifyExitVal
  iterNext := fun _ value => ([], IterStep.done value)
  loopTest := fun _ _ => false
  loopBody := fun _ value => Prim.success value
  loopStep := fun _ _ value => value
  loopDone := fun _ => Val.unit
  notImplemented := Defect.notImplemented
  cancelThenFail := fun name cause => Prim.onSuccess (cancelProgram name) (Name.reFail cause)
  parkOf := fun _ => none
  withFiberOf := fun
    | Thunk.act action => some (actionOf table action)
    | _ => none
  syncState := fun
    | Thunk.op operation, state => syncStep operation state
    | _, _ => none
  registerAsync := fun name fiber token state =>
    match name with
    | Name.registerAwait cell =>
      let (deferreds, immediate) := state.deferreds.register cell fiber token
      ({ state with deferreds := deferreds }, immediate)
    | _ => (state, none)
  dueResumes := fun state =>
    let (due, deferreds) := state.deferreds.drainDue
    (due, { state with deferreds := deferreds })
  cancelName := fun base fiber token => Name.withWaiter base fiber token
  abortName := Name.abortController
  finalizerProgram := fun
    | Name.finalizerName fin, exit => some (finProgram fin exit)
    | _, _ => none
  restoreName := Name.restore
  mergeName := Name.merge
  scopeStatus := fun scope state => state.scopes.status scope
  scopeLinkFiber := fun mode scope key fiber state =>
    match state.scopes.entryAt scope with
    | none => none
    | some entry =>
      let skipSelf :=
        match mode with
        | Supervision.ScopeMode.forkIn => true
        | Supervision.ScopeMode.fiberRunIn => false
      some { state with
        scopes := state.scopes.setEntry
          { entry with scope := entry.scope.addUnsafe key (FinName.interruptFiber fiber skipSelf) } }
  dropFinalizer := fun scope key state =>
    match state.scopes.entryAt scope with
    | none => none
    | some _ => some { state with scopes := state.scopes.removeFinalizer scope key }
  closeScope := fun scope exit closerInterruptible _closer state =>
    closeScopeProgram scope exit closerInterruptible state
  ambientScope := Env.ambientScope
  budgetOf := Env.budgetOf
  emptyContext := Context.empty
  contextValue := encode
  exitValue := fun exit mode =>
    match mode with
    | Supervision.ObserverMode.awaitValue => Prim.success (reifyExitVal exit)
    | Supervision.ObserverMode.joinEffect => Prim.ofExit exit
  fiberValue := Val.fiber
  fibersValue := Val.fibers
  exitsValue := exitsVal
  voidValue := Val.unit
  encodeFiber := id
  stackAnnotations := fun _ => ReasonAnnotations.empty
  asyncFiberError := Defect.asyncFiber
  missingScope := Defect.serviceNotFound scopeKey

/-- The four hooks of `Deep.Context` are read verbatim. -/
theorem interp_hooks (table : LayerTable) : HooksAgree (interp table) := ⟨rfl, rfl, rfl, rfl⟩

/-! ## The census clauses, one theorem each

Every `layer.*` row of `generated/effect-runtime-census.tsv` (sixteen), plus `scope.scoped` and
`scope.acquire-release`, clause by clause. A theorem over a *program shape* says what the machine
will run; a theorem over `syncStep` says what the store does when it runs; the witnesses below run
them. -/

section Clauses

variable (table : LayerTable)

/-! ### `layer.from-build-unsafe` (`Layer.ts:289-298`) -/

/-- An atom's build is its construction at the given scope, with no scope handling of its own.
census: layer.from-build-unsafe -/
theorem fromBuildUnsafe_atom (layer : LayerId) (c : Construction) (memoMap : MemoMapId) (scope : Nat)
    (h : table[layer.index]? = some (LayerDesc.atom c)) :
    layerBuildProgram table layer memoMap scope = constructionProgram c scope := by
  simp only [layerBuildProgram, h]

/-- A succeeding construction is one `Success` of its context: no fork, no finalizer.
census: layer.from-build-unsafe -/
theorem fromBuildUnsafe_no_scope (services : List (ServiceKey × Val)) (scope : Nat) :
    constructionProgram (Construction.succeedContext services) scope =
      Prim.success (encode (ctxOfList services)) := rfl

/-! ### `layer.from-build-child-scope` (`:333-345`) -/

/-- `fromBuild` forks a sequential child of the caller scope before building.
census: layer.from-build-child-scope -/
theorem fromBuild_forks_child (layer inner : LayerId) (memoMap : MemoMapId) (scope : Nat)
    (h : table[layer.index]? = some (LayerDesc.childScope inner)) :
    layerBuildProgram table layer memoMap scope =
      Prim.onSuccess (syncOp (SyncOp.scopeFork scope FinalizerStrategy.sequential))
        (Name.fromBuildThen (LayerDesc.childScope inner) layer memoMap) := by
  simp only [layerBuildProgram, h]

/-- The fork is `scopeForkUnsafe` (`internal/effect.ts:3834-3844`): the parent gains
`scopeClose(child)` and the child `scopeRemoveFinalizerUnsafe(parent, key)` under one key.
census: layer.from-build-child-scope, scope.fork-linkage -/
theorem scopeFork_links (parent : Nat) (strategy : FinalizerStrategy) (st : St) (entry : ScopeEntry)
    (h : st.scopes.entryAt parent = some entry) :
    syncStep (SyncOp.scopeFork parent strategy) st =
      some ({ st with
          scopes := st.scopes.forkChild parent st.nextName (st.nextName + 1) strategy
          nextName := st.nextName + 2 },
        Val.scopeHandle st.nextName) := by
  simp only [syncStep, h]

/-- The build runs inside an `onExit` whose finalizer is `closeChildOnFailure`.
census: layer.from-build-child-scope -/
theorem fromBuild_frame (desc : LayerDesc) (self : LayerId) (memoMap : MemoMapId) (child : Nat) :
    contAOf table (Name.fromBuildThen desc self memoMap) (Val.scopeHandle child) =
      Prim.onExit (innerBuildProgram table desc self memoMap child)
        (Name.finalizerName (FinName.closeChildOnFailure child)) false := rfl

/-- A failing build closes the child scope with the failing exit (`:343`, `Failure` arm).
census: layer.from-build-child-scope -/
theorem fromBuild_closes_on_failure (child : Nat) (cause : CauseV) :
    finProgram (FinName.closeChildOnFailure child) (Exit.failure cause) =
      act (ActionName.closeScope child (Exit.failure cause)) := rfl

/-- A successful build leaves the child scope, and so its finalizers, attached to the caller
(`:343`, the `void` arm). census: layer.from-build-child-scope -/
theorem fromBuild_keeps_on_success (child : Nat) (value : Val) :
    finProgram (FinName.closeChildOnFailure child) (Exit.success value) = Prim.success Val.unit := rfl

/-! ### `layer.build-with-memo-map-service` (`:756-765`) -/

/-- `buildWithMemoMap` is `provideService(map(build, add CurrentMemoMap), CurrentMemoMap, m)`.
census: layer.build-with-memo-map-service -/
theorem buildWithMemoMap_provides (layer : LayerId) (memoMap : MemoMapId) (scope : Nat) :
    progOf table (ProgName.buildWithMemoMap layer memoMap scope) =
      updateContextProgram
        (ContextUpdate.provideService currentMemoMapKey (Val.memoMap memoMap.index))
        (ProgName.buildAdding layer memoMap scope) := rfl

/-- The installed service is readable as `CurrentMemoMap` during the build.
census: layer.build-with-memo-map-service -/
theorem buildWithMemoMap_installs (memoMap : MemoMapId) (prev : Ctx) :
    currentMemoMapOf
        ((ContextUpdate.provideService currentMemoMapKey (Val.memoMap memoMap.index)).apply prev) =
      some memoMap := by
  show memoMapOfVal (((ContextUpdate.provideService currentMemoMapKey
    (Val.memoMap memoMap.index)).apply prev).getV currentMemoMapKey) = some memoMap
  rw [ContextUpdate.apply_provideService_getV]
  rfl

/-- `updateContext` sets the context and pushes the restoring frame, unless nothing changed
(`internal/effect.ts:2088-2095`). census: layer.build-with-memo-map-service -/
theorem updateContext_sets_and_restores (update : ContextUpdate) (body : ProgName) (prev : Ctx) :
    contAOf table (Name.updateThen update body) (encode prev) =
      (if update.apply prev = prev then progOf table body
        else Prim.onSuccess (act (ActionName.setContext (update.apply prev)))
          (Name.bodyThen body prev)) := by
  show updateThenK table update body (decode (encode prev)) = _
  rw [decode_encode]
  rfl

/-- The restoring frame is an `OnExit` whose finalizer is `setContext(prev)` (`:2092-2093`).
census: layer.build-with-memo-map-service -/
theorem updateContext_restore_frame (body : ProgName) (prev : Ctx) (value : Val) :
    contAOf table (Name.bodyThen body prev) value =
      Prim.onExit (progOf table body) (Name.finalizerName (FinName.restoreContext prev)) false ∧
    finProgram (FinName.restoreContext prev) (Exit.success value) = act (ActionName.setContext prev) :=
  ⟨rfl, rfl⟩

/-- The same memo map is added to the produced context (`:762`).
census: layer.build-with-memo-map-service -/
theorem buildWithMemoMap_adds_to_result (memoMap : MemoMapId) (ctx : Ctx) :
    contAOf table (Name.addCurrentMemoMap memoMap) (encode ctx) =
      Prim.success (encode (ctx.addV currentMemoMapKey (Val.memoMap memoMap.index))) := by
  show addCurrentMemoMapK memoMap (decode (encode ctx)) = _
  rw [decode_encode]
  rfl

/-! ### `layer.memo-build-once` (`:390-419`) -/

/-- The entry `memoMapBuild` stores (`:398-410`). -/
def memoBuildEntry (layer : LayerId) (memoMap : MemoMapId) (st : St) : MemoEntry :=
  ⟨1, Prim.async (Name.registerAwait st.deferreds.make.1) true (some (Name.cancelAwait st.deferreds.make.1)),
    st.nextName, st.deferreds.make.1, FinName.memoEntry layer memoMap⟩

/-- The first build allocates a root layer scope and a Deferred and stores an entry with one
observer whose effect is that Deferred's await (`:396-411`). census: layer.memo-build-once -/
theorem memoBuild_allocates (layer : LayerId) (memoMap : MemoMapId) (st : St) :
    syncStep (SyncOp.memoBuild layer memoMap) st =
      some ({ st with
          scopes := st.scopes.make st.nextName FinalizerStrategy.sequential
          deferreds := st.deferreds.make.2
          memo := st.memo.insertEntry memoMap layer (memoBuildEntry layer memoMap st)
          nextName := st.nextName + 1 },
        Val.scopeHandle st.nextName) := rfl

/-- One observer, the await as the effect, the entry finalizer as the name.
census: layer.memo-build-once -/
theorem memoBuild_entry (layer : LayerId) (memoMap : MemoMapId) (st : St) :
    (memoBuildEntry layer memoMap st).observers = 1 ∧
      (memoBuildEntry layer memoMap st).effect =
        Prim.async (Name.registerAwait st.deferreds.make.1) true
          (some (Name.cancelAwait st.deferreds.make.1)) ∧
      (memoBuildEntry layer memoMap st).finalizer = FinName.memoEntry layer memoMap := ⟨rfl, rfl, rfl⟩

/-- The entry finalizer is registered on the *caller* scope before the build (`:412`).
census: layer.memo-build-once -/
theorem memoBuild_registers_on_caller (layer : LayerId) (memoMap : MemoMapId) (scope layerScope : Nat)
    (c : Construction) :
    contAOf table (Name.buildIntoLayerScope layer memoMap scope c) (Val.scopeHandle layerScope) =
      Prim.onSuccess (scopeAddProgram scope (FinName.memoEntry layer memoMap))
        (Name.thenBuildInto layer memoMap c layerScope) := rfl

/-- The build runs into the *layer* scope under the completing `onExit` (`:413-417`).
census: layer.memo-build-once -/
theorem memoBuild_builds_into_layer_scope (layer : LayerId) (memoMap : MemoMapId) (layerScope : Nat)
    (c : Construction) (value : Val) :
    contAOf table (Name.thenBuildInto layer memoMap c layerScope) value =
      Prim.onExit (constructionProgram c layerScope)
        (Name.finalizerName (FinName.memoDone layer memoMap)) false := rfl

/-- On exit the entry effect becomes the exit and the Deferred is completed with it, as an
effect (`:415-416`). census: layer.memo-build-once -/
theorem memoBuild_onExit (layer : LayerId) (memoMap : MemoMapId) (exit : ExitV) (st : St)
    (entry : MemoEntry) (h : st.memo.entryAt memoMap layer = some entry) :
    finProgram (FinName.memoDone layer memoMap) exit = syncOp (SyncOp.memoComplete layer memoMap exit) ∧
    syncStep (SyncOp.memoComplete layer memoMap exit) st =
      some ({ st with
          memo := st.memo.updateEntry memoMap layer fun e => { e with effect := Prim.ofExit exit }
          deferreds := (st.deferreds.complete entry.deferred (Prim.ofExit exit)).1 },
        Val.unit) := by
  refine ⟨rfl, ?_⟩
  simp only [syncStep, h]

/-- Every other observer shares the one build: a lookup after the build hits the own map.
census: layer.memo-build-once, layer.memo-map-parent-lookup -/
theorem MemoWorld.get_hit (w : MemoWorld) (layer : LayerId) (id : MemoMapId) (entry : MemoEntry)
    (h : w.entryAt id layer = some entry) : w.get layer id = some (id, entry) := by
  simp only [MemoWorld.get, MemoWorld.lookup, h]

/-! ### `layer.memo-finalizer-last-observer` (`:401-410`) -/

/-- The entry finalizer is a `suspend` whose body decrements and closes only at zero.
census: layer.memo-finalizer-last-observer -/
theorem memoEntry_finalizer (layer : LayerId) (memoMap : MemoMapId) (exit : ExitV) :
    finProgram (FinName.memoEntry layer memoMap) exit =
      Prim.suspend (Thunk.body (ProgName.memoReleaseOf layer memoMap exit)) ∧
    progOf table (ProgName.memoReleaseOf layer memoMap exit) =
      Prim.onSuccess (syncOp (SyncOp.memoRelease layer memoMap)) (Name.closeIfLast exit) := ⟨rfl, rfl⟩

/-- A close that does not reach zero decrements and is void (`:403`, `:408`).
census: layer.memo-finalizer-last-observer -/
theorem memoRelease_decrements (layer : LayerId) (memoMap : MemoMapId) (st : St) (entry : MemoEntry)
    (h : st.memo.entryAt memoMap layer = some entry) (hobs : 1 < entry.observers) :
    syncStep (SyncOp.memoRelease layer memoMap) st =
      some ({ st with
          memo := st.memo.updateEntry memoMap layer fun e => { e with observers := e.observers - 1 } },
        Val.unit) := by
  simp only [syncStep, h, if_neg (Nat.not_le.mpr hobs)]

/-- The close that brings the count to zero deletes the entry and answers the layer scope, which
the continuation closes with the closing exit (`:404-406`).
census: layer.memo-finalizer-last-observer -/
theorem memoRelease_last (layer : LayerId) (memoMap : MemoMapId) (st : St) (entry : MemoEntry)
    (h : st.memo.entryAt memoMap layer = some entry) (hobs : entry.observers ≤ 1) :
    syncStep (SyncOp.memoRelease layer memoMap) st =
      some ({ st with memo := st.memo.deleteEntry memoMap layer }, Val.scopeHandle entry.layerScope) := by
  simp only [syncStep, h, if_pos hobs]

/-- Only a scope handle closes; the void answer closes nothing.
census: layer.memo-finalizer-last-observer -/
theorem closeIfLast_arms (exit : ExitV) (scope : Nat) :
    contAOf table (Name.closeIfLast exit) (Val.scopeHandle scope) = act (ActionName.closeScope scope exit) ∧
    contAOf table (Name.closeIfLast exit) Val.unit = Prim.success Val.unit := ⟨rfl, rfl⟩

/-! ### `layer.memo-reuse-observer-count` (`:241-250`) -/

/-- A memo hit increments the owning entry's observer count and answers its Deferred and owner.
census: layer.memo-reuse-observer-count -/
theorem memoGet_hit (layer : LayerId) (memoMap owner : MemoMapId) (st : St) (entry : MemoEntry)
    (h : st.memo.get layer memoMap = some (owner, entry)) :
    syncStep (SyncOp.memoGet layer memoMap) st =
      some ({ st with
          memo := st.memo.updateEntry owner layer fun e => { e with observers := e.observers + 1 } },
        Val.pair (Val.promise entry.deferred.index) (Val.memoMap owner.index)) := by
  simp only [syncStep, h]

/-- The hit registers the *same* entry finalizer name on the new caller scope and then yields the
memoized effect (`:246-249`). census: layer.memo-reuse-observer-count -/
theorem memoize_hit (layer : LayerId) (memoMap : MemoMapId) (scope : Nat) (c : Construction)
    (cell owner : Nat) :
    contAOf table (Name.memoize layer memoMap scope c) (Val.pair (Val.promise cell) (Val.memoMap owner)) =
      Prim.onSuccess (scopeAddProgram scope (FinName.memoEntry layer ⟨owner⟩))
        (Name.awaitPromise ⟨cell⟩) := rfl

/-- Reuse rebuilds nothing: the scopes, the Deferreds and the name counter are untouched.
census: layer.memo-reuse-observer-count -/
theorem memoGet_rebuilds_nothing (layer : LayerId) (memoMap : MemoMapId) (st : St) :
    (syncStep (SyncOp.memoGet layer memoMap) st).map (fun r => (r.1.scopes, r.1.deferreds, r.1.nextName)) =
      some (st.scopes, st.deferreds, st.nextName) := by
  cases h : st.memo.get layer memoMap with
  | none => simp only [syncStep, h, Option.map]
  | some p =>
    obtain ⟨owner, entry⟩ := p
    simp only [syncStep, h, Option.map]

/-! ### `layer.memo-map-parent-lookup` (`:434-443`) -/

/-- On a miss in the own map the lookup delegates to the parent.
census: layer.memo-map-parent-lookup -/
theorem MemoWorld.get_parent (w : MemoWorld) (layer : LayerId) (id parent : MemoMapId) (m : MemoMap)
    (hmiss : w.entryAt id layer = none) (hmap : w.mapAt id = some m) (hparent : m.parent = some parent) :
    w.get layer id = w.lookup layer w.length parent := by
  simp only [MemoWorld.get, MemoWorld.lookup, hmiss, hmap, hparent]

/-! ### `layer.memo-get-or-else` (`:445-457`) -/

/-- `getOrElseMemoize` suspends, so the lookup happens at run time; a hit returns the memoized
effect (the Deferred's await); a miss starts exactly one `memoMapBuild`.
census: layer.memo-get-or-else -/
theorem getOrElseMemoize_shape (layer : LayerId) (memoMap : MemoMapId) (scope : Nat) (c : Construction)
    (cell : DeferredKey) (value : Val) :
    getOrElseMemoizeProgram layer memoMap scope c =
        Prim.suspend (Thunk.body (ProgName.memoLookup layer memoMap scope c)) ∧
      progOf table (ProgName.memoLookup layer memoMap scope c) =
        Prim.onSuccess (syncOp (SyncOp.memoGet layer memoMap)) (Name.memoize layer memoMap scope c) ∧
      contAOf table (Name.awaitPromise cell) value =
        Prim.async (Name.registerAwait cell) true (some (Name.cancelAwait cell)) ∧
      contAOf table (Name.memoize layer memoMap scope c) Val.unit =
        memoBuildProgram layer memoMap scope c := ⟨rfl, rfl, rfl, rfl⟩

/-! ### `layer.current-memo-map-fork-or-create` (`:585-588`) -/

/-- A bound `CurrentMemoMap` is forked from; an unbound one is created fresh, with no parent.
census: layer.current-memo-map-fork-or-create -/
theorem forkOrCreate (ctx : Ctx) (id : Nat) (parent : Option MemoMapId) (st : St) :
    currentMemoMapOf (ctx.addV currentMemoMapKey (Val.memoMap id)) = some ⟨id⟩ ∧
      currentMemoMapOf Context.empty = none ∧
      syncStep (SyncOp.memoFork parent) st =
        some ({ st with memo := st.memo ++ [⟨⟨st.nextName⟩, parent, []⟩], nextName := st.nextName + 1 },
          Val.memoMap st.nextName) := by
  refine ⟨?_, rfl, rfl⟩
  show memoMapOfVal ((ctx.addV currentMemoMapKey (Val.memoMap id)).getV currentMemoMapKey) = _
  rw [Context.getV_addV_same]
  rfl

/-! ### `layer.build-uses-ambient-scope` (`:800-809`) -/

/-- `Layer.build` reads both inputs off the fiber context: the memo map by `forkOrCreate`, the scope
by an unchecked lookup carried to the continuation; a missing scope dies there, a typed error
never. census: layer.build-uses-ambient-scope -/
theorem build_uses_ambient_scope (layer : LayerId) (ctx : Ctx) (id scope : Nat) :
    progOf table (ProgName.build layer) =
        Prim.onSuccess (act ActionName.getContext) (Name.buildFromContext layer) ∧
      contAOf table (Name.buildFromContext layer) (encode ctx) =
        Prim.onSuccess (syncOp (SyncOp.memoFork (currentMemoMapOf ctx)))
          (Name.withMemoMapThen layer (ambientScope ctx)) ∧
      contAOf table (Name.withMemoMapThen layer none) (Val.memoMap id) =
        Prim.failure (Cause.die (Defect.serviceNotFound scopeKey)) ∧
      contAOf table (Name.withMemoMapThen layer (some scope)) (Val.memoMap id) =
        buildWithMemoMapProgram layer ⟨id⟩ scope := by
  refine ⟨rfl, ?_, rfl, rfl⟩
  show buildFromContextK layer (decode (encode ctx)) = _
  rw [decode_encode]
  rfl

/-! ### `layer.build-with-scope-still-forks-memo` (`:970-980`) -/

/-- `buildWithScope` replaces only the scope; the memo map is still forked or created.
census: layer.build-with-scope-still-forks-memo -/
theorem buildWithScope_forks_memo (layer : LayerId) (scope : Nat) (ctx : Ctx) :
    contAOf table (Name.buildWithScopeFromContext layer scope) (encode ctx) =
      Prim.onSuccess (syncOp (SyncOp.memoFork (currentMemoMapOf ctx)))
        (Name.withMemoMapThen layer (some scope)) := by
  show buildWithScopeFromContextK layer scope (decode (encode ctx)) = _
  rw [decode_encode]
  rfl

/-! ### `layer.merge-parallel-scopes` (`:1587-1602`) -/

/-- `mergeAll` is a `fromBuild`; inside, one parallel scope is forked from the caller scope, each
layer gets its own sequential child, every build is forked over the one memo map, and the exits
are awaited together and merged. census: layer.merge-parallel-scopes -/
theorem mergeAll_scopes (layer self : LayerId) (layers rest : List LayerId) (l : LayerId)
    (memoMap : MemoMapId) (scope child parent : Nat) (forked : List FiberId) (exits : List ExitV)
    (h : table[layer.index]? = some (LayerDesc.mergeAll layers)) :
    layerBuildProgram table layer memoMap scope =
        Prim.onSuccess (syncOp (SyncOp.scopeFork scope FinalizerStrategy.sequential))
          (Name.fromBuildThen (LayerDesc.mergeAll layers) layer memoMap) ∧
      innerBuildProgram table (LayerDesc.mergeAll layers) self memoMap child =
        Prim.onSuccess (syncOp (SyncOp.scopeFork child FinalizerStrategy.parallel))
          (Name.mergeChildren layers memoMap) ∧
      mergeForkAll memoMap parent (l :: rest) forked =
        Prim.onSuccess (syncOp (SyncOp.scopeFork parent FinalizerStrategy.sequential))
          (Name.mergeForkOne l rest memoMap parent forked) ∧
      contAOf table (Name.mergeForkOne l rest memoMap parent forked) (Val.scopeHandle child) =
        Prim.onSuccess
          (act (ActionName.fork (ProgName.layerBuild l memoMap child)
            ⟨true, false, Supervision.MaskMode.inherit⟩))
          (Name.mergeForkNext rest memoMap parent forked) ∧
      mergeForkAll memoMap parent [] forked =
        Prim.onSuccess (act (ActionName.awaitAllFailFast forked)) Name.mergeContexts ∧
      contAOf table Name.mergeContexts (exitsVal exits) = mergeExitContexts exits := by
  refine ⟨?_, rfl, rfl, rfl, rfl, ?_⟩
  · simp only [layerBuildProgram, h]
  · show mergeExitContexts (exitsOfVal (exitsVal exits)) = _
    rw [exitsOfVal_exitsVal]

/-- The merge of the built contexts is `Context.mergeAll` (`:1600`).
census: layer.merge-parallel-scopes -/
theorem mergeExitContexts_success (exits : List ExitV) (ctxs : List Ctx) (h : contextsOf exits = some ctxs) :
    mergeExitContexts exits = Prim.success (encode (Context.mergeAll ctxs)) := by
  simp only [mergeExitContexts, h]

/-! ### `layer.provide-dependency-first` (`:1907-1926`) -/

/-- `provide` is a `fromBuild`; the dependency builds first on the same memo map and scope, its
context is provided to the dependent's build, and the combiner is the identity for `provide` and
`Context.merge(that, self)` for `provideMerge`. census: layer.provide-dependency-first -/
theorem provide_dependency_first (layer self that : LayerId) (mode : CombineMode) (memoMap : MemoMapId)
    (scope child : Nat) (ctx merged : Ctx)
    (h : table[layer.index]? = some (LayerDesc.provideWith self that mode)) :
    layerBuildProgram table layer memoMap scope =
        Prim.onSuccess (syncOp (SyncOp.scopeFork scope FinalizerStrategy.sequential))
          (Name.fromBuildThen (LayerDesc.provideWith self that mode) layer memoMap) ∧
      innerBuildProgram table (LayerDesc.provideWith self that mode) layer memoMap child =
        Prim.onSuccess (layerBuildProgram table that memoMap child)
          (Name.provideThen self memoMap child mode) ∧
      contAOf table (Name.provideThen self memoMap child mode) (encode ctx) =
        Prim.onSuccess
          (updateContextProgram (ContextUpdate.provide ctx) (ProgName.layerBuild self memoMap child))
          (Name.combineWith mode ctx) ∧
      contAOf table (Name.combineWith CombineMode.provide ctx) (encode merged) =
        Prim.success (encode merged) ∧
      contAOf table (Name.combineWith CombineMode.provideMerge ctx) (encode merged) =
        Prim.success (encode (ctx.merge merged)) := by
  refine ⟨?_, rfl, ?_, ?_, ?_⟩
  · simp only [layerBuildProgram, h]
  · show provideThenK self memoMap child mode (decode (encode ctx)) = _
    rw [decode_encode]
    rfl
  · show combineWithK CombineMode.provide ctx (decode (encode merged)) = _
    rw [decode_encode]
    rfl
  · show combineWithK CombineMode.provideMerge ctx (decode (encode merged)) = _
    rw [decode_encode]
    rfl

/-! ### `layer.fresh-drops-memoization` (`:3850-3851`) -/

/-- `fresh` calls the inner build directly with a brand-new memo map (no parent) on the same
scope, with no `fromBuild` child scope of its own. census: layer.fresh-drops-memoization -/
theorem fresh_drops_memoization (layer inner : LayerId) (memoMap : MemoMapId) (scope id : Nat)
    (h : table[layer.index]? = some (LayerDesc.fresh inner)) :
    layerBuildProgram table layer memoMap scope =
        Prim.onSuccess (syncOp (SyncOp.memoFork none)) (Name.freshThen inner scope) ∧
      contAOf table (Name.freshThen inner scope) (Val.memoMap id) =
        layerBuildProgram table inner ⟨id⟩ scope := by
  refine ⟨?_, rfl⟩
  simp only [layerBuildProgram, h]

/-! ### `layer.launch-holds-scope` (`:3897-3898`) -/

/-- `launch` is `scoped(andThen(build(self), never))`; `never` is an `Async` whose registration
never resumes, so the fiber parks and the scope stays open until it is interrupted. The park is
`op.Async`, which the plan's premise 5 marks partial. census: layer.launch-holds-scope -/
theorem launch_holds_scope (layer : LayerId) (fiber : FiberId) (token : Nat) (st : St) :
    progOf table (ProgName.launch layer) = scopedProgram (ProgName.buildThenNever layer) ∧
      progOf table (ProgName.buildThenNever layer) =
        Prim.onSuccess (progOf table (ProgName.build layer)) (Name.seq ProgName.never) ∧
      progOf table ProgName.never = Prim.async Name.neverRegister false none ∧
      (interp table).registerAsync Name.neverRegister fiber token st = (st, none) := ⟨rfl, rfl, rfl, rfl⟩

/-! ### `layer.provide-effect-scope` (`internal/layer.ts:8-22`) -/

/-- `provide` opens a fresh scope around the program (`scopedWith`), builds the layer into it,
provides the built context, and closes the scope with the program's exit; the `local` option
builds through a private memo map. census: layer.provide-effect-scope -/
theorem provideLayer_scope (layer : LayerId) (isLocal : Bool) (body : ProgName) (scope : Nat)
    (ctx : Ctx) (exit : ExitV) :
    progOf table (ProgName.provideLayer layer isLocal body) =
        Prim.suspend (Thunk.body (ProgName.scopedWithAlloc layer isLocal body)) ∧
      progOf table (ProgName.scopedWithAlloc layer isLocal body) =
        Prim.onSuccess (syncOp (SyncOp.scopeMake FinalizerStrategy.sequential))
          (Name.provideLayerWith layer isLocal body) ∧
      contAOf table (Name.provideLayerWith layer true body) (Val.scopeHandle scope) =
        Prim.onExit
          (Prim.onSuccess
            (Prim.onSuccess (syncOp (SyncOp.memoFork none)) (Name.withMemoMapThen layer (some scope)))
            (Name.provideLayerBody body))
          (Name.finalizerName (FinName.closeScopeWith scope)) false ∧
      contAOf table (Name.provideLayerWith layer false body) (Val.scopeHandle scope) =
        Prim.onExit
          (Prim.onSuccess
            (Prim.onSuccess (act ActionName.getContext) (Name.buildWithScopeFromContext layer scope))
            (Name.provideLayerBody body))
          (Name.finalizerName (FinName.closeScopeWith scope)) false ∧
      contAOf table (Name.provideLayerBody body) (encode ctx) =
        updateContextProgram (ContextUpdate.provide ctx) body ∧
      finProgram (FinName.closeScopeWith scope) exit = act (ActionName.closeScope scope exit) := by
  refine ⟨rfl, rfl, rfl, rfl, ?_, rfl⟩
  show provideLayerBodyK body (decode (encode ctx)) = _
  rw [decode_encode]
  rfl

/-! ### `scope.scoped` (`internal/effect.ts:3937-3947`) — M6 -/

/-- `scoped` reads the context, allocates a fresh default scope, installs it in the fiber context
(`Context.add(fiber.context, scopeTag, scope)`), and runs the body under `Prim.scopedFrame` whose
finalizer restores the previous context *first* and then closes the scope with the fiber's exit.
census: scope.scoped -/
theorem scoped_installs_and_restores (body : ProgName) (prev : Ctx) (scope : Nat) (value : Val)
    (exit : ExitV) :
    scopedProgram body = Prim.onSuccess (act ActionName.getContext) (Name.scopedThen body) ∧
      contAOf table (Name.scopedThen body) (encode prev) =
        Prim.onSuccess (syncOp (SyncOp.scopeMake FinalizerStrategy.sequential))
          (Name.scopedInstall body prev) ∧
      contAOf table (Name.scopedInstall body prev) (Val.scopeHandle scope) =
        Prim.onSuccess (act (ActionName.setContext (prev.addV scopeKey (Val.scopeHandle scope))))
          (Name.scopedBody body prev scope) ∧
      ambientScope (prev.addV scopeKey (Val.scopeHandle scope)) = some scope ∧
      contAOf table (Name.scopedBody body prev scope) value =
        Prim.scopedFrame (progOf table body) (Name.finalizerName (FinName.scopedExit prev scope)) ∧
      (interp table).finalizerProgram (Name.finalizerName (FinName.scopedExit prev scope)) exit =
        some (Prim.onSuccess (act (ActionName.setContext prev)) (Name.thenClose scope exit)) ∧
      contAOf table (Name.thenClose scope exit) value = act (ActionName.closeScope scope exit) := by
  refine ⟨rfl, ?_, rfl, ambientScope_add_scope prev scope, rfl, rfl, rfl⟩
  show scopedThenK body (decode (encode prev)) = _
  rw [decode_encode]
  rfl

/-! ### `scope.acquire-release` (`:3970-3987`) -/

/-- `acquireRelease` captures the context first (`contextWith`), runs under `uninterruptibleMask`,
restores interruptibility for the acquire only when asked, and registers on the ambient scope a
release that re-provides the captured context. census: scope.acquire-release -/
theorem acquireRelease_captured_context (acquire : ProgName) (release : Nat) (ctx : Ctx) (scope : Nat)
    (value : Val) (exit : ExitV) :
    acquireReleaseProgram acquire release true =
        Prim.onSuccess (act ActionName.getContext) (Name.acquireWith acquire release true) ∧
      contAOf table (Name.acquireWith acquire release true) (encode ctx) =
        act (ActionName.setInterruptible (ProgName.acquireMasked acquire release ctx true) false) ∧
      progOf table (ProgName.acquireMasked acquire release ctx true) =
        Prim.onSuccess (serviceProgram scopeKey) (Name.acquireInScope acquire release ctx true) ∧
      contAOf table (Name.acquireInScope acquire release ctx true) (Val.scopeHandle scope) =
        Prim.onSuccess (act (ActionName.setInterruptible acquire true))
          (Name.registerRelease scope release ctx) ∧
      contAOf table (Name.acquireInScope acquire release ctx false) (Val.scopeHandle scope) =
        Prim.onSuccess (progOf table acquire) (Name.registerRelease scope release ctx) ∧
      contAOf table (Name.registerRelease scope release ctx) value =
        Prim.onSuccess (scopeAddProgram scope (FinName.releaseWith release ctx)) (Name.constant value) ∧
      finProgram (FinName.releaseWith release ctx) exit =
        updateContextProgram (ContextUpdate.provide ctx) (ProgName.releaseOf release) := by
  refine ⟨rfl, ?_, rfl, rfl, rfl, rfl, rfl⟩
  show acquireWithK acquire release true (decode (encode ctx)) = _
  rw [decode_encode]
  rfl

end Clauses

/-! ## The executable witnesses

Each `#guard` below *runs*: the store steps under `syncStep`, and whole programs through the
machine of `Deep.Fibers` at this `interp`, from `St.empty` and `Context.empty`, on the sync
scheduler (`Deep.Fibers.runSyncExit`, rc.112's `runSyncExitWith`, `internal/effect.ts:5500`).
The clause theorems above say what shape the machine will run; these say what running it
answers. -/

section Witnesses

/-- Two service keys the witness layers construct. -/
def keyA : ServiceKey := ⟨⟨10⟩, ⟨10⟩⟩
def keyB : ServiceKey := ⟨⟨11⟩, ⟨11⟩⟩

/-- The declared table. `0` an atom; `1` and `2` memoized atoms; `3` a `fromBuild` child scope
of `1`; `4` `fresh 1`; `5` `mergeAll [1, 2]`; `6` `mergeAll [1, 1]`, the same layer twice under
one memo map; `7` `provideWith 8 1 provide`, whose dependent reads `keyA` and binds `keyB`;
`8` that dependent; `9` a build that fails; `10` a build that acquires. -/
def witnessTable : LayerTable :=
  [ LayerDesc.atom (Construction.succeedContext [(keyA, Val.nat 1)])
  , LayerDesc.memoized (Construction.succeedContext [(keyA, Val.nat 1)])
  , LayerDesc.memoized (Construction.succeedContext [(keyB, Val.nat 2)])
  , LayerDesc.childScope ⟨1⟩
  , LayerDesc.fresh ⟨1⟩
  , LayerDesc.mergeAll [⟨1⟩, ⟨2⟩]
  , LayerDesc.mergeAll [⟨1⟩, ⟨1⟩]
  , LayerDesc.provideWith ⟨8⟩ ⟨1⟩ CombineMode.provide
  , LayerDesc.atom (Construction.fromService keyA keyB)
  , LayerDesc.atom (Construction.failWith (Err.tag 9))
  , LayerDesc.atom (Construction.acquire [(keyB, Val.nat 3)] 5) ]

/-! ### Store witnesses: `syncStep` alone -/

/-- `memoBuild` then `memoGet` on the seeded store: one entry, and the hit bumps it to two. -/
def memoBuildThenGet : Option (St × Val) :=
  (syncStep (SyncOp.memoBuild ⟨0⟩ ⟨1⟩) St.seeded).bind fun r =>
    syncStep (SyncOp.memoGet ⟨0⟩ ⟨1⟩) r.1

/-- The observer counts of every entry of every map, as (map id, layer index, observers). -/
def memoCensus (st : St) : List (Nat × Nat × Nat) :=
  st.memo.flatMap fun m => m.entries.map fun e => (m.id.index, e.1.index, e.2.observers)

#guard (memoCensus St.seeded) = []
#guard (memoBuildThenGet.map fun r => memoCensus r.1) = some [(1, 0, 2)]
#guard (memoBuildThenGet.map fun r => (syncStep (SyncOp.memoRelease ⟨0⟩ ⟨1⟩) r.1).isSome) =
  some true

/-- One release off two observers decrements and keeps the entry; the second deletes it. -/
def memoReleaseTwice : Option St :=
  (memoBuildThenGet.bind fun r => syncStep (SyncOp.memoRelease ⟨0⟩ ⟨1⟩) r.1).bind fun r =>
    (syncStep (SyncOp.memoRelease ⟨0⟩ ⟨1⟩) r.1).map Prod.fst

#guard ((memoBuildThenGet.bind fun r => syncStep (SyncOp.memoRelease ⟨0⟩ ⟨1⟩) r.1).map
  fun r => memoCensus r.1) = some [(1, 0, 1)]
#guard (memoReleaseTwice.map memoCensus) = some []

-- The last release answers the layer scope handle `memoBuild` allocated (`Layer.ts:406`).
#guard ((memoBuildThenGet.bind fun r => syncStep (SyncOp.memoRelease ⟨0⟩ ⟨1⟩) r.1).bind
  fun r => (syncStep (SyncOp.memoRelease ⟨0⟩ ⟨1⟩) r.1).map Prod.snd) = some (Val.scopeHandle 2)

/-- A forked map: the parent is the seeded map `⟨1⟩`, the fork takes the next name, `⟨3⟩`. -/
def forkedWorld : Option St :=
  (memoBuildThenGet.bind fun r => syncStep (SyncOp.memoFork (some ⟨1⟩)) r.1).map Prod.fst

/-- One open sequential scope `0`, the shape `scopeFork` links a child onto. -/
def oneScope : ScopeStore := ⟨[⟨0, Effect4.Scope.make FinalizerStrategy.sequential⟩]⟩

/-- `scopeForkUnsafe(parent, strategy)` (`internal/effect.ts:3834-3844`): child `1`, shared
key `2`. -/
def forkedScopes : ScopeStore := oneScope.forkChild 0 1 2 FinalizerStrategy.sequential

-- `scope.fork-linkage`: the parent gains `scopeClose(child, exit)` (`:3841`) and the child
-- gains `scopeRemoveFinalizerUnsafe(parent, key)` (`:3842`), under the one shared key.
#guard ((forkedScopes.entryAt 0).map fun e => e.scope.closeOrder) =
  some [FinName.closeChildScope 1]
#guard ((forkedScopes.entryAt 1).map fun e => e.scope.closeOrder) =
  some [FinName.detachFromParent 0 2]

-- A forked map's lookup falls through to the parent (`:434-443`); an undeclared map answers
-- nothing.
#guard (forkedWorld.map fun st => (st.memo.get ⟨0⟩ ⟨3⟩).map fun p => p.1.index) = some (some 1)
#guard (forkedWorld.map fun st => (st.memo.get ⟨0⟩ ⟨99⟩).isSome) = some false

/-! ### Machine witnesses: whole programs -/

/-- The machine at this instantiation. -/
abbrev LayerMachine := Effect4.Deep.RunMachine Name Thunk Val Err Defect FiberId Ann Ctx St

/-- The fuel every witness runs with. -/
def witnessFuel : Nat := 512

/-- Run a named program as the root fiber over the empty context, on the sync scheduler. -/
def runWitness (program : ProgName) : LayerMachine × ExitV :=
  Effect4.Deep.runSyncExit (interp witnessTable) witnessFuel
    (Effect4.Deep.RunMachine.empty St.empty) (progOf witnessTable program) Context.empty

def witnessExit (program : ProgName) : ExitV := (runWitness program).2
def witnessStore (program : ProgName) : St := (runWitness program).1.state

/-- Whether the run succeeded. -/
def witnessOk (program : ProgName) : Bool :=
  match witnessExit program with
  | Exit.success _ => true
  | _ => false

/-- The services the answered context holds, as (key name, value) pairs in insertion order. -/
def witnessServices (program : ProgName) : List (Nat × Nat) :=
  match witnessExit program with
  | Exit.success value =>
    match decode value with
    | some ctx => ctx.entries.map fun s => (s.key.name.value, natOfVal 0 s.valueVal)
    | none => []
  | _ => []

/-- The memo entries left in the store when the run ended. -/
def witnessMemo (program : ProgName) : List (Nat × Nat × Nat) := memoCensus (witnessStore program)

/-- Every memo map the run allocated: id, parent, number of entries. -/
def witnessMaps (program : ProgName) : List (Nat × Option Nat × Nat) :=
  (witnessStore program).memo.map fun m => (m.id.index, m.parent.map MemoMapId.index, m.entries.length)

/-- Every scope the run allocated, with whether it is closed. -/
def witnessScopes (program : ProgName) : List (Nat × Bool) :=
  (witnessStore program).scopes.entries.map fun e => (e.key, e.scope.isClosed)

/-- W1 `layer.build-uses-ambient-scope`, `scope.scoped`: `scoped(build(atom))` answers the
atom's context; the scope `scoped` allocated is closed on the way out. -/
def w1 : ProgName := ProgName.scoped (ProgName.build ⟨0⟩)
#guard witnessOk w1
#guard witnessServices w1 = [(10, 1), (3, 0)]
#guard witnessMemo w1 = []

/-- W2 `layer.build-uses-ambient-scope`: without an ambient `Scope` the build dies
(`Layer.ts:807` through `internal/effect.ts:670-674`), and never fails typed. -/
def w2 : ProgName := ProgName.build ⟨0⟩
#guard witnessOk w2 = false

/-- W3 `layer.memo-build-once`, `layer.memo-reuse-observer-count`: `mergeAll [1, 1]` names one
memoized layer twice under one memo map, so it is constructed once and observed twice. -/
def w3 : ProgName := ProgName.scoped (ProgName.build ⟨6⟩)
#guard witnessOk w3
#guard witnessServices w3 = [(10, 1), (3, 0)]
-- After the run the entry is gone: the outer `scoped` now closes (the machine delivers the
-- exit to the frame `getCont` answers with, `Fibers.finalizerOr`), and the close that brings
-- the observer count to zero deletes the entry (`layer.memo-finalizer-last-observer`). The
-- mid-run census "one construction, two observers" is pinned at the store level by the
-- `syncStep` witnesses above.
#guard witnessMemo w3 = []

/-- W4 `layer.merge-parallel-scopes`: two distinct layers merge into one context. -/
def w4 : ProgName := ProgName.scoped (ProgName.build ⟨5⟩)
#guard witnessOk w4
#guard witnessServices w4 = [(10, 1), (11, 2), (3, 0)]

/-- W5 `layer.provide-dependency-first`: the dependency builds first, its `keyA` is provided to
the dependent, and `provide`'s combiner keeps only the dependent's `keyB`. -/
def w5 : ProgName := ProgName.scoped (ProgName.build ⟨7⟩)
#guard witnessOk w5
#guard witnessServices w5 = [(11, 1), (3, 0)]

/-- W6 `layer.provide-effect-scope`: `Effect.provide` builds the layer into a fresh scope and
the body reads the provided service. -/
def w6 : ProgName := ProgName.provideLayer ⟨1⟩ true (ProgName.service keyA)
#guard witnessOk w6
#guard witnessExit w6 = Exit.success (Val.nat 1)
-- `provide`'s fresh scope closes on the way out, and its single observer's close deletes
-- the entry (`layer.provide-effect-scope`, `layer.memo-finalizer-last-observer`).
#guard witnessMemo w6 = []

/-- W7: a failing build fails the program with the typed error, not a defect. -/
def w7 : ProgName := ProgName.scoped (ProgName.build ⟨9⟩)
#guard witnessOk w7 = false

/-- W8 `layer.fresh-drops-memoization`: `fresh` builds through a private map, so the caller's
map holds no entry for the inner layer. -/
def w8 : ProgName := ProgName.scoped (ProgName.build ⟨4⟩)
#guard witnessOk w8
-- Both maps exist and both are empty at the end: the caller's never held the inner entry
-- (`fresh` builds through the private map), and the private map's entry was deleted when
-- the scope closed. The private map is `⟨2⟩` and stays parentless.
#guard witnessMemo w8 = []
#guard witnessMaps w8 = [(1, none, 0), (2, none, 0)]
#guard witnessServices w8 = [(10, 1), (3, 0)]

/-- W9 `layer.from-build-child-scope`: a `fromBuild` wrapper builds its inner layer on a forked
child scope and succeeds. -/
def w9 : ProgName := ProgName.scoped (ProgName.build ⟨3⟩)
#guard witnessOk w9
#guard witnessServices w9 = [(10, 1), (3, 0)]

/-- W10 `scope.acquire-release`: the release is registered on the ambient scope with the
captured context, and the acquire's value is the program's answer. -/
def w10 : ProgName :=
  ProgName.scoped (ProgName.acquireRelease (ProgName.value (Val.nat 5)) 3 false)
#guard witnessExit w10 = Exit.success (Val.nat 5)

/-- W11 `layer.launch-holds-scope`: `launch` parks on `never`, so the root never exits and the
sync run reports rc.112's `AsyncFiberError` defect rather than an answer. -/
def w11 : ProgName := ProgName.launch ⟨0⟩
#guard witnessExit w11 = Exit.failure (Cause.die Defect.asyncFiber)

/-! ### A machine defect this spike found, and its fix

`scoped` must close its scope whether or not another `OnExit` frame sits under it. The first
`Deep.Fibers.finalizerOr` took the program-finalizer path only when the stack's **head** was
`Prim.onExit`, while the frame machine delivers an exit to the frame `getCont` answers with,
skipping frames that do not declare the demanded arm (`Effect4/Runtime/Runtime.lean:2300`,
`getCont Arm.contA false`). An inner `onExit`'s `ensure` pushes exactly such a mask-restoring
frame (`Runtime.lean:697-703`), so the outer `OnExit` was reached by a pass and answered by the
pure shortcut `armA`; two adjacent `OnExit` frames ran one finalizer program, not two. Every
`Layer` build sits under `updateContext`'s restoring frame (`internal/effect.ts:2092`), so
every `scoped(build …)` had this shape. `finalizerOr` now consults `getCont` with the same
demand and skip as `resumeValue`/`resumeCause` and intercepts the answering frame
(`Effect4/Deep/Fibers.lean`, `finalizerOr`), so rc.112's behaviour — both finalizer programs
run, both scopes close (`internal/effect.ts:4021`) — is what the witnesses below pin. -/

/-- How many `OnExit` finalizer *programs* a run actually ran. -/
def finProgCount (program : ProgName) : Nat :=
  ((runWitness program).1.trace.filter fun e =>
    match e with
    | Effect4.Deep.RunEvent.finalizerProgram _ _ _ => true
    | _ => false).length

-- One `OnExit`: the scope closes, and one finalizer program ran.
#guard witnessScopes (ProgName.scoped (ProgName.value (Val.nat 7))) = [(0, true)]
#guard finProgCount (ProgName.scoped (ProgName.value (Val.nat 7))) = 1

-- Two adjacent: both close, and both finalizer programs ran.
#guard witnessScopes (ProgName.scoped (ProgName.scoped (ProgName.value (Val.nat 7)))) =
  [(0, true), (1, true)]
#guard finProgCount (ProgName.scoped (ProgName.scoped (ProgName.value (Val.nat 7)))) = 2

-- Separated by a continuation frame, both close as well.
#guard witnessScopes
    (ProgName.scoped (ProgName.seq (ProgName.scoped (ProgName.value (Val.nat 1)))
      (ProgName.value (Val.nat 7)))) = [(0, true), (1, true)]

-- The same shape every build has: `updateContext`'s restoring frame is the inner `OnExit`;
-- the build's scope closes and both programs run.
#guard witnessScopes w1 = [(0, true)]
#guard finProgCount w1 = 2
#guard witnessScopes w10 = [(0, true)]
end Witnesses

/-! ## The forgetful join to `Effect4.LayerFamily`

`Effect4/Layer/LayerFamily.lean` is the *traced* face of the same machinery: a `LayerStore`
of memo maps with a parent, observer counts, a construction ledger and a live set, rendered as
the `Layers` family's rows. The join runs one way only, and that module's docstring already
records why (`Effect4/Layer/LayerFamily.lean:36-54`): the store counts observers exactly and a
host trace cannot, so the direction that exists is the one that *forgets*. What it forgets
here is the Deferred, the layer scope's finalizer list, and the program an entry's `effect`
is; what it carries is the identity, the layer scope and the count. -/

section ForgetfulJoin

/-- A `Deep` memo entry as the family's: the count and the layer scope cross, the Deferred and
the entry program do not. `service` is the family's constructed-service handle, which this
model does not mint — the caller supplies it. -/
def forgetEntry (layer : LayerId) (service : Nat) (e : MemoEntry) :
    Effect4.LayerFamily.MemoEntry :=
  ⟨layer.index, service, e.layerScope, e.observers⟩

/-- A whole map: the parent chain the family's `memoChain` walks is the one carried here. -/
def forgetMap (m : MemoMap) : Effect4.LayerFamily.MemoMap :=
  ⟨m.parent.map MemoMapId.index, m.entries.map fun e => forgetEntry e.1 e.1.index e.2⟩

/-- The count is preserved, so `memoGet`'s bump and the family's `bumpObservers` agree.
census: layer.memo-reuse-observer-count -/
theorem forget_observers (layer : LayerId) (service : Nat) (e : MemoEntry) :
    (forgetEntry layer service { e with observers := e.observers + 1 }).observers =
      (forgetEntry layer service e).observers + 1 := rfl

/-- The layer scope crosses, so `Layers.scopeOf` reads the scope `memoMapBuild` allocated. -/
theorem forget_layerScope (layer : LayerId) (service : Nat) (e : MemoEntry) :
    (forgetEntry layer service e).scope = e.layerScope := rfl

/-- The parent crosses, so the family's parent-chain lookup is this model's `MemoWorld.lookup`
read forgetfully. census: layer.memo-map-parent-lookup -/
theorem forget_parent (m : MemoMap) : (forgetMap m).parent = m.parent.map MemoMapId.index := rfl

/-- A fresh map has no parent on either side. census: layer.fresh-drops-memoization -/
theorem forget_fresh (id : MemoMapId) :
    (forgetMap ⟨id, none, []⟩).parent = none ∧ (forgetMap ⟨id, none, []⟩).entries = [] :=
  ⟨rfl, rfl⟩

end ForgetfulJoin

end Effect4.Deep.Layers
