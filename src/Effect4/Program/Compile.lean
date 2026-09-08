import Effect4.Program.Native
import Effect4.Machine.Fibers

/-!
# Syntax.Compile — `Eff` to the frames, names as addresses (lane A3)

Plan: `docs/research/2026-09-04-eff-compile.md` §1-§2. `compileEff` takes a program and a
`Point` (the subterm's path in the root program, the values in scope, the fuel, the tape)
to a primitive of the frame machine over the name alphabet `EffName` and the thunk alphabet
`EffThunk`. Every name a continuation carries is a *point*, and `interpOf root` gives the
names their meaning by compiling the subterm the point addresses: the table is a function
of the program, so "the table is the AST" is a definition.

What this cut compiles: every constructor of `Eff` except the rows of kind `program` (the
Layer and Context models), which compile to the frontier. `acquireRelease` lowers as rc.112
does (`internal/effect.ts:3971-3987`: `contextWith → uninterruptibleMask → scope → tap(acquire,
scopeAddFinalizerExit)`); its release is a first-order `Capture` in the scope store
(`FinName.foreign`, V1 2026-09-07) that `suspendBodyAt` resolves when the scope closes, on
whichever fiber closes it. `choose` is answered by the point's tape. The stores are `src/Effect4/Machine/Stores.lean`'s, unchanged: the
store-touching arms of `interpOf` call the same `syncOpStep`, `DeferredStore.register`,
`storesCloseScope` and `cancelProgram`-shaped functions (`docs/research/2026-09-04-eff-compile.md`
G5); only the alphabet is new.

Generators (`gen`) compile to a `Suspend` at their own point whose body is one `Iterator`
primitive whose name carries the generator's program counter — a path from the body's
statement list to the list to run next — and the values in scope; `iterNext` walks pure
statements (`return`, `if` decided by the environment, `while`/`break`) with the point's
fuel, folds a yielded pure success inline (`Prim.iteratorFolded`), and resumes with the
*advanced* name (`IterStep.resume next continueAs`, the correction of 2026-09-04). A
block's bindings are dropped at its end, as a `const` inside a brace is.

Three clauses follow the pinned host's eager constructor behaviour rather than the frame a
constructor suggests (P0 record, `docs/research/2026-09-06-p0-fable-record.md`, rows D1–D3):
`exit` of a body that compiles to an immediate exit folds to `Prim.success` of the reified
exit, because `Effect.exit` returns `exitSucceed(self)` for an `Exit`
(`vendor/effect-4.0.0-rc.112/src/internal/effect.ts:3621-3622`); `gen` compiles to a
`Suspend`, because `Effect.gen` is `suspend(() => fromIteratorUnsafe(…))` (`:1175-1196`);
`whileLoop` compiles to a `Suspend`, because the printer wraps `Effect.whileLoop` in
`Effect.suspend` so that every run starts from the initial cursor
(`src/Effect4/Codegen/Print.lean:158-168`). `suspendBodyAt` answers the iterator or the
loop frame at that point, as it answers the branch a `branch` decides.
-/

namespace Effect4.Program

open Effect4 Effect4.Machine

/-! ## Nodes and paths -/

/-- A node of the mutual program family, addressed by a path of child indices. -/
inductive Node
  | eff (e : NativeEff)
  | stmts (s : Stmts NativeOp)
  | stmt (s : Stmt NativeOp)
  | action (a : ActionTerm NativeOp)
  | effs (es : Effs NativeOp)
  /-- A layer (the join): its path is its identity, `LayerId` (`Machine/Stores.lean`). -/
  | layer (l : LayerTerm NativeOp)
deriving DecidableEq

namespace Node

/-- The child at an index. Terms are not nodes: only programs, statements and actions are
addressed. -/
def child : Node → Nat → Option Node
  | eff (.suspend b), 0 => some (eff b)
  | eff (.bind a _), 0 => some (eff a)
  | eff (.bind _ b), 1 => some (eff b)
  | eff (.gen ss), 0 => some (stmts ss)
  | eff (.catchCause b _), 0 => some (eff b)
  | eff (.catchCause _ h), 1 => some (eff h)
  | eff (.matchCause b _ _), 0 => some (eff b)
  | eff (.matchCause _ v _), 1 => some (eff v)
  | eff (.matchCause _ _ c), 2 => some (eff c)
  | eff (.onExit b _), 0 => some (eff b)
  | eff (.onExit _ f), 1 => some (eff f)
  | eff (.exit b), 0 => some (eff b)
  | eff (.uninterruptible b), 0 => some (eff b)
  | eff (.interruptible b), 0 => some (eff b)
  | eff (.branch _ a _), 0 => some (eff a)
  | eff (.branch _ _ b), 1 => some (eff b)
  | eff (.whileLoop _ _ _ b), 0 => some (eff b)
  | eff (.withFiber a), 0 => some (action a)
  | eff (.scoped b), 0 => some (eff b)
  | eff (.acquireRelease a _), 0 => some (eff a)
  | eff (.acquireRelease _ r), 1 => some (eff r)
  | eff (.choose _ l _), 0 => some (eff l)
  | eff (.choose _ _ r), 1 => some (eff r)
  | eff (.provideLayer l _ _), 0 => some (layer l)
  | eff (.provideLayer _ _ b), 1 => some (eff b)
  | eff (.provideService _ _ b), 0 => some (eff b)
  | layer (.effect _ b), 0 => some (eff b)
  | layer (.effectDiscard b), 0 => some (eff b)
  | layer (.provide s _), 0 => some (layer s)
  | layer (.provide _ t), 1 => some (layer t)
  | layer (.provideMerge s _), 0 => some (layer s)
  | layer (.provideMerge _ t), 1 => some (layer t)
  | layer (.merge l _), 0 => some (layer l)
  | layer (.merge _ r), 1 => some (layer r)
  | layer (.fresh i), 0 => some (layer i)
  | layer (.orDie i), 0 => some (layer i)
  | stmts (.cons h _), 0 => some (stmt h)
  | stmts (.cons _ t), 1 => some (stmts t)
  | stmt (.bindYield e), 0 => some (eff e)
  | stmt (.yieldDiscard e), 0 => some (eff e)
  | stmt (.ifElse _ a _), 0 => some (stmts a)
  | stmt (.ifElse _ _ b), 1 => some (stmts b)
  | stmt (.whileTrue b), 0 => some (stmts b)
  | action (.fork p _), 0 => some (eff p)
  | action (.forkIn p _ _), 0 => some (eff p)
  | action (.forkScoped p _), 0 => some (eff p)
  | action (.raceAll es), 0 => some (effs es)
  | effs (.cons h _), 0 => some (eff h)
  | effs (.cons _ t), 1 => some (effs t)
  | _, _ => none

/-- The node at a path. -/
def at_ : Node → List Nat → Option Node
  | n, [] => some n
  | n, i :: rest => (n.child i).bind (at_ · rest)

end Node

/-! ## Points, names, thunks -/

/-- Where a compiled program stands. -/
structure Point where
  /-- The subterm of the root program: child indices from the root. -/
  path : List Nat
  /-- The positional values in scope (D1). -/
  env : List Val
  /-- What is left: every continuation name costs one, every loop iteration one. -/
  fuel : Nat
  /-- The decisions left, for `choose` sites. -/
  tape : List Bool
  /-- Completed fibers observed when this code was constructed. Eager bodies
  retain this first-order view (`internal/effect.ts:767-777,814-822`); source
  callbacks construct new code with the view at their own invocation. -/
  completed : List (FiberId × ExitV) := []
  /-- The root program the path addresses: `0` until a machine holds more than one
  (direction-scout D6, 2026-09-07: added while the alphabet is open, so a later multi-root
  machine changes no format). -/
  root : Nat := 0
deriving DecidableEq

namespace Point

/-- The point of the child at index `i`, same environment, one fuel down. -/
def child (p : Point) (i : Nat) : Point :=
  { p with path := p.path ++ [i], fuel := p.fuel - 1 }

/-- The point a capture stores, at a completed-exit view: `Capture` (`Machine/Stores.lean`) is
`Point` minus that view plus the context, and this is the isomorphism's one direction. -/
def ofCapture (c : Capture) (completed : List (FiberId × ExitV) := []) : Point :=
  { path := c.path, env := c.env, fuel := c.fuel, tape := c.tape, completed, root := c.root }

/-- The capture of a release registered at this point (`internal/effect.ts:3976,3983`): the
acquired value appended to the environment (the release is typed over `env ++ [a, exit]`,
`Typing.lean`), and the context `contextWith` read. -/
def capture (p : Point) (a : Val) (ctx : Ctx) : Capture :=
  { path := p.path, env := p.env ++ [a], fuel := p.fuel, tape := p.tape, ctx, root := p.root }

/-- The point of the child at index `i` with a value appended to the scope. -/
def childWith (p : Point) (i : Nat) (v : Val) : Point :=
  { p with path := p.path ++ [i], env := p.env ++ [v], fuel := p.fuel - 1 }

def childWith2 (p : Point) (i : Nat) (v w : Val) : Point :=
  { p with path := p.path ++ [i], env := p.env ++ [v, w], fuel := p.fuel - 1 }

/-- A join/await constructed after target exit is already an Exit
(`internal/effect.ts:767-769,814-816`). An absent entry retains the Async form. -/
def awaitExit (p : Point) (target : FiberId) (mode : Supervision.ObserverMode) : Option ExitV :=
  (p.completed.find? fun entry => entry.1 = target).map fun entry =>
    match mode with
    | .joinEffect => entry.2
    | .awaitValue => .success (reifyExitVal entry.2)

theorem awaitExit_empty (p : Point) (target : FiberId) (mode : Supervision.ObserverMode)
    (h : p.completed = []) : p.awaitExit target mode = none := by
  simp [awaitExit, h]

end Point

/-- Which of `provideWith`'s combiners (`Layer.ts:1923`): `identity` for `Layer.provide`
(`:2348`), `Context.merge(that, self)` for `Layer.provideMerge` (`:2800`). -/
inductive CombineMode
  | provide
  | provideMerge
deriving DecidableEq

/-- What runs under a context region (`updateContext`, `internal/effect.ts:2087-2096`), as
data: a program at its point; a layer's build at its point into a memo map and a scope
(`self.build(memoMap, scope)` under `provideContext`, `Layer.ts:1920-1922`); that build with
`Context.add(CurrentMemoMap, memoMap)` mapped over its answer (`buildWithMemoMap`, `:762`);
or a leaf's construction — the body at its point, its answer bound under the key
(`Layer.effect`, `:1440`, `Context.make`) or replaced by the empty context (`effectDiscard`,
`:1515`). The Layer machine carried a `ProgName` here; a subterm is its point (the join). -/
inductive Region
  | program (q : Point)
  | build (q : Point) (memoMap : MemoMapId) (scope : Nat)
  | buildAdding (q : Point) (memoMap : MemoMapId) (scope : Nat)
  | construct (q : Point) (key : Option ServiceKey)
deriving DecidableEq

/-- The continuation, finalizer, generator, loop, registration and cancel names. First-order
data; `contAOf`/`contEOf` and the other hooks of `interpOf` give them meaning. -/
inductive EffName
  /-- `bind`'s continuation: the rest at the point's child 1, the answer appended. -/
  | cont (p : Point)
  /-- `catchCause`'s handler: child 1, the cause appended as a reified exit. -/
  | caught (p : Point)
  /-- `matchCause`'s two arms: children 1 and 2. -/
  | onValue (p : Point)
  | onCause (p : Point)
  /-- `onExit`'s finalizer: child 1, the exit appended as a value. -/
  | fin (p : Point)
  /-- The exit path's two names, as the stores spell them. -/
  | restore (exit : ExitV)
  | merge (exit : ExitV)
  /-- A generator: the `gen` node's point (its `env` the values in scope at the program
  counter), the program counter `pc` (a path from the body's statement list to the list to
  run next), and whether the next answer is bound as the next variable. -/
  | gen (p : Point) (pc : List Nat) (bind : Bool)
  /-- `whileLoop` at its point; the cursor is the frame's `β`. -/
  | loop (p : Point)
  /-- `Deferred.await`'s registration and cancel, as the stores spell them. -/
  | registerAwait (cell : DeferredKey)
  | cancelAwait (cell : DeferredKey)
  | withWaiter (base : EffName) (waiter : FiberId) (token : Nat)
  | abort
  | reFail (cause : CauseV)
  /-- `scoped`: the scope was made (the value is its handle). -/
  | scopeOpen (p : Point)
  /-- `scoped`: the context was read (the value is it); provide the scope and run the body. -/
  | scopeProvide (p : Point) (scope : Nat)
  /-- `scoped`: the context was set; run the body under the restoring finalizer. -/
  | scopeBody (p : Point) (previous : Ctx)
  /-- The scoped exit callback restores this context and closes the captured scope
  within the exiting delivery (`internal/effect.ts:3944-3947`). -/
  | scopedExit (previous : Ctx) (scope : Nat)
  /-- The finalizer that closes a scope with the body's exit. -/
  | scopeClose (scope : Nat)
  /-- The finalizer that restores a context. -/
  | restoreCtx (previous : Ctx)
  /-- `forkScoped`'s continuation on the scope handle the `Scope` service read answered:
  `forkIn` on it (`internal/effect.ts:5406`, source-repairs §20). -/
  | forkScopedIn (p : Point)
  | constant (v : Val)
  /-- A name of the stores' own alphabet: the programs the stores build (a scope's close
  chain, a completion, a finalizer name) embed as they are. -/
  | store (name : Name)
  /-- `acquireRelease` (`internal/effect.ts:3971-3987`), one name per step. `contextWith`
  (`:2156-2158`) read the context, the value: mask and acquire under it. -/
  | acquireCtx (p : Point)
  /-- The `Scope` service read (`:3929`, the `flatMap(scope, …)`) answered its handle, the
  value: run the acquire, child 0. -/
  | acquireIn (p : Point) (ctx : Ctx)
  /-- `tap`'s callback (`:1442-1465`): the acquire answered `a`, the value; register the
  release as a capture on the scope. -/
  | acquired (p : Point) (ctx : Ctx) (scope : Nat)
  /-- `scopeAddFinalizerExit` answered: unit (`:3855-3856`, the registration took), or a closed
  scope's closing exit (`:3851-3853`): run the release now, then answer `a`. -/
  | afterScopeAdd (a : Val) (fin : FinName)
  /-- The release, resolved when the scope closes (`provideContext(release(a, exit), context)`,
  `:3983`, `:2180-2199`): the current context was read, the value; provide the captured one.
  `p` is the capture's point, the acquired value already in scope. -/
  | releaseUnder (p : Point) (ctx : Ctx) (exit : ExitV)
  /-- The captured context is set: run the release, child 1 over the exit, under the
  finalizer that restores the previous context. -/
  | releaseBody (p : Point) (exit : ExitV) (previous : Ctx)
  -- The join (2026-09-07): `Effect.provide`, `Effect.service`, `Effect.provideService`, and
  -- `Layer.build`'s protocol — the Layer machine's names (`Machine/Layer.lean`, `7cbd436`)
  -- with a layer's point in place of a table index, one per rc.112 line they cite.
  /-- `scopedWith` made its scope (`internal/effect.ts:3966`), the value its handle: build the
  layer (child 0 of the `provideLayer` at `p`) into it — `buildWithScope` off the fiber
  context's memo map, or `buildWithMemoMap` over a private one when `local` — then the body
  (child 1) under the built context (`internal/layer.ts:15-21`); the scope closes with the
  exit (`:3967`). -/
  | provideLayerWith (p : Point)
  /-- The build answered its context, the value: `provideContext(self, context)`
  (`internal/layer.ts:20`), the body child 1 of `p`. -/
  | provideLayerBody (p : Point)
  /-- `updateContext` read the fiber context, the value (`internal/effect.ts:2089`): apply the
  update, set the next context, and run the region under the restoring finalizer. -/
  | updateThen (update : Env.ContextUpdate) (body : Region)
  /-- The next context is set (`:2091`): the region under the finalizer that restores
  `previous` (`:2092-2095`). -/
  | bodyThen (body : Region) (previous : Ctx)
  /-- `Layer.buildWithScope` read the fiber context, the value (`Layer.ts:974-979`): fork or
  create the memo map (`CurrentMemoMap.forkOrCreate`, `:585-592`), then build into `scope`. -/
  | buildWithScopeFromContext (q : Point) (scope : Nat)
  /-- The memo map forked or created, the value: `buildWithMemoMap` (`Layer.ts:756-765`), a
  `provideService(CurrentMemoMap)` region over the build at `q` into `scope`. -/
  | withMemoMapThen (q : Point) (scope : Nat)
  /-- `map(_, Context.add(CurrentMemoMap, memoMap))` (`Layer.ts:762`), on the built context. -/
  | addCurrentMemoMap (memoMap : MemoMapId)
  /-- `fromBuild` forked the layer scope (`Layer.ts:333-345`), the value its handle: the
  inner build of the layer at `q` under the finalizer that closes it on failure (`:343`). -/
  | fromBuildThen (q : Point) (memoMap : MemoMapId)
  /-- `getOrElseMemoize` after `get` (`Layer.ts:445-457`), the value a hit — the entry's
  deferred and its owning map — or unit: reuse, or `memoMapBuild`. -/
  | memoize (q : Point) (memoMap : MemoMapId) (scope : Nat)
  /-- A memo hit: `entry.effect` is `Deferred.await(deferred)` (`Layer.ts:400`, `:248`). -/
  | awaitPromise (cell : DeferredKey)
  /-- `memoMapBuild` allocated (`Layer.ts:392-411`), the value the layer scope's handle:
  register the entry finalizer on the caller's scope (`:412`), then build into it. -/
  | buildIntoLayerScope (q : Point) (memoMap : MemoMapId) (scope : Nat)
  /-- The entry finalizer is registered: the construction into the layer scope under the
  `onExit` that completes the entry (`Layer.ts:413-417`). -/
  | thenBuildInto (q : Point) (memoMap : MemoMapId) (layerScope : Nat)
  /-- `fresh` made its private memo map (`Layer.ts:3851`), the value: build the inner layer
  at `q` through it, on the same scope. -/
  | freshThen (q : Point) (scope : Nat)
  /-- `provideWith` built the dependency (`Layer.ts:1916-1919`), the value its context: the
  dependent at `q` built under `provideContext(context)`, then the combiner. -/
  | provideThen (q : Point) (memoMap : MemoMapId) (scope : Nat) (mode : CombineMode)
  /-- `map(merged => f(merged, context))` (`Layer.ts:1923`), on the dependent's context. -/
  | combineWith (mode : CombineMode) (that : Env.Ctx)
  /-- `mergeAllEffect` forked its parallel parent (`Layer.ts:1596`), the value its handle:
  fork the first sibling's sequential child of it (`:1597`). -/
  | mergeChildren (q : Point) (memoMap : MemoMapId)
  /-- A sibling's sequential child scope was forked (`Layer.ts:1597`), the value its handle:
  fork the build of sibling `i` (child `i` of the merge at `q`) into it. -/
  | mergeForkOne (q : Point) (i : Nat) (memoMap : MemoMapId) (parent : Nat) (forked : List FiberId)
  /-- A sibling's build was forked, the value its fiber: the next sibling, or the await. -/
  | mergeForkNext (q : Point) (i : Nat) (memoMap : MemoMapId) (parent : Nat)
      (forked : List FiberId)
  /-- `map(contexts => Context.mergeAll(...contexts))` (`Layer.ts:1600`), on the awaited
  exits. -/
  | mergeContexts
  /-- `Effect.service(key)` read the fiber context, the value: the lookup, or the host throw
  as a defect (`Context.getUnsafe`, `internal/effect.ts:2134`, re-entered at `:670-674` —
  `Defect.missingService`, the machine's one name for it). -/
  | serviceLookup (key : ServiceKey)
  /-- `Context.make(key, value)` over a leaf's answer (`Layer.ts:1440`), or `Context.empty()`
  in place of it (`:1515`). -/
  | bindService (key : Option ServiceKey)
  /-- `Layer.orDie`'s `catch_(build, die)` (`Layer.ts:3327`, `internal/effect.ts:3289`). -/
  | orDie
deriving DecidableEq

/-- The thunk alphabet: a pure term at a point, a body to compile at a point, a store
operation, a park, a fiber action at a point, and the context and scope actions the
`scoped` frames need. -/
inductive EffThunk
  | pure (p : Point)
  | body (p : Point)
  | op (operation : SyncOp)
  | park (kind : ParkKind)
  | act (p : Point)
  /-- `forkScoped`'s `forkIn` on the handle its service read answered (§20): the child and
  options at the point, and the scope. -/
  | forkInAt (p : Point) (scope : Nat)
  | getCtx
  | setCtx (context : Ctx)
  | closeScope (scope : Nat) (exit : ExitV)
  /-- A thunk of the stores' own alphabet, embedded. -/
  | store (thunk : Thunk)
  /-- `acquireRelease`'s `uninterruptibleMask` (`internal/effect.ts:3977`, `:4340-4351`) over
  the `Scope` read and the acquire, under the context read: built in `withFiberOf`, since
  `actionAt` is keyed by node and cannot carry the context. `Eff.acquireRelease` has no
  `interruptible` option, so the acquire always runs masked. -/
  | acquireMasked (p : Point) (ctx : Ctx)
  /-- The release at its resolved point under the finalizer that restores `previous`
  (`provideContext`, `:2180-2199`): entered through a mask that is the finalizer's own (every
  path that runs a release is already uninterruptible, `:4021`), so the frame and the term
  reference share one entry shape. -/
  | releaseMasked (p : Point) (previous : Ctx)
  /-- `getOrElseMemoize`'s `suspend` (`Layer.ts:445-457`): the lookup of the layer at `q` in
  `memoMap`, for a build into `scope`, at run time. -/
  | memoLookup (q : Point) (memoMap : MemoMapId) (scope : Nat)
  /-- `mergeAllEffect`'s fork of one sibling's build (`Layer.ts:1597`): the layer at `q`,
  built into `scope` through `memoMap`, as an immediate daemon (`internal/effect.ts:4851`). -/
  | forkLayer (q : Point) (memoMap : MemoMapId) (scope : Nat)
  /-- The await of the forked siblings (`forEach`'s concurrency, `Layer.ts:1597`). -/
  | awaitAllFailFast (targets : List FiberId)
deriving DecidableEq

/-- The compiled program carrier. -/
abbrev NCode := Prim EffName EffThunk Val Err Defect FiberId Ann

/-- The machine's action alphabet at this instantiation. -/
abbrev NAction := WithFiberAction EffName EffThunk Val Err Defect FiberId Ann Ctx

/-! ## The stores' programs embed

The deferred store holds programs of the stores' alphabet (a completion, the resumes it
owes), and the scope store's close is a program of that alphabet. They embed name by name
and thunk by thunk; the hooks of `interpOf` delegate to `Deep.Stores.stores` on an embedded
name, so the stores are reused unchanged (plan G5). -/

/-- The embedding of a stores program. -/
def embed : Program → NCode
  | .success v => .success v
  | .failure c => .failure c
  | .sync t => .sync (.store t)
  | .suspend t => .suspend (.store t)
  | .withFiber t => .withFiber (.store t)
  | .yieldableError e => .yieldableError e
  | .iterator g c => .iterator (.store g) c
  | .onSuccess body n => .onSuccess (embed body) (.store n)
  | .onSuccessConst body next => .onSuccessConst (embed body) (embed next)
  | .onFailure body n => .onFailure (embed body) (.store n)
  | .onSuccessAndFailure body a e => .onSuccessAndFailure (embed body) (.store a) (.store e)
  | .exitFrame body => .exitFrame (embed body)
  | .onExit body f flag => .onExit (embed body) (.store f) flag
  | .setInterruptible flag => .setInterruptible flag
  | .whileLoop l c => .whileLoop (.store l) c
  | .yieldNowWith n => .yieldNowWith n
  | .async r s c => .async (.store r) s (c.map EffName.store)
  | .asyncFinalizer n => .asyncFinalizer (.store n)

/-- The embedding of a stores generator step (a scope's close walk, §20): the next code and
the advanced generator embed. -/
def embedStep : IterStep Name Thunk Val Err Defect FiberId Ann Program →
    IterStep EffName EffThunk Val Err Defect FiberId Ann NCode
  | IterStep.done v => IterStep.done v
  | IterStep.halt c => IterStep.halt c
  | IterStep.resume next n => IterStep.resume (embed next) (.store n)

/-- The embedding of a stores action. -/
def embedAction : WithFiberAction Name Thunk Val Err Defect FiberId Ann Ctx → NAction
  | .fork p o => .fork (embed p) o
  | .forkIn p o s => .forkIn (embed p) o s
  | .forkScoped p o => .forkScoped (embed p) o
  | .runIn t s => .runIn t s
  | .interrupt t => .interrupt t
  | .interruptAs t who => .interruptAs t who
  | .interruptScoped t => .interruptScoped t
  | .interruptAll ts who => .interruptAll ts who
  | .awaitAll ts => .awaitAll ts
  | .awaitAllFailFast ts => .awaitAllFailFast ts
  | .snapshotChildren => .snapshotChildren
  | .awaitNewChildren s => .awaitNewChildren s
  | .raceAll es => .raceAll (es.map embed)
  | .setInterruptible body flag => .setInterruptible (embed body) flag
  | .setContext c => .setContext c
  | .getContext => .getContext
  | .getId => .getId
  | .closeScope s e => .closeScope s e
  | .refuse c => .refuse c
  | .dropObservers t => .dropObservers t
  | .cancelRace r => .cancelRace r
  | .ambientScope => .ambientScope
  | .closePar fins => .closePar (fins.map embed)

/-! ## The compile -/

/-- The error alphabet's image of a value: numbers are tags; anything else is `boom`
(`typeOf` admits only numbers). -/
def errOf : Val → Err
  | Val.nat n => Err.tag n
  | _ => Err.boom

/-- A value of the wrong shape where the program's typing promised another: the same
defect the stores answer for a continuation applied to the wrong value. -/
def badShape : NCode := Prim.failure (Cause.die Defect.badName)

/-- A live frontier: what the compile answers at fuel zero. -/
def frontier (p : Point) : NCode := Prim.suspend (EffThunk.body p)

/-- The cause a cause term spells. -/
def causeOf (env : List Val) : CauseTerm → Option CauseV
  | .fail error => (evalTerm env error).map fun v => Cause.fail (errOf v)
  | .die defect =>
    (evalTerm env defect).map fun
      | Val.nat n => Cause.die (Defect.user n)
      | _ => Cause.die Defect.badName
  | .interrupt none => some (Cause.interrupt none)
  | .interrupt (some who) =>
    match evalTerm env who with
    | some (Val.fiber ⟨id⟩) => some (Cause.interrupt (some ⟨id⟩))
    | _ => none
  | .both left right => do
    let l ← causeOf env left
    let r ← causeOf env right
    some (Cause.combine l r)

/-- The exit a reified exit value spells: the exit image read back (`exitImage`,
`Machine/Stores.lean`), so `Val.exitOk v` is `Exit.success v`, `Val.exitErr c` is
`Exit.failure c`, and any other shape — including a failure whose cause no cause wrote —
is `none`. -/
def exitOfVal : Val → Option ExitV := exitImage.ofVal

theorem exitOfVal_exitOk (v : Val) : exitOfVal (Val.exitOk v) = some (Exit.success v) := rfl

theorem exitOfVal_exitErr (c : CauseV) : exitOfVal (Val.exitErr c) = some (Exit.failure c) :=
  exitImage.ofVal_toVal (Exit.failure c)

/-- `CurrentMemoMap` in a service map (`Layer.ts:584-592`): the map a build forks, if any. -/
def currentMemoMapOf (c : Env.Ctx) : Option MemoMapId :=
  match c.getV Env.currentMemoMapKey with
  | some (Val.memoMap ⟨index⟩) => some ⟨index⟩
  | _ => none

/-- `updateContext(self, f)` (`internal/effect.ts:2087-2096`): read the fiber context, then
`updateThen` on it. -/
def updateContextAt (update : Env.ContextUpdate) (body : Region) : NCode :=
  Prim.onSuccess (Prim.withFiber EffThunk.getCtx) (EffName.updateThen update body)

/-- `scopeAddFinalizerExit(scope, fin)` (`internal/effect.ts:3847-3858`): the `sync` half and
the continuation that runs the finalizer now when the scope had already closed; unit either
way. -/
def scopeAddAt (scope : Nat) (fin : FinName) : NCode :=
  Prim.onSuccess (Prim.sync (EffThunk.op (SyncOp.scopeAdd scope fin)))
    (EffName.afterScopeAdd Val.unit fin)

/-- `updateContext`'s identity test (`internal/effect.ts:2090`, `prevContext === nextContext`):
`Context.add` always builds a fresh map, and `Context.merge(self, that)` answers `self` itself
exactly when `self` holds something and `that` nothing (`Context.ts:1817-1819`); the body then
runs as is, with no restoring frame. -/
def updateKeepsIdentity : Env.ContextUpdate → Env.Ctx → Bool
  | .provide that, prev => decide (prev.entries ≠ [] ∧ that.entries = [])
  | _, _ => false

/-- `catch_(self, die)` (`internal/effect.ts:3289`, `:2558-2572`): the cause's first typed error
becomes the defect, alone; a cause with no typed error passes through. -/
def orDieCause (cause : CauseV) : CauseV :=
  match cause.reasons.findSome? (fun | .fail e _ => some e | _ => none) with
  | some (Err.tag code) => Cause.die (Defect.user code)
  | some Err.boom => Cause.die Defect.badName
  | none => cause

/-- The contexts of a list of reified exits, when every one succeeded with a context. -/
def contextsOfList : List Val → Option (List Env.Ctx)
  | [] => some []
  | x :: rest =>
    match exitOfVal x with
    | some (Exit.success c) =>
      match Env.decode c, contextsOfList rest with
      | some ctx, some ctxs => some (ctx :: ctxs)
      | _, _ => none
    | _ => none

/-- The contexts of an awaited exits value (`exitsVal`, one `list` frame). -/
def contextsOf : Val → Option (List Env.Ctx)
  | .list values => contextsOfList values
  | _ => none

/-- `Context.mergeAll(...contexts)` (`Layer.ts:1600`) over the awaited exits; a failed build
fails the merge with every failure's reasons, in order. -/
def mergeContextsK (v : Val) : NCode :=
  match contextsOf v with
  | some ctxs => Prim.success (Env.encode (Env.Context.mergeAll ctxs))
  | none =>
    match reasonsOfVal v with
    | [] => badShape
    | reason :: rest => Prim.failure ⟨reason :: rest⟩

/-- `compile` of plan §3, structural in the program; the point is data. Names are minted at
the point; `interpOf` resolves them by compiling the subterm they address. -/
def compileEff : NativeEff → Point → NCode
  | e, p =>
    match p.fuel with
    | 0 => frontier p
    | _ + 1 =>
      match e with
      | .succeed v =>
        match evalTerm p.env v with
        | some val => Prim.success val
        | none => badShape
      | .fail e =>
        match evalTerm p.env e with
        | some val => Prim.failure (Cause.fail (errOf val))
        | none => badShape
      | .failCause c =>
        match causeOf p.env c with
        | some cause => Prim.failure cause
        | none => badShape
      | .yieldError e =>
        match evalTerm p.env e with
        | some val => Prim.yieldableError (errOf val)
        | none => badShape
      | .sync _ => Prim.sync (EffThunk.pure p)
      -- The thunk names this suspension, not its child: executing the outer
      -- `suspend` must return the child's complete code, including any suspension
      -- that `Effect.gen` or the printed loop constructs (`internal/effect.ts:1175-1196`).
      | .suspend _ => Prim.suspend (EffThunk.body p)
      | .perform op request =>
        match (NativeOp.row op).kind with
        | .sync =>
          match evalTerm p.env request with
          | some val =>
            match NativeOp.syncOpOf op val with
            | some operation => Prim.sync (EffThunk.op operation)
            | none => badShape
          | none => badShape
        | .async =>
          match (evalTerm p.env request).bind NativeOp.awaitCellOf with
          | some cell =>
            Prim.async (EffName.registerAwait cell) true (some (EffName.cancelAwait cell))
          | none => badShape
        | .program => frontier p
      | .bind first _ => Prim.onSuccess (compileEff first (p.child 0)) (EffName.cont p)
      -- `Effect.gen` is `suspend(() => fromIteratorUnsafe(…))` (`internal/effect.ts:1175-1196`):
      -- the iterator is what `suspendBodyAt` answers at this point.
      | .gen _ => Prim.suspend (EffThunk.body p)
      | .catchCause body _ => Prim.onFailure (compileEff body (p.child 0)) (EffName.caught p)
      | .matchCause body _ _ =>
        Prim.onSuccessAndFailure (compileEff body (p.child 0)) (EffName.onValue p)
          (EffName.onCause p)
      | .onExit body _ => Prim.onExit (compileEff body (p.child 0)) (EffName.fin p) false
      -- `Effect.exit` returns `exitSucceed(self)` when `self` is already an `Exit`
      -- (`internal/effect.ts:3621-3622`); only a body that is not one pushes the frame.
      | .exit body =>
        match (compileEff body (p.child 0)).asExit? with
        | some exit => Prim.success (reifyExitVal exit)
        | none => Prim.exitFrame (compileEff body (p.child 0))
      | .uninterruptible _ => Prim.withFiber (EffThunk.act p)
      | .interruptible _ => Prim.withFiber (EffThunk.act p)
      | .branch _ _ _ => Prim.suspend (EffThunk.body p)
      -- the printed loop is `Effect.suspend(() => { let a0 = initial; return
      -- Effect.whileLoop({…}) })` (`Codegen/Print.lean:158-168`): the cursor is read and the
      -- `While` frame built when the suspension runs, by `suspendBodyAt`.
      | .whileLoop _ _ _ _ => Prim.suspend (EffThunk.body p)
      | .yieldNow priority => Prim.yieldNowWith priority
      | .callback register request =>
        match (NativeOp.row register).kind with
        | .async =>
          match (evalTerm p.env request).bind NativeOp.awaitCellOf with
          | some cell =>
            Prim.async (EffName.registerAwait cell) true (some (EffName.cancelAwait cell))
          | none => badShape
        | _ => badShape
      | .awaitFiber fiber mode =>
        match evalTerm p.env fiber with
        | some (Val.fiber ⟨id⟩) =>
          match p.awaitExit ⟨id⟩ mode with
          | some exit => Prim.ofExit exit
          | none => Prim.suspend (EffThunk.park (ParkKind.join ⟨id⟩ mode))
        | _ => badShape
      -- `forkScoped` is `flatMap(scope, scope => forkIn(self, scope, options))` (`:5381-5406`,
      -- §20): the counted `Service` read at the action, then `forkIn` on its handle
      | .withFiber (.forkScoped _ _) =>
        Prim.onSuccess (Prim.withFiber (EffThunk.act p)) (EffName.forkScopedIn p)
      | .withFiber _ => Prim.withFiber (EffThunk.act p)
      | .scoped _ => Prim.withFiber (EffThunk.act p)
      -- `contextWith(context => uninterruptibleMask(… scope … tap(acquire, scopeAddFinalizerExit
      -- (scope, exit => provideContext(release(a, exit), context)))))` (`:3971-3987`): the
      -- context read first, the rest named step by step (`contAOf`)
      | .acquireRelease _ _ => Prim.onSuccess (Prim.withFiber EffThunk.getCtx) (EffName.acquireCtx p)
      | .choose _ left right =>
        match p.tape with
        | true :: rest => compileEff left { p with path := p.path ++ [0], tape := rest }
        | false :: rest => compileEff right { p with path := p.path ++ [1], tape := rest }
        | [] => frontier p
      -- `Effect.provide(self, layer)` is `scopedWith` (`internal/layer.ts:15`), a `suspend`
      -- (`internal/effect.ts:3960-3968`): `suspendBodyAt` allocates the scope and names the rest
      | .provideLayer _ _ _ => Prim.suspend (EffThunk.body p)
      -- `Effect.service(key)` (`internal/effect.ts:2059`): the context read, then the lookup
      | .service key =>
        Prim.onSuccess (Prim.withFiber EffThunk.getCtx) (EffName.serviceLookup key)
      -- `Effect.provideService(self, key, value)` (`internal/effect.ts:2232`): `updateContext`
      -- with `Context.add(key, value)`, the body child 0 under it
      | .provideService key value _ =>
        match evalTerm p.env value with
        | some v =>
          updateContextAt (Env.ContextUpdate.provideService key v) (Region.program (p.child 0))
        | none => badShape

/-- The program at a point of the root: the subterm compiled there, or the frontier. -/
def resolve (root : NativeEff) (p : Point) : NCode :=
  match Node.at_ (Node.eff root) p.path with
  | some (Node.eff e) => compileEff e p
  | _ => badShape

/-! ## Layers: `self.build(memoMap, scope)` at a point (the join, 2026-09-07)

A layer is a subterm (`Node.layer`), its identity its path (`LayerId`), and its build is
compiled at its point the way a program is at its (`compileEff`): structural in the term,
with the point its address, the memo map and the scope the two arguments `build` takes
(`Layer.ts:230-232`). The protocol is `Machine/Layer.lean`'s (`7cbd436`), arm for arm, with
`resolveLayer root (q.child i)` where it had `progOf table (ProgName.layerBuild …)`. -/

/-- `self.build(memoMap, scope)` by the constructor (`Layer.ts`, one arm per constructor site).
`Layer.succeed` is `fromBuildUnsafe(succeed(Context.make(key, value)))` (`:1129-1130`), no
scope of its own; `fresh` calls the inner build with a brand-new map on the same scope
(`:3851`); `orDie` wraps the inner build in `catch_(_, die)` (`:3327`); every other constructor
is a `fromBuild` wrapper (`:333-345`, `:386`, `:1915`) that forks a child of the caller's scope
first and builds inside it (`innerLayerAt`). -/
def compileLayer : LayerTerm NativeOp → Point → MemoMapId → Nat → NCode
  | .succeed key value, _, _, _ =>
    match Lit.toVal value with
    | some v => Prim.success (Env.encode (Env.Context.empty.addV key v))
    | none => badShape
  | .fresh _, q, _, scope =>
    Prim.onSuccess (Prim.sync (EffThunk.op (SyncOp.memoFork none)))
      (EffName.freshThen (q.child 0) scope)
  | .orDie inner, q, m, scope =>
    Prim.onFailure (compileLayer inner (q.child 0) m scope) EffName.orDie
  | _, q, m, scope =>
    Prim.onSuccess (Prim.sync (EffThunk.op (SyncOp.scopeFork scope FinalizerStrategy.sequential)))
      (EffName.fromBuildThen q m)

/-- The layer at a point of the root, built: `compileLayer` of the node there. -/
def resolveLayer (root : NativeEff) (q : Point) (m : MemoMapId) (scope : Nat) : NCode :=
  match Node.at_ (Node.eff root) q.path with
  | some (Node.layer l) => compileLayer l q m scope
  | _ => badShape

/-- What runs inside a `fromBuild` wrapper, on the forked layer scope, by the layer at `q`:
a memoized leaf's lookup (`Layer.ts:386`, a `suspend`), `provideWith`'s dependency build
(child 1) then the dependent (`:1916-1919`), or `mergeAllEffect`'s parallel parent
(`:1596`). The constructors `compileLayer` handles without a wrapper are compiled as there,
for totality. -/
def innerLayerAt (root : NativeEff) (q : Point) (m : MemoMapId) (child : Nat) : NCode :=
  match Node.at_ (Node.eff root) q.path with
  | some (Node.layer (.effect _ _)) => Prim.suspend (EffThunk.memoLookup q m child)
  | some (Node.layer (.effectDiscard _)) => Prim.suspend (EffThunk.memoLookup q m child)
  | some (Node.layer (.provide _ _)) =>
    Prim.onSuccess (resolveLayer root (q.child 1) m child)
      (EffName.provideThen q m child CombineMode.provide)
  | some (Node.layer (.provideMerge _ _)) =>
    Prim.onSuccess (resolveLayer root (q.child 1) m child)
      (EffName.provideThen q m child CombineMode.provideMerge)
  | some (Node.layer (.merge _ _)) =>
    Prim.onSuccess (Prim.sync (EffThunk.op (SyncOp.scopeFork child FinalizerStrategy.parallel)))
      (EffName.mergeChildren q m)
  | some (Node.layer l) => compileLayer l q m child
  | _ => badShape

/-- A leaf's construction on its layer scope: `effectContext` is `fromBuildMemo((_, scope) =>
Scope.provide(effect, scope))` (`Layer.ts:1482`), and `Scope.provide` is `provideService(Scope)`
(`internal/effect.ts:3932-3935`) — a region over the body at child 0, whose answer
`Context.make(key, _)` binds (`Layer.effect`, `:1440`) or `Context.empty()` replaces
(`effectDiscard`, `:1515`). -/
def constructionAt (root : NativeEff) (q : Point) (layerScope : Nat) : NCode :=
  match Node.at_ (Node.eff root) q.path with
  | some (Node.layer (.effect key _)) =>
    updateContextAt (Env.ContextUpdate.provideService Env.scopeKey (Val.scopeHandle layerScope))
      (Region.construct (q.child 0) (some key))
  | some (Node.layer (.effectDiscard _)) =>
    updateContextAt (Env.ContextUpdate.provideService Env.scopeKey (Val.scopeHandle layerScope))
      (Region.construct (q.child 0) none)
  | _ => badShape

/-- A region's program. -/
def regionCode (root : NativeEff) : Region → NCode
  | .program q => resolve root q
  | .build q m scope => resolveLayer root q m scope
  | .buildAdding q m scope =>
    Prim.onSuccess (resolveLayer root q m scope) (EffName.addCurrentMemoMap m)
  | .construct q key => Prim.onSuccess (resolve root q) (EffName.bindService key)

/-! ### The continuations that read a value

Each is a function of the value, so that a theorem about it case-splits on a reader
(`Val.context?`, `Env.decode`) and never has to match a compiled `match` (the Layer machine's
`*K` functions, `Machine/Layer.lean`). -/

/-- `scopedWith`'s scope is made, the handle in hand (`internal/layer.ts:15-21`): the node's
`local` flag decides the build; the scope closes with the exit (`internal/effect.ts:3967`). -/
def provideLayerWithK (root : NativeEff) (p : Point) (scope : Nat) : NCode :=
  match Node.at_ (Node.eff root) p.path with
  | some (Node.eff (.provideLayer _ isLocal _)) =>
    Prim.onExit
      (Prim.onSuccess
        (if isLocal then
          Prim.onSuccess (Prim.sync (EffThunk.op (SyncOp.memoFork none)))
            (EffName.withMemoMapThen (p.child 0) scope)
        else
          Prim.onSuccess (Prim.withFiber EffThunk.getCtx)
            (EffName.buildWithScopeFromContext (p.child 0) scope))
        (EffName.provideLayerBody p))
      (EffName.scopeClose scope) false
  | _ => badShape

/-- `flatMap(build, context => provideContext(self, context))` (`internal/layer.ts:20`) on the
built context; `provideContext` of an exit is that exit (`internal/effect.ts:2196`). -/
def provideLayerBodyK (root : NativeEff) (p : Point) (v : Val) : NCode :=
  match Env.decode v with
  | some built =>
    match (resolve root (p.child 1)).asExit? with
    | some exit => Prim.ofExit exit
    | none => updateContextAt (Env.ContextUpdate.provide built) (Region.program (p.child 1))
  | none => badShape

/-- `updateContext` on the previous context (`internal/effect.ts:2088-2095`): `f(prev)`; the
same object runs the body as is (`:2090`), else `setContext(next)` and the restoring frame. -/
def updateThenK (root : NativeEff) (update : Env.ContextUpdate) (body : Region) (v : Val) :
    NCode :=
  match Val.context? v with
  | some prev =>
    if updateKeepsIdentity update prev.services then regionCode root body
    else
      Prim.onSuccess
        (Prim.withFiber (EffThunk.setCtx (Ctx.withServices (update.apply prev.services))))
        (EffName.bodyThen body prev)
  | none => badShape

/-- `Layer.buildWithScope` on the fiber context (`Layer.ts:974-979`): `forkOrCreate` first. -/
def buildWithScopeK (q : Point) (scope : Nat) (v : Val) : NCode :=
  match Val.context? v with
  | some ctx =>
    Prim.onSuccess (Prim.sync (EffThunk.op (SyncOp.memoFork (currentMemoMapOf ctx.services))))
      (EffName.withMemoMapThen q scope)
  | none => badShape

/-- `Context.add(CurrentMemoMap, memoMap)` over the built context (`Layer.ts:762`). -/
def addCurrentMemoMapK (m : MemoMapId) (v : Val) : NCode :=
  match Env.decode v with
  | some ctx => Prim.success (Env.encode (ctx.addV Env.currentMemoMapKey (Val.memoMap m)))
  | none => badShape

/-- `provideWith` on the dependency's context (`Layer.ts:1920-1923`): the dependent's build,
child 0, under `provideContext(context)`, then the combiner. -/
def provideThenK (q : Point) (m : MemoMapId) (scope : Nat) (mode : CombineMode) (v : Val) :
    NCode :=
  match Env.decode v with
  | some ctx =>
    Prim.onSuccess
      (updateContextAt (Env.ContextUpdate.provide ctx) (Region.build (q.child 0) m scope))
      (EffName.combineWith mode ctx)
  | none => badShape

/-- `f(merged, context)` (`Layer.ts:1923`): `identity` for `provide` (`:2348`),
`Context.merge(that, self)` for `provideMerge` (`:2800`). -/
def combineWithK (mode : CombineMode) (that : Env.Ctx) (v : Val) : NCode :=
  match Env.decode v with
  | some merged =>
    match mode with
    | CombineMode.provide => Prim.success (Env.encode merged)
    | CombineMode.provideMerge => Prim.success (Env.encode (that.merge merged))
  | none => badShape

/-- `Context.make(key, value)` over a leaf's answer (`Layer.ts:1440`), or `Context.empty()` in
place of it (`:1515`). -/
def bindServiceK (key : Option ServiceKey) (v : Val) : NCode :=
  match key with
  | some key => Prim.success (Env.encode (Env.Context.empty.addV key v))
  | none => Prim.success (Env.encode Env.Context.empty)

/-- `Effect.service(key)` on the fiber context: the value, or the host throw as a defect
(`Context.getUnsafe`, `internal/effect.ts:2134`; `Defect.missingService`). -/
def serviceLookupK (key : ServiceKey) (v : Val) : NCode :=
  match Val.context? v with
  | some ctx =>
    match ctx.services.getV key with
    | some value => Prim.success value
    | none => Prim.failure (Cause.die Defect.missingService)
  | none => badShape

/-! ## Generators: the statement walker behind `iterNext` -/

/-- The number of `bindYield` statements among the first `k` of a list: the bindings a block
has made at position `k`, dropped when the block ends. -/
def localBinds : Stmts NativeOp → Nat → Nat
  | .cons (.bindYield _) t, k + 1 => 1 + localBinds t k
  | .cons _ t, k + 1 => localBinds t k
  | _, _ => 0

/-- Split a program counter into the block it stands in and the position within it. A
program counter is `1^k₀ ++ [0, s₁] ++ 1^k₁ ++ … ++ [0, sₙ] ++ 1^kₙ`: a run of `1`s is the
position in a list, `0` descends into the head statement and the next index selects its
block. Read from the front, so an else block's selector `[0, 1]` is never mistaken for a
position (finding A3-2, 2026-09-04). -/
def walkPc : List Nat → List Nat → Nat → List Nat × Nat
  | [], block, k => (block, k)
  | 1 :: rest, block, k => walkPc rest block (k + 1)
  | 0 :: sel :: rest, block, k => walkPc rest (block ++ List.replicate k 1 ++ [0, sel]) 0
  | _ :: rest, block, k => walkPc rest block k

def splitPc (pc : List Nat) : List Nat × Nat := walkPc pc [] 0

/-- The statements of the block at `block` (a path to a `stmts` node under the generator's
body). -/
def blockAt (root : NativeEff) (p : Point) (block : List Nat) : Option (Stmts NativeOp) :=
  match Node.at_ (Node.eff root) (p.path ++ [0] ++ block) with
  | some (Node.stmts ss) => some ss
  | _ => none

/-- Leave the block at `pc` (its statements exhausted): the environment loses the block's
bindings, and control continues after the enclosing statement — or at the head of the
enclosing `while` again. `none` is the end of the generator's body. -/
def blockExit (root : NativeEff) (p : Point) (pc : List Nat) (env : List Val) :
    Option (List Nat × List Val) :=
  let (block, k) := splitPc pc
  let env := match blockAt root p block with
    | some ss => env.take (env.length - localBinds ss k)
    | none => env
  match block.reverse with
  | _ :: 0 :: outer =>
    let base := outer.reverse
    match Node.at_ (Node.eff root) (p.path ++ [0] ++ base) with
    | some (Node.stmts (.cons (.whileTrue _) _)) => some (base ++ [0, 0], env)
    | _ => some (base ++ [1], env)
  | _ => none

/-- Leave the innermost enclosing `while` (`break`): pop blocks until one is a loop body,
dropping their bindings. -/
def loopExit (root : NativeEff) : Nat → Point → List Nat → List Val →
    Option (List Nat × List Val)
  | 0, _, _, _ => none
  | depth + 1, p, pc, env =>
    let (block, k) := splitPc pc
    let env := match blockAt root p block with
      | some ss => env.take (env.length - localBinds ss k)
      | none => env
    match block.reverse with
    | _ :: 0 :: outer =>
      let base := outer.reverse
      match Node.at_ (Node.eff root) (p.path ++ [0] ++ base) with
      | some (Node.stmts (.cons (.whileTrue _) _)) => some (base ++ [1], env)
      | _ => loopExit root depth p base env
    | _ => none

/-- The generator's step: from the list at `pc` with `env` in scope, through pure statements
to the next yield, the return, or the body's end. Pure successes are folded inline
(`folded`); a yielded failure halts; anything else resumes with the advanced name. -/
def runStmts (root : NativeEff) (p : Point) :
    Nat → List Nat → List Val → List Val → List Val × IterStep EffName EffThunk Val Err Defect FiberId Ann
  | 0, pc, env, folded =>
    (folded, IterStep.resume (frontier { p with path := p.path ++ [0] ++ pc, env := env, fuel := 0 })
      (EffName.gen { p with env := env } pc false))
  | fuel + 1, pc, env, folded =>
    match blockAt root p pc with
    | some .nil =>
      match blockExit root p pc env with
      | none => (folded, IterStep.done Val.unit)
      | some (pc', env') => runStmts root p fuel pc' env' folded
    | some (.cons s _) =>
      match s with
      | .bindYield e => yieldOf e true fuel pc env folded
      | .yieldDiscard e => yieldOf e false fuel pc env folded
      | .ret v =>
        match evalTerm env v with
        | some value => (folded, IterStep.done value)
        | none => (folded, IterStep.halt (Cause.die Defect.badName))
      | .ifElse test _ _ =>
        match evalTerm env test with
        | some (Val.bool true) => runStmts root p fuel (pc ++ [0, 0]) env folded
        | some (Val.bool false) => runStmts root p fuel (pc ++ [0, 1]) env folded
        | _ => (folded, IterStep.halt (Cause.die Defect.badName))
      | .whileTrue _ => runStmts root p fuel (pc ++ [0, 0]) env folded
      | .breakLoop =>
        match loopExit root (pc.length + 1) p pc env with
        | some (pc', env') => runStmts root p fuel pc' env' folded
        | none => (folded, IterStep.halt (Cause.die Defect.badName))
    | none => (folded, IterStep.halt (Cause.die Defect.badName))
  where
    /-- The effect of a yield statement at `pc`, compiled at its own point. -/
    yieldOf (e : NativeEff) (bind : Bool) (fuel : Nat) (pc : List Nat) (env : List Val)
        (folded : List Val) : List Val × IterStep EffName EffThunk Val Err Defect FiberId Ann :=
      let q : Point := { p with path := p.path ++ [0] ++ pc ++ [0, 0], env := env, fuel := fuel + 1 }
      match compileEff e q with
      | Prim.success value =>
        runStmts root p fuel (pc ++ [1]) (if bind then env ++ [value] else env) (folded ++ [value])
      | Prim.failure cause => (folded, IterStep.halt cause)
      | prim => (folded, IterStep.resume prim (EffName.gen { p with env := env } (pc ++ [1]) bind))

/-! ## The names' meaning -/

/-- The fiber action a point names: the action node, or a mask over a body. -/
def actionAt (root : NativeEff) (p : Point) : Option NAction :=
  match Node.at_ (Node.eff root) p.path with
  | some (Node.eff (.uninterruptible _)) =>
    some (WithFiberAction.setInterruptible (resolve root (p.child 0)) false)
  | some (Node.eff (.interruptible _)) =>
    some (WithFiberAction.setInterruptible (resolve root (p.child 0)) true)
  | some (Node.eff (.withFiber a)) =>
    let q := p.child 0
    let refuse : NAction := WithFiberAction.refuse (Cause.die Defect.badName)
    -- a snapshot's fibers, or a tuple of fiber handles
    let handles : Val → Option (List FiberId) := fun
      | Value.fiberSnapshot hs => (Store.Image.list Value.fiberHandle).ofVal hs
      | v => (Val.tuple? v).bind fun vs => vs.mapM fun
        | Val.fiber ⟨id⟩ => some ⟨id⟩
        | _ => none
    some (match a with
      | .fork _ options => WithFiberAction.fork (resolve root (q.child 0)) options
      | .forkIn _ options scope =>
        match evalTerm p.env scope with
        | some (Val.scopeHandle s) =>
          WithFiberAction.forkIn (resolve root (q.child 0)) options s
        | _ => refuse
      -- the `Scope` service read (`Context.ts:423`, §20); `forkScopedAt` is the `forkIn` half
      | .forkScoped _ _ => WithFiberAction.ambientScope
      | .runIn target scope =>
        match evalTerm p.env target, evalTerm p.env scope with
        | some (Val.fiber ⟨id⟩), some (Val.scopeHandle s) => WithFiberAction.runIn ⟨id⟩ s
        | _, _ => refuse
      | .interrupt target =>
        match evalTerm p.env target with
        | some (Val.fiber ⟨id⟩) => WithFiberAction.interrupt ⟨id⟩
        | _ => refuse
      | .interruptScoped target =>
        match evalTerm p.env target with
        | some (Val.fiber ⟨id⟩) => WithFiberAction.interruptScoped ⟨id⟩
        | _ => refuse
      | .interruptAll targets interruptor =>
        match (evalTerm p.env targets).bind handles with
        | some ids =>
          match interruptor with
          | none => WithFiberAction.interruptAll ids none
          | some who =>
            match evalTerm p.env who with
            | some (Val.nat id) => WithFiberAction.interruptAll ids (some ⟨id⟩)
            | _ => refuse
        | none => refuse
      | .awaitAll targets =>
        match (evalTerm p.env targets).bind handles with
        | some ids => WithFiberAction.awaitAll ids
        | none => refuse
      | .awaitAllFailFast targets =>
        match (evalTerm p.env targets).bind handles with
        | some ids => WithFiberAction.awaitAllFailFast ids
        | none => refuse
      | .snapshotChildren => WithFiberAction.snapshotChildren
      | .awaitNewChildren snapshot =>
        match (evalTerm p.env snapshot).bind handles with
        | some ids => WithFiberAction.awaitNewChildren ids
        | none => refuse
      | .raceAll es => WithFiberAction.raceAll (entrants es (q.child 0))
      | .setContext context =>
        -- the context is read back off the value (`Val.context?`); any other shape refuses
        match (evalTerm p.env context).bind Val.context? with
        | some ctx => WithFiberAction.setContext ctx
        | none => refuse
      | .getContext => WithFiberAction.getContext
      | .getId => WithFiberAction.getId
      | .closeScope scope exit =>
        match evalTerm p.env scope, (evalTerm p.env exit).bind exitOfVal with
        | some (Val.scopeHandle s), some e => WithFiberAction.closeScope s e
        | _, _ => refuse)
  | _ => none
where
  /-- The entrants of a race, each compiled at its own point (`effs` node children). -/
  entrants : Effs NativeOp → Point → List NCode
    | .nil, _ => []
    | .cons h t, q => compileEff h (q.child 0) :: entrants t (q.child 1)

/-- `forkScoped`'s second half (`forkIn(self, scope, options)`, `internal/effect.ts:5406`; §20)
at a `forkScoped` node: the child compiled at the action's program, the node's options and the
handle the service read answered. The compile does not mint a registration identity — the
store allocates one per executed registration, as `:5366` does (`E4-CHECK-CE-016`). -/
def forkScopedAt (root : NativeEff) (p : Point) (scope : Nat) : Option NAction :=
  match Node.at_ (Node.eff root) p.path with
  | some (Node.eff (.withFiber (.forkScoped _ options))) =>
    some (WithFiberAction.forkIn (resolve root ((p.child 0).child 0)) options scope)
  | _ => none

/-- `cont[contA](value, fiber)`. -/
def contAOf (root : NativeEff) : EffName → Val → NCode
  | .cont p, v => resolve root (p.childWith 1 v)
  | .onValue p, v => resolve root (p.childWith 1 v)
  | .restore exit, _ => Prim.ofExit exit
  | .merge exit, _ => Prim.ofExit exit
  | .reFail cause, _ => Prim.failure cause
  | .forkScopedIn p, Val.scopeHandle s => Prim.withFiber (EffThunk.forkInAt p s)
  | .forkScopedIn _, _ => badShape
  | .scopeOpen p, Val.scopeHandle s =>
    Prim.onExit (Prim.onSuccess (Prim.withFiber EffThunk.getCtx) (EffName.scopeProvide p s))
      (EffName.scopeClose s) false
  | .scopeOpen _, _ => badShape
  | .scopeProvide p s, v =>
    -- the previous context is read back off the value; any other shape is the wrong one
    match Val.context? v with
    | some previous =>
      Prim.onSuccess (Prim.withFiber (EffThunk.setCtx (previous.withScope s)))
        (EffName.scopeBody p previous)
    | none => badShape
  | .scopeBody p previous, _ =>
    Prim.onExit (resolve root (p.child 0)) (EffName.restoreCtx previous) false
  | .constant v, _ => Prim.success v
  | .abort, _ => Prim.success Val.unit
  | .store name, v => embed (Effect4.Machine.contAOf name v)
  -- `acquireRelease` (`internal/effect.ts:3971-3987`): the context read back off the value
  | .acquireCtx p, v =>
    match Val.context? v with
    | some ctx => Prim.withFiber (EffThunk.acquireMasked p ctx)
    | none => badShape
  -- the `Scope` service read answered its handle (`:3929`): the acquire, child 0
  | .acquireIn p ctx, Val.scopeHandle s =>
    Prim.onSuccess (resolve root (p.child 0)) (EffName.acquired p ctx s)
  | .acquireIn _ _, _ => badShape
  -- `tap`: register the release as a capture on the scope (`:3983`), then answer `a`
  | .acquired p ctx s, a =>
    Prim.onSuccess (Prim.sync (EffThunk.op (SyncOp.scopeAdd s (FinName.foreign (p.capture a ctx)))))
      (EffName.afterScopeAdd a (FinName.foreign (p.capture a ctx)))
  -- `:3856`: unit, the registration took; `:3853`: the scope had closed and its closing exit
  -- came back, so run the release now (one row with an `if`, so the term reference splits
  -- the same way)
  | .afterScopeAdd a fin, v =>
    if v = Val.unit then Prim.success a
    else
      match exitOfVal v with
      | some exit => Prim.onSuccess (embed (finProgram fin exit)) (EffName.constant a)
      | none => badShape
  -- `provideContext(release(a, exit), context)` (`:2180-2199`): the current context read
  -- back off the value, the captured one set, the release under the restoring finalizer
  | .releaseUnder p ctx exit, v =>
    match Val.context? v with
    | some previous =>
      Prim.onSuccess (Prim.withFiber (EffThunk.setCtx ctx)) (EffName.releaseBody p exit previous)
    | none => badShape
  | .releaseBody p exit previous, _ =>
    Prim.withFiber (EffThunk.releaseMasked (p.childWith 1 (reifyExitVal exit)) previous)
  -- the join: `scopedWith`'s scope is made (`internal/effect.ts:3966`); `internal/layer.ts:15-21`
  | .provideLayerWith p, Val.scopeHandle scope => provideLayerWithK root p scope
  | .provideLayerWith _, _ => badShape
  | .provideLayerBody p, v => provideLayerBodyK root p v
  | .updateThen update body, v => updateThenK root update body v
  | .bodyThen body previous, _ =>
    Prim.onExit (regionCode root body) (EffName.restoreCtx previous) false
  | .buildWithScopeFromContext q scope, v => buildWithScopeK q scope v
  -- `buildWithMemoMap` (`Layer.ts:756-765`) on the forked-or-created map
  | .withMemoMapThen q scope, Val.memoMap ⟨id⟩ =>
    updateContextAt (Env.ContextUpdate.provideService Env.currentMemoMapKey (Val.memoMap ⟨id⟩))
      (Region.buildAdding q ⟨id⟩ scope)
  | .withMemoMapThen _ _, _ => badShape
  | .addCurrentMemoMap m, v => addCurrentMemoMapK m v
  -- `fromBuild` (`Layer.ts:339-344`) on the forked layer scope
  | .fromBuildThen q m, Val.scopeHandle child =>
    Prim.onExit (innerLayerAt root q m child)
      (EffName.store (Name.finalizerName (FinName.closeChildOnFailure child))) false
  | .fromBuildThen _ _, _ => badShape
  -- `getOrElseMemoize` after `get` (`Layer.ts:451-455`): a hit is the entry's deferred and its
  -- owning map (`:439-440`, `:246-249`), registering the entry finalizer on the caller scope
  -- then awaiting; unit is a miss, `memoMapBuild`
  | .memoize q _ scope, Val.pair (Val.promise ⟨cell⟩) (Val.memoMap ⟨owner⟩) =>
    Prim.onSuccess (scopeAddAt scope (FinName.memoEntry q.path ⟨owner⟩))
      (EffName.awaitPromise ⟨cell⟩)
  | .memoize q m scope, Val.unit =>
    Prim.onSuccess (Prim.sync (EffThunk.op (SyncOp.memoBuild q.path m)))
      (EffName.buildIntoLayerScope q m scope)
  | .memoize _ _ _, _ => badShape
  | .awaitPromise cell, _ =>
    Prim.async (EffName.registerAwait cell) true (some (EffName.cancelAwait cell))
  | .buildIntoLayerScope q m scope, Val.scopeHandle layerScope =>
    Prim.onSuccess (scopeAddAt scope (FinName.memoEntry q.path m))
      (EffName.thenBuildInto q m layerScope)
  | .buildIntoLayerScope _ _ _, _ => badShape
  | .thenBuildInto q m layerScope, _ =>
    Prim.onExit (constructionAt root q layerScope)
      (EffName.store (Name.finalizerName (FinName.memoDone q.path m))) false
  | .freshThen q scope, Val.memoMap ⟨id⟩ => resolveLayer root q ⟨id⟩ scope
  | .freshThen _ _, _ => badShape
  | .provideThen q m scope mode, v => provideThenK q m scope mode v
  | .combineWith mode that, v => combineWithK mode that v
  -- `mergeAllEffect` (`Layer.ts:1596-1600`): the parallel parent, one sequential child per
  -- sibling with that sibling's build forked into it, then the await and the merge
  | .mergeChildren q m, Val.scopeHandle parent =>
    Prim.onSuccess
      (Prim.sync (EffThunk.op (SyncOp.scopeFork parent FinalizerStrategy.sequential)))
      (EffName.mergeForkOne q 0 m parent [])
  | .mergeChildren _ _, _ => badShape
  | .mergeForkOne q i m parent forked, Val.scopeHandle child =>
    Prim.onSuccess (Prim.withFiber (EffThunk.forkLayer (q.child i) m child))
      (EffName.mergeForkNext q i m parent forked)
  | .mergeForkOne _ _ _ _ _, _ => badShape
  | .mergeForkNext q i m parent forked, Val.fiber ⟨id⟩ =>
    if i = 0 then
      Prim.onSuccess
        (Prim.sync (EffThunk.op (SyncOp.scopeFork parent FinalizerStrategy.sequential)))
        (EffName.mergeForkOne q 1 m parent (forked ++ [⟨id⟩]))
    else
      Prim.onSuccess (Prim.withFiber (EffThunk.awaitAllFailFast (forked ++ [⟨id⟩])))
        EffName.mergeContexts
  | .mergeForkNext _ _ _ _ _, _ => badShape
  | .mergeContexts, v => mergeContextsK v
  | .serviceLookup key, v => serviceLookupK key v
  | .bindService key, v => bindServiceK key v
  | _, v => Prim.success v

/-- `cont[contE](cause, fiber)`. -/
def contEOf (root : NativeEff) : EffName → CauseV → NCode
  | .caught p, cause => resolve root (p.childWith 1 (Val.exitErr cause))
  | .onCause p, cause => resolve root (p.childWith 2 (Val.exitErr cause))
  | .restore exit, cause => Prim.ofExit (Exit.restoreAfterFinalizer exit (Exit.failure cause))
  | .merge exit, cause => Prim.ofExit (Exit.restoreAfterFinalizer exit (Exit.failure cause))
  | .constant v, _ => Prim.success v
  | .store name, cause => embed (Effect4.Machine.contEOf name cause)
  | .orDie, cause => Prim.failure (orDieCause cause)
  | _, cause => Prim.failure cause

/-- The cancel effect a cancel name runs (`Deferred.await`'s cleanup splices the waiter out,
as the stores spell it); an embedded cancel name runs the stores' cancel program. -/
def cancelProgramOf : EffName → NCode
  | .withWaiter (.cancelAwait cell) waiter token =>
    Prim.sync (EffThunk.op (SyncOp.deferredAwaitCleanup cell waiter token))
  | .withWaiter (.store base) waiter token => embed (cancelProgram (Name.withWaiter base waiter token))
  | .store name => embed (cancelProgram name)
  | _ => Prim.success Val.unit

/-- The value of a `sync` thunk that touches no store: the term at its point. -/
def syncValueAt (root : NativeEff) : EffThunk → Val
  | .pure p =>
    match Node.at_ (Node.eff root) p.path with
    | some (Node.eff (.sync t)) => (evalTerm p.env t).getD Val.unit
    | _ => Val.unit
  | _ => Val.unit

/-- What a `suspend` thunk returns: a body compiled at its point, a branch decided by its
point's environment, the iterator of a generator (`Effect.gen`'s `fromIteratorUnsafe`,
`internal/effect.ts:1175-1196`), or the loop frame of a `whileLoop` with its initial cursor
read now (the printed `let a0 = initial` inside the suspension, `Codegen/Print.lean:158-168`). -/
def suspendBodyAt (root : NativeEff) : EffThunk → NCode
  | .body p =>
    match p.fuel with
    | 0 => frontier p
    | _ + 1 =>
      match Node.at_ (Node.eff root) p.path with
      | some (Node.eff (.suspend _)) => resolve root (p.child 0)
      | some (Node.eff (.branch test _ _)) =>
        match evalTerm p.env test with
        | some (Val.bool true) => resolve root (p.child 0)
        | some (Val.bool false) => resolve root (p.child 1)
        | _ => badShape
      | some (Node.eff (.gen _)) => Prim.iterator (EffName.gen p [] false) Val.unit
      | some (Node.eff (.whileLoop initial _ _ _)) =>
        match evalTerm p.env initial with
        | some cursor => Prim.whileLoop (EffName.loop p) cursor
        | none => badShape
      -- `scopedWith` (`internal/effect.ts:3966-3967`): the scope made, the rest named
      | some (Node.eff (.provideLayer _ _ _)) =>
        Prim.onSuccess
          (Prim.sync (EffThunk.op (SyncOp.scopeMake FinalizerStrategy.sequential)))
          (EffName.provideLayerWith p)
      | some (Node.eff e) => compileEff e p
      | _ => badShape
  -- `getOrElseMemoize` (`Layer.ts:451`): the lookup, then `memoize` on its answer
  | .memoLookup q m scope =>
    Prim.onSuccess (Prim.sync (EffThunk.op (SyncOp.memoGet q.path m))) (EffName.memoize q m scope)
  | .store (Thunk.body program) => embed (progOf program)
  -- a capture's release (`FinName.foreign`, V1): `provideContext(release(a, exit), context)`
  -- (`internal/effect.ts:3983`) — read the current context, then `releaseUnder`
  | .store (Thunk.foreign capture exit) =>
    Prim.onSuccess (Prim.withFiber EffThunk.getCtx)
      (EffName.releaseUnder (Point.ofCapture capture) capture.ctx exit)
  | _ => Prim.failure (Cause.die Defect.notImplemented)

/-- The loop at a point: its test, step and body terms. -/
def loopAt (root : NativeEff) (p : Point) : Option (Term × Term × NativeEff) :=
  match Node.at_ (Node.eff root) p.path with
  | some (Node.eff (.whileLoop _ test step body)) => some (test, step, body)
  | _ => none

/-- The interp of a root program: names mean the subterms they address. -/
def interpOf (root : NativeEff) :
    RunInterp EffName EffThunk Val Err Defect FiberId Ann Ctx Stores where
  contA := contAOf root
  contE := contEOf root
  syncValue := syncValueAt root
  suspendBody := suspendBodyAt root
  finalizerExit := fun
    | .store (Name.finalizerName fin), exit => finExit fin exit
    | _, _ => Exit.void
  reifyExit := reifyExitVal
  iterNext := fun name value =>
    match name with
    | .gen p pc bind => runStmts root p p.fuel pc (if bind then p.env ++ [value] else p.env) []
    -- the stores' generators (a scope's close walk, §20), their steps embedded
    | .store n => ((stores.iterNext n value).1, embedStep (stores.iterNext n value).2)
    | _ => ([], IterStep.done value)
  loopTest := fun name cursor =>
    match name with
    | .loop p =>
      match loopAt root p with
      | some (test, _, _) => evalTerm (p.env ++ [cursor]) test = some (Val.bool true)
      | none => false
    | _ => false
  loopBody := fun name cursor =>
    match name with
    | .loop p => resolve root (p.childWith 0 cursor)
    | _ => Prim.success cursor
  loopStep := fun name cursor answer =>
    match name with
    | .loop p =>
      match loopAt root p with
      | some (_, step, _) => (evalTerm (p.env ++ [cursor, answer]) step).getD cursor
      | none => cursor
    | _ => cursor
  loopDone := fun _ => Val.unit
  notImplemented := Defect.notImplemented
  cancelThenFail := fun name cause => Prim.onSuccess (cancelProgramOf name) (EffName.reFail cause)
  parkOf := fun
    | Prim.suspend (EffThunk.park kind) => some (Except.ok kind)
    | Prim.suspend (EffThunk.store (Thunk.park kind)) => some (Except.ok kind)
    | _ => none
  parkCode := fun kind => Prim.suspend (EffThunk.park kind)
  -- the interrupt programs are the stores' named actions, embedded (source-repairs §19, D6b)
  interruptCode := fun target => embed (Prim.withFiber (Thunk.act (ActionName.interrupt target)))
  interruptAsCode := fun target who =>
    embed (Prim.withFiber (Thunk.act (ActionName.interruptAs target who)))
  interruptAllCode := fun targets =>
    embed (Prim.withFiber (Thunk.act (ActionName.interruptAll targets none)))
  withFiberOf := fun
    | EffThunk.act p => actionAt root p
    | EffThunk.forkInAt p scope => forkScopedAt root p scope
    | EffThunk.getCtx => some WithFiberAction.getContext
    | EffThunk.setCtx context => some (WithFiberAction.setContext context)
    | EffThunk.closeScope scope exit => some (WithFiberAction.closeScope scope exit)
    | EffThunk.store (Thunk.act action) => some (embedAction (actionOf action))
    -- `uninterruptibleMask(restore => flatMap(scope, scope => tap(acquire, …)))` (`:3977-3986`):
    -- the `Scope` service read is the stores' own action, embedded
    | EffThunk.acquireMasked p ctx =>
      some (WithFiberAction.setInterruptible
        (Prim.onSuccess (Prim.withFiber (EffThunk.store (Thunk.act ActionName.ambientScope)))
          (EffName.acquireIn p ctx)) false)
    -- the release at its point under the context-restoring finalizer (`:2180-2199`)
    | EffThunk.releaseMasked p previous =>
      some (WithFiberAction.setInterruptible
        (Prim.onExit (resolve root p) (EffName.restoreCtx previous) false) false)
    -- `mergeAllEffect`'s siblings (`Layer.ts:1597`): `forEach`'s concurrency forks each build
    -- as an immediate daemon under the parent's mask (`forkUnsafe(parent, eff, true, true,
    -- "inherit")`, `internal/effect.ts:4851`), then the await
    | EffThunk.forkLayer q m scope =>
      some (WithFiberAction.fork (resolveLayer root q m scope)
        ⟨true, true, Supervision.MaskMode.inherit⟩)
    | EffThunk.awaitAllFailFast targets => some (WithFiberAction.awaitAllFailFast targets)
    | _ => none
  syncState := fun
    | EffThunk.op operation, state => syncOpStep operation state
    | EffThunk.store (Thunk.op operation), state => syncOpStep operation state
    | _, _ => none
  registerAsync := fun name fiber token state =>
    match name with
    | .registerAwait cell =>
      let (deferreds, immediate) := state.deferreds.register cell fiber token
      ({ state with deferreds := deferreds }, immediate.map embed)
    | .store (Name.registerAwait cell) =>
      let (deferreds, immediate) := state.deferreds.register cell fiber token
      ({ state with deferreds := deferreds }, immediate.map embed)
    | _ => (state, none)
  dueResumes := fun state =>
    let (due, deferreds) := state.deferreds.drainDue
    (due.map (Owed.mapCode embed), { state with deferreds := deferreds })
  wakeList := Stores.wakeList
  answerCode := fun answer => embed (completionPrim answer)
  cancelName := fun base fiber token => EffName.withWaiter base fiber token
  -- the parks' cleanups and the settled race's program are the stores' own, embedded
  parkCancelName := EffName.store Name.cancelPark
  raceCancelName := fun race => EffName.store (Name.cancelRace race)
  raceSettle := fun race cleanupNeeded exit => embed (raceSettleProgram race cleanupNeeded exit)
  abortName := EffName.abort
  finalizerProgram := fun name exit =>
    match name with
    | .fin p => some (resolve root (p.childWith 1 (reifyExitVal exit)))
    | .scopeClose scope => some (Prim.withFiber (EffThunk.closeScope scope exit))
    | .restoreCtx previous => some (Prim.withFiber (EffThunk.setCtx previous))
    | .store (Name.finalizerName fin) => some (embed (finProgram fin exit))
    | _ => none
  restoreName := EffName.restore
  mergeName := EffName.merge
  scopeStatus := fun scope state => state.scopes.status scope
  -- the registration identity is the store's, allocated at the executed registration
  -- (`const key = {}`, `internal/effect.ts:5366`, `:5457`); `E4-CHECK-CE-016`
  scopeLinkFiber := fun mode scope fiber state =>
    match state.scopes.entryAt scope with
    | none => none
    | some _ =>
      let skipSelf :=
        match mode with
        | Supervision.ScopeMode.forkIn => true
        | Supervision.ScopeMode.fiberRunIn => false
      some ({ state with
        scopes := (state.scopes.addFinalizer scope state.nextName
          (FinName.interruptFiber fiber skipSelf)).1,
        nextName := state.nextName + 1 }, state.nextName)
  dropFinalizer := fun scope key state =>
    match state.scopes.entryAt scope with
    | none => none
    | some _ => some { state with scopes := state.scopes.removeFinalizer scope key }
  closeScope := fun scope exit closerInterruptible _closer state =>
    (storesCloseScope scope exit closerInterruptible state).map fun r => (r.1, embed r.2)
  ambientScope := Ctx.ambientScope
  budgetOf := fun ctx => (ctx.maxOpsBeforeYield, ctx.preventYield)
  emptyContext := emptyCtx
  contextValue := Val.context
  exitValue := fun exit mode =>
    match mode with
    | Supervision.ObserverMode.awaitValue => Prim.success (reifyExitVal exit)
    | Supervision.ObserverMode.joinEffect => Prim.ofExit exit
  fiberValue := Val.fiber
  fiberIdValue := fun fiber => Val.nat fiber.value
  fibersValue := Val.fibers
  exitsValue := exitsVal
  voidValue := Val.unit
  scopeValue := Val.scopeHandle
  closeDoneName := EffName.store Name.closeParDone
  encodeFiber := id
  stackAnnotations := stackAnnotationsOf
  asyncFiberError := Defect.asyncFiber
  missingScope := Defect.missingService

/-- Native source callbacks construct their code from the exits visible when
invoked (`internal/effect.ts:767-777,814-822`). Eager action bodies and the scoped
administrative callbacks keep the view captured in their point. -/
def interpAt (root : NativeEff) (completed : List (FiberId × ExitV)) :
    RunInterp EffName EffThunk Val Err Defect FiberId Ann Ctx Stores :=
  { interpOf root with
    contA := fun name value => contAOf root (match name with
      | .cont p => .cont { p with completed }
      | .onValue p => .onValue { p with completed }
      -- the release is constructed with the view at its own invocation, as `.fin p` below
      | .releaseBody p exit previous => .releaseBody { p with completed } exit previous
      | name => name) value
    contE := fun name cause => contEOf root (match name with
      | .caught p => .caught { p with completed }
      | .onCause p => .onCause { p with completed }
      | name => name) cause
    suspendBody := fun thunk => suspendBodyAt root (match thunk with
      | .body p => .body { p with completed }
      | thunk => thunk)
    iterNext := fun name value => match name with
      | .gen p pc bind => runStmts root { p with completed } p.fuel pc
          (if bind then p.env ++ [value] else p.env) []
      | .store n => ((stores.iterNext n value).1, embedStep (stores.iterNext n value).2)
      | _ => ([], .done value)
    loopBody := fun name cursor => match name with
      | .loop p => resolve root ({ p with completed }.childWith 0 cursor)
      | _ => Prim.success cursor
    finalizerProgram := fun name exit => match name with
      | .fin p => some (resolve root ({ p with completed }.childWith 1 (reifyExitVal exit)))
      | _ => (interpOf root).finalizerProgram name exit }

/-- Atomic scoped entry (`internal/effect.ts:3938-3948`). Its body was already
constructed, so its point retains the captured completed-exit view. -/
def enterScoped (root : NativeEff) (p : Point)
    (m : RunMachine EffName EffThunk Val Err Defect FiberId Ann Ctx Stores)
    (f : RunFiber EffName EffThunk Val Err Defect FiberId Ann Ctx) (yielding : Bool) :
    Iter EffName EffThunk Val Err Defect FiberId Ann Ctx Stores :=
  let scope := m.state.nextName
  let state := { m.state with
    scopes := m.state.scopes.make scope .sequential, nextName := scope + 1 }
  let context := f.context.withScope scope
  let current := Prim.onExit (resolve root (p.child 0)) (.scopedExit f.context scope) false
  let f := { f with
    context := context
    maxOpsBeforeYield := context.maxOpsBeforeYield
    preventYield := context.preventYield
    frame := { f.frame with current } }
  ⟨{ m with state }, f, yielding, .continue_, []⟩

/-- The scoped callback runs after the real pop, including any passed mask
frames, and restores context before constructing unsafe close's optional effect
(`internal/effect.ts:3944-3947`). Ordinary exits reuse the primitive evaluator. -/
def exitScoped (root : NativeEff)
    (m : RunMachine EffName EffThunk Val Err Defect FiberId Ann Ctx Stores)
    (f : RunFiber EffName EffThunk Val Err Defect FiberId Ann Ctx) (yielding : Bool)
    (exit : ExitV) : Iter EffName EffThunk Val Err Defect FiberId Ann Ctx Stores :=
  let interp := interpAt root m.completedExits
  let pop := f.frame.getCont
    (match exit with | .success _ => .contA | .failure _ => .contE)
    (match exit with | .success _ => false | .failure _ => true)
  match pop.answer with
  | .frame (.onExit _ (.scopedExit previous scope) _) =>
    let f := { f with
      frame := pop.fiber
      context := previous
      maxOpsBeforeYield := previous.maxOpsBeforeYield
      preventYield := previous.preventYield }
    let m := m.emit (pop.events.map (RunEvent.frame f.id))
    match storesCloseScopeUnsafe scope exit f.frame.interruptible m.state with
    | none => ⟨m, f, yielding, .stuck (.unknownScope scope), []⟩
    | some (state, program) =>
      let m := { m with state }
      let m := match program with
        | none => m
        | some _ => m.emit [RunEvent.finalizerProgram f.id (.scopedExit previous scope) exit]
      let current := match program with
        | none => Prim.ofExit exit
        | some code => finalizerCode interp exit (embed code)
      ⟨m, { f with frame := { f.frame with current } }, yielding, .continue_, []⟩
  | _ => evaluatePrim interp m f yielding

/-- Native source actions use the shared loop's stateful evaluator seam. Only
scoped entry and its exit callback need state in addition to the source hooks. -/
def evaluateNative (root : NativeEff)
    (m : RunMachine EffName EffThunk Val Err Defect FiberId Ann Ctx Stores)
    (f : RunFiber EffName EffThunk Val Err Defect FiberId Ann Ctx) (yielding : Bool) :
    Iter EffName EffThunk Val Err Defect FiberId Ann Ctx Stores :=
  match f.frame.current with
  | .withFiber (.act p) =>
    match Node.at_ (.eff root) p.path with
    | some (.eff (.scoped _)) => enterScoped root p m f yielding
    | _ => evaluatePrim (interpAt root m.completedExits) m f yielding
  | .success v => exitScoped root m f yielding (.success v)
  | .failure c => exitScoped root m f yielding (.failure c)
  | _ => evaluatePrim (interpAt root m.completedExits) m f yielding

/-- Native callbacks use the construction view and scoped protocol of this
evaluation. The command loop retains `interpOf` for bookkeeping and stores. -/
@[reducible] def evaluatorFor (root : NativeEff) :
    FiberEvaluator EffName EffThunk Val Err Defect FiberId Ann Ctx Stores NCode
      (FrameFiber EffName EffThunk Val Err Defect FiberId Ann)
      (FrameEvent EffName EffThunk Val Err Defect FiberId Ann) where
  evaluate := fun _ => evaluateNative root

/-- The root point of a program: the empty path, no values, the fuel and the tape. -/
def rootPoint (fuel : Nat) (tape : List Bool := []) : Point :=
  { path := [], env := [], fuel, tape }

/-- The compiled root. -/
def compile (root : NativeEff) (fuel : Nat) (tape : List Bool := []) : NCode :=
  compileEff root (rootPoint fuel tape)

/-! ## Separation-4 gates: names and thunks stay data -/

example : DecidableEq EffName := inferInstance
example : DecidableEq EffThunk := inferInstance
example : DecidableEq NCode := inferInstance

end Effect4.Program
