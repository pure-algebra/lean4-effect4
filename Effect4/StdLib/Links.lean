import Effect4.StdLib.Rc112
import Effect4.Stateful.RefFamily
import Effect4.Stateful.DeferredFamily
import Effect4.Runtime.ScopeFamily
import Effect4.Layer.LayerFamily
import Effect4.Context.ContextFamily
import Effect4.Target.TypeScript.FiberProfile

/-!
# StdLib.Links

Owner: the semantics around an export — what this tree holds for a name in
the pinned standard library.

A `Link` ties a census path to the model elements that reify it: a family row
(the service route's spelling of it), a frame primitive (what the rc.112 run
loop evaluates it as), a machine action (what `withFiber` does for it), a
store operation (what a `sync` thunk does for it). Every link is checked:
the path is a census entry, a row names an operation of the family it cites,
and a primitive, action or store operation names a constructor the model has.

This is the atom-level view of code: a name in a program resolves through the
store to its entry, and through the links to its semantics.
-/

namespace Effect4.StdLib

open Effect4.Store
open Effect4.Target.EffectV4 (ServiceRow)

/-- A model element an export is tied to. -/
inductive ModelRef where
  /-- An operation of a family: the service-route spelling. -/
  | row (family op : String)
  /-- A constructor of `Effect4.Prim`: the frame the run loop evaluates. -/
  | prim (constructor : String)
  /-- A `WithFiberAction`: what the fiber does for it. -/
  | action (name : String)
  /-- A `Deep.Stores.SyncOp`: what the store does for it. -/
  | syncOp (name : String)
deriving DecidableEq, Repr

structure Link where
  path : Path
  refs : List ModelRef
deriving DecidableEq, Repr

/-- The frame primitives, as `Effect4/Runtime/Runtime.lean` declares them. -/
def primNames : List String :=
  ["success", "failure", "sync", "suspend", "withFiber", "yieldableError", "iterator",
   "onSuccess", "onFailure", "onSuccessAndFailure", "exitFrame", "onExit", "setInterruptible",
   "whileLoop", "yieldNowWith", "async", "asyncFinalizer"]

/-- The fiber actions, as `Effect4/Deep/Fibers.lean` declares them. -/
def actionNames : List String :=
  ["fork", "forkIn", "forkScoped", "runIn", "interrupt", "interruptScoped", "interruptAll",
   "awaitAll", "awaitAllFailFast", "snapshotChildren", "awaitNewChildren", "raceAll",
   "setInterruptible", "setContext", "getContext", "getId"]

/-- The store operations, as `Effect4/Deep/Stores.lean` declares them. -/
def syncOpNames : List String :=
  ["refMake", "refGet", "refSet", "refGetAndSet", "refSetAndGet", "refUpdate", "refGetAndUpdate"]

/-- The families a row may cite, with their rows. -/
def families : List (String × ServiceRow) :=
  [ ("Refs", Effect4.RefFamily.Refs.rows)
  , ("Deferreds", Effect4.DeferredFamily.Deferreds.rows)
  , ("Scopes", Effect4.ScopeFamily.Scopes.rows)
  , ("Layers", Effect4.LayerFamily.Layers.rows)
  , ("Contexts", Effect4.ContextFamily.Contexts.rows)
  , ("Fibers", Effect4.Target.EffectV4.fibersRowsNat) ]

/-- The links this tree holds today: the runtime surface the models reify. -/
def links : List Link :=
  [ ⟨["Effect", "gen"], [.prim "iterator"]⟩
  , ⟨["Effect", "sync"], [.prim "sync"]⟩
  , ⟨["Effect", "suspend"], [.prim "suspend"]⟩
  , ⟨["Effect", "succeed"], [.prim "success"]⟩
  , ⟨["Effect", "fail"], [.prim "failure"]⟩
  , ⟨["Effect", "failCause"], [.prim "failure"]⟩
  , ⟨["Effect", "flatMap"], [.prim "onSuccess"]⟩
  , ⟨["Effect", "catchCause"], [.prim "onFailure"]⟩
  , ⟨["Effect", "matchCauseEffect"], [.prim "onSuccessAndFailure"]⟩
  , ⟨["Effect", "onExit"], [.prim "onExit"]⟩
  , ⟨["Effect", "exit"], [.prim "exitFrame"]⟩
  , ⟨["Effect", "uninterruptible"], [.prim "setInterruptible", .action "setInterruptible"]⟩
  , ⟨["Effect", "interruptible"], [.prim "setInterruptible", .action "setInterruptible"]⟩
  , ⟨["Effect", "whileLoop"], [.prim "whileLoop"]⟩
  , ⟨["Effect", "yieldNow"], [.prim "yieldNowWith", .row "Fibers" "yieldNow"]⟩
  , ⟨["Effect", "yieldNowWith"], [.prim "yieldNowWith", .row "Fibers" "yieldNow"]⟩
  , ⟨["Effect", "callback"], [.prim "async", .prim "asyncFinalizer"]⟩
  , ⟨["Effect", "withFiber"], [.prim "withFiber"]⟩
  , ⟨["Effect", "forkChild"], [.prim "withFiber", .action "fork", .row "Fibers" "fork"]⟩
  , ⟨["Effect", "forkDetach"], [.prim "withFiber", .action "fork"]⟩
  , ⟨["Effect", "forkIn"], [.prim "withFiber", .action "forkIn"]⟩
  , ⟨["Effect", "forkScoped"], [.prim "withFiber", .action "forkScoped", .row "Fibers" "forkScoped"]⟩
  , ⟨["Effect", "raceAll"], [.prim "withFiber", .action "raceAll", .row "Fibers" "raceAll"]⟩
  , ⟨["Effect", "provideContext"], [.row "Contexts" "provideContext"]⟩
  , ⟨["Effect", "updateContext"], [.row "Contexts" "updateContext"]⟩
  , ⟨["Effect", "contextWith"], [.prim "withFiber", .action "getContext", .row "Contexts" "withContext"]⟩
  , ⟨["Fiber", "join"], [.row "Fibers" "join"]⟩
  , ⟨["Fiber", "await"], [.row "Fibers" "awaitFiber"]⟩
  , ⟨["Fiber", "interrupt"], [.action "interrupt", .row "Fibers" "interruptFiber"]⟩
  , ⟨["Fiber", "interruptAll"], [.action "interruptAll", .row "Fibers" "interruptAll"]⟩
  , ⟨["Fiber", "awaitAll"], [.action "awaitAll"]⟩
  , ⟨["Ref", "make"], [.prim "sync", .syncOp "refMake", .row "Refs" "make"]⟩
  , ⟨["Ref", "get"], [.prim "sync", .syncOp "refGet", .row "Refs" "get"]⟩
  , ⟨["Ref", "set"], [.prim "sync", .syncOp "refSet", .row "Refs" "set"]⟩
  , ⟨["Ref", "getAndSet"], [.prim "sync", .syncOp "refGetAndSet", .row "Refs" "getAndSet"]⟩
  , ⟨["Ref", "setAndGet"], [.prim "sync", .syncOp "refSetAndGet", .row "Refs" "setAndGet"]⟩
  , ⟨["Ref", "update"], [.prim "sync", .syncOp "refUpdate", .row "Refs" "update"]⟩
  , ⟨["Ref", "getAndUpdate"], [.prim "sync", .syncOp "refGetAndUpdate", .row "Refs" "getAndUpdate"]⟩
  , ⟨["Deferred", "poll"], [.prim "sync", .row "Deferreds" "poll"]⟩
  , ⟨["Deferred", "interrupt"], [.row "Deferreds" "interrupt"]⟩
  , ⟨["Deferred", "interruptWith"], [.row "Deferreds" "interruptWith"]⟩
  , ⟨["Deferred", "await"], [.prim "async"]⟩
  , ⟨["Scope", "close"], [.row "Scopes" "close"]⟩
  , ⟨["Layer", "succeed"], [.row "Layers" "succeed"]⟩
  , ⟨["Layer", "effect"], [.row "Layers" "effect"]⟩
  -- rc.112's `Layer` exports no `scoped`: the family's `scoped` row is the
  -- scoped *construction* (`effect` over a scoped effect), not an export, so it
  -- has no link here. The census is what says so.
  , ⟨["Layer", "provide"], [.row "Layers" "provide"]⟩
  , ⟨["Layer", "provideMerge"], [.row "Layers" "provideMerge"]⟩
  , ⟨["Layer", "merge"], [.row "Layers" "merge"]⟩
  , ⟨["Layer", "mergeAll"], [.row "Layers" "mergeAll"]⟩
  , ⟨["Layer", "fresh"], [.row "Layers" "fresh"]⟩
  , ⟨["Layer", "orDie"], [.row "Layers" "orDie"]⟩
  , ⟨["Layer", "unwrap"], [.row "Layers" "unwrap"]⟩
  , ⟨["Layer", "build"], [.row "Layers" "build"]⟩
  , ⟨["Layer", "buildWithScope"], [.row "Layers" "buildWithScope"]⟩
  , ⟨["Layer", "buildWithMemoMap"], [.row "Layers" "buildWithMemoMap"]⟩
  , ⟨["Layer", "launch"], [.row "Layers" "launch"]⟩
  , ⟨["Context", "empty"], [.row "Contexts" "empty"]⟩
  , ⟨["Context", "make"], [.row "Contexts" "make"]⟩
  , ⟨["Context", "add"], [.row "Contexts" "add"]⟩
  , ⟨["Context", "get"], [.row "Contexts" "get"]⟩
  , ⟨["Context", "getOption"], [.row "Contexts" "getOption"]⟩
  , ⟨["Context", "merge"], [.row "Contexts" "merge"]⟩
  , ⟨["Context", "mergeAll"], [.row "Contexts" "mergeAll"]⟩
  , ⟨["Context", "pick"], [.row "Contexts" "pick"]⟩
  , ⟨["Context", "omit"], [.row "Contexts" "omit"]⟩ ]

/-- Whether a model reference names something the model declares. -/
def ModelRef.declared : ModelRef → Bool
  | .row family op =>
    match families.find? (·.1 == family) with
    | some entry => (entry.2.row? op).isSome
    | none => false
  | .prim name => primNames.contains name
  | .action name => actionNames.contains name
  | .syncOp name => syncOpNames.contains name

/-- The pinned standard library as a store. -/
def rc112 : Store Entry := store Rc112.entries

/-- Whether a link's path is a census entry and every reference is declared. -/
def Link.checked (link : Link) : Bool :=
  (rc112.resolve link.path).isSome && link.refs.all ModelRef.declared

/-- The semantics held for a path: its entry and its references. -/
def semanticsOf (path : Path) : Option (Entry × List ModelRef) :=
  (rc112.resolve path).map fun found =>
    (found.2, ((links.find? (·.path == path)).map (·.refs)).getD [])

end Effect4.StdLib
