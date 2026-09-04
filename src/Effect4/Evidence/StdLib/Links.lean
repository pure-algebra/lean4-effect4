import Effect4.Evidence.StdLib.Rc112

/-!
# StdLib.Links

Owner: the semantics around an export — what this tree holds for a name in
the pinned standard library.

A `Link` ties a census path to the model elements that reify it: a frame
primitive (what the rc.112 run loop evaluates it as), a machine action (what
`withFiber` does for it), a store operation (what a `sync` thunk does for it).
Every link is checked: the path is a census entry, and a primitive, action or
store operation names a constructor the model has. The service-route rows the
links used to cite went to branch `archive/flow-route` with the families
(`docs/research/2026-09-04-prod-cleanup-inventory.md`, D3); the Eff-era
replacement is the `arms` table of `Effect4/Syntax/Eff.lean`, one row per
constructor with the rc.112 line it compiles to.

This is the atom-level view of code: a name in a program resolves through the
store to its entry, and through the links to its semantics.
-/

namespace Effect4.StdLib

open Effect4.Store

/-- A model element an export is tied to. -/
inductive ModelRef where
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
  , ⟨["Effect", "yieldNow"], [.prim "yieldNowWith"]⟩
  , ⟨["Effect", "yieldNowWith"], [.prim "yieldNowWith"]⟩
  , ⟨["Effect", "callback"], [.prim "async", .prim "asyncFinalizer"]⟩
  , ⟨["Effect", "withFiber"], [.prim "withFiber"]⟩
  , ⟨["Effect", "forkChild"], [.prim "withFiber", .action "fork"]⟩
  , ⟨["Effect", "forkDetach"], [.prim "withFiber", .action "fork"]⟩
  , ⟨["Effect", "forkIn"], [.prim "withFiber", .action "forkIn"]⟩
  , ⟨["Effect", "forkScoped"], [.prim "withFiber", .action "forkScoped"]⟩
  , ⟨["Effect", "raceAll"], [.prim "withFiber", .action "raceAll"]⟩
  , ⟨["Effect", "contextWith"], [.prim "withFiber", .action "getContext"]⟩
  , ⟨["Fiber", "interrupt"], [.action "interrupt"]⟩
  , ⟨["Fiber", "interruptAll"], [.action "interruptAll"]⟩
  , ⟨["Fiber", "awaitAll"], [.action "awaitAll"]⟩
  , ⟨["Ref", "make"], [.prim "sync", .syncOp "refMake"]⟩
  , ⟨["Ref", "get"], [.prim "sync", .syncOp "refGet"]⟩
  , ⟨["Ref", "set"], [.prim "sync", .syncOp "refSet"]⟩
  , ⟨["Ref", "getAndSet"], [.prim "sync", .syncOp "refGetAndSet"]⟩
  , ⟨["Ref", "setAndGet"], [.prim "sync", .syncOp "refSetAndGet"]⟩
  , ⟨["Ref", "update"], [.prim "sync", .syncOp "refUpdate"]⟩
  , ⟨["Ref", "getAndUpdate"], [.prim "sync", .syncOp "refGetAndUpdate"]⟩
  , ⟨["Deferred", "poll"], [.prim "sync"]⟩
  , ⟨["Deferred", "await"], [.prim "async"]⟩ ]

/-- Whether a model reference names something the model declares. -/
def ModelRef.declared : ModelRef → Bool
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
