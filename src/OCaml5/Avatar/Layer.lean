import OCaml5.Ml.Reflect
import OCaml5.Avatar.Part
import OCaml5.Avatar.Derived.Layer

/-!
# OCaml5.Avatar.Layer

**What it is.** The descriptions behind the generated block of `ocaml/avatar/deep_layer.ml`, the
port of `src/Effect4/Machine/Layer.lean` (seat F2).

**Depends on.** `OCaml5.Ml.Reflect`, `OCaml5.Avatar.Part`, `OCaml5.Avatar.Derived.Layer`.

**Properties.**
* **Field and constructor order is the Lean order**, arity for arity — *tested* (`Check`).
* **The block is byte-identical to the one the avatar file carries** — *tested*
  (`ocaml/avatar/render-deep.sh`), executed.
-/

namespace OCaml5.Avatar

open OCaml5.Ml

/-! ## `src/Effect4/Machine/Layer.lean` → `ocaml/avatar/deep_layer.ml` (seat F2)

The collision ruling (F1.4 step 2, taken): Layer's carriers keep the Lean type names inside
their own module (`Deep_layer.sync_op` beside `Deep_stores.sync_op`, as `Effect4.Machine.Layers`
beside `Effect4.Machine`), `deep_layer.ml` does not `open Deep_stores`, and every constructor takes
a Layer prefix (`Lc`/`Lk`/`Ld`/`Lfin`/`Ls`/`Lp`/`Ln`/`La`/`Lt`/`Lu`/`Lx`, `Lss` for the
`ScopeState` copy) so a file opening both modules is unambiguous. The SHIM
`DeferredKey`/`DeferredCell`/`DeferredStore` (`Layer.lean:367-429`) are *substituted* by
`Deep_stores`' (one store, as the landing intends); `ScopeEntry`/`ScopeStore` and the `Scope`/
`ScopeState` they are made of are rendered as Layer's own monomorphic copies over Layer's
`FinName` (`Layer.lean:431-482`; the generator has no type parameters here — a row). `Val`
(`Context.lean:797`) is the wire alphabet `value` (W1-1 again: `memoMap`/`promise`/`scopeHandle`
are one `Vhandle`, `ctxNil`/`ctxCons` the context list, `exitOk`/`exitErr` lost); `Ctx` is
`(service_key * value) list`; `Err` is `Deep_stores.err` (the same two constructors,
`Context.lean:772`); `Ann` is `unit`. -/

namespace Layer

def subst : Subst :=
  [("FiberId", Ty.int),
   ("LayerId", Ty.named "layer_id"),
   ("MemoMapId", Ty.named "memo_map_id"),
   ("DeferredKey", Ty.named "Deep_stores.deferred_key"),
   ("DeferredCell", Ty.named "Deep_stores.deferred_cell"),
   ("DeferredStore", Ty.named "Deep_stores.deferred_store"),
   ("ServiceKey", Ty.named "Deep_context.service_key"),
   ("ServiceName", Ty.int),
   ("ServiceTypeCode", Ty.int),
   ("Err", Ty.named "Deep_stores.err"),
   ("Defect", Ty.named "Deep_context.defect"),
   ("Ann", Ty.unit),
   ("Val", Ty.named "value"),
   ("Ctx", Ty.list (Ty.named "service_pair")),
   ("ContextUpdate", Ty.named "Deep_context.context_update"),
   ("CombineMode", Ty.named "combine_mode"),
   ("Construction", Ty.named "construction"),
   ("LayerDesc", Ty.named "layer_desc"),
   ("LayerTable", Ty.list (Ty.named "layer_desc")),
   ("FinName", Ty.named "fin_name"),
   ("SyncOp", Ty.named "sync_op"),
   ("ProgName", Ty.named "prog_name"),
   ("Name", Ty.named "name"),
   ("ActionName", Ty.named "action_name"),
   ("Thunk", Ty.named "thunk"),
   ("Program", Ty.named "program"),
   ("Prim", Ty.named "program"),
   ("MemoEntry", Ty.named "memo_entry"),
   ("MemoMap", Ty.named "memo_map"),
   ("MemoWorld", Ty.list (Ty.named "memo_map")),
   ("ScopeEntry", Ty.named "scope_entry"),
   ("ScopeStore", Ty.named "scope_store"),
   ("ScopeV", Ty.named "scope"),
   ("Scope", Ty.named "scope"),
   ("ScopeState", Ty.named "scope_state"),
   ("FinalizerStrategy", Ty.named "Deep_stores.finalizer_strategy"),
   ("Exit", Ty.named "exitv"), ("ExitV", Ty.named "exitv"),
   ("Cause", Ty.named "cause"), ("CauseV", Ty.named "cause"),
   ("Reason", Ty.named "reason"), ("ReasonV", Ty.named "reason"),
   ("ReasonAnnotations", Ty.list Ty.string),
   ("Supervision.ObserverMode", Ty.named "observer_mode"),
   ("Supervision.ForkOptions", Ty.named "fork_options"),
   ("χ", Ty.list (Ty.named "service_pair"))]

private def fid : LTy := .nm "FiberId"
private def exitL : LTy := .nm "ExitV"
private def causeL : LTy := .nm "CauseV"
private def valL : LTy := .nm "Val"
private def ctxL : LTy := .nm "Ctx"
private def lid : LTy := .nm "LayerId"
private def mid : LTy := .nm "MemoMapId"
private def keyL : LTy := .nm "ServiceKey"
private def progL : LTy := .nm "ProgName"

def layerId : StructDesc where
  leanName := "LayerId"; site := "Layer.lean:53"; subst := subst
  fields := [{ leanName := "index", leanTy := .nat }]
def memoMapId : StructDesc where
  leanName := "MemoMapId"; site := "Layer.lean:58"; subst := subst
  fields := [{ leanName := "index", leanTy := .nat }]
/-- `ServiceKey` (`src/Effect4/Machine/Key.lean:79`): `ServiceName`/`ServiceTypeCode` are `Nat`
boxes, rendered as `int`. -/
def serviceKey : StructDesc where
  leanName := "ServiceKey"; site := "Context/Key.lean:79"; subst := subst
  fields := [{ leanName := "name", leanTy := .nm "ServiceName" },
             { leanName := "service", leanTy := .nm "ServiceTypeCode" }]
/-- `Defect` (`Context.lean:781`), prefix `Lx`. -/
def defect : InductiveDesc where
  leanName := "Defect"; site := "Context.lean:781"; ctorPrefix := "Lx"; subst := subst
  ctors := [{ leanName := "notImplemented" }, { leanName := "asyncFiber" }, { leanName := "badName" },
            { leanName := "serviceNotFound", args := [⟨"key", keyL, false⟩] },
            { leanName := "unknownLayer", args := [⟨"index", .nat, false⟩] }]
/-- `ContextUpdate` (`Context.lean:1005`), prefix `Lu`. -/
def contextUpdate : InductiveDesc where
  leanName := "ContextUpdate"; site := "Context.lean:1005"; ctorPrefix := "Lu"; subst := subst
  ctors := [{ leanName := "setTo", args := [⟨"context", ctxL, false⟩] },
            { leanName := "provide", args := [⟨"that", ctxL, false⟩] },
            { leanName := "provideService", args := [⟨"key", keyL, false⟩, ⟨"value", valL, false⟩] }]
def combineMode : InductiveDesc where
  leanName := "CombineMode"; site := "Layer.lean:69"; ctorPrefix := "Lc"; subst := subst
  ctors := [{ leanName := "provide" }, { leanName := "provideMerge" }]
def construction : InductiveDesc where
  leanName := "Construction"; site := "Layer.lean:76"; ctorPrefix := "Lk"; subst := subst
  ctors := [{ leanName := "succeedContext", args := [⟨"services", .lst (.nm "ServicePair"), false⟩] },
            { leanName := "failWith", args := [⟨"error", .nm "Err", false⟩] },
            { leanName := "acquire", args := [⟨"services", .lst (.nm "ServicePair"), false⟩, ⟨"release", .nat, false⟩] },
            { leanName := "fromService", args := [⟨"input", keyL, false⟩, ⟨"output", keyL, false⟩] }]
def layerDesc : InductiveDesc where
  leanName := "LayerDesc"; site := "Layer.lean:92"; ctorPrefix := "Ld"; subst := subst
  ctors := [{ leanName := "atom", args := [⟨"construction", .nm "Construction", false⟩] },
            { leanName := "memoized", args := [⟨"construction", .nm "Construction", false⟩] },
            { leanName := "childScope", args := [⟨"inner", lid, false⟩] },
            { leanName := "fresh", args := [⟨"inner", lid, false⟩] },
            { leanName := "provideWith", args := [⟨"self", lid, false⟩, ⟨"that", lid, false⟩, ⟨"mode", .nm "CombineMode", false⟩] },
            { leanName := "mergeAll", args := [⟨"layers", .lst lid, false⟩] }]
def finName : InductiveDesc where
  leanName := "FinName"; site := "Layer.lean:115"; ctorPrefix := "Lfin"; subst := subst
  ctors := [{ leanName := "closeChildScope", args := [⟨"scope", .nat, false⟩] },
            { leanName := "detachFromParent", args := [⟨"parent", .nat, false⟩, ⟨"key", .nat, false⟩] },
            { leanName := "closeChildOnFailure", args := [⟨"scope", .nat, false⟩] },
            { leanName := "memoEntry", args := [⟨"layer", lid, false⟩, ⟨"memoMap", mid, false⟩] },
            { leanName := "memoDone", args := [⟨"layer", lid, false⟩, ⟨"memoMap", mid, false⟩] },
            { leanName := "restoreContext", args := [⟨"prev", ctxL, false⟩] },
            { leanName := "scopedExit", args := [⟨"prev", ctxL, false⟩, ⟨"scope", .nat, false⟩] },
            { leanName := "closeScopeWith", args := [⟨"scope", .nat, false⟩] },
            { leanName := "release", args := [⟨"label", .nat, false⟩, ⟨"fails", .bool, false⟩] },
            { leanName := "releaseWith", args := [⟨"label", .nat, false⟩, ⟨"captured", ctxL, false⟩] },
            { leanName := "interruptFiber", args := [⟨"fiber", fid, false⟩, ⟨"skipSelf", .bool, false⟩] }]
def syncOp : InductiveDesc where
  leanName := "SyncOp"; site := "Layer.lean:144"; ctorPrefix := "Ls"; subst := subst
  ctors := [{ leanName := "scopeMake", args := [⟨"strategy", .nm "FinalizerStrategy", false⟩] },
            { leanName := "scopeFork", args := [⟨"parent", .nat, false⟩, ⟨"strategy", .nm "FinalizerStrategy", false⟩] },
            { leanName := "scopeAdd", args := [⟨"scope", .nat, false⟩, ⟨"finalizer", .nm "FinName", false⟩] },
            { leanName := "scopeRemove", args := [⟨"scope", .nat, false⟩, ⟨"key", .nat, false⟩] },
            { leanName := "memoFork", args := [⟨"parent", .opt mid, false⟩] },
            { leanName := "memoGet", args := [⟨"layer", lid, false⟩, ⟨"memoMap", mid, false⟩] },
            { leanName := "memoBuild", args := [⟨"layer", lid, false⟩, ⟨"memoMap", mid, false⟩] },
            { leanName := "memoComplete", args := [⟨"layer", lid, false⟩, ⟨"memoMap", mid, false⟩, ⟨"exit", exitL, false⟩] },
            { leanName := "memoRelease", args := [⟨"layer", lid, false⟩, ⟨"memoMap", mid, false⟩] },
            { leanName := "deferredAwaitCleanup", args := [⟨"cell", .nm "DeferredKey", false⟩, ⟨"waiter", fid, false⟩, ⟨"token", .nat, false⟩] }]
def progName : InductiveDesc where
  leanName := "ProgName"; site := "Layer.lean:174"; ctorPrefix := "Lp"; subst := subst
  ctors := [{ leanName := "value", args := [⟨"v", valL, false⟩] },
            { leanName := "failCause", args := [⟨"cause", causeL, false⟩] },
            { leanName := "getContext" },
            { leanName := "service", args := [⟨"key", keyL, false⟩] },
            { leanName := "setContextTo", args := [⟨"context", ctxL, false⟩, ⟨"body", progL, false⟩] },
            { leanName := "provideContext", args := [⟨"context", ctxL, false⟩, ⟨"body", progL, false⟩] },
            { leanName := "provideService", args := [⟨"key", keyL, false⟩, ⟨"value", valL, false⟩, ⟨"body", progL, false⟩] },
            { leanName := "scoped", args := [⟨"body", progL, false⟩] },
            { leanName := "acquireRelease", args := [⟨"acquire", progL, false⟩, ⟨"release", .nat, false⟩, ⟨"interruptible", .bool, false⟩] },
            { leanName := "acquireMasked", args := [⟨"acquire", progL, false⟩, ⟨"release", .nat, false⟩, ⟨"captured", ctxL, false⟩, ⟨"interruptible", .bool, false⟩] },
            { leanName := "addFinalizer", args := [⟨"label", .nat, false⟩] },
            { leanName := "seq", args := [⟨"first", progL, false⟩, ⟨"second", progL, false⟩] },
            { leanName := "never" },
            { leanName := "closeScope", args := [⟨"scope", .nat, false⟩, ⟨"exit", exitL, false⟩] },
            { leanName := "build", args := [⟨"layer", lid, false⟩] },
            { leanName := "buildWithScope", args := [⟨"layer", lid, false⟩, ⟨"scope", .nat, false⟩] },
            { leanName := "buildWithMemoMap", args := [⟨"layer", lid, false⟩, ⟨"memoMap", mid, false⟩, ⟨"scope", .nat, false⟩] },
            { leanName := "layerBuild", args := [⟨"layer", lid, false⟩, ⟨"memoMap", mid, false⟩, ⟨"scope", .nat, false⟩] },
            { leanName := "buildAdding", args := [⟨"layer", lid, false⟩, ⟨"memoMap", mid, false⟩, ⟨"scope", .nat, false⟩] },
            { leanName := "buildThenNever", args := [⟨"layer", lid, false⟩] },
            { leanName := "launch", args := [⟨"layer", lid, false⟩] },
            { leanName := "provideLayer", args := [⟨"layer", lid, false⟩, ⟨"isLocal", .bool, false⟩, ⟨"body", progL, false⟩] },
            { leanName := "scopedWithAlloc", args := [⟨"layer", lid, false⟩, ⟨"isLocal", .bool, false⟩, ⟨"body", progL, false⟩] },
            { leanName := "memoLookup", args := [⟨"layer", lid, false⟩, ⟨"memoMap", mid, false⟩, ⟨"scope", .nat, false⟩, ⟨"construction", .nm "Construction", false⟩] },
            { leanName := "finalizerOf", args := [⟨"fin", .nm "FinName", false⟩, ⟨"exit", exitL, false⟩] },
            { leanName := "memoReleaseOf", args := [⟨"layer", lid, false⟩, ⟨"memoMap", mid, false⟩, ⟨"exit", exitL, false⟩] },
            { leanName := "releaseOf", args := [⟨"label", .nat, false⟩] }]
def name : InductiveDesc where
  leanName := "Name"; site := "Layer.lean:233"; ctorPrefix := "Ln"; subst := subst
  ctors := [{ leanName := "restore", args := [⟨"exit", exitL, false⟩] },
            { leanName := "merge", args := [⟨"exit", exitL, false⟩] },
            { leanName := "seq", args := [⟨"next", progL, false⟩] },
            { leanName := "constant", args := [⟨"value", valL, false⟩] },
            { leanName := "registerAwait", args := [⟨"cell", .nm "DeferredKey", false⟩] },
            { leanName := "cancelAwait", args := [⟨"cell", .nm "DeferredKey", false⟩] },
            { leanName := "neverRegister" },
            { leanName := "abortController" },
            { leanName := "cancelPark" },
            { leanName := "cancelRace", args := [⟨"race", .nat, false⟩] },
            { leanName := "withWaiter", args := [⟨"base", .nm "Name", false⟩, ⟨"waiter", fid, false⟩, ⟨"token", .nat, false⟩] },
            { leanName := "reFail", args := [⟨"cause", causeL, false⟩] },
            { leanName := "finalizerName", args := [⟨"fin", .nm "FinName", false⟩] },
            { leanName := "closeSeq", args := [⟨"remaining", .lst (.nm "FinName"), false⟩, ⟨"exit", exitL, false⟩, ⟨"captured", .lst (.nm "ReasonV"), false⟩] },
            { leanName := "closePar", args := [⟨"remaining", .lst (.nm "FinName"), false⟩, ⟨"exit", exitL, false⟩, ⟨"forked", .lst fid, false⟩, ⟨"closerInterruptible", .bool, false⟩] },
            { leanName := "mergeAwaitedExits" },
            { leanName := "afterScopeAdd", args := [⟨"fin", .nm "FinName", false⟩] },
            { leanName := "updateThen", args := [⟨"update", .nm "ContextUpdate", false⟩, ⟨"body", progL, false⟩] },
            { leanName := "bodyThen", args := [⟨"body", progL, false⟩, ⟨"prev", ctxL, false⟩] },
            { leanName := "scopedThen", args := [⟨"body", progL, false⟩] },
            { leanName := "scopedInstall", args := [⟨"body", progL, false⟩, ⟨"prev", ctxL, false⟩] },
            { leanName := "scopedBody", args := [⟨"body", progL, false⟩, ⟨"prev", ctxL, false⟩, ⟨"scope", .nat, false⟩] },
            { leanName := "thenClose", args := [⟨"scope", .nat, false⟩, ⟨"exit", exitL, false⟩] },
            { leanName := "serviceLookup", args := [⟨"key", keyL, false⟩] },
            { leanName := "bindService", args := [⟨"output", keyL, false⟩] },
            { leanName := "acquireWith", args := [⟨"acquire", progL, false⟩, ⟨"release", .nat, false⟩, ⟨"interruptible", .bool, false⟩] },
            { leanName := "acquireInScope", args := [⟨"acquire", progL, false⟩, ⟨"release", .nat, false⟩, ⟨"captured", ctxL, false⟩, ⟨"interruptible", .bool, false⟩] },
            { leanName := "registerRelease", args := [⟨"scope", .nat, false⟩, ⟨"release", .nat, false⟩, ⟨"captured", ctxL, false⟩] },
            { leanName := "addFinalizerOn", args := [⟨"label", .nat, false⟩] },
            { leanName := "addFinalizerCaptured", args := [⟨"scope", .nat, false⟩, ⟨"label", .nat, false⟩] },
            { leanName := "buildFromContext", args := [⟨"layer", lid, false⟩] },
            { leanName := "buildWithScopeFromContext", args := [⟨"layer", lid, false⟩, ⟨"scope", .nat, false⟩] },
            { leanName := "withMemoMapThen", args := [⟨"layer", lid, false⟩, ⟨"scope", .opt .nat, false⟩] },
            { leanName := "addCurrentMemoMap", args := [⟨"memoMap", mid, false⟩] },
            { leanName := "memoize", args := [⟨"layer", lid, false⟩, ⟨"memoMap", mid, false⟩, ⟨"scope", .nat, false⟩, ⟨"construction", .nm "Construction", false⟩] },
            { leanName := "awaitPromise", args := [⟨"cell", .nm "DeferredKey", false⟩] },
            { leanName := "buildIntoLayerScope", args := [⟨"layer", lid, false⟩, ⟨"memoMap", mid, false⟩, ⟨"scope", .nat, false⟩, ⟨"construction", .nm "Construction", false⟩] },
            { leanName := "thenBuildInto", args := [⟨"layer", lid, false⟩, ⟨"memoMap", mid, false⟩, ⟨"construction", .nm "Construction", false⟩, ⟨"layerScope", .nat, false⟩] },
            { leanName := "closeIfLast", args := [⟨"exit", exitL, false⟩] },
            { leanName := "fromBuildThen", args := [⟨"desc", .nm "LayerDesc", false⟩, ⟨"self", lid, false⟩, ⟨"memoMap", mid, false⟩] },
            { leanName := "freshThen", args := [⟨"inner", lid, false⟩, ⟨"scope", .nat, false⟩] },
            { leanName := "provideThen", args := [⟨"self", lid, false⟩, ⟨"memoMap", mid, false⟩, ⟨"scope", .nat, false⟩, ⟨"mode", .nm "CombineMode", false⟩] },
            { leanName := "combineWith", args := [⟨"mode", .nm "CombineMode", false⟩, ⟨"thatContext", ctxL, false⟩] },
            { leanName := "mergeChildren", args := [⟨"layers", .lst lid, false⟩, ⟨"memoMap", mid, false⟩] },
            { leanName := "mergeForkOne", args := [⟨"layer", lid, false⟩, ⟨"rest", .lst lid, false⟩, ⟨"memoMap", mid, false⟩, ⟨"parent", .nat, false⟩, ⟨"forked", .lst fid, false⟩] },
            { leanName := "mergeForkNext", args := [⟨"rest", .lst lid, false⟩, ⟨"memoMap", mid, false⟩, ⟨"parent", .nat, false⟩, ⟨"forked", .lst fid, false⟩] },
            { leanName := "mergeContexts" },
            { leanName := "provideLayerWith", args := [⟨"layer", lid, false⟩, ⟨"isLocal", .bool, false⟩, ⟨"body", progL, false⟩] },
            { leanName := "provideLayerBody", args := [⟨"body", progL, false⟩] }]
def actionName : InductiveDesc where
  leanName := "ActionName"; site := "Layer.lean:341"; ctorPrefix := "La"; subst := subst
  ctors := [{ leanName := "fork", args := [⟨"program", progL, false⟩, ⟨"options", .nm "Supervision.ForkOptions", false⟩] },
            { leanName := "forkScoped", args := [⟨"program", progL, false⟩, ⟨"options", .nm "Supervision.ForkOptions", false⟩, ⟨"key", .nat, false⟩] },
            { leanName := "interrupt", args := [⟨"target", fid, false⟩] },
            { leanName := "interruptScoped", args := [⟨"target", fid, false⟩] },
            { leanName := "awaitAll", args := [⟨"targets", .lst fid, false⟩] },
            { leanName := "awaitAllFailFast", args := [⟨"targets", .lst fid, false⟩] },
            { leanName := "setContext", args := [⟨"context", ctxL, false⟩] },
            { leanName := "getContext" },
            { leanName := "getId" },
            { leanName := "closeScope", args := [⟨"scope", .nat, false⟩, ⟨"exit", exitL, false⟩] },
            { leanName := "setInterruptible", args := [⟨"body", progL, false⟩, ⟨"flag", .bool, false⟩] },
            { leanName := "refuse", args := [⟨"cause", causeL, false⟩] },
            { leanName := "dropObservers", args := [⟨"token", .nat, false⟩] }]
def thunk : InductiveDesc where
  leanName := "Thunk"; site := "Layer.lean:361"; ctorPrefix := "Lt"; subst := subst
  ctors := [{ leanName := "act", args := [⟨"action", .nm "ActionName", false⟩] },
            { leanName := "op", args := [⟨"operation", .nm "SyncOp", false⟩] },
            { leanName := "body", args := [⟨"program", progL, false⟩] }]
/-- `ScopeState` (`Scope.lean:71`) at Layer's `FinName`, prefix `Lss`. -/
def scopeState : InductiveDesc where
  leanName := "ScopeState"; site := "Scope.lean:71 at Layer.lean:437"; ctorPrefix := "Lss"; subst := subst
  ctors := [{ leanName := "empty" }, { leanName := "openEmpty" },
            { leanName := "openInline", args := [⟨"key", .nat, false⟩, ⟨"finalizer", .nm "FinName", false⟩] },
            { leanName := "openMap", args := [⟨"entries", .lst (.nm "ScopeEntryPair"), false⟩] },
            { leanName := "closed", args := [⟨"exit", exitL, false⟩] }]
def scope : StructDesc where
  leanName := "Scope"; site := "Scope.lean:86 at Layer.lean:437"; subst := subst
  fields := [{ leanName := "strategy", leanTy := .nm "FinalizerStrategy" },
             { leanName := "state", leanTy := .nm "ScopeState", isMutable := true }]
def scopeEntry : StructDesc where
  leanName := "ScopeEntry"; site := "Layer.lean:439"; subst := subst
  fields := [{ leanName := "key", leanTy := .nat }, { leanName := "scope", leanTy := .nm "ScopeV", isMutable := true }]
def scopeStore : StructDesc where
  leanName := "ScopeStore"; site := "Layer.lean:444"; subst := subst
  fields := [{ leanName := "entries", leanTy := .lst (.nm "ScopeEntry"), isMutable := true }]
def memoEntry : StructDesc where
  leanName := "MemoEntry"; site := "Layer.lean:487"; subst := subst
  fields := [{ leanName := "observers", leanTy := .nat, isMutable := true },
             { leanName := "effect", leanTy := .nm "Program", isMutable := true,
               comment := Option.some "Lean: `Program`; a thunk here (DIVERGENCE 1)" },
             { leanName := "layerScope", leanTy := .nat },
             { leanName := "deferred", leanTy := .nm "DeferredKey" },
             { leanName := "finalizer", leanTy := .nm "FinName" }]
def memoMap : StructDesc where
  leanName := "MemoMap"; site := "Layer.lean:501"; subst := subst
  fields := [{ leanName := "id", leanTy := mid },
             { leanName := "parent", leanTy := .opt mid },
             { leanName := "entries", leanTy := .lst (.nm "MemoPair"), isMutable := true }]
def st : StructDesc where
  leanName := "St"; site := "Layer.lean:624"; subst := subst
  fields := [{ leanName := "memo", leanTy := .nm "MemoWorld", isMutable := true },
             { leanName := "scopes", leanTy := .nm "ScopeStore" },
             { leanName := "deferreds", leanTy := .nm "DeferredStore" },
             { leanName := "nextName", leanTy := .nat, isMutable := true }]

def tupleAliases : List Decl :=
  [.rawD "type service_pair = service_key * value",
   .rawD "type scope_entry_pair = int * fin_name",
   .rawD "type memo_pair = layer_id * memo_entry"]

def structs : List StructDesc := [layerId, memoMapId, scope, scopeEntry, scopeStore, memoEntry, memoMap, st]
def inductives : List InductiveDesc :=
  [combineMode, construction, layerDesc, finName, syncOp, progName, name, actionName, thunk, scopeState]

def generated : List Decl :=
  [.comment ("Generated by OCaml5.Ml (`Render.lean`, seat W1). Do not edit; edit the"
      ++ " descriptions (`Ml.Deep.Layer`, seat F2).\n   One declaration per `src/Effect4/Machine/Layer.lean`"
      ++ " carrier (and the four `Context.lean`/`Key.lean` carriers it names), same field and"
      ++ " constructor order."),
   layerId.header, renameDecl "layer_id" layerId.decl,
   memoMapId.header, renameDecl "memo_map_id" memoMapId.decl,
   .comment "`ServiceKey`, `Defect` and `ContextUpdate` are `deep_context.ml`'s (`Context.lean`, which `Layer.lean` imports).",
   .rawD "type service_pair = Deep_context.service_key * value",
   combineMode.header, renameDecl "combine_mode" combineMode.decl,
   construction.header, renameDecl "construction" construction.decl,
   layerDesc.header, renameDecl "layer_desc" layerDesc.decl,
   finName.header, renameDecl "fin_name" finName.decl,
   .rawD "type scope_entry_pair = int * fin_name",
   scopeState.header, renameDecl "scope_state" scopeState.decl,
   scope.header, renameDecl "scope" scope.decl,
   scopeEntry.header, renameDecl "scope_entry" scopeEntry.decl,
   scopeStore.header, renameDecl "scope_store" scopeStore.decl,
   syncOp.header, renameDecl "sync_op" syncOp.decl,
   .comment ("`ProgName`, `Name`, `ActionName` and `Thunk` are one mutually recursive group in"
      ++ " OCaml; order inside the group is the Lean order."),
   progName.header, renameDecl "prog_name" progName.decl,
   name.header, renameDecl "name" name.decl,
   actionName.header, renameDecl "action_name" actionName.decl,
   thunk.header, renameDecl "thunk" thunk.decl,
   memoEntry.header, renameDecl "memo_entry" memoEntry.decl,
   .rawD "type memo_pair = layer_id * memo_entry",
   memoMap.header, renameDecl "memo_map" memoMap.decl,
   st.header, renameDecl "st" st.decl]


/-- The descriptions under the projection guard, in the order the report prints. -/
def all : List TypeDesc := [.struct layerId, .struct memoMapId, .struct serviceKey, .induct defect, .induct contextUpdate, .induct combineMode, .induct construction, .induct layerDesc, .induct finName, .induct syncOp, .induct progName, .induct name, .induct actionName, .induct thunk, .induct scopeState, .struct scope, .struct scopeEntry, .struct scopeStore, .struct memoEntry, .struct memoMap, .struct st]

/-- `deep_layer.ml` as a part of the avatar. -/
def part : Part :=
  { name := "layer", file := "deep_layer.ml", guarded := all, derived := Derived.Layer.all,
    generated := generated }

end Layer

end OCaml5.Avatar
