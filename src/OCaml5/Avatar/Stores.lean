import OCaml5.Ml.Reflect
import OCaml5.Avatar.Part
import OCaml5.Avatar.Derived.Stores

/-!
# OCaml5.Avatar.Stores

**What it is.** The descriptions behind the generated block of `ocaml/avatar/deep_stores.ml`, the
port of `src/Effect4/Machine/Stores.lean` (seat W1): the substitution table, every carrier of the
three stores and the `Scope` carriers they need, and `generated`, the block `render-deep.sh stores`
prints.

**Depends on.** `OCaml5.Ml.Reflect`, `OCaml5.Avatar.Part`, `OCaml5.Avatar.Derived.Stores`.

**Properties.**
* **Field and constructor order is the Lean order**, arity for arity — *tested* (`Check`).
* **The block is byte-identical to the one the avatar file carries** — *tested*
  (`ocaml/avatar/render-deep.sh`), executed.
-/

namespace OCaml5.Avatar

open OCaml5.Ml

namespace Stores

/-- The substitution table for `deep_stores.ml`. Ten entries are decisions, not derivations, and
each is a row of the report's divergence table:

* `Val` is **substituted** by the avatar's wire alphabet `value` (`deep_fibers.ml:64`). The two
  alphabets are different — `Val.fiber`/`.cell`/`.promise`/`.scopeHandle` are one `Vhandle`
  under the wire's first-seen handle counter, and `Val.exitNil`/`.exitCons` are one `Vlist` —
  so the map is in the report and not here;
* `Prim ν σ β ε δ ι α` is `program`, i.e. `unit -> value`: DIVERGENCE 1, a program is OCaml
  control and not a tree;
* `Exit β ε δ ι α` and `Exit Unit ε δ ι α` are both `exitv` (`deep_fibers.ml:96`), whose value
  half is the wire alphabet by the `Val` row above;
* `Cause`/`Reason`/`ReasonAnnotations` are the avatar's (`:76-77`);
* `χ` is `unit`: the avatar carries no context service (A0 §18);
* `FiberId` is `int`. -/
def subst : Subst :=
  [("FiberId", Ty.int),
   ("RefKey", Ty.named "ref_key"),
   ("DeferredKey", Ty.named "deferred_key"),
   ("Err", Ty.named "err"),
   ("Defect", Ty.named "defect"),
   ("Ann", Ty.unit),
   ("FnName", Ty.named "fn_name"),
   ("FinName", Ty.named "fin_name"),
   ("Ctx", Ty.named "ctx"),
   ("Val", Ty.named "value"),
   ("Completion", Ty.named "completion"),
   ("SyncOp", Ty.named "sync_op"),
   ("RaceName", Ty.named "race_name"),
   ("ProgName", Ty.named "prog_name"),
   ("Name", Ty.named "name"),
   ("ActionName", Ty.named "action_name"),
   ("Thunk", Ty.named "thunk"),
   ("Program", Ty.named "program"),
   ("Prim", Ty.named "program"),
   ("RefHeap", Ty.list (Ty.named "value")),
   ("DeferredCell", Ty.named "deferred_cell"),
   ("DeferredStore", Ty.named "deferred_store"),
   ("ScopeEntry", Ty.named "scope_entry"),
   ("ScopeStore", Ty.named "scope_store"),
   ("ScopeV", Ty.named "scope"),
   ("Scope", Ty.named "scope"),
   ("ScopeState", Ty.named "scope_state"),
   ("FinalizerStrategy", Ty.named "finalizer_strategy"),
   ("Exit", Ty.named "exitv"),
   ("ExitV", Ty.named "exitv"),
   ("VoidExitV", Ty.named "exitv"),
   ("Cause", Ty.named "cause"),
   ("CauseV", Ty.named "cause"),
   ("Reason", Ty.named "reason"),
   ("ReasonAnnotations", Ty.list Ty.string),
   ("ParkKind", Ty.named "park_kind"),
   ("Supervision.ObserverMode", Ty.named "observer_mode"),
   ("Supervision.ForkOptions", Ty.named "fork_options"),
   ("Supervision.ScopeMode", Ty.int),
   ("χ", Ty.unit)]

private def fid : LTy := .nm "FiberId"
private def exitL : LTy := .nm "ExitV"
private def voidExitL : LTy := .nm "VoidExitV"
private def causeL : LTy := .nm "CauseV"
private def valL : LTy := .nm "Val"

/-- `RefKey` (`Stores.lean:56`). -/
def refKey : StructDesc where
  leanName := "RefKey"; site := "Stores.lean:56"; subst := subst
  fields := [{ leanName := "index", leanTy := .nat }]

/-- `DeferredKey` (`Stores.lean:62`). -/
def deferredKey : StructDesc where
  leanName := "DeferredKey"; site := "Stores.lean:62"; subst := subst
  fields := [{ leanName := "index", leanTy := .nat }]

/-- `Err` (`Stores.lean:73`), prefix `E`. -/
def err : InductiveDesc where
  leanName := "Err"; site := "Stores.lean:73"; ctorPrefix := "E"; subst := subst
  ctors := [{ leanName := "boom" }, { leanName := "tag", args := [⟨"code", .nat, false⟩] }]

/-- `Defect` (`Stores.lean:81`), prefix `X`. Five constructors since finding S1-1 (2026-09-04):
`missingService` is `Context.get` on a missing service (`forkScoped` with no ambient `Scope`,
`internal/effect.ts:5400-5406`) and `user n` is `Effect.die(d)` with a numeric payload. Seat F2. -/
def defect : InductiveDesc where
  leanName := "Defect"; site := "Stores.lean:81"; ctorPrefix := "X"; subst := subst
  ctors := [{ leanName := "notImplemented" }, { leanName := "asyncFiber" },
            { leanName := "badName" }, { leanName := "missingService" },
            { leanName := "user", args := [⟨"payload", .nat, false⟩] }]

/-- `FnName` (`Stores.lean:94`), prefix `Fn`. -/
def fnName : InductiveDesc where
  leanName := "FnName"; site := "Stores.lean:94"; ctorPrefix := "Fn"; subst := subst
  ctors := [{ leanName := "incr" }, { leanName := "double" }, { leanName := "zeroWhenPositive" },
            { leanName := "noChange" }, { leanName := "takeAndBump" }]

/-- `FinName` (`Stores.lean:110`), prefix `Fin`. -/
def finName : InductiveDesc where
  leanName := "FinName"; site := "Stores.lean:110"; ctorPrefix := "Fin"; subst := subst
  ctors :=
    [{ leanName := "interruptFiber", args := [⟨"fiber", fid, false⟩, ⟨"skipSelf", .bool, false⟩] },
     { leanName := "closeChildScope", args := [⟨"scope", .nat, false⟩] },
     { leanName := "detachFromParent", args := [⟨"parent", .nat, false⟩, ⟨"key", .nat, false⟩] },
     { leanName := "release", args := [⟨"label", .nat, false⟩, ⟨"fails", .bool, false⟩] },
     -- `57924eb` (seat F2): `awaitAllChildren`'s finalizer (`:5319-5333`, R2-7)
     { leanName := "awaitNewChildren", args := [⟨"snapshot", .lst fid, false⟩] },
     { leanName := "parkThen", args := [⟨"slot", .nat, false⟩] }]

/-- `Ctx` (`Stores.lean:130`). -/
def ctx : StructDesc where
  leanName := "Ctx"; site := "Stores.lean:130"; subst := subst
  fields :=
    [{ leanName := "ambientScope", leanTy := .opt .nat },
     { leanName := "maxOpsBeforeYield", leanTy := .nat },
     { leanName := "preventYield", leanTy := .bool }]

/-- `Completion` (`Stores.lean:184`), prefix `Co`. -/
def completion : InductiveDesc where
  leanName := "Completion"; site := "Stores.lean:184"; ctorPrefix := "Co"; subst := subst
  ctors := [{ leanName := "ofExit", args := [⟨"exit", exitL, false⟩] },
            { leanName := "ofRefGet", args := [⟨"cell", .nm "RefKey", false⟩] }]

/-- `SyncOp` (`Stores.lean:193`), 23 constructors, prefix `S`. -/
def syncOp : InductiveDesc where
  leanName := "SyncOp"; site := "Stores.lean:193"; ctorPrefix := "S"; subst := subst
  ctors :=
    [{ leanName := "refMake", args := [⟨"initial", valL, false⟩] },
     { leanName := "refGet", args := [⟨"cell", .nm "RefKey", false⟩] },
     { leanName := "refSet", args := [⟨"cell", .nm "RefKey", false⟩, ⟨"value", valL, false⟩] },
     { leanName := "refGetAndSet",
       args := [⟨"cell", .nm "RefKey", false⟩, ⟨"value", valL, false⟩] },
     { leanName := "refSetAndGet",
       args := [⟨"cell", .nm "RefKey", false⟩, ⟨"value", valL, false⟩] },
     { leanName := "refUpdate",
       args := [⟨"cell", .nm "RefKey", false⟩, ⟨"f", .nm "FnName", false⟩] },
     { leanName := "refGetAndUpdate",
       args := [⟨"cell", .nm "RefKey", false⟩, ⟨"f", .nm "FnName", false⟩] },
     { leanName := "refUpdateAndGet",
       args := [⟨"cell", .nm "RefKey", false⟩, ⟨"f", .nm "FnName", false⟩] },
     { leanName := "refUpdateSome",
       args := [⟨"cell", .nm "RefKey", false⟩, ⟨"pf", .nm "FnName", false⟩] },
     { leanName := "refGetAndUpdateSome",
       args := [⟨"cell", .nm "RefKey", false⟩, ⟨"pf", .nm "FnName", false⟩] },
     { leanName := "refUpdateSomeAndGet",
       args := [⟨"cell", .nm "RefKey", false⟩, ⟨"pf", .nm "FnName", false⟩] },
     { leanName := "refModify",
       args := [⟨"cell", .nm "RefKey", false⟩, ⟨"f", .nm "FnName", false⟩] },
     { leanName := "refModifySome",
       args := [⟨"cell", .nm "RefKey", false⟩, ⟨"pf", .nm "FnName", false⟩] },
     { leanName := "deferredMake" },
     { leanName := "deferredIsDone", args := [⟨"cell", .nm "DeferredKey", false⟩] },
     { leanName := "deferredPoll", args := [⟨"cell", .nm "DeferredKey", false⟩] },
     { leanName := "deferredCompleteWith",
       args := [⟨"cell", .nm "DeferredKey", false⟩, ⟨"completion", .nm "Completion", false⟩] },
     { leanName := "deferredInterruptWith",
       args := [⟨"cell", .nm "DeferredKey", false⟩, ⟨"interruptor", fid, false⟩] },
     { leanName := "deferredAwaitCleanup",
       args := [⟨"cell", .nm "DeferredKey", false⟩, ⟨"waiter", fid, false⟩,
                ⟨"token", .nat, false⟩] },
     { leanName := "scopeMake", args := [⟨"strategy", .nm "FinalizerStrategy", false⟩] },
     { leanName := "scopeAdd",
       args := [⟨"scope", .nat, false⟩, ⟨"key", .nat, false⟩,
                ⟨"finalizer", .nm "FinName", false⟩] },
     { leanName := "scopeRemove", args := [⟨"scope", .nat, false⟩, ⟨"key", .nat, false⟩] },
     { leanName := "scopeIsClosed", args := [⟨"scope", .nat, false⟩] }]

/-- `RaceName` (`Stores.lean:248`), prefix `Rn`; six since `2f77f7d` (`parkOnly`,
`parkThenSuccess`: R2-12/R2-13's witnesses). Seat F2. -/
def raceName : InductiveDesc where
  leanName := "RaceName"; site := "Stores.lean:248"; ctorPrefix := "Rn"; subst := subst
  ctors := [{ leanName := "empty" }, { leanName := "successThenSecond" },
            { leanName := "failThenSuccess" }, { leanName := "failThenFail" },
            { leanName := "parkOnly" }, { leanName := "parkThenSuccess" }]

/-- `ProgName` (`Stores.lean:265`), 22 constructors, prefix `P`. -/
def progName : InductiveDesc where
  leanName := "ProgName"; site := "Stores.lean:265"; ctorPrefix := "P"; subst := subst
  ctors :=
    [{ leanName := "value", args := [⟨"v", valL, false⟩] },
     { leanName := "failCause", args := [⟨"cause", causeL, false⟩] },
     { leanName := "syncOp", args := [⟨"op", .nm "SyncOp", false⟩] },
     { leanName := "yieldNow", args := [⟨"priority", .nat, false⟩] },
     { leanName := "park", args := [⟨"slot", .nat, false⟩] },
     { leanName := "awaitDeferred", args := [⟨"cell", .nm "DeferredKey", false⟩] },
     { leanName := "intoDeferred",
       args := [⟨"body", .nm "ProgName", false⟩, ⟨"cell", .nm "DeferredKey", false⟩] },
     { leanName := "intoBody",
       args := [⟨"body", .nm "ProgName", false⟩, ⟨"cell", .nm "DeferredKey", false⟩] },
     { leanName := "maskedPark", args := [⟨"slot", .nat, false⟩] },
     { leanName := "awaitFibers", args := [⟨"targets", .lst fid, false⟩] },
     { leanName := "finalizerOf",
       args := [⟨"fin", .nm "FinName", false⟩, ⟨"exit", exitL, false⟩] },
     { leanName := "interruptDeferred", args := [⟨"cell", .nm "DeferredKey", false⟩] },
     { leanName := "onExitOf",
       args := [⟨"body", .nm "ProgName", false⟩, ⟨"fin", .nm "FinName", false⟩,
                ⟨"finalizerInterruptible", .bool, false⟩] },
     { leanName := "seqOf",
       args := [⟨"first", .nm "ProgName", false⟩, ⟨"second", .nm "ProgName", false⟩] },
     { leanName := "forkThen",
       args := [⟨"child", .nm "ProgName", false⟩,
                ⟨"options", .nm "Supervision.ForkOptions", false⟩,
                ⟨"mode", .nm "Supervision.ObserverMode", false⟩] },
     { leanName := "forkOnly",
       args := [⟨"child", .nm "ProgName", false⟩,
                ⟨"options", .nm "Supervision.ForkOptions", false⟩] },
     { leanName := "forkInScope",
       args := [⟨"child", .nm "ProgName", false⟩,
                ⟨"options", .nm "Supervision.ForkOptions", false⟩,
                ⟨"scope", .nat, false⟩, ⟨"key", .nat, false⟩] },
     { leanName := "runInScope",
       args := [⟨"target", fid, false⟩, ⟨"scope", .nat, false⟩, ⟨"key", .nat, false⟩] },
     { leanName := "forkScopedOf",
       args := [⟨"child", .nm "ProgName", false⟩,
                ⟨"options", .nm "Supervision.ForkOptions", false⟩, ⟨"key", .nat, false⟩] },
     { leanName := "raceOf", args := [⟨"race", .nm "RaceName", false⟩] },
     { leanName := "closeScopeOf", args := [⟨"scope", .nat, false⟩, ⟨"exit", exitL, false⟩] },
     { leanName := "awaitAllNew", args := [⟨"body", .nm "ProgName", false⟩] },
     -- `2f77f7d` (seat F2): the settle's cleanup half and a join on an existing handle
     { leanName := "interruptFibers", args := [⟨"targets", .lst fid, false⟩] },
     { leanName := "joinFiber",
       args := [⟨"target", fid, false⟩, ⟨"mode", .nm "Supervision.ObserverMode", false⟩] }]

/-- `Name` (`Stores.lean:321`), 20 constructors, prefix `N`. -/
def name : InductiveDesc where
  leanName := "Name"; site := "Stores.lean:321"; ctorPrefix := "N"; subst := subst
  ctors :=
    [{ leanName := "restore", args := [⟨"exit", exitL, false⟩] },
     { leanName := "merge", args := [⟨"exit", exitL, false⟩] },
     { leanName := "seq", args := [⟨"next", .nm "ProgName", false⟩] },
     { leanName := "joinOn", args := [⟨"mode", .nm "Supervision.ObserverMode", false⟩] },
     { leanName := "interruptWith", args := [⟨"cell", .nm "DeferredKey", false⟩] },
     { leanName := "doneInto", args := [⟨"cell", .nm "DeferredKey", false⟩] },
     { leanName := "constant", args := [⟨"value", valL, false⟩] },
     { leanName := "exitOfValue" },
     -- `Name.awaitNew` retired in `57924eb` (R2-7): the await is `FinName.awaitNewChildren`
     { leanName := "snapshotThen", args := [⟨"body", .nm "ProgName", false⟩] },
     { leanName := "registerAwait", args := [⟨"cell", .nm "DeferredKey", false⟩] },
     { leanName := "cancelAwait", args := [⟨"cell", .nm "DeferredKey", false⟩] },
     { leanName := "externalRegister", args := [⟨"slot", .nat, false⟩] },
     { leanName := "abortController" },
     -- `2f77f7d` (seat F2): `RunInterp.parkCancelName` and `raceCancelName` (R2-3, R2-13)
     { leanName := "cancelPark" },
     { leanName := "cancelRace", args := [⟨"race", .nat, false⟩] },
     { leanName := "withWaiter",
       args := [⟨"base", .nm "Name", false⟩, ⟨"waiter", fid, false⟩, ⟨"token", .nat, false⟩] },
     { leanName := "reFail", args := [⟨"cause", causeL, false⟩] },
     { leanName := "finalizerName", args := [⟨"fin", .nm "FinName", false⟩] },
     { leanName := "closeSeq",
       args := [⟨"remaining", .lst (.nm "FinName"), false⟩, ⟨"exit", exitL, false⟩,
                ⟨"captured", .lst (.nm "Reason"), false⟩] },
     { leanName := "closePar",
       args := [⟨"remaining", .lst (.nm "FinName"), false⟩, ⟨"exit", exitL, false⟩,
                ⟨"forked", .lst fid, false⟩, ⟨"closerInterruptible", .bool, false⟩] },
     { leanName := "mergeAwaitedExits" }]

/-- `ActionName` (`Stores.lean:377`), 17 constructors, prefix `A`. Arm for arm with
`Fibers.lean`'s `WithFiberAction` (`Ml.Avatar.withFiberAction`), except that every `Prim`
argument is a `ProgName` here — which is the whole point of the name alphabet. -/
def actionName : InductiveDesc where
  leanName := "ActionName"; site := "Stores.lean:377"; ctorPrefix := "A"; subst := subst
  ctors :=
    [{ leanName := "fork",
       args := [⟨"program", .nm "ProgName", false⟩,
                ⟨"options", .nm "Supervision.ForkOptions", false⟩] },
     { leanName := "forkIn",
       args := [⟨"program", .nm "ProgName", false⟩,
                ⟨"options", .nm "Supervision.ForkOptions", false⟩,
                ⟨"scope", .nat, false⟩, ⟨"key", .nat, false⟩] },
     { leanName := "forkScoped",
       args := [⟨"program", .nm "ProgName", false⟩,
                ⟨"options", .nm "Supervision.ForkOptions", false⟩, ⟨"key", .nat, false⟩] },
     { leanName := "runIn",
       args := [⟨"target", fid, false⟩, ⟨"scope", .nat, false⟩, ⟨"key", .nat, false⟩] },
     { leanName := "interrupt", args := [⟨"target", fid, false⟩] },
     { leanName := "interruptScoped", args := [⟨"target", fid, false⟩] },
     { leanName := "interruptAll",
       args := [⟨"targets", .lst fid, false⟩, ⟨"interruptor", .opt fid, false⟩] },
     { leanName := "awaitAll", args := [⟨"targets", .lst fid, false⟩] },
     { leanName := "snapshotChildren" },
     { leanName := "awaitNewChildren", args := [⟨"snapshot", .lst fid, false⟩] },
     { leanName := "raceAll", args := [⟨"race", .nm "RaceName", false⟩] },
     { leanName := "setContext", args := [⟨"context", .nm "Ctx", false⟩] },
     { leanName := "getContext" },
     { leanName := "getId" },
     { leanName := "closeScope", args := [⟨"scope", .nat, false⟩, ⟨"exit", exitL, false⟩] },
     { leanName := "setInterruptible",
       args := [⟨"body", .nm "ProgName", false⟩, ⟨"flag", .bool, false⟩] },
     { leanName := "refuse", args := [⟨"cause", causeL, false⟩] },
     -- `2f77f7d` (seat F2): the two park cleanups (R2-3, R2-13)
     { leanName := "dropObservers", args := [⟨"token", .nat, false⟩] },
     { leanName := "cancelRace", args := [⟨"race", .nat, false⟩] }]

/-- `Thunk` (`Stores.lean:403`), prefix `T`. -/
def thunk : InductiveDesc where
  leanName := "Thunk"; site := "Stores.lean:403"; ctorPrefix := "T"; subst := subst
  ctors :=
    [{ leanName := "park", args := [⟨"kind", .nm "ParkKind", false⟩] },
     { leanName := "act", args := [⟨"action", .nm "ActionName", false⟩] },
     { leanName := "op", args := [⟨"operation", .nm "SyncOp", false⟩] },
     { leanName := "body", args := [⟨"program", .nm "ProgName", false⟩] }]

/-! ### `src/Effect4/Machine/Scope.lean`

`ScopeStore` is keyed `Effect4.Scope`s, "reused unchanged" (`Stores.lean:850`). There is no
OCaml module for `Effect4/Runtime` in this pass — the seat's frame is one module per
`Effect4/Machine` module — so the two carriers the store needs are described here and rendered into
`deep_stores.ml` under their own banner, with their Lean site named. -/

/-- `FinalizerStrategy` (`Scope.lean:39`), prefix `Fs`. -/
def finalizerStrategy : InductiveDesc where
  leanName := "FinalizerStrategy"; site := "Scope.lean:39"; ctorPrefix := "Fs"; subst := subst
  ctors := [{ leanName := "sequential" }, { leanName := "parallel" }]

/-- `ScopeState` (`Scope.lean:71`), five states, prefix `Ss`. `κ` is `Nat` and `φ` is `FinName`
at this instantiation (`ScopeV`, `Stores.lean:850`). -/
def scopeState : InductiveDesc where
  leanName := "ScopeState"; site := "Scope.lean:71"; ctorPrefix := "Ss"; subst := subst
  ctors :=
    [{ leanName := "empty" },
     { leanName := "openEmpty" },
     { leanName := "openInline",
       args := [⟨"key", .nat, false⟩, ⟨"finalizer", .nm "FinName", false⟩] },
     { leanName := "openMap",
       args := [⟨"entries", .lst (.nm "ScopeEntryPair"), false⟩] },
     { leanName := "closed", args := [⟨"exit", exitL, false⟩] }]

/-- `Scope` (`Scope.lean:86`). -/
def scope : StructDesc where
  leanName := "Scope"; site := "Scope.lean:86"; subst := subst
  fields :=
    [{ leanName := "strategy", leanTy := .nm "FinalizerStrategy" },
     { leanName := "state", leanTy := .nm "ScopeState", isMutable := true }]

/-! ### The three stores -/

/-- `DeferredCell` (`Stores.lean:680`). Both fields are `mutable`: DIVERGENCE 3, the pure
updates of `DeferredStore.register`/`cancel`/`complete` are in-place writes here. The completion
is Lean's `Option Program` — "the completion is a *primitive*, so `done exit = completeWith
(Prim.ofExit exit)` is definitional" (`:678-679`) — and `Program` is the avatar's `program`
(`unit -> value`, DIVERGENCE 1): the store holds the closure `completionPrim` builds, and the
awaiting arm runs it for its exit (`deep_stores.ml`, `arm_def_await`). Until the drift re-diff of
2026-09-04 the slot was described as `Option Completion`, which is what the avatar stored. The
waiters are Lean's `List (FiberId × Nat)`; the product is the `waiter_pair` alias, a
substitution local to this description because `LTy` has no product head of its own. -/
def deferredCell : StructDesc where
  leanName := "DeferredCell"; site := "Stores.lean:680"
  subst := ("Prod", Ty.named "waiter_pair") :: subst
  fields :=
    [{ leanName := "completion", leanTy := .opt (.nm "Program"), isMutable := true },
     { leanName := "waiters", leanTy := .lst (.app "Prod" [fid, .nat]), isMutable := true }]

/-- `DeferredStore` (`Stores.lean:663`). -/
def deferredStore : StructDesc where
  leanName := "DeferredStore"; site := "Stores.lean:663"; subst := subst
  fields :=
    [{ leanName := "cells", leanTy := .lst (.nm "DeferredCell"), isMutable := true },
     { leanName := "due", leanTy := .lst (.nm "DuePair"), isMutable := true }]

/-- `ScopeEntry` (`Stores.lean:859`). -/
def scopeEntry : StructDesc where
  leanName := "ScopeEntry"; site := "Stores.lean:859"; subst := subst
  fields :=
    [{ leanName := "key", leanTy := .nat },
     { leanName := "scope", leanTy := .nm "ScopeV", isMutable := true }]

/-- `ScopeStore` (`Stores.lean:867`). -/
def scopeStore : StructDesc where
  leanName := "ScopeStore"; site := "Stores.lean:867"; subst := subst
  fields := [{ leanName := "entries", leanTy := .lst (.nm "ScopeEntry"), isMutable := true }]

/-- `Stores` (`Stores.lean:1002`), the `St` of this profile. -/
def stores : StructDesc where
  leanName := "Stores"; site := "Stores.lean:1002"; subst := subst
  fields :=
    [{ leanName := "refs", leanTy := .nm "RefHeap", isMutable := true },
     { leanName := "deferreds", leanTy := .nm "DeferredStore" },
     { leanName := "scopes", leanTy := .nm "ScopeStore" },
     { leanName := "nextName", leanTy := .nat, isMutable := true }]

/-- The tuple aliases the descriptions above name, because `LTy` has no product head: a
`ScopeState.openMap` entry is `Nat × FinName`, a waiter is `FiberId × Nat`, and a due resume is
`FiberId × Nat × Prim`. -/
def tupleAliases : List Decl :=
  [.rawD "type scope_entry_pair = int * fin_name",
   .rawD "type waiter_pair = int * int",
   .rawD "(* `FiberId × Nat × Prim`; the `Prim` is the avatar's `answer` (DIVERGENCE 1). *)",
   .rawD "type due_pair = int * int * answer"]

def structs : List StructDesc :=
  [refKey, deferredKey, ctx, scope, deferredCell, deferredStore, scopeEntry, scopeStore, stores]

def inductives : List InductiveDesc :=
  [err, defect, fnName, finName, completion, syncOp, raceName, progName, name, actionName,
   thunk, finalizerStrategy, scopeState]

/-- The generated carriers of `deep_stores.ml`, in dependency order (which is not the Lean order:
`FinalizerStrategy` and `ScopeState` come from `Scope.lean`, and OCaml needs a type before its
use — P5 §11.7 finding 4). -/
def generatedHead : List Decl :=
  [.comment ("Generated by OCaml5.Ml (`Render.lean`, seat W1). Do not edit; edit the"
      ++ " descriptions.\n   One declaration per `src/Effect4/Machine/Stores.lean` carrier, same field"
      ++ " and constructor order."),
   refKey.header, renameDecl "ref_key" refKey.decl,
   deferredKey.header, renameDecl "deferred_key" deferredKey.decl,
   err.header, renameDecl "err" err.decl,
   defect.header, renameDecl "defect" defect.decl,
   fnName.header, renameDecl "fn_name" fnName.decl,
   finName.header, renameDecl "fin_name" finName.decl,
   .comment ("The tuple aliases the descriptions name, because `LTy` has no product head."
      ++ " `answer` is `deep_fibers.ml:131`.")]

/-- The carriers after the tuple aliases. -/
def generatedTail : List Decl :=
  [.comment "`src/Effect4/Machine/Scope.lean`: the two carriers `ScopeStore` is made of.",
   finalizerStrategy.header, renameDecl "finalizer_strategy" finalizerStrategy.decl,
   scopeState.header, renameDecl "scope_state" scopeState.decl,
   scope.header, renameDecl "scope" scope.decl,
   ctx.header, renameDecl "ctx" ctx.decl,
   completion.header, renameDecl "completion" completion.decl,
   syncOp.header, renameDecl "sync_op" syncOp.decl,
   raceName.header, renameDecl "race_name" raceName.decl,
   .comment ("`ProgName`, `Name`, `ActionName` and `Thunk` are one mutually recursive group in"
      ++ " OCaml, which Lean does not need because its four are separate inductives over"
      ++ " already-declared types. Order inside the group is the Lean order."),
   progName.header, renameDecl "prog_name" progName.decl,
   name.header, renameDecl "name" name.decl,
   actionName.header, renameDecl "action_name" actionName.decl,
   thunk.header, renameDecl "thunk" thunk.decl,
   .comment "The three stores and the `St` over them.",
   deferredCell.header, renameDecl "deferred_cell" deferredCell.decl,
   deferredStore.header, renameDecl "deferred_store" deferredStore.decl,
   scopeEntry.header, renameDecl "scope_entry" scopeEntry.decl,
   scopeStore.header, renameDecl "scope_store" scopeStore.decl,
   stores.header, renameDecl "stores" stores.decl]

/-- The generated carriers of `deep_stores.ml`: the head, the tuple aliases, the tail. -/
def generated : List Decl := generatedHead ++ tupleAliases ++ generatedTail


/-- The descriptions under the projection guard, in the order the report prints. -/
def all : List TypeDesc := [.struct refKey, .struct deferredKey, .induct err, .induct defect, .induct fnName, .induct finName, .struct ctx, .induct completion, .induct syncOp, .induct raceName, .induct progName, .induct name, .induct actionName, .induct thunk, .induct finalizerStrategy, .induct scopeState, .struct scope, .struct deferredCell, .struct deferredStore, .struct scopeEntry, .struct scopeStore, .struct stores]

/-- `deep_stores.ml` as a part of the avatar. -/
def part : Part :=
  { name := "stores", file := "deep_stores.ml", guarded := all, derived := Derived.Stores.all,
    generated := generated }

end Stores

end OCaml5.Avatar
