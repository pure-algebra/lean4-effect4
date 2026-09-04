import Effect4.Deep.Fibers
import Effect4.Runtime.Scope

/-!
# Deep spike S2: the concrete stores and the `RunInterp` over them

Status: design spike, 2026-09-03. Module `Deep.Stores` of the non-default `Deep` library
(`lakefile.toml`, `srcDir = "workshop"`); built with `lake build Deep.Stores`. Plan:
`docs/research/2026-09-03-deep-plan.md` row S2. Contract: `docs/research/2026-09-03-fiber-machine-pass-a.md`.
Model reading: `docs/research/2026-09-03-deep-state-models.md` §2 and §3. Report:
`docs/research/2026-09-03-spike-s2-stores-witnesses.md`.

This file supplies the `St` that `Deep.Fibers` is parametric in, and the `RunInterp` over it,
at concrete first-order alphabets. Nothing here is a closure: every function-valued argument of
rc.112 is a *name* plus a total interpretation, as `PrimInterp` already is
(`Effect4/Runtime/Runtime.lean:188-215`, DB-02).

The three stores:

* `RefHeap` — `Ref.ts`. A `List Val` plus a `RefKey` index. `ref.make` is `Effect.sync` over
  the constructor (`Ref.ts:173`), so every operation is one `refStep` under `Prim.sync`.
* `DeferredStore` — `Deferred.ts`. A completion slot that is `none` or exactly one *primitive*,
  a registration-ordered waiter list of `(FiberId × token)`, and the resume queue a completion
  owes (`Deferred.ts:1655-1659`).
* `ScopeStore` — keyed `Effect4.Scope`s, reused unchanged (`Effect4/Runtime/Scope.lean`),
  over a finalizer *name* alphabet that includes "interrupt fiber `f`" (`internal/effect.ts:5370`)
  and "close child scope `s`" (`:3833-3844`), so `scopeStatus`, `scopeLinkFiber`,
  `dropFinalizer` and `closeScope` are store operations.

**DB-07, stated beside the interp.** Every store operation of this file is a *forward* map:
`refStep`, `DeferredStore.complete`, `ScopeStore.*` and `storesCloseScope` return the store
they reached, and no arm of the interp, and no arm of `Deep.Fibers`, reads a store snapshot
taken before a step. Consequently the store the machine carries after a fiber has failed is the
store that fiber had reached when it failed: state produced before failure remains available to
finalization (`AGENTS.md`, "State produced before failure remains available to finalization",
`docs/DESIGN-BASIS.md` DB-07). The landing proves that as
`state (stepDecision interp fuel m d) = state (the last store operation the trace records)`,
whose falsifier is one reachable decision after which the store is an earlier one; the executable
instance is `Deep.Witnesses.db07_store_survives_failure`.
-/

set_option autoImplicit false

namespace Effect4.Deep

open Effect4

/-! ## Keys

Keys are structures over `Nat` at `Type 0`. rc.112 mints fresh *objects*; the index is the
model's stand-in and owes a refusal row of the `SCOPE-FB-KEY-IDENTITY` shape
(`Effect4/Runtime/Scope.lean:318`, `docs/SCOPE-DAG.md:226`). -/

/-- A cell of the Ref heap. `Ref.ts:142-146` allocates a fresh `MutableRef` object; the index
is the model's stand-in. -/
structure RefKey where
  /-- Allocation order. -/
  index : Nat
deriving DecidableEq, Repr, Inhabited

/-- A cell of the Deferred store (`Deferred.ts:140-145`). -/
structure DeferredKey where
  /-- Allocation order. -/
  index : Nat
deriving DecidableEq, Repr, Inhabited

/-! ## The alphabets

Every alphabet is first-order and derives `DecidableEq`, which the separation gates of
`Deep.Fibers` (`docs/FRAMES-DAG.md` separation 4) need at this instantiation. -/

/-- The typed error alphabet. -/
inductive Err
  | boom
  | tag (code : Nat)
deriving DecidableEq, Repr

/-- The defect alphabet: `defaultEvaluate`'s payload (`PrimInterp.notImplemented`), the
`AsyncFiberError` of a fiber that survives `runSync`'s flush, and the payload a continuation
name applied to a value of the wrong shape answers. -/
inductive Defect
  | notImplemented
  | asyncFiber
  | badName
deriving DecidableEq, Repr

/-- The cause-annotation value alphabet; `stackAnnotations` contributes none
(`internal/effect.ts:579-580` is `fiberStackAnnotations`, host stack data). -/
abbrev Ann := Unit

/-- Names of the pure functions the read-modify-write `Ref` operations apply. rc.112 takes a
JavaScript function; DB-02 forbids storing one, so the operation carries a name and the
interpretation below is the `RefInterp` of the state note §3.1. -/
inductive FnName
  /-- `a ↦ a + 1`. -/
  | incr
  /-- `a ↦ 2 * a`. -/
  | double
  /-- partial: `Some 0` on a positive cell, `None` otherwise. -/
  | zeroWhenPositive
  /-- partial: `None` always — the `modifySome` write-back witness. -/
  | noChange
  /-- `modify`: answer the old value, write the bumped one. -/
  | takeAndBump
deriving DecidableEq, Repr

/-- The scope finalizer *name* alphabet. `Effect4.Scope` stores a `φ`; giving `φ` these arms is
what lets a finalizer name *mean* an operation on another scope or on a fiber — the open half of
`SCOPE-FB-FINALIZER-MEANING` (`docs/SCOPE-DAG.md:228`). -/
inductive FinName
  /-- `forkIn`'s keyed fiber finalizer (`internal/effect.ts:5369-5371`): interrupt the child
  unless the interruptor is the child itself. `skipSelf = false` is `fiberRunIn` (`:5458`). -/
  | interruptFiber (fiber : FiberId) (skipSelf : Bool)
  /-- `scopeForkUnsafe`'s parent-side name (`internal/effect.ts:3833-3844`):
  `scopeClose(child, exit)`. -/
  | closeChildScope (scope : Nat)
  /-- `scopeForkUnsafe`'s child-side name: `scopeRemoveFinalizerUnsafe(parent, key)`. -/
  | detachFromParent (parent : Nat) (key : Nat)
  /-- An ordinary release, observable through the exit it produces. -/
  | release (label : Nat) (fails : Bool)
  /-- A release that parks on an external async before it completes: the observable a masked
  finalizer needs, since `onExit`'s `contAll` masks the fiber while the finalizer runs
  (`Effect4/Runtime/Runtime.lean:560-565`, rc.112 `internal/effect.ts:4021`). -/
  | parkThen (slot : Nat)
deriving DecidableEq, Repr

/-- The fiber `Context`, restricted to what rc.112 reads off it: the ambient `Scope` service
(`forkScoped`, `internal/effect.ts:5400-5406`) and the two cached budget fields
(`setContext`, `:726-727`). -/
structure Ctx where
  /-- The ambient `Scope` service, as a `ScopeStore` key. -/
  ambientScope : Option Nat
  /-- `MaxOpsBeforeYield`. -/
  maxOpsBeforeYield : Nat
  /-- `PreventSchedulerYield`. -/
  preventYield : Bool
deriving DecidableEq, Repr, Inhabited

/-- The one value alphabet. `exitOk`/`exitErr` are `reifyExit`'s image: rc.112's `Exit` is an
ordinary value once an `Exit` frame has caught it (`internal/effect.ts` `exit`). -/
inductive Val
  /-- `exitVoid`'s value (`internal/effect.ts:988`). -/
  | unit
  | nat (n : Nat)
  | bool (b : Bool)
  /-- The handle a fork answers. -/
  | fiber (id : FiberId)
  /-- `awaitAllChildren`'s snapshot. -/
  | fibers (ids : List FiberId)
  /-- `Ref.set`'s success value: the `MutableRef` itself (`Ref.ts:307`, `MutableRef.ts:1063-1070`). -/
  | cell (key : RefKey)
  /-- A `Deferred` handle (`Deferred.ts:140-145`). -/
  | promise (key : DeferredKey)
  /-- A `Scope` handle. -/
  | scopeHandle (scope : Nat)
  /-- `fiber.context` as a value (`getContext`). -/
  | context (ctx : Ctx)
  /-- A reified successful `Exit`. -/
  | exitOk (value : Val)
  /-- A reified failed `Exit`. -/
  | exitErr (cause : Cause Err Defect FiberId Ann)
  /-- The empty list of awaited exits (`fiberAwaitAll`, `internal/effect.ts:779`; M6). A
  `List ExitV` field would make `Val` a *nested* inductive whose `DecidableEq` handler
  refuses, so the list is spelled with these two arms. -/
  | exitNil
  /-- One awaited exit, and the rest. -/
  | exitCons (head : Val) (tail : Val)
deriving DecidableEq

/-- The cause carrier at this instantiation. -/
abbrev CauseV := Cause Err Defect FiberId Ann

/-- The exit carrier at this instantiation. -/
abbrev ExitV := Exit Val Err Defect FiberId Ann

/-- The exit carrier a finalizer produces (`combineFinalizerCause`, `internal/effect.ts:3800-3804`). -/
abbrev VoidExitV := Exit Unit Err Defect FiberId Ann

/-- What a `completeWith` stores. rc.112 assigns the argument *effect* to `self.effect` and
never runs it (`Deferred.ts:456-461` into `:1650`); `done` is `completeWith` itself (`:570-571`),
so an `Exit` completion is the `ofExit` arm. `ofRefGet` is a genuinely non-exit completion — a
`sync` read of a Ref cell — which is what makes
`deferred.complete-with-stores-effect` say something. -/
inductive Completion
  /-- `done(self, exit)` = `completeWith(self, exit)` (`Deferred.ts:570-571`). -/
  | ofExit (exit : ExitV)
  /-- `completeWith(self, Ref.get(cell))`: an effect, stored and not run. -/
  | ofRefGet (cell : RefKey)
deriving DecidableEq

/-- Every `sync` thunk that touches a store. One arm per rc.112 operation, named with its
arguments; `syncState` gives them meaning. -/
inductive SyncOp
  /-- `Ref.make` (`Ref.ts:173`), `Effect.sync` over `makeUnsafe` (`:142-146`). -/
  | refMake (initial : Val)
  /-- `Ref.get` (`Ref.ts:200`). -/
  | refGet (cell : RefKey)
  /-- `Ref.set` (`Ref.ts:306-307`): answers the cell. -/
  | refSet (cell : RefKey) (value : Val)
  /-- `Ref.getAndSet` (`Ref.ts:399-404`). -/
  | refGetAndSet (cell : RefKey) (value : Val)
  /-- `Ref.setAndGet` (`Ref.ts:747`): the assignment expression's value. -/
  | refSetAndGet (cell : RefKey) (value : Val)
  /-- `Ref.update` (`Ref.ts:1273-1276`): answers `undefined`. -/
  | refUpdate (cell : RefKey) (f : FnName)
  /-- `Ref.getAndUpdate` (`Ref.ts:496-501`). -/
  | refGetAndUpdate (cell : RefKey) (f : FnName)
  /-- `Ref.updateAndGet` (`Ref.ts:1368`). -/
  | refUpdateAndGet (cell : RefKey) (f : FnName)
  /-- `Ref.updateSome` (`Ref.ts:1502-1508`). -/
  | refUpdateSome (cell : RefKey) (pf : FnName)
  /-- `Ref.getAndUpdateSome` (`Ref.ts:635-643`): the value read *before* the write. -/
  | refGetAndUpdateSome (cell : RefKey) (pf : FnName)
  /-- `Ref.updateSomeAndGet` (`Ref.ts:1639-1646`): a fresh read *after* the write. -/
  | refUpdateSomeAndGet (cell : RefKey) (pf : FnName)
  /-- `Ref.modify` (`Ref.ts:896-901`). -/
  | refModify (cell : RefKey) (f : FnName)
  /-- `Ref.modifySome` (`Ref.ts:1159-1163`): on `None` it writes back the value `modify`
  already read, never a re-read. -/
  | refModifySome (cell : RefKey) (pf : FnName)
  /-- `Deferred.make` (`Deferred.ts:171`). -/
  | deferredMake
  /-- `Deferred.isDone` (`Deferred.ts:1382`). -/
  | deferredIsDone (cell : DeferredKey)
  /-- `Deferred.poll` (`Deferred.ts:1414-1416`). -/
  | deferredPoll (cell : DeferredKey)
  /-- `Deferred.completeWith` (`Deferred.ts:456-461`) and, through it, `done`, `succeed`,
  `fail`, `failCause`, `die` (`:570-571`, `:1514`, `:669`, `:877`, `:1087`). -/
  | deferredCompleteWith (cell : DeferredKey) (completion : Completion)
  /-- `Deferred.interruptWith` (`Deferred.ts:1332-1337`): `failCause` of `causeInterrupt(id)`. -/
  | deferredInterruptWith (cell : DeferredKey) (interruptor : FiberId)
  /-- `_await`'s cleanup (`Deferred.ts:178-185`): splice this waiter out; a no-op once
  completion has cleared the array. -/
  | deferredAwaitCleanup (cell : DeferredKey) (waiter : FiberId) (token : Nat)
  /-- `scopeMakeUnsafe` (`internal/effect.ts:3914-3922`). -/
  | scopeMake (strategy : FinalizerStrategy)
  /-- `scopeAddFinalizerExit` (`internal/effect.ts:3846-3858`). -/
  | scopeAdd (scope : Nat) (key : Nat) (finalizer : FinName)
  /-- `scopeRemoveFinalizerUnsafe` (`internal/effect.ts:3890-3904`). -/
  | scopeRemove (scope : Nat) (key : Nat)
  /-- Whether a scope has closed (`Scope.ts:99-187`). -/
  | scopeIsClosed (scope : Nat)
deriving DecidableEq

/-- The declared race shapes. A `List ProgName` field would make `ProgName` a *nested*
inductive, whose `DecidableEq` handler refuses (state note §3.5); a race is therefore named and
`raceEntrants` gives it meaning. -/
inductive RaceName
  /-- `raceAll([])`: pending until interrupted
  (`test/fixtures/traces/fiber-m3/emptyRacePendingUntilInterrupted.tsv`). -/
  | empty
  /-- An immediate success followed by a second entrant that is never launched
  (`test/fixtures/traces/fiber-m3/raceImmediateSuccessStopsLaunch.tsv`). -/
  | successThenSecond
  /-- A failure followed by a success
  (`test/fixtures/traces/fiber-m3/raceFailureAllowsNextLaunch.tsv`). -/
  | failThenSuccess
  /-- Two failures, retained in order
  (`test/fixtures/traces/fiber-m3/raceAllFailuresRetainOrder.tsv`). -/
  | failThenFail
deriving DecidableEq, Repr

/-- The declared program names. Names are data; `progOf` is the interpretation. A program name
is what `WithFiberAction.fork` and `raceAll` carry, so the fork alphabet stays first-order. -/
inductive ProgName
  /-- `succeed(value)`. -/
  | value (v : Val)
  /-- `failCause(cause)`. -/
  | failCause (cause : CauseV)
  /-- One store operation under `Prim.sync`. -/
  | syncOp (op : SyncOp)
  /-- `yieldNowWith(priority)` (`internal/effect.ts:982-990`). -/
  | yieldNow (priority : Nat)
  /-- An external `Async` the store never answers; the tape's `answerAsync` does
  (`internal/effect.ts:1109-1143`). -/
  | park (slot : Nat)
  /-- `Deferred.await` (`Deferred.ts:173-186`): the `callback` effect, i.e. `op.Async`, whose
  registration is a store operation. -/
  | awaitDeferred (cell : DeferredKey)
  /-- `Deferred.into` (`Deferred.ts:1774-1784`): the whole thing under an uninterruptible
  mask, which `WithFiberAction.setInterruptible` now spells (M2). -/
  | intoDeferred (body : ProgName) (cell : DeferredKey)
  /-- `into`'s masked body: `flatMap(exit(restore(self)), exit => done(deferred, exit))`
  (`Deferred.ts:1779-1782`); `restore` is `interruptible`, the `true` half of M2. -/
  | intoBody (body : ProgName) (cell : DeferredKey)
  /-- A program that masks its own fiber and then parks (`internal/effect.ts:4302-4310`). -/
  | maskedPark (slot : Nat)
  /-- `fiberAwaitAll(targets)` (`internal/effect.ts:779`), answering the exits (M6). -/
  | awaitFibers (targets : List FiberId)
  /-- The program one scope finalizer *name* runs, as a forkable program. -/
  | finalizerOf (fin : FinName) (exit : ExitV)
  /-- `Deferred.interrupt` (`Deferred.ts:1231-1232`): `withFiber` reads the id, then
  `interruptWith`. -/
  | interruptDeferred (cell : DeferredKey)
  /-- `onExit(body, finalizer)` (`internal/effect.ts:4021`). -/
  | onExitOf (body : ProgName) (fin : FinName) (finalizerInterruptible : Bool)
  /-- `flatMap(first, () => second)`. -/
  | seqOf (first : ProgName) (second : ProgName)
  /-- `fork` then `join`/`await` the child (`:5264-5284`, `:5291`, `:5304`). -/
  | forkThen (child : ProgName) (options : Supervision.ForkOptions)
      (mode : Supervision.ObserverMode)
  /-- `forkUnsafe` alone (`:5264-5284`). -/
  | forkOnly (child : ProgName) (options : Supervision.ForkOptions)
  /-- `forkIn` (`:5364-5378`). -/
  | forkInScope (child : ProgName) (options : Supervision.ForkOptions) (scope : Nat) (key : Nat)
  /-- `fiberRunIn` (`:5447-5461`): bind an *existing* fiber to a scope. Its closed-scope arm
  interrupts with `self.id` and no caller annotations (`:5454`), unlike `forkIn`'s (M10). -/
  | runInScope (target : FiberId) (scope : Nat) (key : Nat)
  /-- `forkScoped` (`:5400-5406`). -/
  | forkScopedOf (child : ProgName) (options : Supervision.ForkOptions) (key : Nat)
  /-- `raceAll` (`Supervision.RaceAllState`). -/
  | raceOf (race : RaceName)
  /-- `scopeClose(scope, exit)` from the fiber (`internal/effect.ts:3826` via the store). -/
  | closeScopeOf (scope : Nat) (exit : ExitV)
  /-- `awaitAllChildren(body)` (`:5314-5322`). -/
  | awaitAllNew (body : ProgName)
deriving DecidableEq

/-- The continuation, finalizer, registration and cancel names. All three of rc.112's
function-valued slots are one `ν`. -/
inductive Name
  /-- `flatMap(finalizer(exit), () => exit)`: `Exit.restoreAfterFinalizer`'s caller side. -/
  | restore (exit : ExitV)
  /-- The failure arm of the same composite: `Exit.mergeFinalizer`
  (`combineFinalizerCause`, `internal/effect.ts:3800-3804`). -/
  | merge (exit : ExitV)
  /-- contA: discard the value and continue with the named program. -/
  | seq (next : ProgName)
  /-- contA on a `Val.fiber`: park as `join` (`:5291`) or `await` (`:5304`). -/
  | joinOn (mode : Supervision.ObserverMode)
  /-- contA on a `Val.fiber`: `Deferred.interrupt`'s second half (`Deferred.ts:1231-1232`). -/
  | interruptWith (cell : DeferredKey)
  /-- contA on a reified `Exit`: `into`'s completion (`Deferred.ts:1781`). -/
  | doneInto (cell : DeferredKey)
  /-- contA/contE: answer a constant. -/
  | constant (value : Val)
  /-- contA on a reified `Exit`: turn it back into an effect. -/
  | exitOfValue
  /-- contA: `awaitAllChildren`'s exit half over the snapshot (`:5318-5322`). -/
  | awaitNew (snapshot : List FiberId)
  /-- contA on the snapshot value: run the body, then await the children added since. -/
  | snapshotThen (body : ProgName)
  /-- `register(resume, signal)` for `Deferred.await` (`Deferred.ts:173-177`). -/
  | registerAwait (cell : DeferredKey)
  /-- `_await`'s cleanup name (`Deferred.ts:178-185`): the cancel effect the registration
  returned, which the `AsyncFinalizer` frame's `contE` runs. -/
  | cancelAwait (cell : DeferredKey)
  /-- An external `register` the store never answers. -/
  | externalRegister (slot : Nat)
  /-- `RunInterp.abortName`: the cancel of an `Async` that asked for a controller and returned
  no cancel effect (`internal/effect.ts:1134-1140`). -/
  | abortController
  /-- `RunInterp.cancelName base waiter token` (M3): the cancel name with the identity of the
  fiber that parked and the token it parked on, which is what `_await`'s cleanup needs to
  splice the right resume out (`Deferred.ts:181-184`). -/
  | withWaiter (base : Name) (waiter : FiberId) (token : Nat)
  /-- `PrimInterp.cancelThenFail`'s tail: `() => failCause(cause)`
  (`internal/effect.ts:1157`). -/
  | reFail (cause : CauseV)
  /-- A scope finalizer name, carried by an `OnExit` frame. -/
  | finalizerName (fin : FinName)
  /-- The sequential close chain (`internal/effect.ts:3817-3818`): the remaining finalizers,
  the closing exit, and the reasons captured so far. -/
  | closeSeq (remaining : List FinName) (exit : ExitV)
      (captured : List (Reason Err Defect FiberId Ann))
  /-- The parallel close chain (`internal/effect.ts:3819-3821`): the remaining finalizers, the
  closing exit, the fibers forked so far, and the closing fiber's inherited mask. -/
  | closePar (remaining : List FinName) (exit : ExitV) (forked : List FiberId)
      (closerInterruptible : Bool)
  /-- The merge of the exits a countdown collected (`internal/effect.ts:3826`, M6): applied to
  the `exitsValue` the `awaitAll` park answered with. -/
  | mergeAwaitedExits
deriving DecidableEq

/-- What a `withFiber` thunk names. The machine's `WithFiberAction` carries `Prim`s; a thunk
cannot, so the alphabet carries `ProgName` and `withFiberOf` expands. -/
inductive ActionName
  | fork (program : ProgName) (options : Supervision.ForkOptions)
  | forkIn (program : ProgName) (options : Supervision.ForkOptions) (scope : Nat) (key : Nat)
  | forkScoped (program : ProgName) (options : Supervision.ForkOptions) (key : Nat)
  | runIn (target : FiberId) (scope : Nat) (key : Nat)
  | interrupt (target : FiberId)
  | interruptScoped (target : FiberId)
  | interruptAll (targets : List FiberId) (interruptor : Option FiberId)
  | awaitAll (targets : List FiberId)
  | snapshotChildren
  | awaitNewChildren (snapshot : List FiberId)
  | raceAll (race : RaceName)
  | setContext (context : Ctx)
  | getContext
  | getId
  | closeScope (scope : Nat) (exit : ExitV)
  /-- `uninterruptible` / `interruptible` bodies (`internal/effect.ts:4302-4310`,
  `:4331-4352`), M2. -/
  | setInterruptible (body : ProgName) (flag : Bool)
  /-- The interp refuses this thunk (S3 §5.2). -/
  | refuse (cause : CauseV)
deriving DecidableEq

/-- Every thunk name: the one park the frame alphabet does not spell (`join`/`await`; yield
and async are `Prim` constructors now), a `withFiber` action, a store operation, or a
`suspend` body. -/
inductive Thunk
  /-- `parkOf` recognises exactly this shape. -/
  | park (kind : ParkKind)
  /-- `withFiberOf` recognises exactly this shape. -/
  | act (action : ActionName)
  /-- `syncState` recognises exactly this shape. -/
  | op (operation : SyncOp)
  /-- `suspend`'s body (`internal/effect.ts` `suspend`). -/
  | body (program : ProgName)
deriving DecidableEq

/-- The program carrier at this instantiation. -/
abbrev Program := Prim Name Thunk Val Err Defect FiberId Ann

/-! ## The Ref heap (`Ref.ts`, `MutableRef.ts`) -/

/-- The Ref heap: one `Val` per allocated cell, in allocation order. -/
abbrev RefHeap := List Val

/-- `self.ref.current` (`Ref.ts:200`); a dangling key is a frontier, never a typed error
(`AGENTS.md`). -/
def refPeek (heap : RefHeap) (cell : RefKey) : Option Val := heap[cell.index]?

/-- `self.ref.current = value` (`MutableRef.ts:1068`). -/
def refPoke (heap : RefHeap) (cell : RefKey) (value : Val) : RefHeap :=
  heap.set cell.index value

/-- `a ↦ f(a)` for the total read-modify-write operations. -/
def FnName.total : FnName → Val → Val
  | FnName.incr, Val.nat n => Val.nat (n + 1)
  | FnName.double, Val.nat n => Val.nat (n * 2)
  | FnName.takeAndBump, Val.nat n => Val.nat (n + 1)
  | _, value => value

/-- `a ↦ pf(a)` for the `Some`/`None` read-modify-write operations. -/
def FnName.partialUpdate : FnName → Val → Option Val
  | FnName.noChange, _ => none
  | FnName.zeroWhenPositive, Val.nat (Nat.succ _) => some (Val.nat 0)
  | FnName.zeroWhenPositive, _ => none
  | f, value => some (f.total value)

/-- `a ↦ [b, a']` (`Ref.ts:898`). -/
def FnName.modify : FnName → Val → Val × Val
  | FnName.takeAndBump, Val.nat n => (Val.nat n, Val.nat (n + 1))
  | f, value => (value, f.total value)

/-- `a ↦ [b, Option a']` (`Ref.ts:1161`). -/
def FnName.modifySome : FnName → Val → Val × Option Val
  | FnName.noChange, value => (value, none)
  | f, value => ((f.modify value).1, some (f.modify value).2)

/-- One step of the Ref heap. `none` is a frontier: a key no allocation of this heap minted.
Every arm is one `Effect.sync` thunk, so the read and the write of a read-modify-write happen
with no intervening runtime step (`Ref.ts:400-404`). -/
def refStep : SyncOp → RefHeap → Option (Val × RefHeap)
  | SyncOp.refMake initial, heap => some (Val.cell ⟨heap.length⟩, heap ++ [initial])
  | SyncOp.refGet cell, heap => (refPeek heap cell).map (fun a => (a, heap))
  | SyncOp.refSet cell value, heap =>
    (refPeek heap cell).map (fun _ => (Val.cell cell, refPoke heap cell value))
  | SyncOp.refGetAndSet cell value, heap =>
    (refPeek heap cell).map (fun a => (a, refPoke heap cell value))
  | SyncOp.refSetAndGet cell value, heap =>
    (refPeek heap cell).map (fun _ => (value, refPoke heap cell value))
  | SyncOp.refUpdate cell f, heap =>
    (refPeek heap cell).map (fun a => (Val.unit, refPoke heap cell (f.total a)))
  | SyncOp.refGetAndUpdate cell f, heap =>
    (refPeek heap cell).map (fun a => (a, refPoke heap cell (f.total a)))
  | SyncOp.refUpdateAndGet cell f, heap =>
    (refPeek heap cell).map (fun a => (f.total a, refPoke heap cell (f.total a)))
  | SyncOp.refUpdateSome cell pf, heap =>
    (refPeek heap cell).map (fun a =>
      (Val.unit,
        match pf.partialUpdate a with
        | some a' => refPoke heap cell a'
        | none => heap))
  | SyncOp.refGetAndUpdateSome cell pf, heap =>
    (refPeek heap cell).map (fun a =>
      (a,
        match pf.partialUpdate a with
        | some a' => refPoke heap cell a'
        | none => heap))
  | SyncOp.refUpdateSomeAndGet cell pf, heap =>
    (refPeek heap cell).bind (fun a =>
      match pf.partialUpdate a with
      | some a' => (refPeek (refPoke heap cell a') cell).map (fun fresh => (fresh, refPoke heap cell a'))
      | none => some (a, heap))
  | SyncOp.refModify cell f, heap =>
    (refPeek heap cell).map (fun a => ((f.modify a).1, refPoke heap cell (f.modify a).2))
  | SyncOp.refModifySome cell pf, heap =>
    (refPeek heap cell).map (fun a =>
      ((pf.modifySome a).1, refPoke heap cell ((pf.modifySome a).2.getD a)))
  | _, _ => none

/-! ### The ten `ref.*` census clauses, one theorem each -/

/-- `ref.make`: the single field is a fresh cell, appended in allocation order.
census: ref.make -/
theorem refStep_make (heap : RefHeap) (a : Val) :
    refStep (SyncOp.refMake a) heap = some (Val.cell ⟨heap.length⟩, heap ++ [a]) := rfl

/-- `ref.make`: every evaluation of the same `make` allocates a distinct cell.
census: ref.make -/
theorem refMake_twice_distinct (heap : RefHeap) (a b : Val) :
    ((refStep (SyncOp.refMake a) heap).map Prod.fst) ≠
      ((refStep (SyncOp.refMake a) heap).bind
        (fun step => (refStep (SyncOp.refMake b) step.2).map Prod.fst)) := by
  -- Both sides compute: the first `make` answers the cell at `heap.length`, the
  -- second the cell at `(heap ++ [a]).length`. Written out rather than by
  -- `simp`, which reached `Classical.choice` here.
  show some (Val.cell ⟨heap.length⟩) ≠ some (Val.cell ⟨(heap ++ [a]).length⟩)
  intro h
  have hlen : heap.length = (heap ++ [a]).length :=
    RefKey.mk.inj (Val.cell.inj (Option.some.inj h))
  rw [List.length_append, List.length_singleton] at hlen
  exact Nat.succ_ne_self heap.length hlen.symm

/-- `ref.make` is `Effect.sync` over the constructor (`Ref.ts:173`). census: ref.make -/
theorem refMake_is_sync (a : Val) :
    (Prim.sync (Thunk.op (SyncOp.refMake a)) : Program) =
      Prim.sync (Thunk.op (SyncOp.refMake a)) := rfl

/-- `ref.get`: a synchronous read of `current` with no copy and no write.
census: ref.get -/
theorem refStep_get (heap : RefHeap) (cell : RefKey) (a : Val) (h : refPeek heap cell = some a) :
    refStep (SyncOp.refGet cell) heap = some (a, heap) := by
  simp [refStep, h]

/-- A live key is in range. -/
private theorem index_lt_of_peek {heap : RefHeap} {cell : RefKey} {a : Val}
    (h : refPeek heap cell = some a) : cell.index < heap.length := by
  cases Nat.lt_or_ge cell.index heap.length with
  | inl hlt => exact hlt
  | inr hge =>
    have hnone : heap[cell.index]? = none := List.getElem?_eq_none hge
    simp [refPeek, hnone] at h

/-- `MutableRef.set` writes the field the next read observes (`MutableRef.ts:1068`).
census: ref.get -/
theorem refPeek_poke_self (heap : RefHeap) (cell : RefKey) (v a : Val)
    (h : refPeek heap cell = some a) : refPeek (refPoke heap cell v) cell = some v := by
  simp only [refPeek, refPoke, List.getElem?_set_self (index_lt_of_peek h)]

/-- `ref.get` observes every write already made through any holder of the same cell.
census: ref.get -/
theorem refStep_get_after_set (heap : RefHeap) (cell : RefKey) (v a : Val)
    (h : refPeek heap cell = some a) :
    (refStep (SyncOp.refGet cell) (refPoke heap cell v)).map Prod.fst = some v := by
  simp [refStep, refPeek_poke_self heap cell v a h]

/-- `ref.set-void-returns-cell`: the success value is the mutable cell, not `undefined`.
census: ref.set-void-returns-cell -/
theorem refStep_set (heap : RefHeap) (cell : RefKey) (v a : Val)
    (h : refPeek heap cell = some a) :
    refStep (SyncOp.refSet cell v) heap = some (Val.cell cell, refPoke heap cell v) := by
  simp [refStep, h]

/-- `ref.set-void-returns-cell`: two `void`-declared operations, two different runtime answers.
census: ref.set-void-returns-cell -/
theorem set_answer_ne_update_answer (cell : RefKey) :
    (Val.cell cell) ≠ (Val.unit : Val) := by
  intro contra
  nomatch contra

/-- `ref.cell-set-returns-self`: `MutableRef.set` returns the very ref it wrote.
census: ref.cell-set-returns-self -/
theorem refStep_set_answers_self (heap : RefHeap) (cell : RefKey) (v a : Val)
    (h : refPeek heap cell = some a) :
    (refStep (SyncOp.refSet cell v) heap).map Prod.fst = some (Val.cell cell) ∧
      (refStep (SyncOp.refSet cell v) heap).map Prod.snd = some (refPoke heap cell v) := by
  simp [refStep, h]

/-- `ref.get-and-set`: the value read is the success value and the write happens in the same
thunk. census: ref.get-and-set -/
theorem refStep_getAndSet (heap : RefHeap) (cell : RefKey) (v a : Val)
    (h : refPeek heap cell = some a) :
    refStep (SyncOp.refGetAndSet cell v) heap = some (a, refPoke heap cell v) := by
  simp [refStep, h]

/-- `ref.set-and-get-assignment`: the success value is the assignment expression, never a
second read. census: ref.set-and-get-assignment -/
theorem refStep_setAndGet (heap : RefHeap) (cell : RefKey) (v a : Val)
    (h : refPeek heap cell = some a) :
    refStep (SyncOp.refSetAndGet cell v) heap = some (v, refPoke heap cell v) := by
  simp [refStep, h]

/-- `ref.update`: the function is applied once, the result is written back, and the effect
succeeds with `undefined`. census: ref.update -/
theorem refStep_update (heap : RefHeap) (cell : RefKey) (f : FnName) (a : Val)
    (h : refPeek heap cell = some a) :
    refStep (SyncOp.refUpdate cell f) heap = some (Val.unit, refPoke heap cell (f.total a)) := by
  simp [refStep, h]

/-- `ref.update`: applied exactly once, not twice. census: ref.update -/
theorem refStep_update_applies_once (heap : RefHeap) (cell : RefKey) (a : Val)
    (h : refPeek heap cell = some a) (hval : a = Val.nat 0) :
    (refStep (SyncOp.refUpdate cell FnName.incr) heap).map Prod.snd =
      some (refPoke heap cell (Val.nat 1)) := by
  subst hval
  simp [refStep, h, FnName.total]

/-- `ref.modify`: the second component is written back and the first is the success value.
census: ref.modify -/
theorem refStep_modify (heap : RefHeap) (cell : RefKey) (f : FnName) (a : Val)
    (h : refPeek heap cell = some a) :
    refStep (SyncOp.refModify cell f) heap =
      some ((f.modify a).1, refPoke heap cell (f.modify a).2) := by
  simp [refStep, h]

/-- `ref.modify-some-no-reread`: on a `None` second component the cell is written back with the
value `modify` already read, not with a re-read. census: ref.modify-some-no-reread -/
theorem refStep_modifySome_none (heap : RefHeap) (cell : RefKey) (a : Val)
    (h : refPeek heap cell = some a) :
    refStep (SyncOp.refModifySome cell FnName.noChange) heap =
      some (a, refPoke heap cell a) := by
  simp [refStep, h, FnName.modifySome]

/-- `ref.modify-some-no-reread`: `modifySome` *is* `modify` of the derived pair
(`Ref.ts:1160-1162`). census: ref.modify-some-no-reread -/
theorem refStep_modifySome_eq_modify (heap : RefHeap) (cell : RefKey) (pf : FnName) (a : Val)
    (h : refPeek heap cell = some a) :
    refStep (SyncOp.refModifySome cell pf) heap =
      some ((pf.modifySome a).1, refPoke heap cell ((pf.modifySome a).2.getD a)) := by
  simp [refStep, h]

/-- `ref.update-some-and-get-reread`: on `Some` the cell is written and the answer is a fresh
read of `current` taken after the write. census: ref.update-some-and-get-reread -/
theorem refStep_updateSomeAndGet_some (heap : RefHeap) (cell : RefKey) (pf : FnName) (a a' : Val)
    (h : refPeek heap cell = some a) (hpf : pf.partialUpdate a = some a') :
    refStep (SyncOp.refUpdateSomeAndGet cell pf) heap =
      (refPeek (refPoke heap cell a') cell).map (fun fresh => (fresh, refPoke heap cell a')) := by
  simp [refStep, h, hpf]

/-- `ref.update-some-and-get-reread`: on `None` nothing is written. -/
theorem refStep_updateSomeAndGet_none (heap : RefHeap) (cell : RefKey) (a : Val)
    (h : refPeek heap cell = some a) :
    refStep (SyncOp.refUpdateSomeAndGet cell FnName.noChange) heap = some (a, heap) := by
  simp [refStep, h, FnName.partialUpdate]

/-- `ref.update-some-and-get-reread`: `updateSomeAndGet` and `getAndUpdateSome` differ — the
first answers after the write, the second before it. census: ref.update-some-and-get-reread -/
theorem updateSomeAndGet_ne_getAndUpdateSome :
    (refStep (SyncOp.refUpdateSomeAndGet ⟨0⟩ FnName.zeroWhenPositive) [Val.nat 3]).map Prod.fst ≠
      (refStep (SyncOp.refGetAndUpdateSome ⟨0⟩ FnName.zeroWhenPositive) [Val.nat 3]).map
        Prod.fst := by
  decide

/-! ## The Deferred store (`Deferred.ts`) -/

/-- One `Deferred`: `effect?` and `resumes?` (`Deferred.ts:58-61`), with no third state. The
completion is a *primitive*, so `done exit = completeWith (Prim.ofExit exit)` is definitional. -/
structure DeferredCell where
  /-- `self.effect`: absent, or exactly one stored effect. -/
  completion : Option Program
  /-- `self.resumes`, in registration order: the parked fiber and its resume token. -/
  waiters : List (FiberId × Nat)
deriving DecidableEq

/-- The Deferred store: the cells plus the resume queue a completion owes.
`doneUnsafe` clears `resumes` *before* resuming (`Deferred.ts:1655-1656`), so the queue is an
answer of the store step and not a promise. -/
structure DeferredStore where
  /-- Allocated cells, in allocation order. -/
  cells : List DeferredCell
  /-- The resumes owed, in registration order (`Deferred.ts:1657-1658`). -/
  due : List (FiberId × Nat × Program)
deriving DecidableEq

namespace DeferredStore

/-- `Deferred.makeUnsafe` (`Deferred.ts:140-145`): both fields undefined. -/
def make (self : DeferredStore) : DeferredKey × DeferredStore :=
  (⟨self.cells.length⟩, { self with cells := self.cells ++ [⟨none, []⟩] })

/-- The cell under a key; `none` is a frontier. -/
def cellAt (self : DeferredStore) (cell : DeferredKey) : Option DeferredCell :=
  self.cells[cell.index]?

/-- Replace one cell. -/
def setCell (self : DeferredStore) (cell : DeferredKey) (value : DeferredCell) : DeferredStore :=
  { self with cells := self.cells.set cell.index value }

/-- `isDoneUnsafe` (`Deferred.ts:1382`): done-ness is exactly the presence of a completion. -/
def isDone (self : DeferredStore) (cell : DeferredKey) : Option Bool :=
  (self.cellAt cell).map (fun c => c.completion.isSome)

/-- `poll` (`Deferred.ts:1414-1416`): a non-blocking sync read of the slot. -/
def poll (self : DeferredStore) (cell : DeferredKey) : Option (Option Program) :=
  (self.cellAt cell).map DeferredCell.completion

/-- `_await` (`Deferred.ts:173-177`), the store half of `registerAsync`: resume at once with the
stored effect when done, otherwise append this waiter in registration order and park. -/
def register (self : DeferredStore) (cell : DeferredKey) (waiter : FiberId) (token : Nat) :
    DeferredStore × Option Program :=
  match self.cellAt cell with
  | none => (self, none)
  | some c =>
    match c.completion with
    | some effect => (self, some effect)
    | none => (self.setCell cell { c with waiters := c.waiters ++ [(waiter, token)] }, none)

/-- `_await`'s cleanup (`Deferred.ts:178-185`): splice this waiter out, order-preserving; a
no-op once completion has cleared the array. -/
def cancel (self : DeferredStore) (cell : DeferredKey) (waiter : FiberId) (token : Nat) :
    DeferredStore :=
  match self.cellAt cell with
  | none => self
  | some c =>
    self.setCell cell { c with waiters := c.waiters.filter (fun w => !(w.1 = waiter && w.2 = token)) }

/-- `doneUnsafe` (`Deferred.ts:1648-1662`): a completion attempt answers `false` and changes
nothing when an effect is already stored; otherwise the effect is stored, the waiter list is
*cleared*, and every waiter is owed a resume with that effect in registration order. -/
def complete (self : DeferredStore) (cell : DeferredKey) (effect : Program) :
    DeferredStore × Bool :=
  match self.cellAt cell with
  | none => (self, false)
  | some c =>
    match c.completion with
    | some _ => (self, false)
    | none =>
      ({ self.setCell cell ⟨some effect, []⟩ with
          due := self.due ++ c.waiters.map (fun w => (w.1, w.2, effect)) }, true)

/-- The resumes the store owes now, drained in registration order. -/
def drainDue (self : DeferredStore) : List (FiberId × Nat × Program) × DeferredStore :=
  (self.due, { self with due := [] })

end DeferredStore

/-! ### The twelve `deferred.*` census clauses, one theorem each -/

/-- `deferred.make`: a fresh cell has no completion and no waiter, and there is no separate
pending tag. census: deferred.make -/
theorem deferredStore_make (self : DeferredStore) :
    self.make = (⟨self.cells.length⟩, { self with cells := self.cells ++ [⟨none, []⟩] }) := rfl

/-- `deferred.make`: a cell is exactly a completion slot and a waiter list; there is no third
field. census: deferred.make -/
theorem deferredCell_cases_receipt (c : DeferredCell) :
    c = ⟨c.completion, c.waiters⟩ := rfl

/-- `deferred.is-done`: done-ness is exactly the presence of the stored effect.
census: deferred.is-done -/
theorem deferredStore_isDone (self : DeferredStore) (cell : DeferredKey) (c : DeferredCell)
    (h : self.cellAt cell = some c) :
    self.isDone cell = some c.completion.isSome := by
  simp [DeferredStore.isDone, h]

/-- `deferred.is-done`: the state space is `undefined` or one effect, and nothing else.
census: deferred.is-done -/
theorem deferredCell_completion_cases (c : DeferredCell) :
    c.completion = none ∨ ∃ e, c.completion = some e := by
  cases h : c.completion with
  | none => exact Or.inl rfl
  | some e => exact Or.inr ⟨e, rfl⟩

/-- `deferred.await`, done half: resume at once with the stored effect; no waiter is appended.
census: deferred.await -/
theorem deferredStore_register_done (self : DeferredStore) (cell : DeferredKey)
    (c : DeferredCell) (e : Program) (waiter : FiberId) (token : Nat)
    (h : self.cellAt cell = some c) (hc : c.completion = some e) :
    self.register cell waiter token = (self, some e) := by
  simp [DeferredStore.register, h, hc]

/-- `deferred.await`, pending half: the waiter array is created lazily and this resume is
appended in registration order. census: deferred.await -/
theorem deferredStore_register_pending (self : DeferredStore) (cell : DeferredKey)
    (c : DeferredCell) (waiter : FiberId) (token : Nat)
    (h : self.cellAt cell = some c) (hc : c.completion = none) :
    self.register cell waiter token =
      (self.setCell cell { c with waiters := c.waiters ++ [(waiter, token)] }, none) := by
  simp [DeferredStore.register, h, hc]

/-- `deferred.await`, cleanup half: the cleanup splices exactly this resume out and preserves
the order of the others. census: deferred.await -/
theorem deferredStore_cancel_removes (self : DeferredStore) (cell : DeferredKey)
    (c : DeferredCell) (waiter : FiberId) (token : Nat) (h : self.cellAt cell = some c) :
    ((self.cancel cell waiter token).cellAt cell).map DeferredCell.waiters =
      ((self.setCell cell
        { c with waiters := c.waiters.filter (fun w => !(w.1 = waiter && w.2 = token)) }).cellAt
          cell).map DeferredCell.waiters := by
  simp [DeferredStore.cancel, h]

/-- `deferred.single-completion`: a second completion answers `false` and changes nothing.
census: deferred.single-completion -/
theorem deferredStore_complete_done (self : DeferredStore) (cell : DeferredKey)
    (c : DeferredCell) (e e' : Program) (h : self.cellAt cell = some c)
    (hc : c.completion = some e) :
    self.complete cell e' = (self, false) := by
  simp [DeferredStore.complete, h, hc]

/-- `deferred.completion-order`: the waiter list is cleared in the *same* state the owed resume
list is read from, and the resumes are in registration order; the attempt answers `true`.
census: deferred.completion-order -/
theorem deferredStore_complete_pending (self : DeferredStore) (cell : DeferredKey)
    (c : DeferredCell) (e : Program) (h : self.cellAt cell = some c)
    (hc : c.completion = none) :
    self.complete cell e =
      ({ self.setCell cell ⟨some e, []⟩ with
          due := self.due ++ c.waiters.map (fun w => (w.1, w.2, e)) }, true) := by
  simp [DeferredStore.complete, h, hc]

/-- A live Deferred key is in range. -/
private theorem cellIndex_lt {self : DeferredStore} {cell : DeferredKey} {c : DeferredCell}
    (h : self.cellAt cell = some c) : cell.index < self.cells.length := by
  cases Nat.lt_or_ge cell.index self.cells.length with
  | inl hlt => exact hlt
  | inr hge =>
    have hnone : self.cells[cell.index]? = none := List.getElem?_eq_none hge
    simp [DeferredStore.cellAt, hnone] at h

/-- Writing a live cell is what the next read observes. -/
theorem deferredStore_setCell_cellAt (self : DeferredStore) (cell : DeferredKey)
    (c value : DeferredCell) (h : self.cellAt cell = some c) :
    (self.setCell cell value).cellAt cell = some value := by
  simp only [DeferredStore.setCell, DeferredStore.cellAt,
    List.getElem?_set_self (cellIndex_lt h)]

/-- `deferred.complete-with-stores-effect`: the argument primitive is stored, for *every*
primitive including a non-exit one, and is never run.
census: deferred.complete-with-stores-effect -/
theorem deferredStore_complete_stores_argument (self : DeferredStore) (cell : DeferredKey)
    (c : DeferredCell) (e : Program) (h : self.cellAt cell = some c)
    (hc : c.completion = none) :
    ((self.complete cell e).1.cellAt cell).map DeferredCell.completion = some (some e) := by
  have hset : (self.setCell cell ⟨some e, []⟩).cellAt cell = some ⟨some e, []⟩ :=
    deferredStore_setCell_cellAt self cell c ⟨some e, []⟩ h
  simp only [DeferredStore.complete, h, hc]
  simp only [DeferredStore.cellAt, DeferredStore.setCell] at hset ⊢
  simp [hset]

/-- `deferred.complete-with-stores-effect`: a waiter is resumed with *that* effect.
census: deferred.complete-with-stores-effect -/
theorem deferredStore_waiter_receives_stored (self : DeferredStore) (cell : DeferredKey)
    (c : DeferredCell) (e : Program) (waiter : FiberId) (token : Nat)
    (h : self.cellAt cell = some c) (hc : c.completion = none)
    (hw : c.waiters = [(waiter, token)]) :
    (self.complete cell e).1.due = self.due ++ [(waiter, token, e)] := by
  simp [DeferredStore.complete, h, hc, hw]

/-! `deferred.done-is-complete-with`, `deferred.interrupt-with`, `deferred.into-uninterruptible`,
`deferred.complete-runs-once`, `deferred.interrupt` and `deferred.poll` are stated below, after
`progOf`, because their content is the *program* the name compiles to. -/

/-! ## The Scope store (`Scope.ts`, `internal/effect.ts:3778-3947`) -/

/-- One keyed `Effect4.Scope`, reused unchanged. -/
abbrev ScopeV := Effect4.Scope Nat FinName Val Err Defect FiberId Ann

/-- `run : φ → Exit → Exit Unit`, the pure finalizer meaning `Effect4.Scope.close` takes.
`FRAME-FB-FINALIZER-EFFECT`'s shape at this alphabet: only `release _ true` fails. -/
def finExit : FinName → ExitV → VoidExitV
  | FinName.release label true, _ => Exit.failure (Cause.fail (Err.tag label))
  | _, _ => Exit.void

/-- One entry of the scope store. -/
structure ScopeEntry where
  /-- The store key. -/
  key : Nat
  /-- The frozen scope state machine (`Effect4/Runtime/Scope.lean`). -/
  scope : ScopeV
deriving DecidableEq

/-- The keyed scopes. -/
structure ScopeStore where
  /-- Entries, in allocation order. -/
  entries : List ScopeEntry
deriving DecidableEq

namespace ScopeStore

/-- The entry under a key; `none` is a frontier. -/
def entryAt (self : ScopeStore) (key : Nat) : Option ScopeEntry :=
  self.entries.find? (fun e => e.key = key)

/-- Replace one entry. -/
def setEntry (self : ScopeStore) (entry : ScopeEntry) : ScopeStore :=
  { entries := self.entries.map (fun e => if e.key = entry.key then entry else e) }

/-- `scopeMakeUnsafe` (`internal/effect.ts:3914-3922`): a new scope starts `Empty`. -/
def make (self : ScopeStore) (key : Nat) (strategy : FinalizerStrategy) : ScopeStore :=
  { entries := self.entries ++ [⟨key, Effect4.Scope.make strategy⟩] }

/-- `scopeAddFinalizerExit` (`internal/effect.ts:3846-3858`): register while open, run now
when closed. The immediate run is `finExit`. -/
def addFinalizer (self : ScopeStore) (key : Nat) (finalizerKey : Nat) (finalizer : FinName) :
    ScopeStore × VoidExitV :=
  match self.entryAt key with
  | none => (self, Exit.void)
  | some entry =>
    let (scope, answer) := Effect4.Scope.addExit finExit entry.scope finalizerKey finalizer
    (self.setEntry { entry with scope := scope }, answer)

/-- `scopeRemoveFinalizerUnsafe` (`internal/effect.ts:3890-3904`). -/
def removeFinalizer (self : ScopeStore) (key : Nat) (finalizerKey : Nat) : ScopeStore :=
  match self.entryAt key with
  | none => self
  | some entry =>
    self.setEntry { entry with scope := Effect4.Scope.removeUnsafe entry.scope finalizerKey }

/-- `scopeForkUnsafe` (`internal/effect.ts:3833-3844`): one shared key links a parent finalizer
closing the child to a child finalizer removing itself from the parent. -/
def forkChild (self : ScopeStore) (parentKey childKey sharedKey : Nat)
    (strategy : FinalizerStrategy) : ScopeStore :=
  match self.entryAt parentKey with
  | none => self
  | some parent =>
    let (parentScope, childScope) :=
      Effect4.Scope.fork parent.scope strategy sharedKey
        (FinName.closeChildScope childKey) (FinName.detachFromParent parentKey sharedKey)
    { entries :=
        (self.setEntry { parent with scope := parentScope }).entries ++
          [⟨childKey, childScope⟩] }

/-- The scope store view `RunInterp.scopeStatus` needs: `none` unknown, `some none` open,
`some (some exit)` closed. -/
def status (self : ScopeStore) (key : Nat) : Option (Option ExitV) :=
  (self.entryAt key).map (fun e => e.scope.closingExit?)

/-- The close order: the materialised registration list, backwards
(`internal/effect.ts:3815`). -/
def closeOrderOf (self : ScopeStore) (key : Nat) : List FinName :=
  match self.entryAt key with
  | none => []
  | some entry => entry.scope.closeOrder

/-- The state half of `scopeCloseUnsafe` (`internal/effect.ts:3778-3798`): state first, so the
written state cannot depend on what any finalizer does. -/
def closeState (self : ScopeStore) (key : Nat) (exit : ExitV) : ScopeStore :=
  match self.entryAt key with
  | none => self
  | some entry =>
    self.setEntry { entry with scope := Effect4.Scope.closeState entry.scope exit }

/-- The purely computed close result of `Effect4.Scope` (`Scope.lean:796-803`), retained so the
merge the machine observes can be compared with it. -/
def closeResultOf (self : ScopeStore) (key : Nat) (exit : ExitV) : VoidExitV :=
  match self.entryAt key with
  | none => Exit.void
  | some entry => Effect4.Scope.closeResult finExit entry.scope exit

end ScopeStore

/-- `exitAsVoidAll` (`internal/effect.ts:2024-2038`) at the value alphabet: the concatenated
reasons, or the void success. -/
def voidAllOf (reasons : List (Reason Err Defect FiberId Ann)) : ExitV :=
  match reasons with
  | [] => Exit.success Val.unit
  | reason :: rest => Exit.failure ⟨reason :: rest⟩

/-- The merge of a list of exits, `Exit.asVoidAll`'s shape at the value alphabet. -/
def mergeExits (exits : List ExitV) : ExitV :=
  voidAllOf (exits.flatMap Exit.causeReasons)

/-- The value-alphabet merge agrees with `Exit.asVoidAll` on which reasons it carries.
census: scope.exit-as-void-all -/
theorem mergeExits_reasons (exits : List ExitV) :
    (mergeExits exits).causeReasons = (Exit.asVoidAll exits).causeReasons := by
  unfold mergeExits voidAllOf Exit.asVoidAll
  cases exits.flatMap Exit.causeReasons <;> rfl

/-- `reifyExit`: an `Exit` as a value of the one value alphabet. -/
def reifyExitVal : ExitV → Val
  | Exit.success value => Val.exitOk value
  | Exit.failure cause => Val.exitErr cause

/-- `RunInterp.exitsValue`: the exits a countdown collected, as one value
(`fiberAwaitAll`, `internal/effect.ts:779`; M6). -/
def exitsVal : List ExitV → Val
  | [] => Val.exitNil
  | exit :: rest => Val.exitCons (reifyExitVal exit) (exitsVal rest)

/-- The reasons carried by an exits value, in order. -/
def reasonsOfVal : Val → List (Reason Err Defect FiberId Ann)
  | Val.exitErr cause => cause.reasons
  | Val.exitCons head tail => reasonsOfVal head ++ reasonsOfVal tail
  | _ => []

/-- Reading the reasons back off an exits value is reading them off the list: the M6 channel
loses nothing, so the merge of an awaited list is `exitAsVoidAll` of that list.
census: scope.close-merge -/
theorem reasonsOfVal_exitsVal (exits : List ExitV) :
    reasonsOfVal (exitsVal exits) = exits.flatMap Exit.causeReasons := by
  induction exits with
  | nil => rfl
  | cons exit rest ih =>
    cases exit <;>
      simp [exitsVal, reifyExitVal, reasonsOfVal, Exit.causeReasons, ih]

/-- Hence the merge computed from what `awaitAll` answered is `mergeExits` of the exits.
census: scope.close-merge -/
theorem mergeAwaited_eq_mergeExits (exits : List ExitV) :
    voidAllOf (reasonsOfVal (exitsVal exits)) = mergeExits exits := by
  rw [reasonsOfVal_exitsVal]
  rfl

/-! ## The service state -/

/-- `St`: the three stores and one fresh-name counter. -/
structure Stores where
  /-- `Ref.ts`. -/
  refs : RefHeap
  /-- `Deferred.ts`. -/
  deferreds : DeferredStore
  /-- `Scope.ts` plus the keyed store. -/
  scopes : ScopeStore
  /-- Fresh scope keys and finalizer keys. -/
  nextName : Nat
deriving DecidableEq

namespace Stores

/-- An empty service state. -/
def empty : Stores := ⟨[], ⟨[], []⟩, ⟨[]⟩, 0⟩

end Stores

/-! ## Names into programs

`progOf` is the `PrimInterp`-style interpretation of the declared program names. It is the only
place a program is built; the alphabets carry names. -/

/-- The programs of a declared race. -/
def raceEntrants : RaceName → List ProgName
  | RaceName.empty => []
  | RaceName.successThenSecond => [ProgName.value (Val.nat 1), ProgName.value (Val.nat 2)]
  | RaceName.failThenSuccess =>
    [ProgName.failCause (Cause.fail (Err.tag 1)), ProgName.value (Val.nat 9)]
  | RaceName.failThenFail =>
    [ProgName.failCause (Cause.fail (Err.tag 1)), ProgName.failCause (Cause.fail (Err.tag 2))]

/-- The program a scope finalizer *name* runs (`internal/effect.ts:4021`: an `OnExit`
finalizer is a program, run as one). -/
def finProgram : FinName → ExitV → Program
  | FinName.interruptFiber fiber true, _ =>
    Prim.withFiber (Thunk.act (ActionName.interruptScoped fiber))
  | FinName.interruptFiber fiber false, _ =>
    Prim.withFiber (Thunk.act (ActionName.interrupt fiber))
  | FinName.closeChildScope scope, exit =>
    Prim.withFiber (Thunk.act (ActionName.closeScope scope exit))
  | FinName.detachFromParent parent key, _ =>
    Prim.sync (Thunk.op (SyncOp.scopeRemove parent key))
  | FinName.release label fails, _ =>
    if fails then Prim.failure (Cause.fail (Err.tag label)) else Prim.success Val.unit
  | FinName.parkThen slot, _ =>
    Prim.async (Name.externalRegister slot) false none

/-- The stored primitive a `Completion` names. `done exit = completeWith (Prim.ofExit exit)`
(`Deferred.ts:570-571`); `ofRefGet` is a non-exit effect, stored and not run (`:456-461`). -/
def completionPrim : Completion → Program
  | Completion.ofExit exit => Prim.ofExit exit
  | Completion.ofRefGet cell => Prim.sync (Thunk.op (SyncOp.refGet cell))

/-- The declared programs. -/
def progOf : ProgName → Program
  | ProgName.value v => Prim.success v
  | ProgName.failCause cause => Prim.failure cause
  | ProgName.syncOp op => Prim.sync (Thunk.op op)
  | ProgName.yieldNow priority => Prim.yieldNowWith priority
  | ProgName.park slot =>
    -- no controller and no cancel, so the run loop pushes no `AsyncFinalizer` (`:1128-1141`)
    Prim.async (Name.externalRegister slot) false none
  | ProgName.awaitDeferred cell =>
    -- `_await` returns the splice-out cleanup (`Deferred.ts:178-185`), so the run loop pushes
    -- `Prim.asyncFinalizer (cancelName (cancelAwait cell) fiber token)` at park time (M3)
    Prim.async (Name.registerAwait cell) true (some (Name.cancelAwait cell))
  | ProgName.intoDeferred body cell =>
    -- `uninterruptibleMask(restore => …)` (`Deferred.ts:1778`), M2
    Prim.withFiber (Thunk.act (ActionName.setInterruptible (ProgName.intoBody body cell) false))
  | ProgName.intoBody body cell =>
    -- `flatMap(exit(restore(self)), exit => done(deferred, exit))` (`Deferred.ts:1779-1782`)
    Prim.onSuccess
      (Prim.exitFrame (Prim.withFiber (Thunk.act (ActionName.setInterruptible body true))))
      (Name.doneInto cell)
  | ProgName.maskedPark slot =>
    Prim.withFiber (Thunk.act (ActionName.setInterruptible (ProgName.park slot) false))
  | ProgName.awaitFibers targets =>
    Prim.withFiber (Thunk.act (ActionName.awaitAll targets))
  | ProgName.finalizerOf fin exit => finProgram fin exit
  | ProgName.interruptDeferred cell =>
    Prim.onSuccess (Prim.withFiber (Thunk.act ActionName.getId)) (Name.interruptWith cell)
  | ProgName.onExitOf body fin flag =>
    Prim.onExit (progOf body) (Name.finalizerName fin) flag
  | ProgName.seqOf first second => Prim.onSuccess (progOf first) (Name.seq second)
  | ProgName.forkThen child options mode =>
    Prim.onSuccess (Prim.withFiber (Thunk.act (ActionName.fork child options)))
      (Name.joinOn mode)
  | ProgName.forkOnly child options => Prim.withFiber (Thunk.act (ActionName.fork child options))
  | ProgName.forkInScope child options scope key =>
    Prim.withFiber (Thunk.act (ActionName.forkIn child options scope key))
  | ProgName.runInScope target scope key =>
    Prim.withFiber (Thunk.act (ActionName.runIn target scope key))
  | ProgName.forkScopedOf child options key =>
    Prim.withFiber (Thunk.act (ActionName.forkScoped child options key))
  | ProgName.raceOf race => Prim.withFiber (Thunk.act (ActionName.raceAll race))
  | ProgName.closeScopeOf scope exit =>
    Prim.withFiber (Thunk.act (ActionName.closeScope scope exit))
  | ProgName.awaitAllNew body =>
    Prim.onSuccess (Prim.withFiber (Thunk.act ActionName.snapshotChildren))
      (Name.snapshotThen body)

/-- The cancel effect a cancel *name* runs. `cancelName` attached the parked fiber's identity
and its resume token, so `_await`'s cleanup can splice exactly that resume out
(`Deferred.ts:178-185`, M3). -/
def cancelProgram : Name → Program
  | Name.withWaiter (Name.cancelAwait cell) waiter token =>
    Prim.sync (Thunk.op (SyncOp.deferredAwaitCleanup cell waiter token))
  | _ => Prim.success Val.unit

/-- The sequential close chain (`internal/effect.ts:3813-3818`): the finalizers in
`closeOrder`, each awaited through its own exit — `exit(finalizer(exit_))` never throws — with
the captured reasons merged by `exitAsVoidAll` at the end (`:3826`). -/
def closeSeqChain : List FinName → ExitV →
    List (Reason Err Defect FiberId Ann) → Program
  | [], _, captured => Prim.ofExit (voidAllOf captured)
  | fin :: rest, exit, captured =>
    Prim.onSuccessAndFailure (finProgram fin exit)
      (Name.closeSeq rest exit captured) (Name.closeSeq rest exit captured)

/-- The parallel close chain (`internal/effect.ts:3819-3821`): each finalizer is forked as an
*immediate daemon* whose mask is the closing fiber's, then all of them are awaited together
(`:3823-3824`) and every exit merged (`:3826`). Since M6 the merge reads the exits the
countdown collected, not a store side-channel. -/
def closeParChain (closerInterruptible : Bool) :
    List FinName → ExitV → List FiberId → Program
  | [], _, forked =>
    Prim.onSuccess (Prim.withFiber (Thunk.act (ActionName.awaitAll forked)))
      Name.mergeAwaitedExits
  | fin :: rest, exit, forked =>
    Prim.onSuccess
      (Prim.withFiber (Thunk.act (ActionName.fork (ProgName.finalizerOf fin exit)
        ⟨true, true,
          if closerInterruptible then Supervision.MaskMode.interruptible
          else Supervision.MaskMode.uninterruptible⟩)))
      (Name.closePar rest exit forked closerInterruptible)

/-- The close program of a scope, by its strategy. `Effect4.Scope.closeState` runs first, so the
state is written before any finalizer program is built (`internal/effect.ts:3784`), and the
close of an already closed scope is void. `none` is an unknown scope key, which the machine
turns into `Stuck.unknownScope` — a live frontier, never a cause (M7). -/
def storesCloseScope (scope : Nat) (exit : ExitV) (closerInterruptible : Bool)
    (state : Stores) : Option (Stores × Program) :=
  match state.scopes.entryAt scope with
  | none => none
  | some entry =>
    if entry.scope.isClosed then some (state, Prim.success Val.unit)
    else
      let order := entry.scope.closeOrder
      let state := { state with scopes := state.scopes.closeState scope exit }
      match entry.scope.strategy with
      | FinalizerStrategy.sequential => some (state, closeSeqChain order exit [])
      | FinalizerStrategy.parallel => some (state, closeParChain closerInterruptible order exit [])

/-! ## The store steps under `Prim.sync` -/

/-- Every `sync` thunk that reads or writes the service state. `none` falls back to the pure
`syncValue`. -/
def syncOpStep : SyncOp → Stores → Option (Stores × Val)
  | SyncOp.deferredMake, st =>
    let (key, deferreds) := st.deferreds.make
    some ({ st with deferreds := deferreds }, Val.promise key)
  | SyncOp.deferredIsDone cell, st =>
    (st.deferreds.isDone cell).map (fun flag => (st, Val.bool flag))
  | SyncOp.deferredPoll cell, st =>
    (st.deferreds.poll cell).map (fun slot => (st, Val.bool slot.isSome))
  | SyncOp.deferredCompleteWith cell completion, st =>
    let (deferreds, answered) := st.deferreds.complete cell (completionPrim completion)
    some ({ st with deferreds := deferreds }, Val.bool answered)
  | SyncOp.deferredInterruptWith cell interruptor, st =>
    let (deferreds, answered) :=
      st.deferreds.complete cell
        (Prim.ofExit (Exit.failure (Cause.interrupt (some interruptor))))
    some ({ st with deferreds := deferreds }, Val.bool answered)
  | SyncOp.deferredAwaitCleanup cell waiter token, st =>
    some ({ st with deferreds := st.deferreds.cancel cell waiter token }, Val.unit)
  | SyncOp.scopeMake strategy, st =>
    some ({ st with scopes := st.scopes.make st.nextName strategy, nextName := st.nextName + 1 },
      Val.scopeHandle st.nextName)
  | SyncOp.scopeAdd scope key finalizer, st =>
    let (scopes, _) := st.scopes.addFinalizer scope key finalizer
    some ({ st with scopes := scopes }, Val.unit)
  | SyncOp.scopeRemove scope key, st =>
    some ({ st with scopes := st.scopes.removeFinalizer scope key }, Val.unit)
  | SyncOp.scopeIsClosed scope, st =>
    (st.scopes.entryAt scope).map (fun entry => (st, Val.bool entry.scope.isClosed))
  | op, st => (refStep op st.refs).map (fun step => ({ st with refs := step.2 }, step.1))

/-! ## Continuations -/

/-- `cont[contA](value, fiber)`. -/
def contAOf : Name → Val → Program
  | Name.restore exit, _ => Prim.ofExit exit
  | Name.merge exit, _ => Prim.ofExit exit
  | Name.seq next, _ => progOf next
  | Name.joinOn mode, Val.fiber id => Prim.suspend (Thunk.park (ParkKind.join id mode))
  | Name.joinOn _, _ => Prim.failure (Cause.die Defect.badName)
  | Name.interruptWith cell, Val.fiber id =>
    Prim.sync (Thunk.op (SyncOp.deferredInterruptWith cell id))
  | Name.interruptWith _, _ => Prim.failure (Cause.die Defect.badName)
  | Name.doneInto cell, Val.exitOk value =>
    Prim.sync (Thunk.op (SyncOp.deferredCompleteWith cell (Completion.ofExit (Exit.success value))))
  | Name.doneInto cell, Val.exitErr cause =>
    Prim.sync (Thunk.op (SyncOp.deferredCompleteWith cell (Completion.ofExit (Exit.failure cause))))
  | Name.doneInto _, _ => Prim.failure (Cause.die Defect.badName)
  | Name.constant value, _ => Prim.success value
  | Name.exitOfValue, Val.exitOk value => Prim.success value
  | Name.exitOfValue, Val.exitErr cause => Prim.failure cause
  | Name.exitOfValue, _ => Prim.failure (Cause.die Defect.badName)
  | Name.awaitNew snapshot, _ =>
    Prim.withFiber (Thunk.act (ActionName.awaitNewChildren snapshot))
  | Name.snapshotThen body, Val.fibers snapshot =>
    Prim.onSuccess (progOf body) (Name.awaitNew snapshot)
  | Name.snapshotThen body, _ => Prim.onSuccess (progOf body) (Name.awaitNew [])
  | Name.closeSeq rest exit captured, _ => closeSeqChain rest exit captured
  | Name.closePar rest exit forked masked, Val.fiber id =>
    closeParChain masked rest exit (forked ++ [id])
  | Name.closePar rest exit forked masked, _ => closeParChain masked rest exit forked
  | Name.mergeAwaitedExits, value => Prim.ofExit (voidAllOf (reasonsOfVal value))
  | Name.reFail cause, _ => Prim.failure cause
  | _, value => Prim.success value

/-- `cont[contE](cause, fiber)`. -/
def contEOf : Name → CauseV → Program
  | Name.restore exit, cause =>
    Prim.ofExit (Exit.restoreAfterFinalizer exit (Exit.failure cause))
  | Name.merge exit, cause =>
    Prim.ofExit (Exit.restoreAfterFinalizer exit (Exit.failure cause))
  | Name.closeSeq rest exit captured, cause =>
    closeSeqChain rest exit (captured ++ cause.reasons)
  | Name.constant value, _ => Prim.success value
  | _, cause => Prim.failure cause

/-- `WithFiberAction` from a name. -/
def actionOf : ActionName → WithFiberAction Name Thunk Val Err Defect FiberId Ann Ctx
  | ActionName.fork program options => WithFiberAction.fork (progOf program) options
  | ActionName.forkIn program options scope key =>
    WithFiberAction.forkIn (progOf program) options scope key
  | ActionName.forkScoped program options key =>
    WithFiberAction.forkScoped (progOf program) options key
  | ActionName.runIn target scope key => WithFiberAction.runIn target scope key
  | ActionName.interrupt target => WithFiberAction.interrupt target
  | ActionName.interruptScoped target => WithFiberAction.interruptScoped target
  | ActionName.interruptAll targets interruptor =>
    WithFiberAction.interruptAll targets interruptor
  | ActionName.awaitAll targets => WithFiberAction.awaitAll targets
  | ActionName.snapshotChildren => WithFiberAction.snapshotChildren
  | ActionName.awaitNewChildren snapshot => WithFiberAction.awaitNewChildren snapshot
  | ActionName.raceAll race => WithFiberAction.raceAll ((raceEntrants race).map progOf)
  | ActionName.setContext context => WithFiberAction.setContext context
  | ActionName.getContext => WithFiberAction.getContext
  | ActionName.getId => WithFiberAction.getId
  | ActionName.closeScope scope exit => WithFiberAction.closeScope scope exit
  | ActionName.setInterruptible body flag =>
    WithFiberAction.setInterruptible (progOf body) flag
  | ActionName.refuse cause => WithFiberAction.refuse cause

/-! ## The interp -/

/-- The default `MaxOpsBeforeYield` of the sync scheduler (`Scheduler.ts:174-176`); large
enough that a witness never gets an injected yield it did not ask for. -/
def defaultBudget : Nat := 2048

/-- The empty context (`internal/effect.ts:627`). -/
def emptyCtx : Ctx := ⟨none, defaultBudget, false⟩

/-- The annotation key `currentStackFrame` contributes for one fiber. A small closed set, so
`decide` never has to compute a string append. -/
def stackKey (fiber : FiberId) : String :=
  match fiber.value with
  | 0 => "stack0"
  | 1 => "stack1"
  | 2 => "stack2"
  | _ => "stackN"

/-- `RunInterp.stackAnnotations`: what the *named* fiber's `currentStackFrame` contributes to an
interrupt cause (`internal/effect.ts:579-580`). Deliberately **not** constant, so that *whose*
stack an interrupt carries is observable: `interruptUnsafe` annotates from the target's own
frame (`:579-580`) and again from the caller's argument (`:582-583`), and only a per-fiber key
can tell the two apart — which is what M10 is about. `Ann` is `Unit`, so the key carries the
identity and the value carries nothing. -/
def stackAnnotationsOf (fiber : FiberId) : ReasonAnnotations Ann where
  entries := [(stackKey fiber, ())]
  keysNodup := by simp

/-- The `RunInterp` this spike supplies. Every field cites the rc.112 line the machine's
docstring cites; nothing here is canonical program content.

DB-07: read the module header. Every arm below threads the store *out*; there is no arm that
takes a store snapshot and no arm that restores one, so a failing step leaves the store the
failing fiber reached. -/
def stores : RunInterp Name Thunk Val Err Defect FiberId Ann Ctx Stores where
  contA := contAOf
  contE := contEOf
  syncValue := fun _ => Val.unit
  suspendBody := fun
    | Thunk.body program => progOf program
    | _ => Prim.failure (Cause.die Defect.notImplemented)
  finalizerExit := fun
    | Name.finalizerName fin, exit => finExit fin exit
    | _, _ => Exit.void
  reifyExit := reifyExitVal
  iterNext := fun _ value => ([], IterStep.done value)
  loopTest := fun _ _ => false
  loopBody := fun _ value => Prim.success value
  loopStep := fun _ _ value => value
  loopDone := fun _ => Val.unit
  notImplemented := Defect.notImplemented
  cancelThenFail := fun name cause =>
    -- `flatMap(this[args](), () => failCause(cause))` (`internal/effect.ts:1157`), S1
    Prim.onSuccess (cancelProgram name) (Name.reFail cause)
  parkOf := fun
    | Prim.suspend (Thunk.park kind) => some (Except.ok kind)
    | _ => none
  withFiberOf := fun
    | Thunk.act action => some (actionOf action)
    | _ => none
  syncState := fun
    | Thunk.op operation, state => syncOpStep operation state
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
    | some _ =>
      -- `forkIn` registers the self-guarded finalizer (`:5370`), `fiberRunIn` the unguarded
      -- one (`:5458`) — M4
      let skipSelf :=
        match mode with
        | Supervision.ScopeMode.forkIn => true
        | Supervision.ScopeMode.fiberRunIn => false
      some { state with
        scopes := (state.scopes.addFinalizer scope key (FinName.interruptFiber fiber skipSelf)).1 }
  dropFinalizer := fun scope key state =>
    match state.scopes.entryAt scope with
    | none => none
    | some _ => some { state with scopes := state.scopes.removeFinalizer scope key }
  closeScope := fun scope exit closerInterruptible _closer state =>
    storesCloseScope scope exit closerInterruptible state
  ambientScope := Ctx.ambientScope
  budgetOf := fun ctx => (ctx.maxOpsBeforeYield, ctx.preventYield)
  emptyContext := emptyCtx
  contextValue := Val.context
  exitValue := fun exit mode =>
    match mode with
    | Supervision.ObserverMode.awaitValue => Prim.success (reifyExitVal exit)
    | Supervision.ObserverMode.joinEffect => Prim.ofExit exit
  fiberValue := Val.fiber
  fibersValue := Val.fibers
  exitsValue := exitsVal
  voidValue := Val.unit
  encodeFiber := id
  stackAnnotations := stackAnnotationsOf
  asyncFiberError := Defect.asyncFiber

/-! ### The remaining `deferred.*` clauses, as facts about the compiled program -/

/-- `deferred.done-is-complete-with`: `done` *is* `completeWith`; completing from an `Exit`
stores that `Exit`. census: deferred.done-is-complete-with -/
theorem completionPrim_ofExit (exit : ExitV) :
    completionPrim (Completion.ofExit exit) = Prim.ofExit exit := rfl

/-- `deferred.done-is-complete-with`: an `Exit` completion is shared — every awaiter is resumed
with the same primitive, and that primitive reads back as the same exit
(`Effect4/Runtime/Runtime.lean:514`). census: deferred.done-is-complete-with -/
theorem doneWith_shared (exit : ExitV) :
    (completionPrim (Completion.ofExit exit)).asExit? = some exit :=
  Prim.ofExit_asExit? exit

/-- `deferred.complete-with-stores-effect`: a non-exit completion is stored as an effect, and
it is *not* an exit — so what a waiter is resumed with is that effect, not a computed result.
census: deferred.complete-with-stores-effect -/
theorem completeWith_non_exit (cell : RefKey) :
    (completionPrim (Completion.ofRefGet cell)).asExit? = none := rfl

/-- `deferred.interrupt-with`: `interruptWith` is `failCause` of an interrupt cause carrying the
given fiber id, i.e. an ordinary stored failure completion and not a distinguished state.
census: deferred.interrupt-with -/
theorem interruptWith_is_completion (st : Stores) (cell : DeferredKey) (interruptor : FiberId) :
    syncOpStep (SyncOp.deferredInterruptWith cell interruptor) st =
      syncOpStep (SyncOp.deferredCompleteWith cell
        (Completion.ofExit (Exit.failure (Cause.interrupt (some interruptor))))) st := rfl

/-- `deferred.interrupt`: the interruptor is read through `withFiber` and is the *completing*
fiber, not the awaiting one — the spelling is `withFiber getId` followed by the
`interruptWith` continuation. census: deferred.interrupt -/
theorem interruptDeferred_spelling (cell : DeferredKey) :
    progOf (ProgName.interruptDeferred cell) =
      Prim.onSuccess (Prim.withFiber (Thunk.act ActionName.getId)) (Name.interruptWith cell) :=
  rfl

/-- `deferred.interrupt`: the continuation applied to the running fiber's own id delegates to
`interruptWith` with that id. census: deferred.interrupt -/
theorem interruptDeferred_delegates (cell : DeferredKey) (id : FiberId) :
    contAOf (Name.interruptWith cell) (Val.fiber id) =
      Prim.sync (Thunk.op (SyncOp.deferredInterruptWith cell id)) := rfl

/-- `deferred.into-uninterruptible`: the body runs under an `Exit` frame, so an interrupted body
still completes the Deferred with its own `Exit` (`Deferred.ts:1780-1781`).
census: deferred.into-uninterruptible -/
theorem intoDeferred_spelling (body : ProgName) (cell : DeferredKey) :
    progOf (ProgName.intoDeferred body cell) =
      Prim.withFiber (Thunk.act
        (ActionName.setInterruptible (ProgName.intoBody body cell) false)) := rfl

/-- `deferred.into-uninterruptible`, the mask clause (M2): the body runs under
`uninterruptible`, with interruptibility restored only *inside*, by `restore`
(`Deferred.ts:1778-1781`). -/
theorem intoDeferred_masks (body : ProgName) (cell : DeferredKey) :
    actionOf (ActionName.setInterruptible (ProgName.intoBody body cell) false) =
      WithFiberAction.setInterruptible (progOf (ProgName.intoBody body cell)) false ∧
    progOf (ProgName.intoBody body cell) =
      Prim.onSuccess
        (Prim.exitFrame (Prim.withFiber (Thunk.act (ActionName.setInterruptible body true))))
        (Name.doneInto cell) :=
  ⟨rfl, rfl⟩

/-- `deferred.into-uninterruptible`: the value handed to the completion is the body's `Exit`. -/
theorem intoDeferred_takes_exit (cell : DeferredKey) (cause : CauseV) :
    contAOf (Name.doneInto cell) (reifyExitVal (Exit.failure cause)) =
      Prim.sync (Thunk.op (SyncOp.deferredCompleteWith cell
        (Completion.ofExit (Exit.failure cause)))) := rfl

/-- `deferred.await`: the await is the `callback` effect, so the machine sees it as a park whose
registration is a store operation. census: deferred.await -/
theorem awaitDeferred_is_a_park (cell : DeferredKey) :
    progOf (ProgName.awaitDeferred cell) =
      Prim.async (Name.registerAwait cell) true (some (Name.cancelAwait cell)) := rfl

/-- `deferred.await`, the cleanup half (M3): the cancel name the run loop mints carries the
parked fiber and its token, and the cancel effect it runs is the splice-out
(`Deferred.ts:181-184`). -/
theorem cancelAwait_splices_the_waiter (cell : DeferredKey) (waiter : FiberId) (token : Nat) :
    cancelProgram (stores.cancelName (Name.cancelAwait cell) waiter token) =
      Prim.sync (Thunk.op (SyncOp.deferredAwaitCleanup cell waiter token)) := rfl

/-- The `AsyncFinalizer` frame`s `contE` runs the cancel and then re-fails with the very cause
that was passing (`internal/effect.ts:1157`). -/
theorem cancelThenFail_runs_then_refails (name : Name) (cause : CauseV) :
    stores.cancelThenFail name cause =
      Prim.onSuccess (cancelProgram name) (Name.reFail cause) := rfl

/-- `deferred.poll`: a non-blocking sync read that writes nothing. census: deferred.poll -/
theorem deferredPoll_no_write (st : Stores) (cell : DeferredKey) :
    (syncOpStep (SyncOp.deferredPoll cell) st).map Prod.fst =
      (st.deferreds.poll cell).map (fun _ => st) := by
  cases h : st.deferreds.poll cell <;> simp [syncOpStep, h]

/-! ### The `scope.*` clauses this store makes statable -/

/-- `scope.close-lifo`: the close order is the materialised registration list, backwards, and
the close program runs the finalizers in exactly that order.
census: scope.close-lifo, scope.close-sequential -/
theorem closeSeqChain_order (fin : FinName) (rest : List FinName) (exit : ExitV)
    (captured : List (Reason Err Defect FiberId Ann)) :
    closeSeqChain (fin :: rest) exit captured =
      Prim.onSuccessAndFailure (finProgram fin exit)
        (Name.closeSeq rest exit captured) (Name.closeSeq rest exit captured) := rfl

/-- `scope.close-sequential`: a failing finalizer does not abort the loop; its reasons are
captured and the chain continues with the next finalizer.
census: scope.close-sequential -/
theorem closeSeqChain_captures (rest : List FinName) (exit : ExitV)
    (captured : List (Reason Err Defect FiberId Ann)) (cause : CauseV) :
    contEOf (Name.closeSeq rest exit captured) cause =
      closeSeqChain rest exit (captured ++ cause.reasons) := rfl

/-- `scope.close-merge`: an empty remainder merges the captured reasons by the `exitAsVoidAll`
shape. census: scope.close-merge -/
theorem closeSeqChain_merges (exit : ExitV)
    (captured : List (Reason Err Defect FiberId Ann)) :
    closeSeqChain [] exit captured = Prim.ofExit (voidAllOf captured) := rfl

/-- `scope.close-parallel`: each finalizer is forked as an *immediate daemon* whose mask is the
closing fiber's. census: scope.close-parallel -/
theorem closeParChain_forks_immediate_daemon (fin : FinName) (rest : List FinName)
    (exit : ExitV) (forked : List FiberId) :
    closeParChain true (fin :: rest) exit forked =
      Prim.onSuccess
        (Prim.withFiber (Thunk.act (ActionName.fork (ProgName.finalizerOf fin exit)
          ⟨true, true, Supervision.MaskMode.interruptible⟩)))
        (Name.closePar rest exit forked true) := rfl

/-- `scope.close-parallel`: a masked closer's finalizer daemons are masked too. -/
theorem closeParChain_inherits_mask (fin : FinName) (rest : List FinName)
    (exit : ExitV) (forked : List FiberId) :
    closeParChain false (fin :: rest) exit forked =
      Prim.onSuccess
        (Prim.withFiber (Thunk.act (ActionName.fork (ProgName.finalizerOf fin exit)
          ⟨true, true, Supervision.MaskMode.uninterruptible⟩)))
        (Name.closePar rest exit forked false) := rfl

/-- `scope.close-merge`: the parallel finalizer fibers are awaited together and every exit is
merged. census: scope.close-merge -/
theorem closeParChain_awaits_all (exit : ExitV) (forked : List FiberId) :
    closeParChain true [] exit forked =
      Prim.onSuccess (Prim.withFiber (Thunk.act (ActionName.awaitAll forked)))
        Name.mergeAwaitedExits := rfl

/-- `scope.close-merge` (M6): the merge the close answers is `exitAsVoidAll` of exactly the
exits the countdown collected — no store side-channel. -/
theorem mergeAwaitedExits_is_asVoidAll (exits : List ExitV) :
    contAOf Name.mergeAwaitedExits (stores.exitsValue exits) =
      Prim.ofExit (mergeExits exits) := by
  show Prim.ofExit (voidAllOf (reasonsOfVal (exitsVal exits))) = _
  rw [mergeAwaited_eq_mergeExits]

/-- `scope.close-state-first`: the state is written before any finalizer program is built, so
the written state cannot depend on what a finalizer does.
census: scope.close-state-first -/
theorem storesCloseScope_state_first (scope : Nat) (exit : ExitV) (state : Stores)
    (entry : ScopeEntry) (h : state.scopes.entryAt scope = some entry)
    (hopen : entry.scope.isClosed = false) :
    (storesCloseScope scope exit true state).map Prod.fst =
      some { state with scopes := state.scopes.closeState scope exit } ∧
    (storesCloseScope scope exit false state).map Prod.fst =
      some { state with scopes := state.scopes.closeState scope exit } := by
  constructor <;>
    · simp only [storesCloseScope, h, hopen, Bool.false_eq_true, if_false]
      split <;> rfl

/-- M7: an unknown scope key is a frontier, not a cause — the hook answers `none` and the
machine halts with `Stuck.unknownScope`. -/
theorem storesCloseScope_unknown (scope : Nat) (exit : ExitV) (masked : Bool) (state : Stores)
    (h : state.scopes.entryAt scope = none) :
    storesCloseScope scope exit masked state = none := by
  simp [storesCloseScope, h]

/-- `scope.fork-linkage`: the linked names *are* `scopeClose(child, exit)` on the parent side
and `scopeRemoveFinalizerUnsafe(parent, key)` on the child side, under one shared key — the
clause `RuntimeCoverage.lean:3096` says needs a scope store.
census: scope.fork-linkage -/
theorem scopeStore_forkChild_names (self : ScopeStore) (parentKey childKey sharedKey : Nat)
    (strategy : FinalizerStrategy) (parent : ScopeEntry)
    (h : self.entryAt parentKey = some parent) (hopen : parent.scope.closingExit? = none) :
    (self.forkChild parentKey childKey sharedKey strategy).entries =
      (self.setEntry { parent with
          scope := parent.scope.addUnsafe sharedKey (FinName.closeChildScope childKey) }).entries ++
        [⟨childKey,
          (Effect4.Scope.make strategy : ScopeV).addUnsafe sharedKey
            (FinName.detachFromParent parentKey sharedKey)⟩] := by
  simp [ScopeStore.forkChild, h, Effect4.Scope.fork, hopen]

/-- `scope.fork-linkage`: the fiber finalizer `forkIn` registers is the self-guarded
"interrupt fiber `f`" name (`internal/effect.ts:5370`).
census: scope.fork-linkage, fork.scope-linkage -/
theorem scopeLinkFiber_name (scope key : Nat) (fiber : FiberId) (state : Stores)
    (entry : ScopeEntry) (h : state.scopes.entryAt scope = some entry) :
    stores.scopeLinkFiber Supervision.ScopeMode.forkIn scope key fiber state =
      some { state with
        scopes :=
          (state.scopes.addFinalizer scope key (FinName.interruptFiber fiber true)).1 } := by
  simp [stores, h]

/-- M4: `fiberRunIn` registers the *unguarded* finalizer (`internal/effect.ts:5458`).
census: scope.fork-linkage -/
theorem scopeLinkFiber_runIn_name (scope key : Nat) (fiber : FiberId) (state : Stores)
    (entry : ScopeEntry) (h : state.scopes.entryAt scope = some entry) :
    stores.scopeLinkFiber Supervision.ScopeMode.fiberRunIn scope key fiber state =
      some { state with
        scopes :=
          (state.scopes.addFinalizer scope key (FinName.interruptFiber fiber false)).1 } := by
  simp [stores, h]

/-- M7 again: linking into an unknown scope is a frontier. -/
theorem scopeLinkFiber_unknown (mode : Supervision.ScopeMode) (scope key : Nat)
    (fiber : FiberId) (state : Stores) (h : state.scopes.entryAt scope = none) :
    stores.scopeLinkFiber mode scope key fiber state = none := by
  simp [stores, h]

/-- The fiber finalizer compiles to `WithFiberAction.interruptScoped`, whose machine arm is
"interrupt unless the interruptor is the fiber itself, then await" (`:5369-5371`).
census: scope.fork-linkage -/
theorem interruptFiber_compiles_to_interruptScoped (fiber : FiberId) (exit : ExitV) :
    finProgram (FinName.interruptFiber fiber true) exit =
      Prim.withFiber (Thunk.act (ActionName.interruptScoped fiber)) := rfl

/-! ## Separation gates at this instantiation

`docs/FRAMES-DAG.md` separation 4: names stay data. The gates of `Deep.Fibers` must keep
holding when the alphabets are the concrete ones above. -/

example : DecidableEq Val := inferInstance
example : DecidableEq Name := inferInstance
example : DecidableEq Thunk := inferInstance
example : DecidableEq Program := inferInstance
example : DecidableEq Stores := inferInstance
example : DecidableEq (RunFiber Name Thunk Val Err Defect FiberId Ann Ctx) := inferInstance
example : DecidableEq (RunDecision Name Thunk Val Err Defect FiberId Ann) := inferInstance
example :
    DecidableEq (WithFiberAction Name Thunk Val Err Defect FiberId Ann Ctx) := inferInstance
example : DecidableEq (RunEvent Name Thunk Val Err Defect FiberId Ann Ctx) := inferInstance

end Effect4.Deep
