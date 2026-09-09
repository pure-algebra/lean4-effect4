import Effect4.Machine.Fibers
import Effect4.Machine.Scope
import Effect4.Machine.Value
import Effect4.Machine.ContextMap
import Effect4.Machine.Wake
import Effect4.Machine.Timer

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
(`src/Effect4/Machine/Frames.lean:188-215`, DB-02).

The three stores:

* `RefHeap` — `Ref.ts`. A `List Val` plus a `RefKey` index. `ref.make` is `Effect.sync` over
  the constructor (`Ref.ts:173`), so every operation is one `refStep` under `Prim.sync`.
* `DeferredStore` — `Deferred.ts`. A completion slot that is `none` or exactly one *primitive*,
  a registration-ordered waiter list of `(FiberId × token)`, and the resume queue a completion
  owes (`Deferred.ts:1655-1659`).
* `ScopeStore` — keyed `Effect4.Scope`s, reused unchanged (`src/Effect4/Machine/Scope.lean`),
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

namespace Effect4.Machine

open Effect4

-- `DeferredKey`, a cell of the Deferred store, lives in `Machine/Wake.lean` (the scheduler
-- surface, 2026-09-08), below the fiber machine, so a task can name a Deferred's waiter list.

/-! ## The alphabets

Every alphabet is first-order and derives `DecidableEq`, which the separation gates of
`Deep.Fibers` (`docs/research/FRAMES-DAG.md` separation 4) need at this instantiation.
The generic Completion data and its Ref key are shared through `Machine.Completion`. -/

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
  /-- `Context.get` on a missing service (`forkScoped` with no ambient `Scope`,
  `internal/effect.ts:5400-5406`); finding S1-1, 2026-09-04. -/
  | missingService
  /-- A user defect, `Effect.die(d)` with a numeric payload (the `Eff` compile's `die`). -/
  | user (payload : Nat)
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

/-- The fiber `Context` (rc.112 `fiber.context`, `internal/effect.ts:2152`): the service map
(`Machine/ContextMap.lean`) and the two budget fields `setContext` caches off it (`:726-727`).
The ambient `Scope` service is read off the map (`forkScoped`, `:5400-5406`; `Ctx.ambientScope`),
cached nowhere; the two caches are stored because rc.112 stores them, and `Ctx.withServices`,
which recomputes them, is the one constructor the runtime calls, so the join's cache law
(`Ctx.CacheAgrees`) holds by construction (`docs/research/2026-09-07-join-dispatch.md` §2). The
law is not a field: a proof field would put `Env.budgetOf` inside the type and its `match` on
the carrier (`propext`) into the receipt of every theorem naming a `Ctx`. -/
structure Ctx where
  /-- The service map. -/
  services : Env.Ctx
  /-- `MaxOpsBeforeYield`, as `setContext` caches it. -/
  maxOpsBeforeYield : Nat
  /-- `PreventSchedulerYield`, as `setContext` caches it. -/
  preventYield : Bool
deriving DecidableEq, Repr, Inhabited

namespace Ctx

/-- The one constructor: the caches recomputed off the map (`setContext`, `:726-727`). -/
def withServices (services : Env.Ctx) : Ctx :=
  ⟨services, (Env.budgetOf services).1, (Env.budgetOf services).2⟩

/-- `forkScoped`'s read of the `Scope` service (`:5406`): a lookup, cached nowhere. -/
def ambientScope (c : Ctx) : Option Nat := Env.ambientScope c.services

/-- The cache law: the join's composition law (`probe-u1b-layer-join.md` §3.5). Every context
`withServices` builds satisfies it (`withServices_cacheAgrees`). -/
def CacheAgrees (c : Ctx) : Prop := (c.maxOpsBeforeYield, c.preventYield) = Env.budgetOf c.services

instance (c : Ctx) : Decidable c.CacheAgrees := by unfold CacheAgrees; infer_instance

theorem withServices_cacheAgrees (services : Env.Ctx) : (withServices services).CacheAgrees := rfl

/-- `provideService`'s region write (`internal/effect.ts:2232`, `Context.add(key, impl)`). -/
def provide (c : Ctx) (key : ServiceKey) (value : Effect4.Store.Val) : Ctx :=
  withServices (c.services.addV key value)

/-- `scoped`'s install (`internal/effect.ts:3942`, `Context.add(fiber.context, scopeTag, scope)`). -/
def withScope (c : Ctx) (scope : Nat) : Ctx := c.provide Env.scopeKey (Value.scope scope)

theorem withServices_services (services : Env.Ctx) : (withServices services).services = services :=
  rfl

theorem provide_services (c : Ctx) (key : ServiceKey) (value : Effect4.Store.Val) :
    (c.provide key value).services = c.services.addV key value := rfl

/-- The install is what `ambientScope` reads back (`Env.ambientScope_add_scope`). -/
theorem ambientScope_withScope (c : Ctx) (scope : Nat) :
    (c.withScope scope).ambientScope = some scope :=
  Env.ambientScope_add_scope c.services scope

end Ctx

/-- A compiled release, captured at registration (`internal/effect.ts:3976,3983`): the
point's path and environment (the acquired value already appended), its fuel and tape, and
the context `contextWith` read, under which the release runs. First-order; the compiler
resolves it (`Program/Compile.lean`, `suspendBodyAt`). It is `Point` minus the completed-exit
view plus the context (`Point.ofCapture` is the isomorphism), so it carries the point's
`root` too (direction-scout D6). -/
structure Capture where
  path : List Nat
  env : List Effect4.Store.Val
  fuel : Nat
  tape : List Bool
  ctx : Ctx
  /-- The root program the path addresses; `0` until a machine holds more than one. -/
  root : Nat := 0
deriving DecidableEq, Repr

/-- A layer, by the path of its node from the root program (`Program/Compile.lean`'s `Node`;
the join, `docs/research/2026-09-07-join-dispatch.md` §4): layers are program subterms
addressed by path, never a table. The memo world keys on it, and two evaluations of one site
under two memo maps are two entries — the path is the key, never an identity. -/
abbrev LayerId := List Nat

/-- A `MemoMapImpl` (`Layer.ts:421-432`), by allocation order from the one supply. -/
structure MemoMapId where
  index : Nat
deriving DecidableEq, Repr

/-- The scope finalizer *name* alphabet. `Effect4.Scope` stores a `φ`; giving `φ` these arms is
what lets a finalizer name *mean* an operation on another scope or on a fiber — the open half of
`SCOPE-FB-FINALIZER-MEANING` (`docs/research/SCOPE-DAG.md:228`). -/
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
  /-- `awaitAllChildren`'s finalizer (`internal/effect.ts:5319-5333`, R2-7): await the
  children added since the snapshot, on any exit, under the finalizer mask. -/
  | awaitNewChildren (snapshot : List FiberId)
  /-- A release that parks on an external async before it completes: the observable a masked
  finalizer needs, since `onExit`'s `contAll` masks the fiber while the finalizer runs
  (`src/Effect4/Machine/Frames.lean:560-565`, rc.112 `internal/effect.ts:4021`). -/
  | parkThen (slot : Nat)
  /-- A compiled `acquireRelease` release (`internal/effect.ts:3983`): the capture the compile
  route resolves when the scope closes, on whichever fiber closes it (V1, 2026-09-07). -/
  | foreign (capture : Capture)
  /-- `fromBuild`'s `onExit` (`Layer.ts:343`): close the layer scope only on `Failure` (join). -/
  | closeChildOnFailure (scope : Nat)
  /-- The memo entry finalizer (`Layer.ts:401-410`), registered on every observer's caller
  scope: `observers--`, the last observer closing the layer scope with the exit (join). -/
  | memoEntry (layer : LayerId) (memoMap : MemoMapId)
  /-- `memoMapBuild`'s `onExit` (`Layer.ts:414-417`): store the exit, complete the Deferred
  (join). -/
  | memoDone (layer : LayerId) (memoMap : MemoMapId)
deriving DecidableEq, Repr

/-! ## The alphabets as values

The one value alphabet is the shared carrier `Effect4.Store.Val` (U1,
`docs/research/2026-09-07-u1-cutover-dispatch.md`, on the U0 contract
`docs/research/2026-09-07-u0-value-foundation.md`). The alphabets above are written on it at
the generated rule of `Machine/Value.lean`: a case of a sum is `ctor i [args…]` with `i` the
declaration index, a structure is `ctor 0 [fields…]`, a handle is a `handle` frame with its
`HandleKind` byte. These images are what the runtime reads and writes at the semantic sites
below (`reifyExitVal`, `contAOf`, the action decode of `Program/Compile.lean`); nothing in the
tree builds a second value representation. -/

open Effect4.Store (Image)

def ofErr : Store.Val → Option Err
  | .ctor 0 [] => some .boom
  | .ctor 1 [.nat c] => some (.tag c)
  | _ => none

/-- `Err` at the generated rule: `boom` is `ctor 0 []`, `tag c` is `ctor 1 [nat c]`. -/
def Err.image : Image Err where
  toVal
    | .boom => .ctor 0 []
    | .tag c => .ctor 1 [.nat c]
  ofVal := ofErr
  ofVal_toVal e := by cases e <;> rfl
  ofVal_exact := by
    intro v e h
    unfold ofErr at h
    split at h <;> first | (injection h with h; subst h; rfl) | exact nomatch h

theorem Err.image_handleFree : Image.HandleFree Err.image := by
  intro e
  cases e <;> rfl

def ofDefect : Store.Val → Option Defect
  | .ctor 0 [] => some .notImplemented
  | .ctor 1 [] => some .asyncFiber
  | .ctor 2 [] => some .badName
  | .ctor 3 [] => some .missingService
  | .ctor 4 [.nat n] => some (.user n)
  | _ => none

/-- `Defect` at the generated rule, in declaration order; `user n` is `ctor 4 [nat n]`. -/
def Defect.image : Image Defect where
  toVal
    | .notImplemented => .ctor 0 []
    | .asyncFiber => .ctor 1 []
    | .badName => .ctor 2 []
    | .missingService => .ctor 3 []
    | .user n => .ctor 4 [.nat n]
  ofVal := ofDefect
  ofVal_toVal d := by cases d <;> rfl
  ofVal_exact := by
    intro v d h
    unfold ofDefect at h
    split at h <;> first | (injection h with h; subst h; rfl) | exact nomatch h

theorem Defect.image_handleFree : Image.HandleFree Defect.image := by
  intro d
  cases d <;> rfl

/-- The cause carrier at this instantiation. -/
abbrev CauseV := Cause Err Defect FiberId Ann

/-- The cause carrier as a value (`Ann = Unit`): the reason list under `ctor 0`, each reason
at the generated rule, the interruptor recorded as a fiber *identity*
(`Value.fiberIdentity`, `ctor 0 [nat]`), never as a handle — a reified failed exit carries a
cause only, and `Val.keys` counts nothing in it (`causeImage_handleFree`). -/
def causeImage : Image CauseV :=
  Value.cause Err.image Defect.image Value.fiberIdentity Image.unit

theorem causeImage_handleFree : Image.HandleFree causeImage :=
  Value.cause_handleFree _ _ _ _ Err.image_handleFree Defect.image_handleFree
    Value.fiberIdentity_handleFree Image.unit_handleFree

/-- A `Ref` cell as a value (`Value.cell`, kind 2). -/
def cellHandle : Image RefKey :=
  (HandleKind.handleOf .cell).equiv RefKey.mk RefKey.index (fun _ => rfl) (fun _ => rfl)

/-- A `Deferred` cell as a value (`Value.promise`, kind 3). -/
def promiseHandle : Image DeferredKey :=
  (HandleKind.handleOf .promise).equiv DeferredKey.mk DeferredKey.index (fun _ => rfl)
    (fun _ => rfl)

/-- A scope-store key as a value (`Value.scope`, kind 4). -/
def scopeKeyHandle : Image Nat := HandleKind.handleOf .scope

/-- A context read off a `fiberContext` frame: the service spine at `Env.decode`, and the two
caches as written; any other shape is no context. -/
def ofCtx : Store.Val → Option Ctx
  | Value.fiberContext spine (.nat maxOps) (.bool prevent) =>
    (Env.decode spine).map fun services => ⟨services, maxOps, prevent⟩
  | _ => none

/-- `Ctx` as a value: `Value.fiberContext`, i.e. `ctor 2 [service spine, nat, bool]` — the
same constructor and arity as before the join, the first field the spine of
`Env.contextImage` (`Value.serviceContext`) where it was an option of a scope handle. `Ctx.keys`
(`Machine/Handles.lean`) counts the handles of every service value. -/
def ctxImage : Image Ctx where
  toVal c :=
    Value.fiberContext (Env.encode c.services) (.nat c.maxOpsBeforeYield) (.bool c.preventYield)
  ofVal := ofCtx
  ofVal_toVal c := by
    obtain ⟨s, m, p⟩ := c
    show (Env.decode (Env.encode s)).map (fun services => (⟨services, m, p⟩ : Ctx)) =
      some ⟨s, m, p⟩
    rw [Env.decode_encode]
    rfl
  ofVal_exact := by
    intro v c hv
    unfold ofCtx at hv
    split at hv
    · next spine m p =>
      obtain ⟨services, hs, hj⟩ := Image.map_eq_some_inv hv
      subst hj
      show Store.Val.ctor 2 [spine, .nat m, .bool p] =
        Store.Val.ctor 2 [Env.encode services, .nat m, .bool p]
      rw [Env.decode_exact hs]
    · exact nomatch hv

theorem ctxImage_toVal (ctx : Ctx) :
    ctxImage.toVal ctx =
      Value.fiberContext (Env.encode ctx.services) (.nat ctx.maxOpsBeforeYield)
        (.bool ctx.preventYield) := rfl

/-! ## The value alphabet -/

/-- The one value alphabet: the shared carrier. rc.112's values at this instantiation are
numbers, booleans and `undefined` (`exitVoid`, `internal/effect.ts:988`); the handles the
stores mint — a `MutableRef` (`Ref.ts:307`, `MutableRef.ts:1063-1070`), a `Deferred`
(`Deferred.ts:140-145`), a `Scope`, a `FiberImpl` (the handle a fork answers);
`fiber.context` (`getContext`); a reified `Exit`, an ordinary value once an `Exit` frame has
caught it (`internal/effect.ts` `exit`); `awaitAllChildren`'s snapshot of `fiber.children`, a
`Set` (`:534`, `:703-704`); and the array `fiberAwaitAll` answers (`:779`, M6). Each is one
shape of the carrier at the table of `Machine/Value.lean`. The spellings below are those
shapes at the old argument types: `Val.cell k` is written where it was, and a pattern
matches `Val.cell ⟨k⟩` (the argument's projection is the one thing a pattern cannot
abstract over). -/
abbrev Val := Effect4.Store.Val

namespace Val

export Effect4.Store.Val (unit nat bool str bytes list pair ctor ref handle)

/-- A reified successful `Exit` (`Value.exitOk`), at this alphabet's type so a dotted
argument (`.exitOk (.cell ⟨k⟩)`) resolves here. -/
@[match_pattern] abbrev exitOk (value : Val) : Val := Value.exitOk value
/-- The handle a fork answers (`Value.fiber`, kind 1). -/
@[match_pattern] abbrev fiber (id : FiberId) : Val := Value.fiber id.value
/-- `Ref.set`'s success value: the `MutableRef` itself (`Ref.ts:307`, `MutableRef.ts:1063-1070`;
`Value.cell`, kind 2). -/
@[match_pattern] abbrev cell (key : RefKey) : Val := Value.cell key.index
/-- A `Deferred` handle (`Deferred.ts:140-145`; `Value.promise`, kind 3). -/
@[match_pattern] abbrev promise (key : DeferredKey) : Val := Value.promise key.index
/-- A `Scope` handle (`Value.scope`, kind 4). -/
@[match_pattern] abbrev scopeHandle (scope : Nat) : Val := Value.scope scope
/-- A `MemoMap` handle (`Layer.ts:421-458`; `Value.memoMap`, kind 5; the join). -/
@[match_pattern] abbrev memoMap (id : MemoMapId) : Val := Value.memoMap id.index
/-- The empty list of awaited exits (`fiberAwaitAll`, `internal/effect.ts:779`; M6): the
carrier's empty `list`. One exit list is one `list` frame; there is no cons arm. -/
@[match_pattern] abbrev exitNil : Val := .list []
/-- `awaitAllChildren`'s snapshot: the fiber handles under `Value.fiberSnapshot`, distinct
from a list of exits (rc.112's `fiber.children` is a `Set`, `internal/effect.ts:534`). -/
abbrev fibers (ids : List FiberId) : Val :=
  Value.fiberSnapshot ((Image.list Value.fiberHandle).toVal ids)
/-- The fiber a fiber handle names; `none` on any other shape. A decidable case split on
the shape (`cases h : v.fiber?`) is how a proof reads the handle off a value. -/
def fiber? : Val → Option FiberId
  | Value.fiber index => some ⟨index⟩
  | _ => none
/-- The scope key a scope handle names; `none` on any other shape. -/
def scope? : Val → Option Nat
  | Value.scope index => some index
  | _ => none
/-- The snapshot read back: `none` unless the value is a snapshot of fiber handles. -/
def snapshot? : Val → Option (List FiberId)
  | Value.fiberSnapshot handles => (Image.list Value.fiberHandle).ofVal handles
  | _ => none
/-- `fiber.context` as a value (`getContext`): `ctxImage`. -/
abbrev context (ctx : Ctx) : Val := ctxImage.toVal ctx
/-- A context read back; `none` on any other shape. -/
def context? : Val → Option Ctx := ctxImage.ofVal
/-- A reified failed `Exit`: the cause written by `causeImage` under `Value.exitErr`. -/
abbrev exitErr (cause : CauseV) : Val := Value.exitErr (causeImage.toVal cause)
/-- The cause of a reified failed exit read back; `none` on any other shape. -/
def cause? : Val → Option CauseV
  | Value.exitErr written => causeImage.ofVal written
  | _ => none

theorem fiber?_fiber (id : FiberId) : fiber? (fiber id) = some id := rfl

theorem fiber?_exact {v : Val} {id : FiberId} (h : fiber? v = some id) : v = fiber id := by
  unfold fiber? at h
  split at h
  · injection h with h
    subst h
    rfl
  · exact nomatch h

theorem fiber?_none {v : Val} (h : fiber? v = none) (id : FiberId) : v ≠ fiber id := by
  intro hv
  subst hv
  exact nomatch h

theorem scope?_scopeHandle (s : Nat) : scope? (scopeHandle s) = some s := rfl

theorem scope?_exact {v : Val} {s : Nat} (h : scope? v = some s) : v = scopeHandle s := by
  unfold scope? at h
  split at h
  · injection h with h
    subst h
    rfl
  · exact nomatch h

theorem scope?_none {v : Val} (h : scope? v = none) (s : Nat) : v ≠ scopeHandle s := by
  intro hv
  subst hv
  exact nomatch h

/-- The memo map a memo-map handle names (the join); `none` on any other shape. -/
def memoMap? : Val → Option MemoMapId
  | Value.memoMap index => some ⟨index⟩
  | _ => none

theorem memoMap?_memoMap (id : MemoMapId) : memoMap? (memoMap id) = some id := rfl

theorem memoMap?_exact {v : Val} {id : MemoMapId} (h : memoMap? v = some id) : v = memoMap id := by
  unfold memoMap? at h
  split at h
  · injection h with h
    subst h
    rfl
  · exact nomatch h

theorem memoMap?_none {v : Val} (h : memoMap? v = none) (id : MemoMapId) : v ≠ memoMap id := by
  intro hv
  subst hv
  exact nomatch h

/-- A memo hit read back (`SyncOp.memoGet`'s answer on a hit: the entry's deferred and its
owning map, `Layer.ts:439-440`); `none` on any other shape. -/
def memoHit? : Val → Option (DeferredKey × MemoMapId)
  | .pair (Value.promise c) (Value.memoMap o) => some (⟨c⟩, ⟨o⟩)
  | _ => none

theorem memoHit?_pair (c : DeferredKey) (o : MemoMapId) :
    memoHit? (.pair (promise c) (memoMap o)) = some (c, o) := by
  cases c; cases o; rfl

theorem memoHit?_exact {v : Val} {c : DeferredKey} {o : MemoMapId}
    (h : memoHit? v = some (c, o)) : v = .pair (promise c) (memoMap o) := by
  unfold memoHit? at h
  split at h
  · injection h with h
    injection h with h₁ h₂
    subst h₁ h₂
    rfl
  · exact nomatch h

theorem memoHit?_none {v : Val} (h : memoHit? v = none) (c : DeferredKey) (o : MemoMapId) :
    v ≠ .pair (promise c) (memoMap o) := by
  intro hv
  subst hv
  cases c; cases o
  exact nomatch h

theorem fibers_eq (ids : List FiberId) :
    fibers ids = Value.fiberSnapshot (.list (ids.map fun id => Value.fiber id.value)) := rfl

theorem snapshot?_fibers (ids : List FiberId) : snapshot? (fibers ids) = some ids :=
  (Image.list Value.fiberHandle).ofVal_toVal ids

theorem snapshot?_exact {v : Val} {ids : List FiberId} (h : snapshot? v = some ids) :
    v = fibers ids := by
  unfold snapshot? at h
  split at h
  · next handles =>
    show Store.Val.ctor 3 [handles] = Store.Val.ctor 3 [(Image.list Value.fiberHandle).toVal ids]
    rw [(Image.list Value.fiberHandle).ofVal_exact h]
  · exact nomatch h

theorem context_eq (ctx : Ctx) :
    context ctx =
      Value.fiberContext (Env.encode ctx.services) (.nat ctx.maxOpsBeforeYield)
        (.bool ctx.preventYield) := rfl

theorem context?_context (ctx : Ctx) : context? (context ctx) = some ctx :=
  ctxImage.ofVal_toVal ctx

theorem context?_exact {v : Val} {ctx : Ctx} (h : context? v = some ctx) : v = context ctx :=
  ctxImage.ofVal_exact h

theorem cause?_exitErr (c : CauseV) : cause? (exitErr c) = some c :=
  causeImage.ofVal_toVal c

theorem cause?_exact {v : Val} {c : CauseV} (h : cause? v = some c) : v = exitErr c := by
  unfold cause? at h
  split at h
  · next written =>
    show Store.Val.ctor 1 [written] = Store.Val.ctor 1 [causeImage.toVal c]
    rw [causeImage.ofVal_exact h]
  · exact nomatch h

/-- The carrier's own image: the identity. -/
def image : Image Val := ⟨id, some, fun _ => rfl, fun h => Option.some.inj h⟩

end Val

/-- The exit carrier at this instantiation. -/
abbrev ExitV := Exit Val Err Defect FiberId Ann

/-- The exit carrier a finalizer produces (`combineFinalizerCause`, `internal/effect.ts:3800-3804`). -/
abbrev VoidExitV := Exit Unit Err Defect FiberId Ann

/-- The exit carrier as a value (`Value.exit`): `Exit.success v` is `Value.exitOk v`,
`Exit.failure c` is `Val.exitErr c`. One encoding serves the reified value and the exit record
(D1 of the U0 record). -/
def exitImage : Image ExitV := Value.exit Val.image causeImage

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
  | deferredCompleteWith (cell : DeferredKey) (completion : Completion Val Err Defect FiberId Ann)
  /-- `Deferred.interruptWith` (`Deferred.ts:1332-1337`): `failCause` of `causeInterrupt(id)`. -/
  | deferredInterruptWith (cell : DeferredKey) (interruptor : FiberId)
  /-- `_await`'s cleanup (`Deferred.ts:178-185`): splice this waiter out; a no-op once
  completion has cleared the array. -/
  | deferredAwaitCleanup (cell : DeferredKey) (waiter : FiberId) (token : Nat)
  /-- `clock.currentTimeMillis` (`internal/effect.ts:6043`; `testing/TestClock.ts:262`): the
  logical clock, read (the timer, A4). -/
  | clockNow
  /-- `clearTimeout(handle)` (`internal/effect.ts:6063`): this fiber's sleep under this token
  removed; a no-op once it fired. -/
  | sleepCancel (waiter : FiberId) (token : Nat)
  /-- `scopeMakeUnsafe` (`internal/effect.ts:3914-3922`). -/
  | scopeMake (strategy : FinalizerStrategy)
  /-- `scopeAddFinalizerExit` (`internal/effect.ts:3846-3858`): the registration key is
  allocated by the step from the store's supply (`const key = {}`, `:3855`), as
  `scopeLinkFiber` allocates its own (`E4-CHECK-CE-016`); a closed scope answers its closing
  exit instead (`:3851-3853`), an unknown one is a frontier. -/
  | scopeAdd (scope : Nat) (finalizer : FinName)
  /-- `scopeRemoveFinalizerUnsafe` (`internal/effect.ts:3890-3904`). -/
  | scopeRemove (scope : Nat) (key : Nat)
  /-- Whether a scope has closed (`Scope.ts:99-187`). -/
  | scopeIsClosed (scope : Nat)
  /-- `scopeForkUnsafe(parent, strategy)` (`internal/effect.ts:3834-3844`): the child under a
  fresh key, linked to the parent under a shared registration key, both from the supply;
  answers the child's handle. An unknown parent is a frontier (join). -/
  | scopeFork (parent : Nat) (strategy : FinalizerStrategy)
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
deriving DecidableEq

/-- The declared race shapes. A `List ProgName` field would make `ProgName` a *nested*
inductive, whose `DecidableEq` handler refuses (state note §3.5); a race is therefore named and
`raceEntrants` gives it meaning. -/
inductive RaceName
  /-- `raceAll([])`: pending until interrupted
  (`Test/fixtures/traces/fiber-m3/emptyRacePendingUntilInterrupted.tsv`). -/
  | empty
  /-- An immediate success followed by a second entrant that is never launched
  (`Test/fixtures/traces/fiber-m3/raceImmediateSuccessStopsLaunch.tsv`). -/
  | successThenSecond
  /-- A failure followed by a success
  (`Test/fixtures/traces/fiber-m3/raceFailureAllowsNextLaunch.tsv`). -/
  | failThenSuccess
  /-- Two failures, retained in order
  (`Test/fixtures/traces/fiber-m3/raceAllFailuresRetainOrder.tsv`). -/
  | failThenFail
  /-- One entrant that parks on an external async: the host's interrupt reaches it through
  the race park's cleanup (`internal/effect.ts:1530`, R2-13). -/
  | parkOnly
  /-- A parked loser and an immediate winner: the settle interrupts the loser on the host,
  under a mask (`:1510-1514`, R2-12). -/
  | parkThenSuccess
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
  /-- `forkIn` (`:5364-5378`). The registration identity is not part of the name: the store
  allocates it at the executed registration (`:5366`, `E4-CHECK-CE-016`). -/
  | forkInScope (child : ProgName) (options : Supervision.ForkOptions) (scope : Nat)
  /-- `fiberRunIn` (`:5447-5461`): bind an *existing* fiber to a scope. Its closed-scope arm
  interrupts with `self.id` and no caller annotations (`:5454`), unlike `forkIn`'s (M10). -/
  | runInScope (target : FiberId) (scope : Nat)
  /-- `forkScoped` (`:5400-5406`). -/
  | forkScopedOf (child : ProgName) (options : Supervision.ForkOptions)
  /-- `raceAll` (`Supervision.RaceAllState`). -/
  | raceOf (race : RaceName)
  /-- `scopeClose(scope, exit)` from the fiber (`internal/effect.ts:3826` via the store). -/
  | closeScopeOf (scope : Nat) (exit : ExitV)
  /-- `awaitAllChildren(body)` (`:5314-5322`). -/
  | awaitAllNew (body : ProgName)
  /-- `fiberInterruptAll(targets)` (`:889-896`): the settled race's cleanup half (R2-12). -/
  | interruptFibers (targets : List FiberId)
  /-- The masked cleanup half of a settled race: `fiberInterruptAll(fibers)` over the race's
  live set *at cleanup time* (`internal/effect.ts:1510-1514`, D6a). -/
  | cancelRace (race : Nat)
  /-- `fiberJoin`/`fiberAwait` on an existing handle (`:5291`, `:5304`). -/
  | joinFiber (target : FiberId) (mode : Supervision.ObserverMode)
  /-- `scopeCloseFinalizers(scope, exit)` (`internal/effect.ts:3806-3827`, source-repairs
  §20): the close of two or more finalizers, a `fnUntraced` generator walked by the counted
  `Iterator` — sequential through the `Exit` primitive per finalizer, parallel as immediate
  daemons awaited together. -/
  | closeWalk (strategy : FinalizerStrategy) (order : List FinName) (exit : ExitV)
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
  /-- contA on a numeric ID (`Val.nat`): `Deferred.interrupt`'s second half (`Deferred.ts:1231-1232`). -/
  | interruptWith (cell : DeferredKey)
  /-- contA on a reified `Exit`: `into`'s completion (`Deferred.ts:1781`). -/
  | doneInto (cell : DeferredKey)
  /-- contA/contE: answer a constant. -/
  | constant (value : Val)
  /-- contA on a reified `Exit`: turn it back into an effect. -/
  | exitOfValue
  /-- contA on the snapshot value: `onExit(self, …)` — run the body, and on any exit await
  the children added since (`:5319-5333`, R2-7). -/
  | snapshotThen (body : ProgName)
  /-- `register(resume, signal)` for `Deferred.await` (`Deferred.ts:173-177`). -/
  | registerAwait (cell : DeferredKey)
  /-- `_await`'s cleanup name (`Deferred.ts:178-185`): the cancel effect the registration
  returned, which the `AsyncFinalizer` frame's `contE` runs. -/
  | cancelAwait (cell : DeferredKey)
  /-- `register(resume, signal)` for `Effect.sleep(d)`, `0 < d < ∞` (`internal/effect.ts:6057-6062`,
  the timer, A4): the sleep registered at its deadline; nothing is answered at once. -/
  | registerSleep (millis : Nat)
  /-- `clearTimeout` (`internal/effect.ts:6063`): the cancel effect a sleep's registration
  returned. -/
  | cancelSleep
  /-- An external `register` the store never answers. -/
  | externalRegister (slot : Nat)
  /-- `RunInterp.abortName`: the cancel of an `Async` that asked for a controller and returned
  no cancel effect (`internal/effect.ts:1134-1140`). -/
  | abortController
  /-- `RunInterp.parkCancelName`: a fiber-observer park's cleanup (`fiberJoin`/`fiberAwait`,
  `:773`, `:821`; `fiberAwaitAll`, `:812`), R2-3. -/
  | cancelPark
  /-- `RunInterp.raceCancelName race`: the race park's cleanup, `fiberInterruptAll(fibers)`
  (`:1530`), R2-13. -/
  | cancelRace (race : Nat)
  /-- `RunInterp.cancelName base waiter token` (M3): the cancel name with the identity of the
  fiber that parked and the token it parked on, which is what `_await`'s cleanup needs to
  splice the right resume out (`Deferred.ts:181-184`). -/
  | withWaiter (base : Name) (waiter : FiberId) (token : Nat)
  /-- `PrimInterp.cancelThenFail`'s tail: `() => failCause(cause)`
  (`internal/effect.ts:1157`). -/
  | reFail (cause : CauseV)
  /-- A scope finalizer name, carried by an `OnExit` frame. -/
  | finalizerName (fin : FinName)
  /-- The sequential close generator (`internal/effect.ts:3813-3818`, §20), the iterator
  frame's name: the remaining finalizers, the closing exit, and the reasons captured so far. -/
  | closeSeq (remaining : List FinName) (exit : ExitV)
      (captured : List (Reason Err Defect FiberId Ann))
  /-- The parallel close generator under its await (`internal/effect.ts:3823-3826`, §20; M6):
  the frame's next step is `exitAsVoidAll` of the exits the `awaitAll` park answered with. -/
  | closeParDone
  /-- `memoEntry`'s continuation after `memoRelease` (`Layer.ts:403-408`, the join): the last
  observer's release answers the layer scope, closed with the exit; any other answer is done. -/
  | closeIfLast (exit : ExitV)
deriving DecidableEq

/-- What a `withFiber` thunk names. The machine's `WithFiberAction` carries `Prim`s; a thunk
cannot, so the alphabet carries `ProgName` and `withFiberOf` expands. -/
inductive ActionName
  | fork (program : ProgName) (options : Supervision.ForkOptions)
  | forkIn (program : ProgName) (options : Supervision.ForkOptions) (scope : Nat)
  | forkScoped (program : ProgName) (options : Supervision.ForkOptions)
  /-- The `Scope` service read (`Context.ts:423`, source-repairs §20): the ambient scope's
  handle as a value. -/
  | ambientScope
  | runIn (target : FiberId) (scope : Nat)
  | interrupt (target : FiberId)
  /-- `fiberInterruptAs(target, who)` (`internal/effect.ts:871-884`): what the public
  interrupt's `withFiber` returns (source-repairs §19, D6b). -/
  | interruptAs (target : FiberId) (who : FiberId)
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
  /-- A fiber-observer park's cleanup (R2-3). -/
  | dropObservers (token : Nat)
  /-- The race park's cleanup (R2-13). -/
  | cancelRace (race : Nat)
  /-- The parallel close's generator step (`internal/effect.ts:3819-3824`, §20): every
  finalizer of the close order, at the closing exit, forked as an immediate daemon in the
  closer's mask, then awaited under the generator's frame. -/
  | closePar (order : List FinName) (exit : ExitV)
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
  /-- The delayed release of a compiled `acquireRelease`: the capture and the exit the scope
  closed with. The bare stores answer `notImplemented` for it (`stores.suspendBody`); the
  compile route resolves it (`Program/Compile.lean`, `suspendBodyAt`). -/
  | foreign (capture : Capture) (exit : ExitV)
deriving DecidableEq

/-- The program carrier at this instantiation. -/
abbrev Program := Prim Name Thunk Val Err Defect FiberId Ann

/-! ## The memo world (`Layer.ts:235-239`, `:421-458`)

The Layer machine's memo store, joined into the one `Stores`
(`docs/research/2026-09-07-join-dispatch.md` §3; `MemoEntry`, `MemoMap`, `MemoWorld` and its two
laws are `Machine/Layer.lean`'s, verbatim; that file retired with the join, `git:4aae12f`). A memo map is keyed by `LayerId`, the layer's path:
inserting under one path leaves every other path's entry untouched (`find?_append_other_key`),
and memo identity is allocation, never a description. The build's in-flight cell is a Deferred,
never a fiber: the world owns the entries and borrows the Deferred family's wakeup
(`memoComplete` completes the cell; the one `due` drain carries its waiters). -/

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

/-- `LAYER-FB-LAYER-IDENTITY`, the `SCOPE-FB-KEY-IDENTITY` shape (`Machine/Scope.lean`): the
memo map is keyed by the layer's path, which is where the layer *is*, never what it says.
Inserting under one path leaves every other path's entry untouched — rc.112 keys on the layer
object (`Layer.ts:411`, `:438`). The model cannot stop a program from forging a path; that
boundary is the refusal row. -/
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

/-- A map that is in the world is found under its id. -/
theorem mapAt_isSome_of_mem {w : MemoWorld} {m : MemoMap} (h : m ∈ w) :
    (w.mapAt m.id).isSome = true := by
  unfold mapAt
  rw [List.find?_isSome]
  exact ⟨m, h, by simp⟩

/-- The map `mapAt` finds is in the world, under the id asked for. -/
theorem mapAt_mem {w : MemoWorld} {id : MemoMapId} {m : MemoMap} (h : w.mapAt id = some m) :
    m ∈ w ∧ m.id = id :=
  ⟨List.mem_of_find?_eq_some h, by simpa using List.find?_some h⟩

/-- An entry `entryAt` finds is one of its map's, under the layer asked for. -/
theorem entryAt_mem {w : MemoWorld} {id : MemoMapId} {layer : LayerId} {entry : MemoEntry}
    (h : w.entryAt id layer = some entry) : ∃ m ∈ w, m.id = id ∧ (layer, entry) ∈ m.entries := by
  unfold entryAt at h
  obtain ⟨m, hm, hfind⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨e, he, hsnd⟩ := Option.map_eq_some_iff.mp hfind
  obtain ⟨hmem, hid⟩ := mapAt_mem hm
  have hkey : e.1 = layer := by simpa using List.find?_some he
  refine ⟨m, hmem, hid, ?_⟩
  have : e = (layer, entry) := Prod.ext hkey hsnd
  rw [← this]
  exact List.mem_of_find?_eq_some he

/-- What `lookup` answers is an entry of some map of the world, under the layer asked for. -/
theorem lookup_mem {w : MemoWorld} {layer : LayerId} :
    ∀ {fuel : Nat} {id owner : MemoMapId} {entry : MemoEntry},
      w.lookup layer fuel id = some (owner, entry) →
        ∃ m ∈ w, m.id = owner ∧ (layer, entry) ∈ m.entries
  | 0, _, _, _, h => nomatch h
  | fuel + 1, id, owner, entry, h => by
    simp only [lookup] at h
    split at h
    · next e he =>
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact entryAt_mem he
    · split at h
      · exact nomatch h
      · split at h
        · exact nomatch h
        · exact lookup_mem h

theorem get_mem {w : MemoWorld} {layer : LayerId} {id owner : MemoMapId} {entry : MemoEntry}
    (h : w.get layer id = some (owner, entry)) : ∃ m ∈ w, m.id = owner ∧ (layer, entry) ∈ m.entries :=
  lookup_mem h

/-- `MemoMapImpl.get` answers its own map first (`Layer.ts:438-442`).
census: layer.memo-map-parent-lookup -/
theorem get_own (w : MemoWorld) (layer : LayerId) (id : MemoMapId) (entry : MemoEntry)
    (h : w.entryAt id layer = some entry) : w.get layer id = some (id, entry) := by
  simp only [MemoWorld.get, MemoWorld.lookup, h]

/-- On a miss in the own map the lookup delegates to the parent (`:443`), so a forked map sees
what its parent built. census: layer.memo-map-parent-lookup -/
theorem get_parent (w : MemoWorld) (layer : LayerId) (id parent : MemoMapId) (m : MemoMap)
    (hmiss : w.entryAt id layer = none) (hmap : w.mapAt id = some m)
    (hparent : m.parent = some parent) :
    w.get layer id = w.lookup layer w.length parent := by
  simp only [MemoWorld.get, MemoWorld.lookup, hmiss, hmap, hparent]

/-- The maps `setMap` leaves: the replacement, or one of the old ones. -/
theorem mem_setMap {w : MemoWorld} {m n : MemoMap} (h : n ∈ w.setMap m) : n = m ∨ n ∈ w := by
  unfold setMap at h
  obtain ⟨n', hn', hnn⟩ := List.mem_map.mp h
  split at hnn
  · exact Or.inl hnn.symm
  · exact Or.inr (hnn ▸ hn')

/-- `setMap` keeps every id: the replacement carries the id it replaces. -/
theorem mapAt_setMap_isSome {w : MemoWorld} {m : MemoMap} {id : MemoMapId}
    (h : (w.mapAt id).isSome = true) : ((w.setMap m).mapAt id).isSome = true := by
  unfold mapAt at h ⊢
  rw [List.find?_isSome] at h ⊢
  obtain ⟨n, hn, hid⟩ := h
  unfold setMap
  refine ⟨if n.id = m.id then m else n, List.mem_map.mpr ⟨n, hn, rfl⟩, ?_⟩
  split
  · next heq =>
    rw [← heq]
    exact hid
  · exact hid

/-- The entries `updateEntry` leaves: an old map's, or an old entry of the updated map, as it
was or through `f`. -/
theorem mem_updateEntry_entries {w : MemoWorld} {id : MemoMapId} {layer : LayerId}
    {f : MemoEntry → MemoEntry} {n : MemoMap} (hn : n ∈ w.updateEntry id layer f)
    {e' : LayerId × MemoEntry} (he' : e' ∈ n.entries) :
    ∃ m ∈ w, ∃ e ∈ m.entries, e' = e ∨ e' = (e.1, f e.2) := by
  unfold updateEntry at hn
  split at hn
  · exact ⟨n, hn, e', he', Or.inl rfl⟩
  · next m hm =>
    rcases mem_setMap hn with rfl | hn
    · obtain ⟨e, he, hee⟩ := List.mem_map.mp he'
      refine ⟨m, (mapAt_mem hm).1, e, he, ?_⟩
      split at hee
      · exact Or.inr hee.symm
      · exact Or.inl hee.symm
    · exact ⟨n, hn, e', he', Or.inl rfl⟩

/-- The entries `insertEntry` leaves: an old one, or the inserted one. -/
theorem mem_insertEntry_entries {w : MemoWorld} {id : MemoMapId} {layer : LayerId}
    {entry : MemoEntry} {n : MemoMap} (hn : n ∈ w.insertEntry id layer entry)
    {e' : LayerId × MemoEntry} (he' : e' ∈ n.entries) :
    (∃ m ∈ w, e' ∈ m.entries) ∨ e' = (layer, entry) := by
  unfold insertEntry at hn
  split at hn
  · exact Or.inl ⟨n, hn, he'⟩
  · next m hm =>
    rcases mem_setMap hn with rfl | hn
    · rcases List.mem_append.mp he' with he' | he'
      · exact Or.inl ⟨m, (mapAt_mem hm).1, he'⟩
      · exact Or.inr (List.mem_singleton.mp he')
    · exact Or.inl ⟨n, hn, he'⟩

/-- The entries `deleteEntry` leaves are old ones. -/
theorem mem_deleteEntry_entries {w : MemoWorld} {id : MemoMapId} {layer : LayerId} {n : MemoMap}
    (hn : n ∈ w.deleteEntry id layer) {e' : LayerId × MemoEntry} (he' : e' ∈ n.entries) :
    ∃ m ∈ w, e' ∈ m.entries := by
  unfold deleteEntry at hn
  split at hn
  · exact ⟨n, hn, he'⟩
  · next m hm =>
    rcases mem_setMap hn with rfl | hn
    · exact ⟨m, (mapAt_mem hm).1, (List.mem_filter.mp he').1⟩
    · exact ⟨n, hn, he'⟩

theorem mapAt_updateEntry_isSome {w : MemoWorld} {id id' : MemoMapId} {layer : LayerId}
    {f : MemoEntry → MemoEntry} (h : (w.mapAt id').isSome = true) :
    ((w.updateEntry id layer f).mapAt id').isSome = true := by
  unfold updateEntry
  split
  · exact h
  · exact mapAt_setMap_isSome h

theorem mapAt_insertEntry_isSome {w : MemoWorld} {id id' : MemoMapId} {layer : LayerId}
    {entry : MemoEntry} (h : (w.mapAt id').isSome = true) :
    ((w.insertEntry id layer entry).mapAt id').isSome = true := by
  unfold insertEntry
  split
  · exact h
  · exact mapAt_setMap_isSome h

theorem mapAt_deleteEntry_isSome {w : MemoWorld} {id id' : MemoMapId} {layer : LayerId}
    (h : (w.mapAt id').isSome = true) : ((w.deleteEntry id layer).mapAt id').isSome = true := by
  unfold deleteEntry
  split
  · exact h
  · exact mapAt_setMap_isSome h

theorem mapAt_append_isSome {w : MemoWorld} {m : MemoMap} {id : MemoMapId}
    (h : (w.mapAt id).isSome = true) : ((w ++ [m]).mapAt id).isSome = true := by
  unfold mapAt at h ⊢
  rw [List.find?_isSome] at h ⊢
  obtain ⟨n, hn, hid⟩ := h
  exact ⟨n, List.mem_append_left _ hn, hid⟩

theorem mapAt_append_self (w : MemoWorld) (m : MemoMap) : ((w ++ [m]).mapAt m.id).isSome = true := by
  unfold mapAt
  rw [List.find?_isSome]
  exact ⟨m, List.mem_append_right _ (List.mem_singleton.mpr rfl), by simp⟩

end MemoWorld

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
    (Store.Val.handle.inj (Option.some.inj h)).2
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
completion is a *primitive*, so `done exit = completeWith (Prim.ofExit exit)` is definitional.
The waiters are the wake protocol's list (`Machine/Wake.lean`, the scheduler surface): payload
`Unit`, policy `broadcast`, mode `now` — a Deferred completes inline and never schedules a
batch. -/
structure DeferredCell where
  /-- `self.effect`: absent, or exactly one stored effect. -/
  completion : Option Program
  /-- `self.resumes`, in registration order: the parked fiber, its resume token, its phase. -/
  wake : WakeList Unit
deriving DecidableEq

/-- The Deferred store: the cells plus the resume queue a completion owes.
`doneUnsafe` clears `resumes` *before* resuming (`Deferred.ts:1655-1656`), so the queue is an
answer of the store step and not a promise. -/
structure DeferredStore where
  /-- Allocated cells, in allocation order. -/
  cells : List DeferredCell
  /-- The resumes owed, in registration order (`Deferred.ts:1657-1658`), every one `now`. -/
  due : List (Owed Program)
deriving DecidableEq

namespace DeferredStore

/-- `Deferred.makeUnsafe` (`Deferred.ts:140-145`): both fields undefined. -/
def make (self : DeferredStore) : DeferredKey × DeferredStore :=
  (⟨self.cells.length⟩, { self with cells := self.cells ++ [⟨none, WakeList.empty⟩] })

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
    | none => (self.setCell cell { c with wake := c.wake.register waiter token () }, none)

/-- `_await`'s cleanup (`Deferred.ts:178-185`): splice this waiter out, order-preserving; a
no-op once completion has cleared the array. The clause's owed wake (`WakeList.cancel`) is a
broadcast's, which reached every waiter: nothing to re-owe. -/
def cancel (self : DeferredStore) (cell : DeferredKey) (waiter : FiberId) (token : Nat) :
    DeferredStore :=
  match self.cellAt cell with
  | none => self
  | some c => self.setCell cell { c with wake := (c.wake.cancel waiter token).1 }

/-- `doneUnsafe` (`Deferred.ts:1648-1662`): a completion attempt answers `false` and changes
nothing when an effect is already stored; otherwise the effect is stored, the waiter list is
*cleared* (`WakeList.wakeAll`, the phase advanced), and every waiter is owed a resume with
that effect in registration order, inline (`WakeMode.now`). -/
def complete (self : DeferredStore) (cell : DeferredKey) (effect : Program) :
    DeferredStore × Bool :=
  match self.cellAt cell with
  | none => (self, false)
  | some c =>
    match c.completion with
    | some _ => (self, false)
    | none =>
      ({ self.setCell cell ⟨some effect, (c.wake.wakeAll).2⟩ with
          due := self.due ++ (c.wake.wakeAll).1.map fun w =>
            ⟨w.fiber, w.token, effect, WakeMode.now⟩ }, true)

/-- The resumes the store owes now, drained in registration order. -/
def drainDue (self : DeferredStore) : List (Owed Program) × DeferredStore :=
  (self.due, { self with due := [] })

/-- A posted batch wake runs on a Deferred's list (`Task.wake (WakeKey.deferred cell)`): the
batch's waiters are owed the stored completion inline; with no completion stored they return
to the pending list, no wake lost. No Deferred operation schedules a batch (a Deferred
completes inline), so this is the protocol's meaning at the store, reached only through a
posted task. -/
def wakeBatch (self : DeferredStore) (cell : DeferredKey) : DeferredStore :=
  match self.cellAt cell with
  | none => self
  | some c =>
    match c.completion with
    | some effect =>
      { self.setCell cell { c with wake := (c.wake.runBatch).2 } with
          due := self.due ++ (c.wake.runBatch).1.map fun w =>
            ⟨w.fiber, w.token, effect, WakeMode.now⟩ }
    | none =>
      self.setCell cell
        { c with wake := { (c.wake.runBatch).2 with
            waiters := (c.wake.runBatch).2.waiters ++ (c.wake.runBatch).1 } }

end DeferredStore

/-! ### The twelve `deferred.*` census clauses, one theorem each -/

/-- `deferred.make`: a fresh cell has no completion and no waiter, and there is no separate
pending tag. census: deferred.make -/
theorem deferredStore_make (self : DeferredStore) :
    self.make =
      (⟨self.cells.length⟩, { self with cells := self.cells ++ [⟨none, WakeList.empty⟩] }) := rfl

/-- `deferred.make`: a cell is exactly a completion slot and a waiter list; there is no third
field. census: deferred.make -/
theorem deferredCell_cases_receipt (c : DeferredCell) :
    c = ⟨c.completion, c.wake⟩ := rfl

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
      (self.setCell cell { c with wake := c.wake.register waiter token () }, none) := by
  simp [DeferredStore.register, h, hc]

/-- `deferred.await`, cleanup half: the cleanup splices exactly this resume out and preserves
the order of the others. census: deferred.await -/
theorem deferredStore_cancel_removes (self : DeferredStore) (cell : DeferredKey)
    (c : DeferredCell) (waiter : FiberId) (token : Nat) (h : self.cellAt cell = some c) :
    ((self.cancel cell waiter token).cellAt cell).map DeferredCell.wake =
      ((self.setCell cell { c with wake := (c.wake.cancel waiter token).1 }).cellAt cell).map
        DeferredCell.wake := by
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
      ({ self.setCell cell ⟨some e, (c.wake.wakeAll).2⟩ with
          due := self.due ++ (c.wake.wakeAll).1.map fun w =>
            ⟨w.fiber, w.token, e, WakeMode.now⟩ }, true) := by
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
  have hset : (self.setCell cell ⟨some e, (c.wake.wakeAll).2⟩).cellAt cell =
      some ⟨some e, (c.wake.wakeAll).2⟩ :=
    deferredStore_setCell_cellAt self cell c ⟨some e, (c.wake.wakeAll).2⟩ h
  simp only [DeferredStore.complete, h, hc]
  simp only [DeferredStore.cellAt, DeferredStore.setCell] at hset ⊢
  simp [hset]

/-- `deferred.complete-with-stores-effect`: a waiter is resumed with *that* effect.
census: deferred.complete-with-stores-effect -/
theorem deferredStore_waiter_receives_stored (self : DeferredStore) (cell : DeferredKey)
    (c : DeferredCell) (e : Program) (waiter : FiberId) (token : Nat) (phase : WakePhase)
    (h : self.cellAt cell = some c) (hc : c.completion = none)
    (hw : c.wake.waiters = [⟨waiter, token, phase, ()⟩]) :
    (self.complete cell e).1.due = self.due ++ [⟨waiter, token, e, WakeMode.now⟩] := by
  simp [DeferredStore.complete, WakeList.wakeAll, h, hc, hw]

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
  /-- The frozen scope state machine (`src/Effect4/Machine/Scope.lean`). -/
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

/-! ### The registration-key bound

rc.112 allocates a brand new object for every open-scope registration (`const key = {}`,
`internal/effect.ts:5366-5372` for `forkIn`/`forkScoped` and `:5457-5460` for
`fiberRunIn`). A `Nat` key cannot be new by construction, so freshness is a property of the
*store*: every registration key any scope holds is below the store's supply, so the supply's
current value is a key no scope holds. `E4-CHECK-CE-016`. -/

/-- Every registration key any scope in this store holds is below `n`. -/
def KeysBelow (self : ScopeStore) (n : Nat) : Prop :=
  ∀ e ∈ self.entries, ∀ k ∈ e.scope.finalizerKeys, k < n

theorem KeysBelow.mono {self : ScopeStore} {n m : Nat} (h : KeysBelow self n) (hle : n ≤ m) :
    KeysBelow self m := fun e he k hk => Nat.lt_of_lt_of_le (h e he k hk) hle

/-- What the bound is for: the bound itself is a key no scope in the store holds. -/
theorem KeysBelow.fresh {self : ScopeStore} {n : Nat} (h : KeysBelow self n) :
    ∀ e ∈ self.entries, n ∉ e.scope.finalizerKeys :=
  fun e he hmem => Nat.lt_irrefl _ (h e he n hmem)

/-- A scope carrying no closing exit is not closed. -/
private theorem not_closed_of_closingExit_none {sc : ScopeV} (h : sc.closingExit? = none) :
    sc.isClosed = false := by
  show sc.state.isClosed = false
  cases hstate : sc.state with
  | empty => rfl
  | openEmpty => rfl
  | openInline _ _ => rfl
  | openMap _ => rfl
  | closed ex =>
    rw [show sc.closingExit? = some ex by
      show sc.state.closingExit? = _; rw [hstate]; rfl] at h
    cases h

/-- An entry of a `setEntry` result is the replacement or one of the originals. -/
theorem mem_setEntry {self : ScopeStore} {entry e : ScopeEntry}
    (he : e ∈ (self.setEntry entry).entries) : e = entry ∨ e ∈ self.entries := by
  obtain ⟨g, hg, rfl⟩ := List.mem_map.mp he
  by_cases hk : g.key = entry.key
  · exact Or.inl (by rw [if_pos hk])
  · exact Or.inr (by rw [if_neg hk]; exact hg)

/-- An entry found under a key carries that key. -/
theorem key_of_entryAt {self : ScopeStore} {key : Nat} {entry : ScopeEntry}
    (h : self.entryAt key = some entry) : entry.key = key := by
  have := List.find?_eq_some_iff_getElem.mp h
  simpa using this.1

/-- Replacing an entry's scope leaves it findable under the same key. -/
theorem setEntry_entryAt (self : ScopeStore) {key : Nat} {entry : ScopeEntry} (sc : ScopeV)
    (h : self.entryAt key = some entry) :
    (self.setEntry { entry with scope := sc }).entryAt key =
      some { entry with scope := sc } := by
  have hkey : entry.key = key := key_of_entryAt h
  show List.find? (fun e => decide (e.key = key))
    (self.entries.map (fun e => if e.key = entry.key then { entry with scope := sc } else e)) = _
  rw [List.find?_map]
  have hcomp : ((fun e => decide (e.key = key)) ∘
      (fun e => if e.key = entry.key then { entry with scope := sc } else e)) =
      (fun e : ScopeEntry => decide (e.key = key)) := by
    funext e
    show decide ((if e.key = entry.key then { entry with scope := sc } else e).key = key) =
      decide (e.key = key)
    by_cases hk : e.key = entry.key
    · rw [if_pos hk, hk]
    · rw [if_neg hk]
  rw [hcomp,
    show List.find? (fun e => decide (e.key = key)) self.entries = some entry from h,
    Option.map_some]
  rw [if_pos (rfl : entry.key = entry.key)]

/-- Registering a key the scope does not hold appends it: the whole prior registration list
is kept. With `Scope.tableInsert`'s replace-on-equal-key semantics this is exactly what a
*fresh* identity buys, and its failure is `E4-CHECK-CE-016`. census: scope.add-finalizer -/
theorem addFinalizer_appends {self : ScopeStore} {scope key : Nat} {entry : ScopeEntry}
    {fin : FinName} (hentry : self.entryAt scope = some entry)
    (hopen : entry.scope.isClosed = false) (hkey : key ∉ entry.scope.finalizerKeys) :
    ((self.addFinalizer scope key fin).1.entryAt scope).map (fun e => e.scope.finalizers) =
      some (entry.scope.finalizers ++ [(key, fin)]) := by
  unfold addFinalizer
  rw [hentry]
  dsimp only
  rw [Effect4.Scope.addExit_open _ _ _ _ hopen]
  dsimp only
  rw [setEntry_entryAt _ _ hentry, Option.map_some]
  dsimp only
  rw [Effect4.Scope.addUnsafe_finalizers _ _ _ hopen hkey]

/-- The observer removes exactly the registration it was given: dropping the key its own
registration allocated restores the scope's registration list unchanged.
census: scope.remove-finalizer -/
theorem removeFinalizer_addFinalizer_self {self : ScopeStore} {scope key : Nat}
    {entry : ScopeEntry} {fin : FinName} (hentry : self.entryAt scope = some entry)
    (hopen : entry.scope.isClosed = false) (hkey : key ∉ entry.scope.finalizerKeys) :
    (((self.addFinalizer scope key fin).1.removeFinalizer scope key).entryAt scope).map
      (fun e => e.scope.finalizers) = some entry.scope.finalizers := by
  unfold addFinalizer
  rw [hentry]
  dsimp only
  rw [Effect4.Scope.addExit_open _ _ _ _ hopen]
  dsimp only
  unfold removeFinalizer
  rw [setEntry_entryAt _ _ hentry]
  dsimp only
  rw [setEntry_entryAt _ _ (setEntry_entryAt _ _ hentry), Option.map_some]
  dsimp only
  rw [Effect4.Scope.removeUnsafe_addUnsafe_self _ _ _ hopen hkey]

/-- Registration adds at most the key it was given, so a bound that already covers the store
and the new key covers the result. -/
theorem keysBelow_addFinalizer_bound {self : ScopeStore} {n m scope key : Nat} {fin : FinName}
    (hb : KeysBelow self n) (hn : n ≤ m) (hkey : key < m) :
    KeysBelow (self.addFinalizer scope key fin).1 m := by
  unfold addFinalizer
  cases hentry : self.entryAt scope with
  | none => exact hb.mono hn
  | some entry =>
    have hmem : entry ∈ self.entries := List.mem_of_find?_eq_some hentry
    dsimp only
    intro e he k hk
    rcases mem_setEntry he with rfl | he
    · dsimp only at hk
      unfold Effect4.Scope.addExit at hk
      cases hclose : entry.scope.closingExit? with
      | some ex =>
        rw [hclose] at hk
        exact Nat.lt_of_lt_of_le (hb entry hmem k hk) hn
      | none =>
        rw [hclose] at hk
        dsimp only at hk
        rcases List.mem_cons.mp
            (Effect4.Scope.addUnsafe_keys_subset entry.scope key fin hk) with hk | hk
        · exact hk ▸ hkey
        · exact Nat.lt_of_lt_of_le (hb entry hmem k hk) hn
    · exact Nat.lt_of_lt_of_le (hb e he k hk) hn

/-- Registering at the supply's own value keeps the bound, one higher: the new key is the
only one added, and it is `n`. -/
theorem keysBelow_addFinalizer {self : ScopeStore} {n scope : Nat} {fin : FinName}
    (hb : KeysBelow self n) : KeysBelow (self.addFinalizer scope n fin).1 (n + 1) :=
  keysBelow_addFinalizer_bound hb (Nat.le_succ n) (Nat.lt_succ_self n)

/-- The open branch of `scopeAdd` (`syncOpStep`): registering at the supply's own value into
an entry the store holds keeps the bound, one higher. -/
theorem keysBelow_addUnsafe_entry {self : ScopeStore} {n scope : Nat} {entry : ScopeEntry}
    {fin : FinName} (hb : KeysBelow self n) (hentry : self.entryAt scope = some entry) :
    KeysBelow (self.setEntry { entry with scope := entry.scope.addUnsafe n fin }) (n + 1) := by
  have hmem : entry ∈ self.entries := List.mem_of_find?_eq_some hentry
  intro e he k hk
  rcases mem_setEntry he with rfl | he
  · rcases List.mem_cons.mp (Effect4.Scope.addUnsafe_keys_subset entry.scope n fin hk) with hk | hk
    · exact hk ▸ Nat.lt_succ_self n
    · exact Nat.lt_succ_of_lt (hb entry hmem k hk)
  · exact Nat.lt_succ_of_lt (hb e he k hk)

/-- A fork registers one key on each side, the shared one (`internal/effect.ts:3841-3842`):
below any bound that key is below (the join). -/
theorem keysBelow_forkChild {self : ScopeStore} {n m parent child shared : Nat}
    {strategy : FinalizerStrategy} (hb : KeysBelow self n) (hn : n ≤ m) (hshared : shared < m) :
    KeysBelow (self.forkChild parent child shared strategy) m := by
  unfold forkChild
  cases hentry : self.entryAt parent with
  | none => exact hb.mono hn
  | some entry =>
    have hmem : entry ∈ self.entries := List.mem_of_find?_eq_some hentry
    intro e he k hk
    cases hclose : entry.scope.closingExit? with
    | some ex =>
      simp only [Effect4.Scope.fork, hclose, List.mem_append, List.mem_singleton] at he
      rcases he with he | rfl
      · rcases mem_setEntry he with rfl | he
        · exact Nat.lt_of_lt_of_le (hb entry hmem k hk) hn
        · exact Nat.lt_of_lt_of_le (hb e he k hk) hn
      · exact absurd hk List.not_mem_nil
    | none =>
      simp only [Effect4.Scope.fork, hclose, List.mem_append, List.mem_singleton] at he
      rcases he with he | rfl
      · rcases mem_setEntry he with rfl | he
        · rcases List.mem_cons.mp
              (Effect4.Scope.addUnsafe_keys_subset entry.scope shared _ hk) with hk | hk
          · exact hk ▸ hshared
          · exact Nat.lt_of_lt_of_le (hb entry hmem k hk) hn
        · exact Nat.lt_of_lt_of_le (hb e he k hk) hn
      · rcases List.mem_cons.mp
            (Effect4.Scope.addUnsafe_keys_subset (Effect4.Scope.make strategy) shared _ hk) with hk | hk
        · exact hk ▸ hshared
        · exact absurd hk List.not_mem_nil

/-- Removal keeps the bound: removal only removes. -/
theorem keysBelow_removeFinalizer {self : ScopeStore} {n scope key : Nat}
    (hb : KeysBelow self n) : KeysBelow (self.removeFinalizer scope key) n := by
  unfold removeFinalizer
  cases hentry : self.entryAt scope with
  | none => exact hb
  | some entry =>
    have hmem : entry ∈ self.entries := List.mem_of_find?_eq_some hentry
    dsimp only
    intro e he k hk
    rcases mem_setEntry he with rfl | he
    · exact hb entry hmem k
        (((Effect4.Scope.removeUnsafe_finalizers_sublist entry.scope key).map Prod.fst).subset hk)
    · exact hb e he k hk

/-- A newly made scope holds no registrations, so the bound survives. -/
theorem keysBelow_make {self : ScopeStore} {n key : Nat} {strategy : FinalizerStrategy}
    (hb : KeysBelow self n) : KeysBelow (self.make key strategy) n := by
  intro e he k hk
  rcases List.mem_append.mp he with he | he
  · exact hb e he k hk
  · rw [List.mem_singleton] at he
    subst he
    cases hk

/-- Closing a scope keeps the bound: `closeState` replaces the state, never adding a key. -/
theorem keysBelow_closeState {self : ScopeStore} {n key : Nat} {exit : ExitV}
    (hb : KeysBelow self n) : KeysBelow (self.closeState key exit) n := by
  unfold closeState
  cases hentry : self.entryAt key with
  | none => exact hb
  | some entry =>
    dsimp only
    intro e he k hk
    rcases mem_setEntry he with rfl | he
    · dsimp only at hk
      unfold Effect4.Scope.closeState at hk
      by_cases hc : entry.scope.isClosed = true
      · rw [if_pos hc] at hk
        exact hb entry (List.mem_of_find?_eq_some hentry) k hk
      · rw [if_neg hc] at hk
        cases hk
    · exact hb e he k hk

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

/-- A generator that returns or yields an exit inline (`internal/effect.ts:1362-1372`): the
step a value exit ends with, and the step a failure exit halts with. -/
def stepOfExit {ν σ κ : Type} : ExitV → IterStep ν σ Val Err Defect FiberId Ann κ
  | Exit.success value => IterStep.done value
  | Exit.failure cause => IterStep.halt cause

/-- `exitAsVoidAll` yielded inline at the end of `scopeCloseFinalizers` (`:3826`, `:2024-2038`;
§20): the generator returns `void` when no reason was captured and yields the combined
failure otherwise. -/
def closeDone {ν σ κ : Type} : List (Reason Err Defect FiberId Ann) → IterStep ν σ Val Err Defect FiberId Ann κ
  | [] => IterStep.done Val.unit
  | reason :: rest => IterStep.halt ⟨reason :: rest⟩

/-- The inline merge is `exitAsVoidAll` as a step. census: scope.close-merge -/
theorem closeDone_eq {ν σ κ : Type} (reasons : List (Reason Err Defect FiberId Ann)) :
    (closeDone reasons : IterStep ν σ Val Err Defect FiberId Ann κ) = stepOfExit (voidAllOf reasons) := by
  cases reasons <;> rfl

/-- The value-alphabet merge agrees with `Exit.asVoidAll` on which reasons it carries.
census: scope.exit-as-void-all -/
theorem mergeExits_reasons (exits : List ExitV) :
    (mergeExits exits).causeReasons = (Exit.asVoidAll exits).causeReasons := by
  unfold mergeExits voidAllOf Exit.asVoidAll
  cases exits.flatMap Exit.causeReasons <;> rfl

/-- `reifyExit`: an `Exit` as a value of the one value alphabet — `exitImage.toVal`, written
out so each arm is an equation. -/
def reifyExitVal : ExitV → Val
  | Exit.success value => Val.exitOk value
  | Exit.failure cause => Val.exitErr cause

theorem reifyExitVal_eq_exitImage (exit : ExitV) : reifyExitVal exit = exitImage.toVal exit := by
  cases exit <;> rfl

/-- `RunInterp.exitsValue`: the exits a countdown collected, as one value — one `list` frame
(`fiberAwaitAll`, `internal/effect.ts:779`; M6). -/
def exitsVal (exits : List ExitV) : Val := .list (exits.map reifyExitVal)

mutual
/-- The reasons carried by an exits value, in order: a reified failed exit's cause, read back
through `causeImage`, and the members of a list. -/
def reasonsOfVal : Val → List (Reason Err Defect FiberId Ann)
  | Value.exitErr written => ((causeImage.ofVal written).map Cause.reasons).getD []
  | .list values => reasonsOfList values
  | _ => []
/-- The reasons of a list of values, back to back. -/
def reasonsOfList : List Val → List (Reason Err Defect FiberId Ann)
  | [] => []
  | value :: rest => reasonsOfVal value ++ reasonsOfList rest
end

theorem reasonsOfVal_exitErr (cause : CauseV) : reasonsOfVal (Val.exitErr cause) = cause.reasons := by
  show ((causeImage.ofVal (causeImage.toVal cause)).map Cause.reasons).getD [] = cause.reasons
  rw [Image.ofVal_toVal]
  rfl

theorem reasonsOfVal_reifyExitVal (exit : ExitV) :
    reasonsOfVal (reifyExitVal exit) = exit.causeReasons := by
  cases exit with
  | success value => rfl
  | failure cause => exact reasonsOfVal_exitErr cause

theorem reasonsOfList_map_reifyExitVal (exits : List ExitV) :
    reasonsOfList (exits.map reifyExitVal) = exits.flatMap Exit.causeReasons := by
  induction exits with
  | nil => rfl
  | cons exit rest ih =>
    rw [List.map_cons, reasonsOfList, reasonsOfVal_reifyExitVal, List.flatMap_cons, ih]

/-- Reading the reasons back off an exits value is reading them off the list: the M6 channel
loses nothing, so the merge of an awaited list is `exitAsVoidAll` of that list.
census: scope.close-merge -/
theorem reasonsOfVal_exitsVal (exits : List ExitV) :
    reasonsOfVal (exitsVal exits) = exits.flatMap Exit.causeReasons :=
  reasonsOfList_map_reifyExitVal exits

/-- Hence the merge computed from what `awaitAll` answered is `mergeExits` of the exits.
census: scope.close-merge -/
theorem mergeAwaited_eq_mergeExits (exits : List ExitV) :
    voidAllOf (reasonsOfVal (exitsVal exits)) = mergeExits exits := by
  rw [reasonsOfVal_exitsVal]
  rfl

/-! ## The service state -/

/-- Answers supplied by the host, in encounter order, and the target spellings
of resources minted by the machine. A refused head stays available to admission. -/
structure ExternalStore where
  answers : List (Completion Val Err Defect FiberId Ann)
  allocated : List String
  /-- First rejected registration: row index, offered completion, queue length.
  It stays visible even if another fiber consumes that head before the decision ends. -/
  rejected : Option (Nat × Completion Val Err Defect FiberId Ann × Nat)
deriving DecidableEq

namespace ExternalStore

def empty : ExternalStore := ⟨[], [], none⟩

def ofAnswers (answers : List (Completion Val Err Defect FiberId Ann)) : ExternalStore :=
  ⟨answers, [], none⟩

end ExternalStore

/-- `St`: the four stores and one fresh-name counter, which mints scope keys, registration keys
and memo-map ids alike — each is an *object* in rc.112 (`finalizerKey: {}`, `MemoMapImpl`,
`ScopeImpl`) and identity is the only fact the runtime reads off one, so one counter mints every
identity distinct and separate counters would add numeric coincidences no clause could read
(the Layer machine's ruling, kept in the join). -/
structure Stores where
  /-- `Ref.ts`. -/
  refs : RefHeap
  /-- `Deferred.ts`. -/
  deferreds : DeferredStore
  /-- `Scope.ts` plus the keyed store. -/
  scopes : ScopeStore
  /-- `Layer.ts:421-458`, the memo world (the join). -/
  memo : MemoWorld
  /-- The logical clock and its sleeps (`Machine/Timer.lean`, A4). -/
  timers : TimerStore
  /-- Fresh scope keys, finalizer keys and memo-map ids. -/
  nextName : Nat
  externals : ExternalStore
deriving DecidableEq

namespace Stores

/-- An empty service state: the bottom every family's law holds at. -/
def empty : Stores := ⟨[], ⟨[], []⟩, ⟨[]⟩, [], TimerStore.empty, 0, ExternalStore.empty⟩

/-- The registration-identity invariant (`E4-CHECK-CE-016`): every registration key any
scope holds is below the store's fresh-name supply, so `nextName` is a key no scope holds.
The runtime carries this through `Sched.StoresOk`. -/
def ScopeKeysFresh (self : Stores) : Prop := self.scopes.KeysBelow self.nextName

theorem scopeKeysFresh_empty : ScopeKeysFresh empty := by
  intro e he
  cases he

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
  | RaceName.parkOnly => [ProgName.park 1]
  | RaceName.parkThenSuccess => [ProgName.park 1, ProgName.value (Val.nat 2)]

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
  | FinName.awaitNewChildren snapshot, _ =>
    Prim.withFiber (Thunk.act (ActionName.awaitNewChildren snapshot))
  -- the release closure is called when the finalizer runs (`:3983`): a suspension the
  -- compile route's `suspendBody` resolves, through every close path's `finProgram`
  | FinName.foreign capture, exit => Prim.suspend (Thunk.foreign capture exit)
  | FinName.closeChildOnFailure scope, Exit.failure cause =>                              -- Layer.ts:343
    Prim.withFiber (Thunk.act (ActionName.closeScope scope (Exit.failure cause)))
  | FinName.closeChildOnFailure _, Exit.success _ => Prim.success Val.unit
  -- the memo entry finalizer (`Layer.ts:401-410`): `observers--`, the last observer closing
  -- the layer scope with the exit
  | FinName.memoEntry layer memoMap, exit =>
    Prim.onSuccess (Prim.sync (Thunk.op (SyncOp.memoRelease layer memoMap))) (Name.closeIfLast exit)
  | FinName.memoDone layer memoMap, exit =>                                               -- :414-417
    Prim.sync (Thunk.op (SyncOp.memoComplete layer memoMap exit))

/-- One step of the sequential close generator (`internal/effect.ts:3813-3818`, §20). The value
delivered to the iterator frame is the previous finalizer's reified exit — the answer of the
`Exit` primitive around it (`:3621-3637`) — or the entry cursor; its reasons are captured, a
failing finalizer never aborting the walk. The next finalizer is yielded under `Exit`, in
close order; with none left the walk ends with `exitAsVoidAll` inline (`:3826`). -/
def closeSeqStep (remaining : List FinName) (exit : ExitV)
    (captured : List (Reason Err Defect FiberId Ann)) (value : Val) :
    IterStep Name Thunk Val Err Defect FiberId Ann Program :=
  let captured := captured ++ reasonsOfVal value
  match remaining with
  | [] => closeDone captured
  | fin :: rest =>
    IterStep.resume (Prim.exitFrame (finProgram fin exit)) (Name.closeSeq rest exit captured)

/-- The stored primitive a `Completion` names. `done exit = completeWith (Prim.ofExit exit)`
(`Deferred.ts:570-571`); `ofRefGet` is a non-exit effect, stored and not run (`:456-461`). -/
def completionPrim : Completion Val Err Defect FiberId Ann → Program
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
  | ProgName.forkInScope child options scope =>
    Prim.withFiber (Thunk.act (ActionName.forkIn child options scope))
  | ProgName.runInScope target scope =>
    Prim.withFiber (Thunk.act (ActionName.runIn target scope))
  | ProgName.forkScopedOf child options =>
    Prim.withFiber (Thunk.act (ActionName.forkScoped child options))
  | ProgName.raceOf race => Prim.withFiber (Thunk.act (ActionName.raceAll race))
  | ProgName.closeScopeOf scope exit =>
    Prim.withFiber (Thunk.act (ActionName.closeScope scope exit))
  | ProgName.awaitAllNew body =>
    Prim.onSuccess (Prim.withFiber (Thunk.act ActionName.snapshotChildren))
      (Name.snapshotThen body)
  | ProgName.interruptFibers targets =>
    Prim.withFiber (Thunk.act (ActionName.interruptAll targets none))
  | ProgName.joinFiber target mode => Prim.suspend (Thunk.park (ParkKind.join target mode))
  | ProgName.cancelRace race => Prim.withFiber (Thunk.act (ActionName.cancelRace race))
  -- the counted `Iterator` entry of `scopeCloseFinalizers` (`:3806-3827`, §20): the sequential
  -- generator from its first finalizer, or the parallel step as the one action
  | ProgName.closeWalk FinalizerStrategy.sequential order exit =>
    Prim.iterator (Name.closeSeq order exit []) Val.unit
  | ProgName.closeWalk FinalizerStrategy.parallel order exit =>
    Prim.withFiber (Thunk.act (ActionName.closePar order exit))

/-- What a settled race resumes its host with (`internal/effect.ts:1510-1514`, R2-12):
`exit` when the winning callback saw no live entrant, otherwise
`flatMap(uninterruptible(fiberInterruptAll(fibers)), () => exit)` over the race's live set
at cleanup time, which `ProgName.cancelRace` names (D6a). `Name.restore exit` is the
`() => exit` (its contA discards the value). -/
def raceSettleProgram (race : Nat) (cleanupNeeded : Bool) (exit : ExitV) : Program :=
  if cleanupNeeded then
    Prim.onSuccess
      (Prim.withFiber (Thunk.act (ActionName.setInterruptible (ProgName.cancelRace race) false)))
      (Name.restore exit)
  else Prim.ofExit exit

/-- The cancel effect a cancel *name* runs. `cancelName` attached the parked fiber's identity
and its resume token, so `_await`'s cleanup can splice exactly that resume out
(`Deferred.ts:178-185`, M3); a fiber-observer park's cleanup drops the observers of that token
(R2-3); a race park's cleanup interrupts the race's live entrants (R2-13). -/
def cancelProgram : Name → Program
  | Name.withWaiter (Name.cancelAwait cell) waiter token =>
    Prim.sync (Thunk.op (SyncOp.deferredAwaitCleanup cell waiter token))
  | Name.withWaiter Name.cancelSleep waiter token =>
    Prim.sync (Thunk.op (SyncOp.sleepCancel waiter token))
  | Name.withWaiter Name.cancelPark _ token =>
    Prim.withFiber (Thunk.act (ActionName.dropObservers token))
  | Name.withWaiter (Name.cancelRace race) _ _ =>
    Prim.withFiber (Thunk.act (ActionName.cancelRace race))
  | _ => Prim.success Val.unit

/-- The state and captured finalizers of `scopeCloseUnsafe`
(`internal/effect.ts:3782-3797`). A closed scope has an empty close order; closing
it again retains its recorded exit. Both code representations use this snapshot. -/
def scopeCloseSnapshot (scope : Nat) (exit : ExitV) (state : Stores) :
    Option (Stores × FinalizerStrategy × List FinName) := do
  let entry ← state.scopes.entryAt scope
  return ({ state with scopes := state.scopes.closeState scope exit },
    entry.scope.strategy, entry.scope.closeOrder)

/-- Unsafe close may return no effect (`internal/effect.ts:3782-3797`). A single finalizer is
returned directly; two or more are `scopeCloseFinalizers` (`:3806-3827`, §20): the counted
`fnUntraced` suspend whose body is the counted `Iterator` walk (`ProgName.closeWalk`). The
closer's mask is what the parallel walk's daemons inherit at their fork, so it is not part of
the program. `Effect4.Scope.closeState` runs first: the state is written before any finalizer
program is built (`:3784`). -/
def storesCloseScopeUnsafe (scope : Nat) (exit : ExitV) (_closerInterruptible : Bool)
    (state : Stores) : Option (Stores × Option Program) := do
  let (state, strategy, order) ← scopeCloseSnapshot scope exit state
  return (state, match order with
    | [] => none
    | [fin] => some (finProgram fin exit)
    | _ => some (Prim.suspend (Thunk.body (ProgName.closeWalk strategy order exit))))

/-- `Scope.close(scope, exit)` (`internal/effect.ts:3775-3776`): `scopeCloseUnsafe(...) ??
void_` — the unsafe close's program, or void when it returns none (an empty or already
closed scope). `none` is an unknown scope key, which the machine turns into
`Stuck.unknownScope` — a live frontier, never a cause (M7). -/
def storesCloseScope (scope : Nat) (exit : ExitV) (closerInterruptible : Bool)
    (state : Stores) : Option (Stores × Program) :=
  (storesCloseScopeUnsafe scope exit closerInterruptible state).map fun r =>
    (r.1, r.2.getD (Prim.success Val.unit))

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
  | SyncOp.clockNow, st => some (st, Val.nat st.timers.now)
  | SyncOp.sleepCancel waiter token, st =>
    some ({ st with timers := st.timers.cancel waiter token }, Val.unit)
  | SyncOp.scopeMake strategy, st =>
    some ({ st with scopes := st.scopes.make st.nextName strategy, nextName := st.nextName + 1 },
      Val.scopeHandle st.nextName)
  -- `scopeAddFinalizerExit` (`internal/effect.ts:3846-3858`): an unknown scope is a frontier
  -- (M7); a closed scope answers its closing exit, the caller running the finalizer now
  -- (`:3851-3853`); an open one registers under a key allocated from the supply (`:3855-3856`,
  -- `E4-CHECK-CE-016`), so the supply keeps dominating every key the store holds
  | SyncOp.scopeAdd scope finalizer, st =>
    match st.scopes.entryAt scope with
    | none => none
    | some entry =>
      match entry.scope.closingExit? with
      | some exit => some (st, reifyExitVal exit)
      | none =>
        some ({ st with
            scopes := st.scopes.setEntry
              { entry with scope := entry.scope.addUnsafe st.nextName finalizer }
            nextName := st.nextName + 1 },
          Val.unit)
  | SyncOp.scopeRemove scope key, st =>
    some ({ st with scopes := st.scopes.removeFinalizer scope key }, Val.unit)
  | SyncOp.scopeIsClosed scope, st =>
    (st.scopes.entryAt scope).map (fun entry => (st, Val.bool entry.scope.isClosed))
  -- `scopeForkUnsafe(parent, strategy)` (`internal/effect.ts:3834-3844`): the child under a
  -- fresh key, both linked under a shared registration key, both from the supply; an unknown
  -- parent is a frontier
  | SyncOp.scopeFork parent strategy, st =>
    match st.scopes.entryAt parent with
    | none => none
    | some _ =>
      some ({ st with
          scopes := st.scopes.forkChild parent st.nextName (st.nextName + 1) strategy
          nextName := st.nextName + 2 },
        Val.scopeHandle st.nextName)
  | SyncOp.memoFork parent, st =>                                                         -- Layer.ts:492, :511
    some ({ st with memo := st.memo ++ [⟨⟨st.nextName⟩, parent, []⟩], nextName := st.nextName + 1 },
      Val.memoMap ⟨st.nextName⟩)
  | SyncOp.memoGet layer memoMap, st =>
    match st.memo.get layer memoMap with
    | none => some (st, Val.unit)
    | some (owner, entry) =>                                                              -- :245, :438-442
      some ({ st with
          memo := st.memo.updateEntry owner layer fun e => { e with observers := e.observers + 1 } },
        Val.pair (Val.promise entry.deferred) (Val.memoMap owner))
  | SyncOp.memoBuild layer memoMap, st =>                                                 -- :396-411
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
  | SyncOp.memoComplete layer memoMap exit, st =>                                         -- :415-416
    match st.memo.entryAt memoMap layer with
    | none => some (st, Val.unit)
    | some entry =>
      let (deferreds, _) := st.deferreds.complete entry.deferred (Prim.ofExit exit)
      some ({ st with
          memo := st.memo.updateEntry memoMap layer fun e => { e with effect := Prim.ofExit exit }
          deferreds := deferreds },
        Val.unit)
  | SyncOp.memoRelease layer memoMap, st =>                                               -- :403-408
    match st.memo.entryAt memoMap layer with
    | none => some (st, Val.unit)
    | some entry =>
      if entry.observers ≤ 1 then
        some ({ st with memo := st.memo.deleteEntry memoMap layer }, Val.scopeHandle entry.layerScope)
      else
        some ({ st with
            memo := st.memo.updateEntry memoMap layer fun e => { e with observers := e.observers - 1 } },
          Val.unit)
  | op, st => (refStep op st.refs).map (fun step => ({ st with refs := step.2 }, step.1))

/-! ## Continuations -/

/-- `cont[contA](value, fiber)`. -/
def contAOf : Name → Val → Program
  | Name.restore exit, _ => Prim.ofExit exit
  | Name.merge exit, _ => Prim.ofExit exit
  | Name.seq next, _ => progOf next
  | Name.joinOn mode, Val.fiber ⟨id⟩ => Prim.suspend (Thunk.park (ParkKind.join ⟨id⟩ mode))
  | Name.joinOn _, _ => Prim.failure (Cause.die Defect.badName)
  | Name.interruptWith cell, Val.nat id =>
    Prim.sync (Thunk.op (SyncOp.deferredInterruptWith cell ⟨id⟩))
  | Name.interruptWith _, _ => Prim.failure (Cause.die Defect.badName)
  | Name.doneInto cell, Val.exitOk value =>
    Prim.sync (Thunk.op (SyncOp.deferredCompleteWith cell (Completion.ofExit (Exit.success value))))
  | Name.doneInto cell, Value.exitErr written =>
    -- the cause is read back off the value; a reified failure no cause wrote is a wrong shape
    match causeImage.ofVal written with
    | some cause =>
      Prim.sync (Thunk.op (SyncOp.deferredCompleteWith cell (Completion.ofExit (Exit.failure cause))))
    | none => Prim.failure (Cause.die Defect.badName)
  | Name.doneInto _, _ => Prim.failure (Cause.die Defect.badName)
  | Name.constant value, _ => Prim.success value
  | Name.exitOfValue, Val.exitOk value => Prim.success value
  | Name.exitOfValue, Value.exitErr written =>
    match causeImage.ofVal written with
    | some cause => Prim.failure cause
    | none => Prim.failure (Cause.die Defect.badName)
  | Name.exitOfValue, _ => Prim.failure (Cause.die Defect.badName)
  | Name.snapshotThen body, Value.fiberSnapshot handles =>
    -- `onExit(self, _ => asVoid(fiberAwaitAll(new children)))` (`:5319-5333`, R2-7): awaited
    -- on any exit, under the finalizer mask; a snapshot that is not of fiber handles is empty
    Prim.onExit (progOf body)
      (Name.finalizerName
        (FinName.awaitNewChildren (((Image.list Value.fiberHandle).ofVal handles).getD [])))
      false
  | Name.snapshotThen body, _ =>
    Prim.onExit (progOf body) (Name.finalizerName (FinName.awaitNewChildren [])) false
  | Name.reFail cause, _ => Prim.failure cause
  | Name.closeIfLast exit, Val.scopeHandle scope =>                                       -- Layer.ts:406
    Prim.withFiber (Thunk.act (ActionName.closeScope scope exit))
  | Name.closeIfLast _, _ => Prim.success Val.unit                                        -- :408
  | _, value => Prim.success value

/-- `cont[contE](cause, fiber)`. -/
def contEOf : Name → CauseV → Program
  | Name.restore exit, cause =>
    Prim.ofExit (Exit.restoreAfterFinalizer exit (Exit.failure cause))
  | Name.merge exit, cause =>
    Prim.ofExit (Exit.restoreAfterFinalizer exit (Exit.failure cause))
  | Name.constant value, _ => Prim.success value
  | _, cause => Prim.failure cause

/-- `WithFiberAction` from a name. -/
def actionOf : ActionName → WithFiberAction Name Thunk Val Err Defect FiberId Ann Ctx
  | ActionName.fork program options => WithFiberAction.fork (progOf program) options
  | ActionName.forkIn program options scope =>
    WithFiberAction.forkIn (progOf program) options scope
  | ActionName.forkScoped program options =>
    WithFiberAction.forkScoped (progOf program) options
  | ActionName.ambientScope => WithFiberAction.ambientScope
  | ActionName.runIn target scope => WithFiberAction.runIn target scope
  | ActionName.interrupt target => WithFiberAction.interrupt target
  | ActionName.interruptAs target who => WithFiberAction.interruptAs target who
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
  | ActionName.dropObservers token => WithFiberAction.dropObservers token
  | ActionName.cancelRace race => WithFiberAction.cancelRace race
  -- the parallel walk's step: the finalizer programs at the closing exit, in close order (§20)
  | ActionName.closePar order exit => WithFiberAction.closePar (order.map fun fin => finProgram fin exit)

/-! ## The interp -/

/-- The default `MaxOpsBeforeYield` of the sync scheduler (`Scheduler.ts:174-176`); large
enough that a witness never gets an injected yield it did not ask for. -/
def defaultBudget : Nat := 2048

/-- The empty context (`internal/effect.ts:627`): the empty map, whose references read the
defaults (`Env.hooks_empty`), so the literal is `Ctx.withServices Context.empty`. -/
def emptyCtx : Ctx := ⟨Env.Context.empty, defaultBudget, false⟩

theorem emptyCtx_eq : emptyCtx = Ctx.withServices Env.Context.empty := rfl

theorem emptyCtx_cacheAgrees : emptyCtx.CacheAgrees := rfl

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


/-- A batch wake runs on a waiter list (`Task.wake`, the scheduler surface): by the key's
family. A Deferred's list owes its batch the stored completion inline (`wakeBatch`); the phase
is the schedule's stamp, which a Deferred, completing inline, never mints. No other family
holds a list yet, so every other kind is the identity. -/
def Stores.wakeList (key : WakeKey) (_phase : WakePhase) (s : Stores) : Stores :=
  match key.kind with
  | HandleKind.promise => { s with deferreds := s.deferreds.wakeBatch ⟨key.index⟩ }
  | _ => s

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
  -- the close generators (`scopeCloseFinalizers`, `:3806-3827`, §20): the sequential walk's
  -- step, and the parallel walk's inline merge of the exits its await answered
  iterNext := fun
    | Name.closeSeq remaining exit captured, value => ([], closeSeqStep remaining exit captured value)
    | Name.closeParDone, value => ([], closeDone (reasonsOfVal value))
    | _, value => ([], IterStep.done value)
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
  parkCode := fun kind => Prim.suspend (Thunk.park kind)
  -- the interrupt programs are the named `withFiber` actions (source-repairs §19, D6b)
  interruptCode := fun target => Prim.withFiber (Thunk.act (ActionName.interrupt target))
  interruptAsCode := fun target who => Prim.withFiber (Thunk.act (ActionName.interruptAs target who))
  interruptAllCode := fun targets => Prim.withFiber (Thunk.act (ActionName.interruptAll targets none))
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
    | Name.registerSleep millis =>
      ({ state with timers := state.timers.sleep fiber token millis }, none)
    | _ => (state, none)
  dueResumes := fun state =>
    let (due, deferreds) := state.deferreds.drainDue
    (due, { state with deferreds := deferreds })
  wakeList := Stores.wakeList
  -- a fired sleep resumes with `void` (`internal/effect.ts:6062`), posted on its dispatcher
  clockStep := fun millis state =>
    let (owed, timers) := state.timers.clockStep millis (Prim.success Val.unit)
    (owed, { state with timers := timers })
  answerCode := completionPrim
  cancelName := fun base fiber token => Name.withWaiter base fiber token
  abortName := Name.abortController
  parkCancelName := Name.cancelPark
  raceCancelName := Name.cancelRace
  raceSettle := raceSettleProgram
  finalizerProgram := fun
    | Name.finalizerName fin, exit => some (finProgram fin exit)
    | _, _ => none
  restoreName := Name.restore
  mergeName := Name.merge
  scopeStatus := fun scope state => state.scopes.status scope
  scopeLinkFiber := fun mode scope fiber state =>
    match state.scopes.entryAt scope with
    | none => none
    | some _ =>
      -- `forkIn` registers the self-guarded finalizer (`:5370`), `fiberRunIn` the unguarded
      -- one (`:5458`) — M4. The identity is allocated here, from the store's own supply,
      -- because the source allocates `const key = {}` at each registration (`:5366`,
      -- `:5457`) — `E4-CHECK-CE-016`.
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
  fiberIdValue := fun fiber => Val.nat fiber.value
  fibersValue := Val.fibers
  exitsValue := exitsVal
  voidValue := Val.unit
  scopeValue := Val.scopeHandle
  closeDoneName := Name.closeParDone
  encodeFiber := id
  stackAnnotations := stackAnnotationsOf
  asyncFiberError := Defect.asyncFiber
  missingScope := Defect.missingService

/-! ### The remaining `deferred.*` clauses, as facts about the compiled program -/

/-- `deferred.done-is-complete-with`: `done` *is* `completeWith`; completing from an `Exit`
stores that `Exit`. census: deferred.done-is-complete-with -/
theorem completionPrim_ofExit (exit : ExitV) :
    completionPrim (Completion.ofExit exit) = Prim.ofExit exit := rfl

/-- `deferred.done-is-complete-with`: an `Exit` completion is shared — every awaiter is resumed
with the same primitive, and that primitive reads back as the same exit
(`src/Effect4/Machine/Frames.lean:514`). census: deferred.done-is-complete-with -/
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
    contAOf (Name.interruptWith cell) (Val.nat id.value) =
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
        (Completion.ofExit (Exit.failure cause)))) := by
  simp only [reifyExitVal, contAOf, Image.ofVal_toVal]

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

/-- `scope.close-lifo`, `scope.close-sequential`: two or more finalizers close through the
generator `scopeCloseFinalizers` (`internal/effect.ts:3806-3827`, §20). The counted
`fnUntraced` suspend returns the counted `Iterator` over the close order — the materialised
registration list, backwards — from its first finalizer, with nothing captured yet.
census: scope.close-lifo, scope.close-sequential -/
theorem closeWalk_sequential (order : List FinName) (exit : ExitV) :
    progOf (ProgName.closeWalk FinalizerStrategy.sequential order exit) =
      Prim.iterator (Name.closeSeq order exit []) Val.unit := rfl

/-- `scope.close-sequential`: each step of the sequential walk yields the next finalizer of the
close order under the `Exit` primitive (`:3617`, `:3621-3637`), whose reified exit is what the
frame delivers to the next step; the reasons of the delivered value are captured first.
census: scope.close-lifo, scope.close-sequential -/
theorem closeSeq_step (fin : FinName) (rest : List FinName) (exit : ExitV)
    (captured : List (Reason Err Defect FiberId Ann)) (value : Val) :
    stores.iterNext (Name.closeSeq (fin :: rest) exit captured) value =
      ([], IterStep.resume (Prim.exitFrame (finProgram fin exit))
        (Name.closeSeq rest exit (captured ++ reasonsOfVal value))) := rfl

/-- `scope.close-sequential`: a failing finalizer does not abort the walk; the reasons of its
reified failure exit are captured and the walk continues with the next finalizer.
census: scope.close-sequential -/
theorem closeSeq_captures (rest : List FinName) (exit : ExitV)
    (captured : List (Reason Err Defect FiberId Ann)) (cause : CauseV) :
    stores.iterNext (Name.closeSeq rest exit captured) (Val.exitErr cause) =
      ([], closeSeqStep rest exit (captured ++ cause.reasons) Val.unit) := by
  cases rest <;> simp [stores, closeSeqStep, reasonsOfVal, Image.ofVal_toVal]

/-- `scope.close-merge`: with no finalizer left the walk ends with `exitAsVoidAll` of the
captured reasons, yielded inline (`:3826`, `:2024-2038`): the generator returns `void`, or
halts with the combined failure. census: scope.close-merge -/
theorem closeSeq_merges (exit : ExitV) (captured : List (Reason Err Defect FiberId Ann))
    (value : Val) :
    stores.iterNext (Name.closeSeq [] exit captured) value =
      ([], closeDone (captured ++ reasonsOfVal value)) := rfl

/-- `scope.close-parallel`: the parallel walk's `Iterator` entry is the one action that forks
every finalizer of the close order, at the closing exit (`:3819-3821`).
census: scope.close-parallel -/
theorem closeWalk_parallel (order : List FinName) (exit : ExitV) :
    progOf (ProgName.closeWalk FinalizerStrategy.parallel order exit) =
      Prim.withFiber (Thunk.act (ActionName.closePar order exit)) := rfl

/-- `scope.close-parallel`: the parallel step's programs are the finalizer programs at the
closing exit, in close order; the machine forks each as an immediate daemon inheriting the
closer's mask (`withFiber_closePar`, `forkFinalizers_cons`). census: scope.close-parallel -/
theorem actionOf_closePar (order : List FinName) (exit : ExitV) :
    actionOf (ActionName.closePar order exit) =
      WithFiberAction.closePar (order.map fun fin => finProgram fin exit) := rfl

/-- `scope.close-merge` (M6, §20): the parallel walk's done step, delivered the exits its await
answered, is `exitAsVoidAll` of exactly those exits — no store side-channel. -/
theorem closeParDone_is_asVoidAll (exits : List ExitV) :
    stores.iterNext Name.closeParDone (stores.exitsValue exits) =
      ([], stepOfExit (mergeExits exits)) := by
  show ([], closeDone (reasonsOfVal (exitsVal exits))) = _
  rw [closeDone_eq, mergeAwaited_eq_mergeExits]

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
  have _ := hopen
  constructor <;> simp [storesCloseScope, storesCloseScopeUnsafe, scopeCloseSnapshot, h]

/-- M7: an unknown scope key is a frontier, not a cause — the hook answers `none` and the
machine halts with `Stuck.unknownScope`. -/
theorem storesCloseScope_unknown (scope : Nat) (exit : ExitV) (masked : Bool) (state : Stores)
    (h : state.scopes.entryAt scope = none) :
    storesCloseScope scope exit masked state = none := by
  simp [storesCloseScope, storesCloseScopeUnsafe, scopeCloseSnapshot, h]

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
"interrupt fiber `f`" name (`internal/effect.ts:5370`), under the identity this registration
allocates from the store's own supply (`const key = {}`, `:5366`).
census: scope.fork-linkage, fork.scope-linkage -/
theorem scopeLinkFiber_name (scope : Nat) (fiber : FiberId) (state : Stores)
    (entry : ScopeEntry) (h : state.scopes.entryAt scope = some entry) :
    stores.scopeLinkFiber Supervision.ScopeMode.forkIn scope fiber state =
      some ({ state with
        scopes :=
          (state.scopes.addFinalizer scope state.nextName
            (FinName.interruptFiber fiber true)).1,
        nextName := state.nextName + 1 }, state.nextName) := by
  simp [stores, h]

/-- M4: `fiberRunIn` registers the *unguarded* finalizer (`internal/effect.ts:5458`), under
its own freshly allocated identity (`:5457`). census: scope.fork-linkage -/
theorem scopeLinkFiber_runIn_name (scope : Nat) (fiber : FiberId) (state : Stores)
    (entry : ScopeEntry) (h : state.scopes.entryAt scope = some entry) :
    stores.scopeLinkFiber Supervision.ScopeMode.fiberRunIn scope fiber state =
      some ({ state with
        scopes :=
          (state.scopes.addFinalizer scope state.nextName
            (FinName.interruptFiber fiber false)).1,
        nextName := state.nextName + 1 }, state.nextName) := by
  simp [stores, h]

/-- M7 again: linking into an unknown scope is a frontier. -/
theorem scopeLinkFiber_unknown (mode : Supervision.ScopeMode) (scope : Nat)
    (fiber : FiberId) (state : Stores) (h : state.scopes.entryAt scope = none) :
    stores.scopeLinkFiber mode scope fiber state = none := by
  simp [stores, h]

/-! ### The registration identity is fresh (`E4-CHECK-CE-016`)

`internal/effect.ts:5366-5372` and `:5457-5460` allocate a brand new key object at every
executed registration; the theorems below are that protocol at this store. They are stated
against the store's *whole* scope table under one reachable-state invariant, not about two
chosen keys. -/

/-- Registration answers the supply's current value and advances the supply. -/
theorem scopeLinkFiber_allocates (mode : Supervision.ScopeMode) (scope : Nat)
    (fiber : FiberId) {state state' : Stores} {key : Nat}
    (h : stores.scopeLinkFiber mode scope fiber state = some (state', key)) :
    key = state.nextName ∧ state'.nextName = state.nextName + 1 := by
  dsimp only [stores] at h
  cases hentry : state.scopes.entryAt scope with
  | none => rw [hentry] at h; cases h
  | some entry =>
    rw [hentry] at h
    dsimp only at h
    obtain ⟨h₁, h₂⟩ := Prod.mk.inj (Option.some.inj h)
    exact ⟨h₂.symm, by rw [← h₁]⟩

/-- Under the invariant the allocated identity is held by *no* scope in the store — not the
target's, not another scope's, and not a slot an earlier removal freed. -/
theorem scopeLinkFiber_fresh (mode : Supervision.ScopeMode) (scope : Nat) (fiber : FiberId)
    {state state' : Stores} {key : Nat} (hfresh : state.ScopeKeysFresh)
    (h : stores.scopeLinkFiber mode scope fiber state = some (state', key)) :
    ∀ e ∈ state.scopes.entries, key ∉ e.scope.finalizerKeys := by
  obtain ⟨rfl, -⟩ := scopeLinkFiber_allocates mode scope fiber h
  exact hfresh.fresh

/-- Registration preserves the invariant, so the next registration is fresh again. -/
theorem scopeLinkFiber_keysFresh (mode : Supervision.ScopeMode) (scope : Nat) (fiber : FiberId)
    {state state' : Stores} {key : Nat} (hfresh : state.ScopeKeysFresh)
    (h : stores.scopeLinkFiber mode scope fiber state = some (state', key)) :
    state'.ScopeKeysFresh := by
  dsimp only [stores] at h
  cases hentry : state.scopes.entryAt scope with
  | none => rw [hentry] at h; cases h
  | some entry =>
    rw [hentry] at h
    dsimp only at h
    obtain ⟨h₁, -⟩ := Prod.mk.inj (Option.some.inj h)
    subst h₁
    exact ScopeStore.keysBelow_addFinalizer hfresh

/-- Hence the registration appends: the whole prior registration list is kept, and no earlier
registration is replaced. This is the defect `E4-CHECK-CE-016` recorded — a repeated compile
point used to supply an equal key, and `Scope.tableInsert` correctly replaced it.
census: scope.add-finalizer -/
theorem scopeLinkFiber_appends (mode : Supervision.ScopeMode) (scope : Nat) (fiber : FiberId)
    {state state' : Stores} {key : Nat} {entry : ScopeEntry}
    (hfresh : state.ScopeKeysFresh) (hentry : state.scopes.entryAt scope = some entry)
    (hopen : entry.scope.isClosed = false)
    (h : stores.scopeLinkFiber mode scope fiber state = some (state', key)) :
    ∃ fin, ((state'.scopes.entryAt scope).map (fun e => e.scope.finalizers)) =
      some (entry.scope.finalizers ++ [(key, fin)]) := by
  have hkey : key ∉ entry.scope.finalizerKeys := by
    obtain ⟨rfl, -⟩ := scopeLinkFiber_allocates mode scope fiber h
    exact hfresh.fresh entry (List.mem_of_find?_eq_some hentry)
  dsimp only [stores] at h
  rw [hentry] at h
  cases mode with
  | forkIn =>
    dsimp only at h
    obtain ⟨hs, hk⟩ := Prod.mk.inj (Option.some.inj h)
    subst hs; subst hk
    exact ⟨_, ScopeStore.addFinalizer_appends hentry hopen hkey⟩
  | fiberRunIn =>
    dsimp only at h
    obtain ⟨hs, hk⟩ := Prod.mk.inj (Option.some.inj h)
    subst hs; subst hk
    exact ⟨_, ScopeStore.addFinalizer_appends hentry hopen hkey⟩

/-- The observer removes exactly the registration it was given: dropping the key this
registration allocated restores the scope's registration list unchanged, even though other
registrations may have arrived in between (they are all under different keys).
census: scope.remove-finalizer -/
theorem dropFinalizer_removes_its_own (mode : Supervision.ScopeMode) (scope : Nat)
    (fiber : FiberId) {state state' : Stores} {key : Nat} {entry : ScopeEntry}
    (hfresh : state.ScopeKeysFresh) (hentry : state.scopes.entryAt scope = some entry)
    (hopen : entry.scope.isClosed = false)
    (h : stores.scopeLinkFiber mode scope fiber state = some (state', key)) :
    ((state'.scopes.removeFinalizer scope key).entryAt scope).map
      (fun e => e.scope.finalizers) = some entry.scope.finalizers := by
  have hkey : key ∉ entry.scope.finalizerKeys := by
    obtain ⟨rfl, -⟩ := scopeLinkFiber_allocates mode scope fiber h
    exact hfresh.fresh entry (List.mem_of_find?_eq_some hentry)
  dsimp only [stores] at h
  rw [hentry] at h
  cases mode with
  | forkIn =>
    dsimp only at h
    obtain ⟨hs, hk⟩ := Prod.mk.inj (Option.some.inj h)
    subst hs; subst hk
    exact ScopeStore.removeFinalizer_addFinalizer_self hentry hopen hkey
  | fiberRunIn =>
    dsimp only at h
    obtain ⟨hs, hk⟩ := Prod.mk.inj (Option.some.inj h)
    subst hs; subst hk
    exact ScopeStore.removeFinalizer_addFinalizer_self hentry hopen hkey

/-- The fiber finalizer compiles to `WithFiberAction.interruptScoped`, whose machine arm is
"interrupt unless the interruptor is the fiber itself, then await" (`:5369-5371`).
census: scope.fork-linkage -/
theorem interruptFiber_compiles_to_interruptScoped (fiber : FiberId) (exit : ExitV) :
    finProgram (FinName.interruptFiber fiber true) exit =
      Prim.withFiber (Thunk.act (ActionName.interruptScoped fiber)) := rfl

/-! ## Separation gates at this instantiation

`docs/research/FRAMES-DAG.md` separation 4: names stay data. The gates of `Deep.Fibers` must keep
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

/-- The composition law of the join (`docs/research/2026-09-07-probe-u1b-layer-join.md` §3.5,
`join-dispatch.md` §2): the fiber machine's four context hooks are the service map's — the
ambient scope a lookup, the budget through the caches under the cache law (`Ctx.CacheAgrees`,
which every `Ctx.withServices` satisfies), the empty context the empty map, the context value
the map's spine under `Value.fiberContext`. -/
theorem stores_hooks :
    (∀ c : Ctx, stores.ambientScope c = Env.ambientScope c.services) ∧
    (∀ c : Ctx, c.CacheAgrees → stores.budgetOf c = Env.budgetOf c.services) ∧
    stores.emptyContext = Ctx.withServices Env.Context.empty ∧
    (∀ c : Ctx, stores.contextValue c =
      Value.fiberContext (Env.encode c.services) (.nat c.maxOpsBeforeYield)
        (.bool c.preventYield)) :=
  ⟨fun _ => rfl, fun _ h => h, rfl, fun _ => rfl⟩

end Effect4.Machine
