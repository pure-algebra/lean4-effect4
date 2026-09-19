import Effect4.Machine.Value
import Effect4.Machine.Completion
import Effect4.Machine.Wake

/-!
# Machine.Alphabets — the error, defect and value alphabets, once, below the stores

The typed error alphabet `Err`, the defect alphabet `Defect`, the annotation alphabet `Ann`,
their images on the shared carrier, the cause and exit carriers at this instantiation
(`CauseV`, `ExitV`) with their images, the identities the memo world keys on (`LayerId`,
`MemoMapId`), and the machine's view of the carrier (`Machine.Val` with its typed-handle
spellings). Moved out of `Machine/Stores.lean` at L1 of the language push
(`docs/research/2026-09-18-rows-42-43-plan.md` §2c) so that a term can be evaluated inside a
store step: the atoms that query a cause read `Val.cause?`, and `refStep` runs the terms the
function-taking rows carry. The S5 spike's second copy of this alphabet under
`Effect4.Machine.Env` (`Machine/Context.lean`) had no consumer and is gone. Every name keeps
its namespace, so no reader changes.
-/

namespace Effect4.Machine

open Effect4

/-! ## The alphabets

Every alphabet is first-order and derives `DecidableEq`, which the separation gates of
`Deep.Fibers` (`docs/research/FRAMES-DAG.md` separation 4) need at this instantiation.
The generic Completion data and its Ref key are shared through `Machine.Completion`. -/

/-- The typed error alphabet: `boom` a failure with no typed payload, `tag n` a numeric
error (`Effect.fail(7)`), and `tagged tag message` a host package failure crossing as the
ratified `prod string string` (DB-15, the host rows slice): the error's `_tag` and its
message. Appended 2026-09-09, so every existing golden keeps its bytes. -/
inductive Err
  | boom
  | tag (code : Nat)
  | tagged (tag message : String)
  /-- A textual typed failure (DI-62), preserving its exact payload. -/
  | text (message : String)
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
  /-- A represented typed error promoted to a defect by `orDie` (DI-31). -/
  | error (payload : Err)
deriving DecidableEq, Repr

/-- The defect a represented error becomes, whether promoted by `orDie`
(`internal/effect.ts:3289`, DI-31) or spelled directly as `Cause.die` of an admitted error
value (DI-74): a numeric error keeps its number as a user defect, a text or package error keeps
its exact payload, and the payload-less `boom` is the wrong-shape defect. The one owner of
that conversion, used by both sites in `Program/Compile.lean` (`orDieCause`, `causeOf`). -/
def Defect.ofError : Err → Defect
  | .tag code => .user code
  | .boom => .badName
  | .tagged tag message => .error (.tagged tag message)
  | .text message => .error (.text message)

/-- The cause-annotation value alphabet; `stackAnnotations` contributes none
(`internal/effect.ts:579-580` is `fiberStackAnnotations`, host stack data). -/
abbrev Ann := Unit


/-! ## Identities -/

/-- A layer, by the path of its node from the root program (`Program/Compile.lean`'s `Node`;
the join, `docs/research/2026-09-07-join-dispatch.md` §4): layers are program subterms
addressed by path, never a table. The memo world keys on it, and two evaluations of one site
under two memo maps are two entries — the path is the key, never an identity. -/
abbrev LayerId := List Nat

/-- A `MemoMapImpl` (`Layer.ts:421-432`), by allocation order from the one supply. -/
structure MemoMapId where
  index : Nat
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
  | .ctor 2 [.str t, .str m] => some (.tagged t m)
  | .ctor 3 [.str s] => some (.text s)
  | _ => none

/-- `Err` at the generated rule: `boom` is `ctor 0 []`, `tag c` is `ctor 1 [nat c]`,
`tagged tag message` is `ctor 2 [str tag, str message]`, and `text s` is
`ctor 3 [str s]`. Existing constructor encodings remain fixed. -/
def Err.image : Image Err where
  toVal
    | .boom => .ctor 0 []
    | .tag c => .ctor 1 [.nat c]
    | .tagged t m => .ctor 2 [.str t, .str m]
    | .text s => .ctor 3 [.str s]
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
  | .ctor 5 [e] => (ofErr e).map Defect.error
  | _ => none

/-- `Defect` at the generated rule, in declaration order; `user n` is `ctor 4 [nat n]`
and `error e` is `ctor 5 [Err.image.toVal e]`. A malformed nested error is refused. -/
def Defect.image : Image Defect where
  toVal
    | .notImplemented => .ctor 0 []
    | .asyncFiber => .ctor 1 []
    | .badName => .ctor 2 []
    | .missingService => .ctor 3 []
    | .user n => .ctor 4 [.nat n]
    | .error e => .ctor 5 [Err.image.toVal e]
  ofVal := ofDefect
  ofVal_toVal d := by
    cases d <;> try rfl
    next e =>
      change (ofErr (Err.image.toVal e)).map Defect.error = some (.error e)
      rw [show ofErr (Err.image.toVal e) = some e from Err.image.ofVal_toVal e]
      rfl
  ofVal_exact := by
    intro v d h
    unfold ofDefect at h
    split at h
    all_goals try (injection h with h; subst h; rfl)
    · next written =>
      obtain ⟨e, he, hd⟩ := Image.map_eq_some_inv h
      subst hd
      show Store.Val.ctor 5 [written] = Store.Val.ctor 5 [Err.image.toVal e]
      rw [Err.image.ofVal_exact he]
    · exact nomatch h

theorem Defect.image_handleFree : Image.HandleFree Defect.image := by
  intro d
  cases d <;> try rfl
  next e =>
    change (Err.image.toVal e).handles ++ [] = []
    rw [Err.image_handleFree e]
    rfl

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

-- Exported patterns retain dotted matching; only typed-key wrappers need definitions here.
-- In a shared pattern's payload, qualify typed handles (`.exitOk (Val.cell ⟨k⟩)`).
export Value (exitOk resultFailure resultSuccess exitNil)
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
/-- A list read back from a value: either the carrier's `.list`, or a fiber snapshot through `snapshot?`. -/
def asList? : Val → Option (List Val)
  | .list values => some values
  | v => (snapshot? v).map fun ids => ids.map fiber

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

end Effect4.Machine
