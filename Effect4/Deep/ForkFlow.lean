import Effect4.Deep.Fibers
import Effect4.Semantics.RegionSimulation
import Effect4.Target.TypeScript.ScriptFlow
import Effect4.Flow.Interrupt

/-!
# Deep spike S3: Flow names a concurrent child through an operation

Status: design spike, 2026-09-03, third pass — rebased onto the fiber machine that folded in
this spike's two machine findings (pass two) and onto spike S4's rewritten region compile
(pass three, `docs/research/2026-09-03-spike-s4-compile.md`).
Module `Deep.ForkFlow` of the non-default `Deep` library
(`lakefile.toml:98-101`, `srcDir = "workshop"`); built with `lake build Deep.ForkFlow`.
Plan row: `docs/research/2026-09-03-deep-plan.md:98` (S3). Rulings 3, 6, 7 of that file's §0;
review findings 1, 2, 3, 12, 13, 14 of `docs/research/2026-09-03-deep-plan-review.md`.
Report: `docs/research/2026-09-03-spike-s3-fork-flow.md`.

## What this module is

Ruling 3: a Flow names a concurrent child through an **operation of the supplied
alphabet**, never a new `RawTerm`/`RegionTerm` constructor. Everything below is that
sentence made executable:

* §1 the **fiber profile** — twelve `OpSpec` rows (`Effect4/Target/TypeScript/ScriptFlow.lean:39-56`)
  that `tableAlphabet` (`:84-108`) turns into a `FlowAlphabet String` and that the lowering
  prints as ordinary service calls. No constructor, no admission clause, no denotation
  summand, no exhaustive match anywhere changes.
* §2 the **value alphabet** of the profile: a fiber handle as a `Val`, the `Val → Option
  FiberId` that a request's `fiber` argument is decoded through, the fork request's four
  fields, the root reference a masked body names, and the exit reading `await` answers.
* §3 the **run-time refusal** (review finding 2, cost (a)): admission cannot look inside a
  request value, so "the request names a declared root of this flow with a matching
  parameter count" is a decidable check *at the operation*, `checkFork`. Its refusal is
  raised as `WithFiberAction.refuse` — the arm this spike's first pass asked for — except
  for the three rows that compile to a primitive the machine reads directly and therefore
  have no action channel (`join`, `await`, `yieldNow`), which compile to `Prim.suspend` and
  whose defect the interp's `suspendBody` raises.
* §4 the **compile**, `compileFork`, written beside `RegionSimulation.compileAt`
  (`Effect4/Semantics/RegionSimulation.lean:645-647`) and **calling** `compileRegion` on
  every arm it does not change, so it reuses S4's `Config`, `RegionName`, `Code`, `Table`,
  `performOp`, `performCont`, `catchCont`, `closeExit` and `statelessOracle` unchanged and
  does not mirror any of its bodies.
* §5 the **interp**: `parkOf` classifies `join`/`await` as `ParkKind.join target mode`,
  `withFiberOf` reads the fork request and answers `WithFiberAction.fork
  (compileFork … ⟨fuel, root, args, tape⟩) options`, and everything else is `regionInterp`
  under a record update.
* §6 `WellSourced` (ruling 6, finding 12), proved for every program-carrying action, and
  `ConfigWellSourced` over the fiber's whole configuration with its fork arm proved.
* §7 the decision partition (ruling 7, finding 13), proved.
* §8 the fuel bound (finding 3), stated as an obligation.
* §9 seven executable witnesses.

## What the carrier gave this pass, and what changed here

The fiber machine (`Effect4/Deep/Fibers.lean`) folded in spike S1's `Prim` constructors and
both of this spike's findings. The consequences, each visible below:

1. `Prim.yieldNowWith`, `Prim.async` and `Prim.asyncFinalizer` are constructors, and
   `PrimInterp` gained `cancelThenFail`. `ParkKind` is therefore just `join`
   (`Fibers.lean:52-54`), and `forkParkOf` classifies only that. The profile gains a
   `yieldNow` row that compiles **straight to `Prim.yieldNowWith`** rather than through the
   interp — the representational debt the first pass recorded is gone.
2. A `join` on a fiber the machine does not hold is `Outcome.stuck (Stuck.unknownFiber …)`
   and surfaces as `ReplayResult.stuck` (`Fibers.lean:731`). §9's `strandedJoinStuck`
   witnesses it; the first pass's `strandedJoinSpins` is retired.
3. `WithFiberAction.refuse` exists (`Fibers.lean:295-296`), so a refused operation is a
   machine event with a cause, not a compile-time constant.
4. `WithFiberAction.setInterruptible body flag` exists (`Fibers.lean:282-284`), so a program
   can mask its own fiber. The profile gains `uninterruptibleIn`/`interruptibleIn`, and §9's
   masked-child witness is the first thing in this spike that exercises the interrupt half.

## What spike S4 gave the third pass

S4 rewrote the region compile under this module. Four consequences:

5. **`compileFork` now delegates.** Every arm this module does not change is one call to the
   new `compileRegion`, so `compileFork_eq_compileRegion` has three real cases (the two
   transfers and the region body) and the rest by `rfl`. The module no longer mirrors
   `compileRegion`'s bodies and does not go stale when they change again.
6. **P1: one frame per region.** The `enter` arm emits
   `Prim.onSuccessAndFailure body (RegionName.regionCont region enterPoint)
   (RegionName.close region enterPoint)`, and `forkTable` carries S4's five-way `RegionName`
   match, including `regionCont`'s close check (`closeExit oracle (oracle.registrations
   point)`) and `close`'s reason concatenation.
7. **P2: the compile emits `Prim.failure` nowhere.** Every frontier is `Prim.suspend point`.
   The refusal of the three `direct` rows moved with it: they compile to `Prim.suspend` and
   `forkTable.suspendBody` raises the defect, so `compileFork_not_failure` holds for the
   profile compile too — a strictly better answer than the first pass's compile-time
   `Prim.failure (Cause.die ())`.
8. **P3 is upstream.** A caught operation compiles to
   `onSuccessAndFailure … (RegionName.cont point) (RegionName.caught point)` and
   `contE (caught point)` reads the error off the cause. The hand-rolled `firstError` the
   second pass carried is gone; `catchesMachineFailure` now only decides *which* profile
   rows need the failure arm at all.

Names are data: `RegionName` and `Config` are the same first-order carriers fence B and
`RegionSimulation` fixed, and the separation-4 gates at the foot of this file fail to
elaborate the moment a name alphabet is instantiated at a function type.
-/

namespace Effect4.Deep.ForkFlow

open Effects
open Effects.Trace (Val)
open Effect4.RegionSimulation (Config RegionName Code Err Res Table RegionOracle
  compileRegion compileAt regionInterp performOp performCont catchCont statelessOracle
  regionBound failuresOfCause isFailure compileRegion_not_failure regionSuspendBody
  closeExit leaveConfig)
open Effect4.Target.EffectV4 (OpSpec OpKind tableAlphabet requestSpelling)

/-! ## 1. The fiber profile

Twelve rows. Read `docs/research/2026-09-03-deep-plan-review.md:524-556` (finding 14) for why
`daemon` and `region` are *request fields* rather than three more formers, and why
`forkScoped` is nevertheless a row of its own: `forkIn` names its scope, but `forkScoped`
reads the *ambient* `Scope` of the fiber's context (`rc.112 internal/effect.ts:5400-5406`),
which is a machine fact and not something a request can carry. -/

/-- The operations of the fiber profile, in the order `fiberProfile` declares them. The
carrier is an index into the profile, never a string: a table position is what
`tableAlphabet` makes an operation (`Effect4/Target/TypeScript/ScriptFlow.lean:84-88`). -/
inductive FiberOp
  /-- `forkUnsafe` (`:5264-5284`), by `daemon`; `forkIn` (`:5364-5378`) when `region` is
  `some`. -/
  | fork
  /-- `forkScoped` (`:5400-5406`): `forkIn` on the ambient scope, which no request names. -/
  | forkScoped
  /-- `fiberJoin` (`:5291`): the child's exit continues *as an effect*. -/
  | join
  /-- `fiberAwait` (`:5304`): the child's exit continues *as a value*. -/
  | await
  /-- `fiberInterrupt` (`:859`). -/
  | interrupt
  /-- `fiberInterruptAll` (`:895`). -/
  | interruptAll
  /-- `awaitAllChildren`'s snapshot half (`:5318`). -/
  | childrenSnapshot
  /-- `awaitAllChildren`'s exit half: await the children added since the snapshot. -/
  | awaitChildren
  /-- `raceAll`: entrants named as declared roots. -/
  | raceAll
  /-- `Effect.uninterruptible` (`:4302-4310`): run a declared root's body masked. -/
  | uninterruptibleIn
  /-- `Effect.interruptible` (`:4331-4352`): run a declared root's body unmasked. -/
  | interruptibleIn
  /-- `Effect.yieldNow` (`:982-994`): park behind the fiber's own dispatcher. -/
  | yieldNow
deriving DecidableEq, Repr

namespace FiberOp

/-- The profile position of an operation. -/
def index : FiberOp → Nat
  | fork => 0
  | forkScoped => 1
  | join => 2
  | await => 3
  | interrupt => 4
  | interruptAll => 5
  | childrenSnapshot => 6
  | awaitChildren => 7
  | raceAll => 8
  | uninterruptibleIn => 9
  | interruptibleIn => 10
  | yieldNow => 11

/-- The operation at a profile position; `none` outside the profile. -/
def ofIndex : Nat → Option FiberOp
  | 0 => some fork
  | 1 => some forkScoped
  | 2 => some join
  | 3 => some await
  | 4 => some interrupt
  | 5 => some interruptAll
  | 6 => some childrenSnapshot
  | 7 => some awaitChildren
  | 8 => some raceAll
  | 9 => some uninterruptibleIn
  | 10 => some interruptibleIn
  | 11 => some yieldNow
  | _ => none

theorem ofIndex_index (op : FiberOp) : ofIndex op.index = some op := by cases op <;> rfl

/-- The number of rows the profile occupies. -/
def count : Nat := 12

theorem ofIndex_ge (n : Nat) (h : count ≤ n) : ofIndex n = none := by
  unfold count at h
  match n, h with
  | _ + 12, _ => rfl

/-- The three rows that compile to a primitive the machine reads *directly* —
`Prim.sync` under `parkOf` for the two joins, `Prim.yieldNowWith` for the yield — and
therefore have no `WithFiberAction` channel through which to refuse. -/
def direct : FiberOp → Bool
  | join => true
  | await => true
  | yieldNow => true
  | _ => false

end FiberOp

/-- The TypeScript spelling of a fiber handle over a child answering `answerTy` and failing
with `errorTy`. rc.112 `Fiber.Fiber<A, E>`. -/
def handleTy (answerTy errorTy : String) : String :=
  "Fiber.Fiber<" ++ answerTy ++ ", " ++ errorTy ++ ">"

/-- The TypeScript spelling of the exit `await` answers with. rc.112 has no `Either`, and
`Effect4/Target/TypeScript/EffectV4.lean:49-52` records that an `Except E A` answer is
spelled `Result.Result<A, E>`; on the wire it is the `Val` of
`Effects.Trace.ToVal (Except ε α)` (`.lake/packages/effects/Effects/Trace.lean:69-70`),
namely `pair (bool true) value` / `pair (bool false) error`. -/
def exitTy (answerTy errorTy : String) : String :=
  "Result.Result<" ++ answerTy ++ ", " ++ errorTy ++ ">"

/-- The four fields of a fork request: which declared root, the arguments its parameter
list receives, whether the child is a daemon, and the region to link it to. -/
def forkParams : List (String × String) :=
  [("root", "number"), ("args", "ReadonlyArray<unknown>"), ("daemon", "boolean"),
    ("region", "Option.Option<number>")]

/-- The two fields of a plain root reference: which declared root, and its arguments. What
`uninterruptibleIn` and `interruptibleIn` take. -/
def rootParams : List (String × String) :=
  [("root", "number"), ("args", "ReadonlyArray<unknown>")]

/-- The request spelling of a fork: the right-nested product `requestSpelling` builds
(`Effect4/Target/TypeScript/ScriptFlow.lean:201-204`), which is exactly the nesting
`Effects.Trace.ToVal` builds from the parameter product. -/
def forkRequestTy : String := requestSpelling forkParams

/-- The request spelling of a masked or unmasked body. -/
def rootRequestTy : String := requestSpelling rootParams

/-- The profile's rows, in `FiberOp.index` order. Ordinary `OpSpec` rows: `tableAlphabet`
builds the `FlowAlphabet` from them and `Skeleton.render` prints them
(`Effect4/Target/TypeScript/SkeletonRender.lean:96-97`). -/
def fiberProfile (answerTy errorTy : String) : List OpSpec :=
  [ { name := "fork", kind := OpKind.family, requestTy := forkRequestTy,
      answerTy := handleTy answerTy errorTy, errorTy := "never", params := forkParams }
  , { name := "forkScoped", kind := OpKind.family, requestTy := forkRequestTy,
      answerTy := handleTy answerTy errorTy, errorTy := "never", params := forkParams }
  , { name := "join", kind := OpKind.family, requestTy := handleTy answerTy errorTy,
      answerTy := answerTy, errorTy := errorTy,
      params := [("fiber", handleTy answerTy errorTy)] }
  , { name := "awaitFiber", kind := OpKind.family, requestTy := handleTy answerTy errorTy,
      answerTy := exitTy answerTy errorTy, errorTy := "never",
      params := [("fiber", handleTy answerTy errorTy)] }
  , { name := "interruptFiber", kind := OpKind.family,
      requestTy := handleTy answerTy errorTy, answerTy := "void", errorTy := "never",
      params := [("fiber", handleTy answerTy errorTy)] }
  , { name := "interruptAll", kind := OpKind.family,
      requestTy := "ReadonlyArray<" ++ handleTy answerTy errorTy ++ ">",
      answerTy := "void", errorTy := "never",
      params := [("fibers", "ReadonlyArray<" ++ handleTy answerTy errorTy ++ ">")] }
    -- REFUSAL against rc.112's public API. The tracked children live on the fiber
    -- *implementation*: the field `_children` (`internal/effect.ts:534`) and the accessor
    -- `children()` (`:703-705`), populated by `forkUnsafe` only for a non-daemon fork
    -- (`:5279-5282`, which is `commitFork_daemon_untracked`). The public `Fiber.Fiber`
    -- (`Fiber.ts:70-92`) exposes neither, `./internal/*` is not exported, and the one public
    -- combinator is the *fused* `Effect.awaitAllChildren` (`internal/effect.ts:5314-5334`),
    -- which snapshots before and awaits after one effect and never hands the snapshot out.
    -- These two rows are the unfused halves the machine is stated over
    -- (`WithFiberAction.snapshotChildren` / `awaitAll`); the host tail reads rc.112's own
    -- state through a documented cast, so a golden over them is evidence about the runtime's
    -- state and never a claim about its public surface, until rc.112 exports the pair
    -- (`docs/research/2026-09-03-lowering-l2-host-tails.md` §12.1).
  , { name := "childrenSnapshot", kind := OpKind.family, requestTy := "void",
      answerTy := "ReadonlyArray<" ++ handleTy answerTy errorTy ++ ">", errorTy := "never",
      params := [] }
  , { name := "awaitChildren", kind := OpKind.family,
      requestTy := "ReadonlyArray<" ++ handleTy answerTy errorTy ++ ">",
      answerTy := "void", errorTy := "never",
      params := [("snapshot", "ReadonlyArray<" ++ handleTy answerTy errorTy ++ ">")] }
  , { name := "raceAll", kind := OpKind.family,
      requestTy := "ReadonlyArray<readonly [number, ReadonlyArray<unknown>]>",
      answerTy := answerTy, errorTy := errorTy,
      params := [("entrants", "ReadonlyArray<readonly [number, ReadonlyArray<unknown>]>")] }
  , { name := "uninterruptibleIn", kind := OpKind.family, requestTy := rootRequestTy,
      answerTy := answerTy, errorTy := errorTy, params := rootParams }
  , { name := "interruptibleIn", kind := OpKind.family, requestTy := rootRequestTy,
      answerTy := answerTy, errorTy := errorTy, params := rootParams }
  , { name := "yieldNow", kind := OpKind.family, requestTy := "number",
      answerTy := "void", errorTy := "never", params := [("priority", "number")] }
  ]

theorem fiberProfile_length (answerTy errorTy : String) :
    (fiberProfile answerTy errorTy).length = FiberOp.count := rfl

/-! Every row of the profile is a legal generated binding name
(`Effect4/Target/TypeScript/EffectV4.lean:145-147`). `await` is reserved in the profile,
which is the same refusal the retired M3 `FiberFamily` (2026-09-04; the fact is `TypeScript.reservedIdentifiers`) already records, so
the row is `awaitFiber` and `interruptFiber` follows it for symmetry. The fork's request is
four slots, so `Lowering.tupleArgs` (`SkeletonRender.lean:58-61`) destructures it at the
call into exactly `fibers.fork(root, args, daemon, region)`. -/
#guard (fiberProfile "number" "number").all fun row =>
  Effect4.Target.EffectV4.bindingName row.name
#guard ((fiberProfile "number" "number")[0]!).arity = 4
#guard ((fiberProfile "number" "number")[2]!).arity = 1
#guard ((fiberProfile "number" "number")[6]!).requestTy = "void"
#guard ((fiberProfile "number" "number")[9]!).arity = 2
#guard ((fiberProfile "number" "number")[11]!).arity = 1

/-- A table that carries the profile: the profile's rows first, the flow's own operations
after. The profile is *prefixed*, so a table position below `FiberOp.count` is a profile
row and every other position is the flow's own. -/
def profileTable (answerTy errorTy : String) (user : List OpSpec) : List OpSpec :=
  fiberProfile answerTy errorTy ++ user

/-- The classification a compile and an interp are parameterised by: which alphabet
operations are profile operations. For a `tableAlphabet` over a `profileTable` this is the
table position, and nothing reads a name. -/
def profileOpOf {answerTy errorTy : String} {user : List OpSpec}
    (op : (tableAlphabet ⟨0⟩ (profileTable answerTy errorTy user)).Op) : Option FiberOp :=
  FiberOp.ofIndex op.val

/-! ## 2. The value alphabet of the profile

Every request and answer of the profile is a `Val` (`Effects/Trace.lean:41-50`). These are
the codings, each with its inverse; the fork's `Val → Option FiberId` is the answer to
"where does a handle become a `FiberId`". -/

/-- The handle a fork answers with: the `Fiber` tag and the child's id. -/
def handleValue (id : FiberId) : Val := Val.pair (Val.str "Fiber") (Val.nat id.value)

/-- **The decoding a request's `fiber` argument goes through.** It lives on the profile's
value alphabet, not on the machine: `RunInterp.fiberValue` mints a handle
(`Effect4/Deep/Fibers.lean:433-434`) and this reads one back, and the two are inverse. -/
def handleOf : Val → Option FiberId
  | Val.pair (Val.str "Fiber") (Val.nat n) => some ⟨n⟩
  | _ => none

theorem handleOf_handleValue (id : FiberId) : handleOf (handleValue id) = some id := by
  cases id; rfl

/-- A number on the wire: the `yieldNow` priority. -/
def natOf : Val → Option Nat
  | Val.nat n => some n
  | _ => none

/-- A list on the wire, as `Effects.Trace.ToVal (List α)` spells it
(`Effects/Trace.lean:67-68`): right-nested pairs terminated by `unit`. -/
def listValue : List Val → Val
  | [] => Val.unit
  | value :: rest => Val.pair value (listValue rest)

def listOf : Val → Option (List Val)
  | Val.unit => some []
  | Val.pair value rest => (listOf rest).map (value :: ·)
  | _ => none

theorem listOf_listValue (values : List Val) : listOf (listValue values) = some values := by
  induction values with
  | nil => rfl
  | cons value rest ih => simp [listValue, listOf, ih]

def handlesValue (ids : List FiberId) : Val := listValue (ids.map handleValue)

def handlesOf (value : Val) : Option (List FiberId) :=
  (listOf value).bind fun values => values.foldr
    (fun v acc => match handleOf v, acc with
      | some id, some rest => some (id :: rest)
      | _, _ => none) (some [])

/-- The exit `await` answers with, as a value: `Result.Result<A, E>` on the host and
`pair (bool ok) payload` on the wire. A failure projects to its first `fail` error exactly
as `Exit.toOutcome` does (`RegionSimulation.failuresOfCause`,
`Effect4/Semantics/RegionSimulation.lean:458-459`); a cause carrying only a `die` or an
`interrupt` has no `Val` preimage and reads as `unit`, which is the recorded loss. -/
def exitAsValue (exit : Res) : Val :=
  match exit with
  | Effect4.Exit.success value => Val.pair (Val.bool true) value
  | Effect4.Exit.failure cause =>
    Val.pair (Val.bool false)
      (match failuresOfCause cause with
        | error :: _ => error
        | [] => Val.unit)

/-- A plain reference to a declared root and the arguments its parameter list receives.
What `uninterruptibleIn` and `interruptibleIn` carry. -/
structure RootRequest where
  root : BlockId
  args : List Val
deriving DecidableEq, Repr

def RootRequest.value (request : RootRequest) : Val :=
  Val.pair (Val.nat request.root.value) (listValue request.args)

def rootRequestOf : Val → Option RootRequest
  | Val.pair (Val.nat root) args => (listOf args).map fun args => ⟨⟨root⟩, args⟩
  | _ => none

theorem rootRequestOf_value (request : RootRequest) :
    rootRequestOf request.value = some request := by
  obtain ⟨root, args⟩ := request
  simp [RootRequest.value, rootRequestOf, listOf_listValue]

/-- A fork request, decoded. `root` is a **declared root** of the flow (`RegionFlow.roots`,
`.lake/packages/effects/Effects/Flow/Region.lean:83-91`), never an arbitrary block. -/
structure ForkRequest where
  root : BlockId
  args : List Val
  daemon : Bool
  region : Option Nat
deriving DecidableEq, Repr

/-- The request on the wire: the right-nested product of the four `forkParams`. -/
def ForkRequest.value (request : ForkRequest) : Val :=
  Val.pair (Val.nat request.root.value)
    (Val.pair (listValue request.args)
      (Val.pair (Val.bool request.daemon)
        (match request.region with
          | none => Val.none
          | some region => Val.some (Val.nat region))))

def forkRequestOf : Val → Option ForkRequest
  | Val.pair (Val.nat root) (Val.pair args (Val.pair (Val.bool daemon) region)) =>
    match listOf args, region with
    | some args, Val.none => some ⟨⟨root⟩, args, daemon, none⟩
    | some args, Val.some (Val.nat region) => some ⟨⟨root⟩, args, daemon, some region⟩
    | _, _ => none
  | _ => none

theorem forkRequestOf_value (request : ForkRequest) :
    forkRequestOf request.value = some request := by
  obtain ⟨root, args, daemon, region⟩ := request
  cases region <;> simp [ForkRequest.value, forkRequestOf, listOf_listValue]

/-- One entrant of a `raceAll`: a declared root and its arguments. -/
def entrantsOf (value : Val) : Option (List (BlockId × List Val)) :=
  (listOf value).bind fun values => values.foldr
    (fun v acc => match v, acc with
      | Val.pair (Val.nat root) args, some rest =>
        (listOf args).map fun args => (⟨root⟩, args) :: rest
      | _, _ => none) (some [])

/-! ## 3. The run-time refusal

Review finding 2, cost (a) (`docs/research/2026-09-03-deep-plan-review.md:110-115`): the
named block sits inside a *request value*, so `danglingSuccessor`, `reachSet` and
`CyclesWF` never see it. "The request names a declared root of this flow with a matching
parameter count" is therefore a decidable check **at the operation** and a strictly weaker
guarantee than an admission clause. It is recorded here rather than assumed. -/

/-- Why the machine refuses a profile operation. A refusal is a **defect**, not a typed
failure: nothing in the flow declared it, so a `performCatch` must not be able to catch it
(`docs/DESIGN-BASIS.md:121-125`). -/
inductive ForkRefusal where
  /-- The request value is not of the operation's shape. -/
  | requestMalformed (request : Val)
  /-- The named block is not a declared root of this flow. -/
  | rootUndeclared (root : BlockId)
  /-- The named root is declared but resolves to no block. -/
  | rootUnknown (root : BlockId)
  /-- The root's parameter list and the supplied argument list disagree. -/
  | rootArity (root : BlockId) (declared supplied : Nat)
  /-- A `fiber` argument that does not decode to a handle. -/
  | handleMalformed (request : Val)
  /-- `forkScoped` names a region; the ambient scope is the machine's, not the request's. -/
  | scopedNamesRegion (root : BlockId)
deriving DecidableEq, Repr

variable {Ty : Type}

/-- The decidable check of one root reference. -/
def checkRoot (flow : RegionFlow Ty) (root : BlockId) (args : List Val) :
    Option ForkRefusal :=
  if !(flow.roots.contains root) then some (.rootUndeclared root)
  else
    match flow.block? root with
    | none => some (.rootUnknown root)
    | some block =>
      if block.params.length = args.length then none
      else some (.rootArity root block.params.length args.length)

/-- The fork's run-time refusal, in full. -/
def checkFork (flow : RegionFlow Ty) (request : Val) : Except ForkRefusal ForkRequest :=
  match forkRequestOf request with
  | none => .error (.requestMalformed request)
  | some decoded =>
    match checkRoot flow decoded.root decoded.args with
    | some refusal => .error refusal
    | none => .ok decoded

/-- The refusal of any profile operation at a request value; `none` is "admitted". -/
def refusal? (flow : RegionFlow Ty) : FiberOp → Val → Option ForkRefusal
  | .fork, request =>
    match checkFork flow request with
    | .error refusal => some refusal
    | .ok _ => none
  | .forkScoped, request =>
    match checkFork flow request with
    | .error refusal => some refusal
    | .ok decoded =>
      match decoded.region with
      | some _ => some (.scopedNamesRegion decoded.root)
      | none => none
  | .uninterruptibleIn, request
  | .interruptibleIn, request =>
    match rootRequestOf request with
    | none => some (.requestMalformed request)
    | some decoded => checkRoot flow decoded.root decoded.args
  | .join, request
  | .await, request
  | .interrupt, request =>
    match handleOf request with
    | some _ => none
    | none => some (.handleMalformed request)
  | .interruptAll, request
  | .awaitChildren, request =>
    match handlesOf request with
    | some _ => none
    | none => some (.handleMalformed request)
  | .childrenSnapshot, _ => none
  | .yieldNow, request =>
    match natOf request with
    | some _ => none
    | none => some (.requestMalformed request)
  | .raceAll, request =>
    match entrantsOf request with
    | none => some (.requestMalformed request)
    | some entrants =>
      entrants.foldr (fun entrant acc =>
        match checkRoot flow entrant.1 entrant.2 with
        | some refusal => some refusal
        | none => acc) none

/-- The refusal that cannot travel on a `WithFiberAction`: `join` and `await` compile to a
primitive `parkOf` classifies, and `yieldNow` to `Prim.yieldNowWith`, and neither path can
carry a cause. Those three are raised by the **interp's `suspendBody`** (§5) at a point the
compile suspends, so the compile still emits `Prim.failure` nowhere (P2). Every other row's
refusal is `WithFiberAction.refuse`. -/
def compileRefusal? (flow : RegionFlow Ty) (kind : FiberOp) (request : Val) :
    Option ForkRefusal :=
  if kind.direct then refusal? flow kind request else none

/-- The refusal of the operation performed at a point, when that operation is one of the
three `direct` rows. This is what `forkTable.suspendBody` reads before it falls through to
`regionSuspendBody`. -/
def directRefusalAt (alphabet : FlowAlphabet Ty) (flow : RegionFlow Ty)
    (opOf : alphabet.Op → Option FiberOp) (point : Config) : Option ForkRefusal :=
  match performOp alphabet flow point with
  | none => none
  | some (op, request) =>
    match opOf op with
    | none => none
    | some kind => compileRefusal? flow kind request

/-! ## 4. The compile

Spike S4 (`docs/research/2026-09-03-spike-s4-compile.md`) rewrote `compileRegion`: P1 emits
**one** frame per region, `Prim.onSuccessAndFailure body (RegionName.regionCont region
enterPoint) (RegionName.close region enterPoint)`, with each release an `onExit` frame whose
`finalizerExit` is constantly `Exit.success ()` and the whole close applied once as
`closeExit`; P2 sends every frontier arm to `Prim.suspend point` rather than to
`Prim.failure Cause.empty`, so `compileRegion_not_failure` holds; P3 compiles a
`performCatch` to `Prim.onSuccessAndFailure (Prim.suspend point) (RegionName.cont point)
(RegionName.caught point)` and routes the failure through `regionInterp.contE`.

`compileFork` is therefore written to **call** the new `compileRegion` on every arm it does
not change. It differs in exactly four places: the two `perform` arms when the operation is
a profile row, and the three recursion sites (`jump`, `choose`, the `enter` body) where the
recursive call has to be `compileFork` so a nested block's profile operation is still seen.
Every other arm — `ret`, the six frontier arms, `acquire`, `leave` — is one delegation, so
this module does not mirror `compileRegion`'s bodies and does not go stale when they change
again. `compileFork_eq_compileRegion` then has three real cases and six `rfl`s. -/

/-- Which primitive a profile operation compiles to. `fork`, `forkScoped`, `interrupt`,
`interruptAll`, `childrenSnapshot`, `awaitChildren`, `raceAll` and the two mask rows reach
the fiber through `withFiber` (rc.112 `:1147`, the only way to the raw fiber); `join` and
`await` *park* on the target, which `parkOf` classifies; `yieldNow` is `Prim.yieldNowWith`,
a constructor since spike S1, and the machine reads it before it consults `parkOf`
(`Effect4/Deep/Fibers.lean:701-709`). -/
def fiberPrim : FiberOp → Config → Val → Code
  | .join, point, _ => Effect4.Prim.sync point
  | .await, point, _ => Effect4.Prim.sync point
  | .yieldNow, _, request => Effect4.Prim.yieldNowWith ((natOf request).getD 0)
  | _, point, _ => Effect4.Prim.withFiber point

/-- Whether a profile operation's continuation needs the *failure* arm as well. `join`
delivers the child's cause as a machine-level `Prim.failure` on the resume, not as an
oracle `.error`, so a caught `join` needs `onSuccessAndFailure` — packet P3's repair
(`docs/research/2026-09-03-deep-plan.md:63-65`), here for the profile arm only. -/
def catchesMachineFailure : FiberOp → Bool
  | .join => true
  | .raceAll => true
  | .uninterruptibleIn => true
  | .interruptibleIn => true
  | _ => false

/-- The region-aware compilation with the fiber profile. Structural on fuel, as
`compileRegion` is, so the compiled program is kernel-reducible and the witnesses of §9
evaluate. Every arm this module does not change is **one delegation** to the new
`compileRegion`; only the two `perform` arms and the three recursion sites are written
out. -/
def compileFork (alphabet : FlowAlphabet Ty) (flow : RegionFlow Ty)
    (opOf : alphabet.Op → Option FiberOp) :
    Nat → BlockId → Effect4.Flow.Env → Effect4.Flow.Tape → Code
  | 0, block, env, tape => compileRegion alphabet flow 0 block env tape
  | fuel + 1, block, env, tape =>
    match flow.block? block with
    | none => compileRegion alphabet flow (fuel + 1) block env tape
    | some current =>
      match current.term with
      | .plain term =>
        match Effect4.Flow.plan alphabet
            { id := current.id, params := current.params, term := term } env tape with
        | .jump target env' => compileFork alphabet flow opOf fuel target env' tape
        | .choose _ _ target env' rest => compileFork alphabet flow opOf fuel target env' rest
        | .perform op request _ _ =>
          performShape alphabet flow opOf op request ⟨fuel + 1, block, env, tape⟩ false
        | .performCatch op request _ _ _ _ =>
          performShape alphabet flow opOf op request ⟨fuel + 1, block, env, tape⟩ true
        | _ => compileRegion alphabet flow (fuel + 1) block env tape
      | .enter region body args =>
        match Effect4.Flow.readArgs env args with
        | some values =>
          -- P1: one frame per region, answering both arms.
          Effect4.Prim.onSuccessAndFailure (compileFork alphabet flow opOf fuel body values tape)
            (RegionName.regionCont region.value ⟨fuel + 1, block, env, tape⟩)
            (RegionName.close region.value ⟨fuel + 1, block, env, tape⟩)
        | none => compileRegion alphabet flow (fuel + 1) block env tape
      | _ => compileRegion alphabet flow (fuel + 1) block env tape
where
  /-- The only arm that differs from `compileRegion`. An operation outside the profile is
  delegated, so it is `compileRegion`'s own shape whatever that becomes. A profile
  operation is its own primitive under `RegionName.cont`; a caught one that can fail at the
  machine level gets P3's `RegionName.caught` cause name as well; and a refused `direct`
  row compiles to `Prim.suspend point`, whose `suspendBody` raises the defect (§5), so this
  compile emits `Prim.failure` **nowhere** — P2's law survives the profile. -/
  performShape (alphabet : FlowAlphabet Ty) (flow : RegionFlow Ty)
      (opOf : alphabet.Op → Option FiberOp) (op : alphabet.Op) (request : Val)
      (point : Config) (caught : Bool) : Code :=
    match opOf op with
    | none => compileRegion alphabet flow point.fuel point.block point.env point.tape
    | some kind =>
      match compileRefusal? flow kind request with
      | some _ => Effect4.Prim.suspend point
      | none =>
        if caught && catchesMachineFailure kind then
          Effect4.Prim.onSuccessAndFailure (fiberPrim kind point request)
            (RegionName.cont point) (RegionName.caught point)
        else
          Effect4.Prim.onSuccess (fiberPrim kind point request) (RegionName.cont point)

/-- The compilation at a point, as `RegionSimulation.compileAt` is (`:645-647`). -/
def compileForkAt (alphabet : FlowAlphabet Ty) (flow : RegionFlow Ty)
    (opOf : alphabet.Op → Option FiberOp) (point : Config) : Code :=
  compileFork alphabet flow opOf point.fuel point.block point.env point.tape

/-- Off the profile the compile *is* `compileRegion`, by delegation rather than by a
mirrored body. This is the statement the landing needs: adding the profile arm to
`compileRegion` changes no existing program, whatever `compileRegion`'s arms are. -/
theorem compileFork_perform_off_profile (alphabet : FlowAlphabet Ty)
    (flow : RegionFlow Ty) (opOf : alphabet.Op → Option FiberOp) (op : alphabet.Op)
    (request : Val) (point : Config) (caught : Bool) (h : opOf op = none) :
    compileFork.performShape alphabet flow opOf op request point caught =
      compileRegion alphabet flow point.fuel point.block point.env point.tape := by
  simp [compileFork.performShape, h]

/-- **A flow with no profile operation compiles exactly as it did.** This is the statement
the landing needs to add the arm to `compileRegion` without re-proving a single existing
receipt: `E4-TARGET-CE-019..021`, the five region instances closed by evaluation in
`Effect4Test/Semantics/RegionSimulationContract.lean`, and the harness's `frame-trace`
output are all about programs this equation covers. Three real cases — the two transfers
and the region body — and the rest by delegation. -/
theorem compileFork_eq_compileRegion (alphabet : FlowAlphabet Ty) (flow : RegionFlow Ty) :
    ∀ (fuel : Nat) (block : BlockId) (env : Effect4.Flow.Env) (tape : Effect4.Flow.Tape),
      compileFork alphabet flow (fun _ => none) fuel block env tape =
        compileRegion alphabet flow fuel block env tape := by
  intro fuel
  induction fuel with
  | zero => intro block env tape; rfl
  | succ fuel ih =>
    intro block env tape
    cases hblock : flow.block? block with
    | none => simp only [compileFork, hblock]
    | some current =>
      cases hterm : current.term with
      | plain term =>
        cases hplan : Effect4.Flow.plan alphabet
            { id := current.id, params := current.params, term := term } env tape with
        | ret value => simp only [compileFork, hblock, hterm, hplan]
        | jump target env' =>
          simp only [compileFork, compileRegion, hblock, hterm, hplan, ih]
        | perform op request target env' =>
          simp only [compileFork, hblock, hterm, hplan, compileFork.performShape]
        | performCatch op request target env' onError errorEnv =>
          simp only [compileFork, hblock, hterm, hplan, compileFork.performShape]
        | choose site branch target env' rest =>
          simp only [compileFork, compileRegion, hblock, hterm, hplan, ih]
        | stuck => simp only [compileFork, hblock, hterm, hplan]
        | exhausted site => simp only [compileFork, hblock, hterm, hplan]
        | mismatch expected actual => simp only [compileFork, hblock, hterm, hplan]
      | enter region body args =>
        cases hargs : Effect4.Flow.readArgs env args with
        | none => simp only [compileFork, hblock, hterm, hargs]
        | some values => simp only [compileFork, compileRegion, hblock, hterm, hargs, ih]
      | acquire operation request release target args =>
        simp only [compileFork, hblock, hterm]
      | leave value => simp only [compileFork, hblock, hterm]

/-- **P2 survives the profile.** `compileFork` emits `Prim.failure` nowhere either: the
profile's arms emit `suspend`, `onSuccess` or `onSuccessAndFailure`, the transfers recurse,
and everything else is `compileRegion`, which `compileRegion_not_failure` already settles.
A refused `direct` row is a `Prim.suspend`, and the defect is raised by the interp. -/
theorem compileFork_not_failure (alphabet : FlowAlphabet Ty) (flow : RegionFlow Ty)
    (opOf : alphabet.Op → Option FiberOp) :
    ∀ (fuel : Nat) (block : BlockId) (env : Effect4.Flow.Env) (tape : Effect4.Flow.Tape),
      isFailure (compileFork alphabet flow opOf fuel block env tape) = false := by
  intro fuel
  induction fuel with
  | zero =>
    intro block env tape
    simp only [compileFork]
    exact compileRegion_not_failure alphabet flow 0 block env tape
  | succ fuel ih =>
    intro block env tape
    cases hblock : flow.block? block with
    | none =>
      simp only [compileFork, hblock]
      exact compileRegion_not_failure alphabet flow (fuel + 1) block env tape
    | some current =>
      cases hterm : current.term with
      | plain term =>
        cases hplan : Effect4.Flow.plan alphabet
            { id := current.id, params := current.params, term := term } env tape with
        | ret value =>
          simp only [compileFork, hblock, hterm, hplan]
          exact compileRegion_not_failure alphabet flow (fuel + 1) block env tape
        | jump target env' => simp only [compileFork, hblock, hterm, hplan, ih]
        | choose site branch target env' rest =>
          simp only [compileFork, hblock, hterm, hplan, ih]
        | perform op request target env' =>
          simp only [compileFork, hblock, hterm, hplan]
          exact performShape_not_failure alphabet flow opOf op request _ false
        | performCatch op request target env' onError errorEnv =>
          simp only [compileFork, hblock, hterm, hplan]
          exact performShape_not_failure alphabet flow opOf op request _ true
        | stuck =>
          simp only [compileFork, hblock, hterm, hplan]
          exact compileRegion_not_failure alphabet flow (fuel + 1) block env tape
        | exhausted site =>
          simp only [compileFork, hblock, hterm, hplan]
          exact compileRegion_not_failure alphabet flow (fuel + 1) block env tape
        | mismatch expected actual =>
          simp only [compileFork, hblock, hterm, hplan]
          exact compileRegion_not_failure alphabet flow (fuel + 1) block env tape
      | enter region body args =>
        cases hargs : Effect4.Flow.readArgs env args with
        | none =>
          simp only [compileFork, hblock, hterm, hargs]
          exact compileRegion_not_failure alphabet flow (fuel + 1) block env tape
        | some values => simp only [compileFork, hblock, hterm, hargs, isFailure]
      | acquire operation request release target args =>
        simp only [compileFork, hblock, hterm]
        exact compileRegion_not_failure alphabet flow (fuel + 1) block env tape
      | leave value =>
        simp only [compileFork, hblock, hterm]
        exact compileRegion_not_failure alphabet flow (fuel + 1) block env tape
where
  /-- The profile arm, on its own. -/
  performShape_not_failure (alphabet : FlowAlphabet Ty) (flow : RegionFlow Ty)
      (opOf : alphabet.Op → Option FiberOp) (op : alphabet.Op) (request : Val)
      (point : Config) (caught : Bool) :
      isFailure (compileFork.performShape alphabet flow opOf op request point caught)
        = false := by
    unfold compileFork.performShape
    split
    · exact compileRegion_not_failure alphabet flow point.fuel point.block point.env point.tape
    · split
      · rfl
      · split <;> rfl

/-! ## 5. The interp

`regionInterp` (`Effect4/Semantics/RegionSimulation.lean:874-931`) is reused under a record
update: `contA` and `contE` move because the *compile* they call is `compileFork` rather
than `compileRegion`, and `suspendBody` moves because it is where the three `direct` rows'
refusal is raised. Everything else — `cancelThenFail` (S1), `finalizerExit` constantly
`Exit.success ()` (S4's P1), `syncValue`, and the six loop fillers — is inherited. At the
landing, when `compileRegion` gains the arm, `contA` and `contE` are the same functions
again and only `suspendBody` differs. -/

abbrev ForkAction := Effect4.Deep.WithFiberAction RegionName Config Val Val Unit Unit Unit Unit
abbrev ForkInterp := Effect4.Deep.RunInterp RegionName Config Val Val Unit Unit Unit Unit Unit
abbrev ForkMachine := Effect4.Deep.RunMachine RegionName Config Val Val Unit Unit Unit Unit Unit
abbrev ForkFiber := Effect4.Deep.RunFiber RegionName Config Val Val Unit Unit Unit Unit
abbrev ForkDecision := Effect4.Deep.RunDecision RegionName Config Val Val Unit Unit Unit
abbrev ForkReplay := Effect4.Deep.ReplayResult RegionName Config Val Val Unit Unit Unit Unit Unit

/-- The pure continuation table: `regionInterp` with `compileRegion` replaced by
`compileFork` and `suspendBody` guarded by the three `direct` rows' refusal. The five
`RegionName` arms are S4's, unchanged in shape: `cont`'s erroring answer is a machine-level
failure (P3 moved the catch routing to `contE`), `regionCont` checks the region's close
first (P1) and then resumes at `leaveConfig`'s configuration (S4b), `caught` routes the
caught failure, `close` appends the closing reasons, and `fin` is an `onExit` finalizer name
whose value arm is never demanded. -/
def forkTable (alphabet : FlowAlphabet Ty) (flow : RegionFlow Ty)
    (opOf : alphabet.Op → Option FiberOp) (oracle : RegionOracle) : Table :=
  { regionInterp alphabet flow oracle with
    contA := fun name value =>
      match name with
      | RegionName.cont point =>
        match oracle.answer point with
        | .error error => Effect4.Prim.failure (Effect4.Cause.fail error)
        | .ok _ =>
          match performCont alphabet flow point with
          | some (target, env', none) =>
            compileFork alphabet flow opOf (point.fuel - 1) target (env' ++ [value]) point.tape
          | some (target, env', some region) =>
            Effect4.Prim.onExit
              (compileFork alphabet flow opOf (point.fuel - 1) target (env' ++ [value])
                point.tape)
              (RegionName.fin region point) false
          | none => Effect4.Prim.suspend point
      | RegionName.regionCont _ point =>
        match closeExit oracle (oracle.registrations point) with
        | Effect4.Exit.failure closing => Effect4.Prim.failure closing
        | Effect4.Exit.success _ =>
          -- S4b: resume at the configuration the runner holds at the region's `leave`
          -- (fuel, block and tape reached by the body), exactly as `regionInterp.contA`
          -- does; resuming at the *enter*'s `point.fuel - 1` and `point.tape` was the
          -- defect `tapeAfterRegion` refuted.
          match leaveConfig alphabet flow oracle.answer oracle.release point with
          | some resume =>
            compileFork alphabet flow opOf resume.fuel resume.block [value] resume.tape
          | none => Effect4.Prim.suspend point
      | RegionName.caught point => Effect4.Prim.suspend point
      | RegionName.close _ point => Effect4.Prim.suspend point
      | RegionName.fin _ point => Effect4.Prim.suspend point
    contE := fun name cause =>
      match name with
      | RegionName.caught point =>
        match catchCont alphabet flow point, (failuresOfCause cause).head? with
        | some (onError, errorEnv), some error =>
          compileFork alphabet flow opOf (point.fuel - 1) onError (errorEnv ++ [error])
            point.tape
        | _, _ => Effect4.Prim.failure cause
      | RegionName.close _ point =>
        match closeExit oracle (oracle.registrations point) with
        | Effect4.Exit.success _ => Effect4.Prim.failure cause
        | Effect4.Exit.failure closing =>
          Effect4.Prim.failure ⟨cause.reasons ++ closing.reasons⟩
      | _ => Effect4.Prim.failure cause
    -- The one field that is not `regionInterp`'s: a `direct` row whose request is refused
    -- compiles to `Prim.suspend point` (so the compile emits no failure, P2), and the
    -- defect is raised here, at the operation, on the run's own configuration.
    suspendBody := fun point =>
      match directRefusalAt alphabet flow opOf point with
      | some _ => Effect4.Prim.failure (Effect4.Cause.die ())
      | none => regionSuspendBody alphabet flow oracle point }

/-- Which primitives park, and how. `join` and `await` are the profile's two parks; the
target is read out of the request value through `handleOf`, and the mode is what decides
whether the child's exit continues as an effect (`join`, rc.112 `:5291`) or as a value
(`await`, `:5304`). `ParkKind` has only this one constructor since spike S1 made the yield
and the async `Prim` constructors (`Effect4/Deep/Fibers.lean:52-54`). -/
def forkParkOf (alphabet : FlowAlphabet Ty) (flow : RegionFlow Ty)
    (opOf : alphabet.Op → Option FiberOp) :
    Code → Option (Except (Effect4.Cause Val Unit Unit Unit) Effect4.Deep.ParkKind)
  | Effect4.Prim.sync point =>
    match performOp alphabet flow point with
    | none => none
    | some (op, request) =>
      -- A request that is not a fiber handle is refused with a cause through the park
      -- channel itself (S3 §9), never answered from the oracle.
      match opOf op with
      | some .join =>
        some (match handleOf request with
          | some target =>
            Except.ok (Effect4.Deep.ParkKind.join target Effect4.Supervision.ObserverMode.joinEffect)
          | none => Except.error (Effect4.Cause.die ()))
      | some .await =>
        some (match handleOf request with
          | some target =>
            Except.ok (Effect4.Deep.ParkKind.join target Effect4.Supervision.ObserverMode.awaitValue)
          | none => Except.error (Effect4.Cause.die ()))
      | _ => none
  | _ => none

/-- The action an admitted profile operation takes. This is where a Flow *names* a
concurrent child: the request's `root` and `args` are compiled, at the point's own fuel and
tape, into the child's program, and the machine spawns a fiber over it. Immediacy is
**not** here — it is `RunDecision.fire`/`flush` (review finding 3), so
`startImmediately := false` always. -/
def forkActionOf (alphabet : FlowAlphabet Ty) (flow : RegionFlow Ty)
    (opOf : alphabet.Op → Option FiberOp) (point : Config) :
    FiberOp → Val → Option ForkAction
  | .fork, request =>
    match forkRequestOf request with
    | none => none
    | some decoded =>
      let program := compileFork alphabet flow opOf point.fuel decoded.root decoded.args
        point.tape
      let options : Effect4.Supervision.ForkOptions :=
        ⟨false, decoded.daemon, Effect4.Supervision.MaskMode.inherit⟩
      some (match decoded.region with
        | none => Effect4.Deep.WithFiberAction.fork program options
        | some scope =>
          Effect4.Deep.WithFiberAction.forkIn program options scope point.fuel)
  | .forkScoped, request =>
    match forkRequestOf request with
    | none => none
    | some decoded =>
      let program := compileFork alphabet flow opOf point.fuel decoded.root decoded.args
        point.tape
      let options : Effect4.Supervision.ForkOptions :=
        ⟨false, decoded.daemon, Effect4.Supervision.MaskMode.inherit⟩
      some (Effect4.Deep.WithFiberAction.forkScoped program options point.fuel)
  | .uninterruptibleIn, request =>
    match rootRequestOf request with
    | none => none
    | some decoded =>
      some (Effect4.Deep.WithFiberAction.setInterruptible
        (compileFork alphabet flow opOf point.fuel decoded.root decoded.args point.tape)
        false)
  | .interruptibleIn, request =>
    match rootRequestOf request with
    | none => none
    | some decoded =>
      some (Effect4.Deep.WithFiberAction.setInterruptible
        (compileFork alphabet flow opOf point.fuel decoded.root decoded.args point.tape)
        true)
  | .interrupt, request =>
    match handleOf request with
    | none => none
    | some target => some (Effect4.Deep.WithFiberAction.interrupt target)
  | .interruptAll, request =>
    match handlesOf request with
    | none => none
    | some targets => some (Effect4.Deep.WithFiberAction.interruptAll targets none)
  | .childrenSnapshot, _ => some Effect4.Deep.WithFiberAction.snapshotChildren
  | .awaitChildren, request =>
    match handlesOf request with
    | none => none
    | some snapshot => some (Effect4.Deep.WithFiberAction.awaitNewChildren snapshot)
  | .raceAll, request =>
    match entrantsOf request with
    | none => none
    | some entrants =>
      some (Effect4.Deep.WithFiberAction.raceAll
        (entrants.map fun entrant =>
          compileFork alphabet flow opOf point.fuel entrant.1 entrant.2 point.tape))
  | .join, _ => none
  | .await, _ => none
  | .yieldNow, _ => none

/-- What a `withFiber` thunk does. A refused operation answers `WithFiberAction.refuse`
(`Effect4/Deep/Fibers.lean:295-296`, `:896-898`) — the arm this spike's first pass asked
for — so the refusal is a machine event with a cause rather than a compile-time constant,
and the fiber fails with a **defect** rather than going stuck. -/
def forkWithFiberOf (alphabet : FlowAlphabet Ty) (flow : RegionFlow Ty)
    (opOf : alphabet.Op → Option FiberOp) (point : Config) : Option ForkAction :=
  match performOp alphabet flow point with
  | none => none
  | some (op, request) =>
    match opOf op with
    | none => none
    | some kind =>
      match refusal? flow kind request with
      | some _ => some (Effect4.Deep.WithFiberAction.refuse (Effect4.Cause.die ()))
      | none => forkActionOf alphabet flow opOf point kind request

/-- The machine-level interp of a forking flow. `χ := Unit` and `St := Unit`: the stores
are spike S2's, and nothing in the profile touches one. -/
def forkInterp (alphabet : FlowAlphabet Ty) (flow : RegionFlow Ty)
    (opOf : alphabet.Op → Option FiberOp) (oracle : RegionOracle) : ForkInterp where
  toPrimInterp := forkTable alphabet flow opOf oracle
  parkOf := forkParkOf alphabet flow opOf
  withFiberOf := forkWithFiberOf alphabet flow opOf
  syncState := fun _ _ => none
  registerAsync := fun _ _ _ state => (state, none)
  dueResumes := fun state => ([], state)
  -- No `Prim.async` is ever compiled, so no `asyncFinalizer` frame is ever pushed and
  -- neither cancel name is ever read; the fillers are the identity and a frontier name.
  cancelName := fun name _ _ => name
  abortName := RegionName.fin 0 ⟨0, ⟨0⟩, [], []⟩
  finalizerProgram := fun _ _ => none
  -- `restoreName`/`mergeName` are read only by the middleware exit path and a settled
  -- race, neither of which a witness here reaches. A `fin` name compiles to the empty
  -- failure — the compile's own frontier marker — so a use would be visible, not silent.
  restoreName := fun _ => RegionName.fin 0 ⟨0, ⟨0⟩, [], []⟩
  mergeName := fun _ => RegionName.fin 0 ⟨0, ⟨0⟩, [], []⟩
  scopeStatus := fun _ _ => some none
  scopeLinkFiber := fun _ _ _ _ state => some state
  dropFinalizer := fun _ _ state => some state
  closeScope := fun _ _ _ _ state => some (state, Effect4.Prim.success Val.unit)
  ambientScope := fun _ => none
  budgetOf := fun _ => (0, true)
  emptyContext := ()
  contextValue := fun _ => Val.unit
  exitValue := fun exit mode =>
    match mode with
    | Effect4.Supervision.ObserverMode.joinEffect => Effect4.Prim.ofExit exit
    | Effect4.Supervision.ObserverMode.awaitValue =>
      Effect4.Prim.success (exitAsValue exit)
  fiberValue := handleValue
  fibersValue := handlesValue
  exitsValue := fun exits => listValue (exits.map exitAsValue)
  voidValue := Val.unit
  encodeFiber := fun _ => ()
  stackAnnotations := fun _ => Effect4.ReasonAnnotations.empty
  asyncFiberError := ()
  missingScope := ()

/-- The oracle a forking flow runs against: the profile's operations answer `ok unit` —
their value is minted by the machine, not by a service, and `contA` continues with the
machine's value, never with the oracle's (`RegionSimulation.lean:381-389`) — and every
other operation is the flow's own service, through `statelessOracle` unchanged. -/
def forkAnswerOf (alphabet : FlowAlphabet Ty) (opOf : alphabet.Op → Option FiberOp)
    (answerOf : alphabet.Op → Val → Except Val Val) : alphabet.Op → Val → Except Val Val :=
  fun op request =>
    match opOf op with
    | some _ => .ok Val.unit
    | none => answerOf op request

def forkOracle (alphabet : FlowAlphabet Ty) (flow : RegionFlow Ty)
    (opOf : alphabet.Op → Option FiberOp)
    (answerOf : alphabet.Op → Val → Except Val Val) : RegionOracle :=
  statelessOracle alphabet flow (forkAnswerOf alphabet opOf answerOf)

/-! ## 6. `WellSourced`

Plan ruling 6 (`:48-52`) and review finding 12 (`:458-487`): `Prim` is a target-profile
machine syntax with no admission of its own, so the machine must carry the invariant that
every program it steps is the compile of an admitted flow. On the operation route the fork
arm makes it *provable*, because the child's program is literally a `compileFork` of the
flow at a point the request names. -/

/-- Every program the machine steps is the compile of this flow at some point. -/
def WellSourced (alphabet : FlowAlphabet Ty) (flow : RegionFlow Ty)
    (opOf : alphabet.Op → Option FiberOp) (program : Code) : Prop :=
  ∃ point : Config, program = compileForkAt alphabet flow opOf point

theorem wellSourced_compileForkAt (alphabet : FlowAlphabet Ty) (flow : RegionFlow Ty)
    (opOf : alphabet.Op → Option FiberOp) (point : Config) :
    WellSourced alphabet flow opOf (compileForkAt alphabet flow opOf point) :=
  ⟨point, rfl⟩

/-- Every program a `withFiber` action carries. Five of the seventeen actions carry one:
the three fork shapes, `setInterruptible`'s masked body, and `raceAll`'s entrant list
(`Effect4/Deep/Fibers.lean:254-297`). -/
def actionPrograms : ForkAction → List Code
  | Effect4.Deep.WithFiberAction.fork program _ => [program]
  | Effect4.Deep.WithFiberAction.forkIn program _ _ _ => [program]
  | Effect4.Deep.WithFiberAction.forkScoped program _ _ => [program]
  | Effect4.Deep.WithFiberAction.setInterruptible body _ => [body]
  | Effect4.Deep.WithFiberAction.raceAll entrants => entrants
  | _ => []

/-- **The fork arm, proved.** Every program the machine spawns a fiber over or masks — the
three fork shapes, a masked body, and every `raceAll` entrant — is the compile of *this*
flow at a point the request names. This is the arm review finding 12 says makes the
invariant provable, and it is provable because the request carries a **block reference**,
not a computation: DB-05's conditional (`docs/DESIGN-BASIS.md:216-219`) discharged by the
machine rather than by admission, exactly as review finding 2's cost (c) requires. -/
theorem wellSourced_actions (alphabet : FlowAlphabet Ty) (flow : RegionFlow Ty)
    (opOf : alphabet.Op → Option FiberOp) (point : Config) (action : ForkAction)
    (spawned : forkWithFiberOf alphabet flow opOf point = some action) :
    ∀ program ∈ actionPrograms action, WellSourced alphabet flow opOf program := by
  intro program mem
  have base : ∀ (root : BlockId) (args : List Val),
      WellSourced alphabet flow opOf
        (compileFork alphabet flow opOf point.fuel root args point.tape) :=
    fun root args => ⟨⟨point.fuel, root, args, point.tape⟩, rfl⟩
  unfold forkWithFiberOf at spawned
  cases hperf : performOp alphabet flow point with
  | none => simp only [hperf] at spawned; exact absurd spawned (by simp)
  | some pair =>
    obtain ⟨op, request⟩ := pair
    simp only [hperf] at spawned
    cases hkind : opOf op with
    | none => simp only [hkind] at spawned; exact absurd spawned (by simp)
    | some kind =>
      simp only [hkind] at spawned
      cases hrefusal : refusal? flow kind request with
      | some refusal =>
        simp only [hrefusal] at spawned
        injection spawned with shape
        subst shape
        simp [actionPrograms] at mem
      | none =>
        simp only [hrefusal] at spawned
        unfold forkActionOf at spawned
        cases kind with
        | fork =>
          cases hdecoded : forkRequestOf request with
          | none => simp only [hdecoded] at spawned; exact absurd spawned (by simp)
          | some decoded =>
            simp only [hdecoded] at spawned
            cases hregion : decoded.region with
            | none =>
              simp only [hregion] at spawned
              injection spawned with shape
              subst shape
              simp only [actionPrograms, List.mem_singleton] at mem
              subst mem
              exact base _ _
            | some scope =>
              simp only [hregion] at spawned
              injection spawned with shape
              subst shape
              simp only [actionPrograms, List.mem_singleton] at mem
              subst mem
              exact base _ _
        | forkScoped =>
          cases hdecoded : forkRequestOf request with
          | none => simp only [hdecoded] at spawned; exact absurd spawned (by simp)
          | some decoded =>
            simp only [hdecoded] at spawned
            injection spawned with shape
            subst shape
            simp only [actionPrograms, List.mem_singleton] at mem
            subst mem
            exact base _ _
        | uninterruptibleIn =>
          cases hdecoded : rootRequestOf request with
          | none => simp only [hdecoded] at spawned; exact absurd spawned (by simp)
          | some decoded =>
            simp only [hdecoded] at spawned
            injection spawned with shape
            subst shape
            simp only [actionPrograms, List.mem_singleton] at mem
            subst mem
            exact base _ _
        | interruptibleIn =>
          cases hdecoded : rootRequestOf request with
          | none => simp only [hdecoded] at spawned; exact absurd spawned (by simp)
          | some decoded =>
            simp only [hdecoded] at spawned
            injection spawned with shape
            subst shape
            simp only [actionPrograms, List.mem_singleton] at mem
            subst mem
            exact base _ _
        | join => exact absurd spawned (by simp)
        | await => exact absurd spawned (by simp)
        | yieldNow => exact absurd spawned (by simp)
        | interrupt =>
          cases hhandle : handleOf request with
          | none => simp only [hhandle] at spawned; exact absurd spawned (by simp)
          | some target =>
            simp only [hhandle] at spawned
            injection spawned with shape
            subst shape
            simp [actionPrograms] at mem
        | interruptAll =>
          cases hhandles : handlesOf request with
          | none => simp only [hhandles] at spawned; exact absurd spawned (by simp)
          | some targets =>
            simp only [hhandles] at spawned
            injection spawned with shape
            subst shape
            simp [actionPrograms] at mem
        | childrenSnapshot =>
          injection spawned with shape
          subst shape
          simp [actionPrograms] at mem
        | awaitChildren =>
          cases hhandles : handlesOf request with
          | none => simp only [hhandles] at spawned; exact absurd spawned (by simp)
          | some snapshot =>
            simp only [hhandles] at spawned
            injection spawned with shape
            subst shape
            simp [actionPrograms] at mem
        | raceAll =>
          cases hentrants : entrantsOf request with
          | none => simp only [hentrants] at spawned; exact absurd spawned (by simp)
          | some entrants =>
            simp only [hentrants] at spawned
            injection spawned with shape
            subst shape
            simp only [actionPrograms, List.mem_map] at mem
            obtain ⟨entrant, _, rfl⟩ := mem
            exact base _ _

/-- The fork arm, in the shape ruling 6 words it. -/
theorem wellSourced_fork (alphabet : FlowAlphabet Ty) (flow : RegionFlow Ty)
    (opOf : alphabet.Op → Option FiberOp) (point : Config) (program : Code)
    (options : Effect4.Supervision.ForkOptions)
    (spawned : forkWithFiberOf alphabet flow opOf point =
      some (Effect4.Deep.WithFiberAction.fork program options)) :
    WellSourced alphabet flow opOf program := by
  refine wellSourced_actions alphabet flow opOf point _ spawned program ?_
  simp [actionPrograms]

/-! ### The invariant over the fiber's whole configuration

This spike's first pass recorded (§7.1 of the report) that `WellSourced` on `current` alone
cannot be closed under the machine's step, because the machine steps intermediate programs
— a pushed frame's body, a `Prim.success value` between a resume and a `contA` — that are
not literally a compile image. The recommendation was to state the invariant on the fiber's
whole configuration, `current` plus `stack`. That is what follows. -/

/-- A fiber's whole configuration is well-sourced: its current primitive is the compile's
image, and so is every frame on its stack. -/
def ConfigWellSourced (alphabet : FlowAlphabet Ty) (flow : RegionFlow Ty)
    (opOf : alphabet.Op → Option FiberOp) (f : ForkFiber) : Prop :=
  WellSourced alphabet flow opOf f.frame.current ∧
    ∀ frame ∈ f.frame.stack, WellSourced alphabet flow opOf frame

/-- **The fork arm of the closure, proved.** A fiber the machine creates over a program the
fork named starts with that program as its `current` and an **empty stack**
(`FrameFiber.start`), so its whole configuration is well-sourced from birth. `spawn`
(`Effect4/Deep/Fibers.lean:616-634`) builds its child by exactly this call. -/
theorem configWellSourced_make (alphabet : FlowAlphabet Ty) (flow : RegionFlow Ty)
    (opOf : alphabet.Op → Option FiberOp) (id : FiberId) (program : Code)
    (interruptible : Bool) (budget : Nat × Bool) (context : Unit)
    (sourced : WellSourced alphabet flow opOf program) :
    ConfigWellSourced alphabet flow opOf
      (Effect4.Deep.RunFiber.make id program interruptible budget context) := by
  refine ⟨sourced, ?_⟩
  intro frame mem
  simp [Effect4.Deep.RunFiber.make, Effect4.FrameFiber.start] at mem

/-- The fork arm of the closure at the fork itself: the child of an admitted fork request
is well-sourced in its whole configuration. -/
theorem configWellSourced_forkChild (alphabet : FlowAlphabet Ty) (flow : RegionFlow Ty)
    (opOf : alphabet.Op → Option FiberOp) (point : Config) (program : Code)
    (options : Effect4.Supervision.ForkOptions) (id : FiberId) (interruptible : Bool)
    (budget : Nat × Bool)
    (spawned : forkWithFiberOf alphabet flow opOf point =
      some (Effect4.Deep.WithFiberAction.fork program options)) :
    ConfigWellSourced alphabet flow opOf
      (Effect4.Deep.RunFiber.make id program interruptible budget ()) :=
  configWellSourced_make alphabet flow opOf id program interruptible budget ()
    (wellSourced_fork alphabet flow opOf point program options spawned)

/-- The closure obligation the landing owes, stated (not proved) over the whole
configuration as §7.1 recommends. Every live fiber of a machine reached from a well-sourced
one is still stepping this flow's compile. -/
def WellSourcedClosed (alphabet : FlowAlphabet Ty) (flow : RegionFlow Ty)
    (opOf : alphabet.Op → Option FiberOp) (interp : ForkInterp) : Prop :=
  ∀ (fuel : Nat) (before : ForkMachine) (decision : ForkDecision),
    (∀ f ∈ before.fibers, f.exit.isNone → ConfigWellSourced alphabet flow opOf f) →
      ∀ f ∈ (Effect4.Deep.stepDecision interp fuel before decision).fibers, f.exit.isNone →
        ConfigWellSourced alphabet flow opOf f

/-! ## 7. The decision partition

Plan ruling 7 (`:53-57`) and review finding 13 (`:489-523`): one interrupt *model*, two
decision kinds, with the separation proved. Three site families, pairwise disjoint:

* the Flow decision tape owns `choose` and `branch`, whose sites `sitesSeparated`
  (`Effect4/Flow/Interrupt.lean:117-122`) keeps below `interruptBase`;
* the Flow interrupt tape owns delivery at a Flow interrupt point, whose sites are at or
  above `interruptBase` (`Point.site_ge`, `:81-82`);
* `RunDecision` owns dispatcher firing, the yield verdict, the external async answer, the
  machine-level interrupt with its interruptor id and the caller's annotations, and the
  middleware latch — and names **no `DecisionId` at all**. That last is the fact this
  section pins, and it survived the carrier's change to `interruptFrom`, which gained a
  `ReasonAnnotations α` and still names no site. -/

/-- The site a `RunDecision` names. There is none: `RunDecision`'s five constructors carry
fiber ids, tokens, primitives, annotations and booleans (`Effect4/Deep/Fibers.lean:358-376`),
and no `DecisionId`. This is the function whose constancy is the third clause of the
partition. -/
def runDecisionSite : ForkDecision → Option DecisionId := fun _ => none

@[simp] theorem runDecisionSite_none (decision : ForkDecision) :
    runDecisionSite decision = none := rfl

/-- A `choose` of a flow admitted by `sitesSeparated` names a site below `interruptBase`. -/
theorem choose_site_lt_base {flow : RegionFlow Ty}
    (separated : Effect4.Flow.sitesSeparated flow = true)
    {block : RegionBlock Ty} (mem : block ∈ flow.blocks)
    {site : DecisionId} {left right : BlockId} {args : List Var}
    (term : block.term = .plain (.choose site left right args)) :
    site.value < Effect4.Flow.interruptBase := by
  have all := List.all_eq_true.mp separated block mem
  rw [term] at all
  simpa using all

/-- The `sitesSeparated` shape one level up (ruling 7). -/
structure SitesSeparated (flow : RegionFlow Ty) : Prop where
  /-- The Flow decision tape's sites. -/
  chooseBelowBase : ∀ {block : RegionBlock Ty}, block ∈ flow.blocks →
    ∀ {site : DecisionId} {left right : BlockId} {args : List Var},
      block.term = .plain (.choose site left right args) →
        site.value < Effect4.Flow.interruptBase
  /-- The Flow interrupt tape's sites. -/
  interruptAtOrAboveBase : ∀ point : Effect4.Flow.Point,
    Effect4.Flow.interruptBase ≤ point.site.value
  /-- `RunDecision` names no site at all. -/
  runDecisionNamesNoSite : ∀ decision : ForkDecision, runDecisionSite decision = none

theorem sitesSeparated_holds {flow : RegionFlow Ty}
    (separated : Effect4.Flow.sitesSeparated flow = true) : SitesSeparated flow where
  chooseBelowBase := by
    intro block mem site left right args term
    exact choose_site_lt_base separated mem term
  interruptAtOrAboveBase := Effect4.Flow.Point.site_ge
  runDecisionNamesNoSite := runDecisionSite_none

/-- The corollary the partition exists for: a Flow interrupt site and a Flow `choose` site
are never the same site, and no `RunDecision` names either. -/
theorem interrupt_ne_choose {flow : RegionFlow Ty}
    (separated : Effect4.Flow.sitesSeparated flow = true)
    {block : RegionBlock Ty} (mem : block ∈ flow.blocks)
    {site : DecisionId} {left right : BlockId} {args : List Var}
    (term : block.term = .plain (.choose site left right args))
    (point : Effect4.Flow.Point) : point.site ≠ site :=
  Effect4.Flow.Point.site_ne_choose (choose_site_lt_base separated mem term)

/-! ## 8. The fuel bound

Review finding 3 (`:139-169`): admission's fuel argument bounds *one* control walk
(`Effect4/Semantics/Fuel.lean:166`), and `regionBound runnerFuel = 4 * runnerFuel + 1`
(`Effect4/Semantics/RegionSimulation.lean:440`) is one fiber's worth. With `k` fibers the
machine performs `k` walks, and on the operation route nothing in `CyclesWF` bounds `k`,
because the fork's root is inside a request value. The bound is therefore a **sum over live
fibers**, and starting a fork is a machine decision so that the machine tape bounds `k`
exactly as the Flow tape bounds `choose`. -/

/-- `Effect4.Flow.regionFuelFor flow tape`, spelled from `regionFuelFor_blocks`
(`Effect4/Semantics/Approximation.lean:2143`) so this spike keeps the import list of the
plan's S3 row. At the landing this is the imported function, not a copy. -/
def runnerFuel (flow : RegionFlow Ty) (tape : Effect4.Flow.Tape) : Nat :=
  (tape.length + 1) * flow.blocks.length + 1

/-- The per-fiber bound of a fiber that started at `point`: `regionBound` of the runner
fuel it holds. -/
def fiberBound (point : Config) : Nat := regionBound point.fuel

/-- The machine bound: a sum over live fibers of the per-fiber bound, plus one command per
fiber for the start and one for the resume. **Obligation**, stated with the shape the
landing must prove; nothing here proves it. -/
def ForkFuelBound (alphabet : FlowAlphabet Ty) (flow : RegionFlow Ty)
    (opOf : alphabet.Op → Option FiberOp) (interp : ForkInterp) : Prop :=
  ∀ (machine : ForkMachine) (tape : List ForkDecision) (fuel : Nat),
    (∀ f ∈ machine.fibers, f.exit.isNone → ConfigWellSourced alphabet flow opOf f) →
      ((machine.fibers.filter fun f => f.exit.isNone).length *
          (regionBound (runnerFuel flow []) + 2) ≤ fuel) →
        -- a machine that halts on a state rc.112 cannot reach (`Stuck`) also ends in bounded
        -- fuel; it is not `finished`, and the bound must admit it
        (∃ after, Effect4.Deep.replayEval interp fuel tape machine =
          Effect4.Deep.ReplayResult.finished after) ∨
        (∃ why after, Effect4.Deep.replayEval interp fuel tape machine =
          Effect4.Deep.ReplayResult.stuck why after)

/-! ## 9. The witnesses

Six flows over one table. Each is admitted by `Effects.admitRegions`
(`.lake/packages/effects/Effects/Flow/Region.lean:651-660`) — no clause of the eighteen v3
clauses or the fourteen region clauses changes, which is ruling 3's whole claim — compiled
by `compileForkAt`, and run through `replayEval` on an explicit `RunDecision` tape. -/

/-- The child answers a number and fails with a number. -/
def childAnswerTy : String := "number"
def childErrorTy : String := "number"

/-- The flow's own operations, after the profile. `boom` fails with `9`; `boomExit` is the
same at the exit spelling so that the await witness's child root types; `forkRequest` mints
the fork request the masked-child witness needs from a number in scope. -/
def userRows : List OpSpec :=
  [ { name := "boom", kind := OpKind.family, requestTy := "number", answerTy := "number",
      errorTy := "number", params := [("n", "number")] }
  , { name := "boomExit", kind := OpKind.family,
      requestTy := exitTy childAnswerTy childErrorTy,
      answerTy := exitTy childAnswerTy childErrorTy,
      errorTy := "number", params := [("e", exitTy childAnswerTy childErrorTy)] }
  , { name := "forkRequest", kind := OpKind.family, requestTy := "number",
      answerTy := forkRequestTy, errorTy := "never", params := [("n", "number")] } ]

def witnessTable : List OpSpec := profileTable childAnswerTy childErrorTy userRows

abbrev WitnessAlphabet : FlowAlphabet String := tableAlphabet ⟨0⟩ witnessTable

/-- The classification: a table position below `FiberOp.count` is a profile row. -/
def witnessOpOf (op : WitnessAlphabet.Op) : Option FiberOp := FiberOp.ofIndex op.val

def witnessHandleTy : String := handleTy childAnswerTy childErrorTy
def witnessExitTy : String := exitTy childAnswerTy childErrorTy

/-- The fork request the masked-child witness's `forkRequest` row answers: fork the child
root `6` with the masked body root `8` and its argument as the child's own argument list. -/
def maskedForkRequest : Val :=
  ForkRequest.value ⟨⟨6⟩, [RootRequest.value ⟨⟨8⟩, [Val.nat 0]⟩], false, none⟩

/-- The flow's service: `boom` and `boomExit` fail with `9`, `forkRequest` mints the masked
child's fork request; nothing else is asked. -/
def witnessAnswerOf : WitnessAlphabet.Op → Val → Except Val Val := fun op _ =>
  if op.val = 12 || op.val = 13 then .error (Val.nat 9)
  else if op.val = 14 then .ok maskedForkRequest
  else .ok Val.unit

def wblock (id : Nat) (params : List String) (term : RegionTerm) : RegionBlock String :=
  { id := ⟨id⟩, region := none, params := params, term := term }

/-- Witness A: the entry forks the declared root `3` and joins it; the child returns its
argument. -/
def flowJoin : RegionFlow String :=
  { alphabet := ⟨0⟩, roots := [⟨0⟩, ⟨3⟩], entry := ⟨0⟩,
    inputTy := forkRequestTy, resultTy := "number", regions := [],
    blocks :=
      [ wblock 0 [forkRequestTy] (.plain (.perform ⟨0⟩ ⟨0⟩ ⟨1⟩ []))
      , wblock 1 [witnessHandleTy] (.plain (.perform ⟨2⟩ ⟨0⟩ ⟨2⟩ []))
      , wblock 2 ["number"] (.plain (.ret ⟨0⟩))
      , wblock 3 ["number"] (.plain (.ret ⟨0⟩)) ] }

/-- Witness B: the same shape, but the child performs `boom` and fails; `join` fails the
parent with the child's cause. -/
def flowJoinFails : RegionFlow String :=
  { alphabet := ⟨0⟩, roots := [⟨0⟩, ⟨3⟩], entry := ⟨0⟩,
    inputTy := forkRequestTy, resultTy := "number", regions := [],
    blocks :=
      [ wblock 0 [forkRequestTy] (.plain (.perform ⟨0⟩ ⟨0⟩ ⟨1⟩ []))
      , wblock 1 [witnessHandleTy] (.plain (.perform ⟨2⟩ ⟨0⟩ ⟨2⟩ []))
      , wblock 2 ["number"] (.plain (.ret ⟨0⟩))
      , wblock 3 ["number"] (.plain (.perform ⟨12⟩ ⟨0⟩ ⟨4⟩ []))
      , wblock 4 ["number"] (.plain (.ret ⟨0⟩)) ] }

/-- Witness C: `await` answers the child's failure as a value, and the parent succeeds
with it. -/
def flowAwait : RegionFlow String :=
  { alphabet := ⟨0⟩, roots := [⟨0⟩, ⟨3⟩], entry := ⟨0⟩,
    inputTy := forkRequestTy, resultTy := witnessExitTy, regions := [],
    blocks :=
      [ wblock 0 [forkRequestTy] (.plain (.perform ⟨0⟩ ⟨0⟩ ⟨1⟩ []))
      , wblock 1 [witnessHandleTy] (.plain (.perform ⟨3⟩ ⟨0⟩ ⟨2⟩ []))
      , wblock 2 [witnessExitTy] (.plain (.ret ⟨0⟩))
      , wblock 3 [witnessExitTy] (.plain (.perform ⟨13⟩ ⟨0⟩ ⟨4⟩ []))
      , wblock 4 [witnessExitTy] (.plain (.ret ⟨0⟩)) ] }

/-- Witness D: a *caught* `join` (Flow v3 `performCatch`). The child's cause arrives as a
machine-level failure on the resume, so this is the arm P3's `onSuccessAndFailure` repair
buys; without it the failure would unwind past the catch. -/
def flowJoinCaught : RegionFlow String :=
  { alphabet := ⟨0⟩, roots := [⟨0⟩, ⟨3⟩], entry := ⟨0⟩,
    inputTy := forkRequestTy, resultTy := "number", regions := [],
    blocks :=
      [ wblock 0 [forkRequestTy] (.plain (.perform ⟨0⟩ ⟨0⟩ ⟨1⟩ []))
      , wblock 1 [witnessHandleTy] (.plain (.performCatch ⟨2⟩ ⟨0⟩ ⟨2⟩ [] ⟨5⟩ []))
      , wblock 2 ["number"] (.plain (.ret ⟨0⟩))
      , wblock 3 ["number"] (.plain (.perform ⟨12⟩ ⟨0⟩ ⟨4⟩ []))
      , wblock 4 ["number"] (.plain (.ret ⟨0⟩))
      , wblock 5 ["number"] (.plain (.ret ⟨0⟩)) ] }

/-- Witness F: a **masked child**. The parent mints its fork request, forks the child root
`6`, yields so the child is given the processor, then interrupts it and joins it. The child
runs its body under `uninterruptibleIn`, and that body parks on its own yield — so the
parent's interrupt is *recorded* while the mask holds and *delivered* when the mask frame
pops. -/
def flowMaskedChild : RegionFlow String :=
  { alphabet := ⟨0⟩, roots := [⟨0⟩, ⟨6⟩, ⟨8⟩], entry := ⟨0⟩,
    inputTy := "number", resultTy := "number", regions := [],
    blocks :=
      [ wblock 0 ["number"] (.plain (.perform ⟨14⟩ ⟨0⟩ ⟨1⟩ [⟨0⟩]))
      , wblock 1 ["number", forkRequestTy] (.plain (.perform ⟨0⟩ ⟨1⟩ ⟨2⟩ [⟨0⟩]))
      , wblock 2 ["number", witnessHandleTy] (.plain (.perform ⟨11⟩ ⟨0⟩ ⟨3⟩ [⟨1⟩]))
      , wblock 3 [witnessHandleTy, "void"] (.plain (.perform ⟨4⟩ ⟨0⟩ ⟨4⟩ [⟨0⟩]))
      , wblock 4 [witnessHandleTy, "void"] (.plain (.perform ⟨2⟩ ⟨0⟩ ⟨5⟩ []))
      , wblock 5 ["number"] (.plain (.ret ⟨0⟩))
      , wblock 6 [rootRequestTy] (.plain (.perform ⟨9⟩ ⟨0⟩ ⟨7⟩ []))
      , wblock 7 ["number"] (.plain (.ret ⟨0⟩))
      , wblock 8 ["number"] (.plain (.perform ⟨11⟩ ⟨0⟩ ⟨9⟩ [⟨0⟩]))
      , wblock 9 ["number", "void"] (.plain (.ret ⟨0⟩)) ] }

/-- Admission: nothing in the profile changes a clause. -/
def admitted (flow : RegionFlow String) : Bool :=
  match admitRegions WitnessAlphabet flow with
  | .ok _ => true
  | .error _ => false

#guard admitted flowJoin
#guard admitted flowJoinFails
#guard admitted flowAwait
#guard admitted flowJoinCaught
#guard admitted flowMaskedChild

/-- The interp of a witness flow. -/
def witnessInterp (flow : RegionFlow String) : ForkInterp :=
  forkInterp WitnessAlphabet flow witnessOpOf
    (forkOracle WitnessAlphabet flow witnessOpOf witnessAnswerOf)

/-- The input value: the fork request the entry block performs on. -/
def forkInput (root : Nat) (args : List Val) (daemon : Bool) (region : Option Nat) : Val :=
  ForkRequest.value ⟨⟨root⟩, args, daemon, region⟩

/-- The machine fuel each witness runs with. -/
def witnessFuel : Nat := 512

/-- Start the root fiber over the compiled entry, then replay the tape. `runFork`
(`Effect4/Deep/Fibers.lean:1168-1174`) is rc.112's `runForkWith`: the root is evaluated
synchronously on the caller's stack. -/
def runWitness (flow : RegionFlow String) (input : Val) (tape : List ForkDecision) :
    ForkReplay :=
  let interp := witnessInterp flow
  let program := compileForkAt WitnessAlphabet flow witnessOpOf
    ⟨runnerFuel flow [], flow.entry, [input], []⟩
  let (machine, _) := Effect4.Deep.runFork interp witnessFuel
    (Effect4.Deep.RunMachine.empty ()) program ()
  Effect4.Deep.replayEval interp witnessFuel tape machine

/-- Every replay result carries its machine, stuck or not. -/
def machineOf (result : ForkReplay) : ForkMachine :=
  match result with
  | Effect4.Deep.ReplayResult.finished machine
  | Effect4.Deep.ReplayResult.frontier machine
  | Effect4.Deep.ReplayResult.stuck _ machine => machine

def exitOf (result : ForkReplay) (fiber : FiberId) : Option Res :=
  ((machineOf result).fiber? fiber).bind Effect4.Deep.RunFiber.exit

def isFinished (result : ForkReplay) : Bool :=
  match result with
  | Effect4.Deep.ReplayResult.finished _ => true
  | _ => false

/-- Why the machine stopped, when it did (`Fibers.lean:326-331`). -/
def stuckOf (result : ForkReplay) : Option Effect4.Deep.Stuck :=
  match result with
  | Effect4.Deep.ReplayResult.stuck why _ => some why
  | _ => none

/-- Which fibers the machine holds, and whether each has exited. -/
def fiberSummary (result : ForkReplay) : List (Nat × Bool) :=
  (machineOf result).fibers.map fun f => (f.id.value, f.exit.isSome)

/-- Whether an interrupt cause has been *recorded* on a fiber
(`RunFiber.interruptPending`, `Fibers.lean:192-193`). -/
def interruptPendingOf (result : ForkReplay) (fiber : FiberId) : Bool :=
  (((machineOf result).fiber? fiber).map Effect4.Deep.RunFiber.interruptPending).getD false

/-- Whether a fiber is masked: the frame's `interruptible` flag, negated. -/
def maskedOf (result : ForkReplay) (fiber : FiberId) : Bool :=
  (((machineOf result).fiber? fiber).map fun f => !f.frame.interruptible).getD false

/-- Whether an exit is a failure carrying an interrupt. -/
def exitInterrupted : Option Res → Bool
  | some (Effect4.Exit.failure cause) => cause.hasInterrupts
  | _ => false

/-- The tape most witnesses run on: the parent's dispatcher is fired once. The fork is
*deferred* (`startImmediately := false`, review finding 3), so before the `fire` the child
has not started and the parent is parked on the join; the `fire` drains the parent's
dispatcher (`Scheduler.ts:225-233`), the child runs to its exit, its observers fire in
index order and the join's resume comes back as a command. -/
def fireParent : List ForkDecision := [Effect4.Deep.RunDecision.fire ⟨0⟩]

/-- The masked-child witness needs a second fire: the child's own dispatcher, which holds
the resume of the yield its masked body parked on. -/
def fireParentThenChild : List ForkDecision :=
  [Effect4.Deep.RunDecision.fire ⟨0⟩, Effect4.Deep.RunDecision.fire ⟨1⟩]

/-! The parent is parked and the child unstarted before the `fire`: two fibers exist,
neither has exited, and with an empty tape the replay reports a frontier, not a finish.
This is what "the fork is a machine decision, never a term field" looks like from outside
(review finding 3). -/
#guard !isFinished (runWitness flowJoin (forkInput 3 [Val.nat 7] false none) [])
#guard exitOf (runWitness flowJoin (forkInput 3 [Val.nat 7] false none) []) ⟨0⟩ = none
#guard fiberSummary (runWitness flowJoin (forkInput 3 [Val.nat 7] false none) [])
  = [(0, false), (1, false)]
#guard fiberSummary (runWitness flowJoin (forkInput 3 [Val.nat 7] false none) fireParent)
  = [(0, true), (1, true)]

/-! **Witness A.** Two fibers: the parent forks root `3` with `[7]` and joins it; the child
returns `7`; the parent exits with `7`. -/
#guard isFinished (runWitness flowJoin (forkInput 3 [Val.nat 7] false none) fireParent)
#guard exitOf (runWitness flowJoin (forkInput 3 [Val.nat 7] false none) fireParent) ⟨0⟩
  = some (Effect4.Exit.success (Val.nat 7))
#guard exitOf (runWitness flowJoin (forkInput 3 [Val.nat 7] false none) fireParent) ⟨1⟩
  = some (Effect4.Exit.success (Val.nat 7))

/-! **Witness B.** The child fails with `9`; `join` continues the parent with the child's
exit *as an effect*, so the parent fails with the child's cause. -/
#guard exitOf (runWitness flowJoinFails (forkInput 3 [Val.nat 1] false none) fireParent) ⟨1⟩
  = some (Effect4.Exit.failure (Effect4.Cause.fail (Val.nat 9)))
#guard exitOf (runWitness flowJoinFails (forkInput 3 [Val.nat 1] false none) fireParent) ⟨0⟩
  = some (Effect4.Exit.failure (Effect4.Cause.fail (Val.nat 9)))

/-! **Witness C.** The same child under `await`: the exit is a *value*, `Result.failure(9)`
on the host and `pair (bool false) (nat 9)` on the wire, and the parent succeeds. -/
#guard exitOf (runWitness flowAwait (forkInput 3 [Val.nat 1] false none) fireParent) ⟨0⟩
  = some (Effect4.Exit.success (Val.pair (Val.bool false) (Val.nat 9)))

/-! **Witness D.** A caught `join`: the failure successor binds the child's typed error and
the parent succeeds with it. -/
#guard exitOf (runWitness flowJoinCaught (forkInput 3 [Val.nat 1] false none) fireParent) ⟨0⟩
  = some (Effect4.Exit.success (Val.nat 9))

/-! The refusal is reachable and decidable: a request naming a block that is not a declared
root, and one whose argument count disagrees with the root's parameter list. -/
#guard checkRoot flowJoin ⟨2⟩ [Val.nat 7] = some (ForkRefusal.rootUndeclared ⟨2⟩)
#guard checkRoot flowJoin ⟨3⟩ [] = some (ForkRefusal.rootArity ⟨3⟩ 1 0)
#guard checkRoot flowJoin ⟨3⟩ [Val.nat 7] = none
#guard (refusal? flowJoin FiberOp.fork (forkInput 2 [Val.nat 7] false none)).isSome
#guard (refusal? flowJoin FiberOp.forkScoped (forkInput 3 [Val.nat 7] false (some 1))).isSome
#guard (refusal? flowJoin FiberOp.fork (forkInput 3 [Val.nat 7] false none)).isNone

/-! **Witness E.** A `fork` whose request names an undeclared root is refused **visibly**
through `WithFiberAction.refuse` (`Fibers.lean:896-898`): the parent dies with a defect, no
child is created, and the machine is **not stuck**. That last clause is the point — a
refusal is a fiber's failure, not a state the machine cannot leave. -/
#guard forkActionOf WitnessAlphabet flowJoin witnessOpOf ⟨1, ⟨0⟩, [], []⟩ FiberOp.fork
    (forkInput 2 [Val.nat 7] false none)
  = some (Effect4.Deep.WithFiberAction.fork
      (compileFork WitnessAlphabet flowJoin witnessOpOf 1 ⟨2⟩ [Val.nat 7] [])
      ⟨false, false, Effect4.Supervision.MaskMode.inherit⟩)
#guard forkWithFiberOf WitnessAlphabet flowJoin witnessOpOf
    ⟨runnerFuel flowJoin [], ⟨0⟩, [forkInput 2 [Val.nat 7] false none], []⟩
  = some (Effect4.Deep.WithFiberAction.refuse (Effect4.Cause.die ()))
#guard exitOf (runWitness flowJoin (forkInput 2 [Val.nat 7] false none) fireParent) ⟨0⟩
  = some (Effect4.Exit.failure (Effect4.Cause.die ()))
#guard stuckOf (runWitness flowJoin (forkInput 2 [Val.nat 7] false none) fireParent) = none
#guard isFinished (runWitness flowJoin (forkInput 2 [Val.nat 7] false none) fireParent)
#guard fiberSummary (runWitness flowJoin (forkInput 2 [Val.nat 7] false none) fireParent)
  = [(0, true)]

/-! ### The two shapes spike S4 moved

A refused `direct` row — here a `join` whose request slot holds a number rather than a
handle — compiles to `Prim.suspend point`, so `compileFork` emits `Prim.failure` nowhere
(P2, `compileFork_not_failure`), and the defect is raised by `forkTable.suspendBody` at
that point. A fiber that steps it therefore **dies with a defect** rather than suspending
for ever: the refusal is still visible, on a channel that did not exist before S4. -/
def refusedJoinPoint : Config := ⟨8, ⟨1⟩, [Val.nat 7], []⟩

#guard compileForkAt WitnessAlphabet flowJoin witnessOpOf refusedJoinPoint
  = Effect4.Prim.suspend refusedJoinPoint
#guard isFailure (compileForkAt WitnessAlphabet flowJoin witnessOpOf refusedJoinPoint) = false
#guard (forkTable WitnessAlphabet flowJoin witnessOpOf
    (forkOracle WitnessAlphabet flowJoin witnessOpOf witnessAnswerOf)).suspendBody
    refusedJoinPoint
  = Effect4.Prim.failure (Effect4.Cause.die ())

def refusedJoinMachine : ForkMachine :=
  { Effect4.Deep.RunMachine.empty () with
    fibers := [Effect4.Deep.RunFiber.make (ν := RegionName) (σ := Config)
      ⟨0⟩ (compileForkAt WitnessAlphabet flowJoin witnessOpOf refusedJoinPoint) true (0, true) ()]
    nextId := 1 }

#guard exitOf (Effect4.Deep.replayEval (witnessInterp flowJoin) witnessFuel
    [Effect4.Deep.RunDecision.evaluate ⟨0⟩] refusedJoinMachine) ⟨0⟩
  = some (Effect4.Exit.failure (Effect4.Cause.die ()))
#guard stuckOf (Effect4.Deep.replayEval (witnessInterp flowJoin) witnessFuel
    [Effect4.Deep.RunDecision.evaluate ⟨0⟩] refusedJoinMachine) = none

/-! And P3's shape, at the profile arm: a caught `join` compiles to S4's
`onSuccessAndFailure` over `RegionName.cont` and `RegionName.caught`, and `forkTable.contE`
routes the child's cause off the `caught` name — the hand-rolled repair the first pass
carried is now the upstream one. -/
#guard compileForkAt WitnessAlphabet flowJoinCaught witnessOpOf
    ⟨8, ⟨1⟩, [handleValue ⟨1⟩], []⟩
  = Effect4.Prim.onSuccessAndFailure (Effect4.Prim.sync ⟨8, ⟨1⟩, [handleValue ⟨1⟩], []⟩)
      (RegionName.cont ⟨8, ⟨1⟩, [handleValue ⟨1⟩], []⟩)
      (RegionName.caught ⟨8, ⟨1⟩, [handleValue ⟨1⟩], []⟩)

/-! **Witness F.** The masked child. After the first `fire` the child has started, entered
its `uninterruptibleIn` body and parked on the body's own yield; the parent has resumed,
interrupted it and parked awaiting it. The interrupt is **recorded on a masked fiber and
not delivered**: the child is masked, its pending flag is set, and it has no exit.

After the second `fire` — the child's own dispatcher, holding the resume of that yield —
the body finishes, the `setInterruptible true` frame pops, and `ensure`
(`Effect4/Runtime/Runtime.lean:649-655`) substitutes the pending cause: **delivered at the
unmask**. The child exits interrupted, its countdown resumes the parent, and the parent's
`join` carries the child's cause up. -/
#guard fiberSummary (runWitness flowMaskedChild (Val.nat 0) fireParent)
  = [(0, false), (1, false)]
#guard maskedOf (runWitness flowMaskedChild (Val.nat 0) fireParent) ⟨1⟩
#guard interruptPendingOf (runWitness flowMaskedChild (Val.nat 0) fireParent) ⟨1⟩
#guard exitOf (runWitness flowMaskedChild (Val.nat 0) fireParent) ⟨1⟩ = none
#guard stuckOf (runWitness flowMaskedChild (Val.nat 0) fireParent) = none

#guard isFinished (runWitness flowMaskedChild (Val.nat 0) fireParentThenChild)
#guard exitInterrupted (exitOf (runWitness flowMaskedChild (Val.nat 0) fireParentThenChild) ⟨1⟩)
#guard exitInterrupted (exitOf (runWitness flowMaskedChild (Val.nat 0) fireParentThenChild) ⟨0⟩)

/-! ### The machine finding this spike's first pass reported, now closed

`iteration`'s `ParkKind.join` arm used to answer a target the machine does not hold by
returning the fiber unchanged with `Outcome.continue_`, which `drive` re-enqueued
identically — a silent spin. The carrier now answers `Outcome.stuck (Stuck.unknownFiber …)`
(`Effect4/Deep/Fibers.lean:731`), `drive` halts on it (`:1050-1051`) and `replayEval`
reports it (`:1151-1158`). The witness below is the first pass's `strandedJoinSpins`,
turned into its repair. -/

/-- A fiber parked on a join whose target is not a fiber of the machine. -/
def strandedJoinPoint : Config := ⟨8, ⟨1⟩, [handleValue ⟨99⟩], []⟩

/-- The park classification is right — the target is read out of the request value. -/
def strandedJoinKind :
    Option (Except (Effect4.Cause Val Unit Unit Unit) Effect4.Deep.ParkKind) :=
  forkParkOf WitnessAlphabet flowJoin witnessOpOf (Effect4.Prim.sync strandedJoinPoint)

#guard strandedJoinKind
  = some (Except.ok (Effect4.Deep.ParkKind.join ⟨99⟩ Effect4.Supervision.ObserverMode.joinEffect))

/-- The machine holding only that fiber. -/
def strandedMachine : ForkMachine :=
  { Effect4.Deep.RunMachine.empty () with
    fibers := [Effect4.Deep.RunFiber.make (ν := RegionName) (σ := Config)
      ⟨0⟩ (Effect4.Prim.sync strandedJoinPoint) true (0, true) ()]
    nextId := 1 }

/-- One iteration halts with the reason, instead of returning the fiber unchanged. -/
def strandedJoinOutcome : Option Effect4.Deep.Stuck :=
  let interp := witnessInterp flowJoin
  match (Effect4.Deep.iteration interp strandedMachine
      (Effect4.Deep.RunFiber.make (ν := RegionName) (σ := Config)
        ⟨0⟩ (Effect4.Prim.sync strandedJoinPoint) true (0, true) ()) false).outcome with
  | Effect4.Deep.Outcome.stuck why => some why
  | _ => none

#guard strandedJoinOutcome = some (Effect4.Deep.Stuck.unknownFiber ⟨99⟩)

/-! And the whole replay reports it, rather than exhausting fuel in silence. -/
#guard stuckOf (Effect4.Deep.replayEval (witnessInterp flowJoin) witnessFuel
    [Effect4.Deep.RunDecision.evaluate ⟨0⟩] strandedMachine)
  = some (Effect4.Deep.Stuck.unknownFiber ⟨99⟩)

/-! ## Separation gates (`docs/FRAMES-DAG.md` separation 4): names stay data.

These fail to elaborate the moment `RegionName` or `Config` is instantiated at a function
type, which is what the profile route must never do: a fork request carries a *block
reference*, never a computation (DB-05, `docs/DESIGN-BASIS.md:201-208`). -/

example : DecidableEq Code := inferInstance
example : DecidableEq ForkAction := inferInstance
example : DecidableEq ForkDecision := inferInstance
example : DecidableEq ForkRequest := inferInstance
example : DecidableEq RootRequest := inferInstance
example : DecidableEq ForkRefusal := inferInstance

/-! ## Axiom report

Every theorem of this module, at the `propext`/`Quot.sound` ceiling the landing's
`#effect4_axiom_gate` enforces. There is no `sorry` in this file: the two things the spike
owes are `Prop`-valued statements (`WellSourcedClosed`, `ForkFuelBound`), and both are
stated, not assumed. -/

#print axioms compileFork_eq_compileRegion
#print axioms compileFork_perform_off_profile
#print axioms compileFork_not_failure
#print axioms wellSourced_actions
#print axioms wellSourced_fork
#print axioms wellSourced_compileForkAt
#print axioms configWellSourced_make
#print axioms configWellSourced_forkChild
#print axioms sitesSeparated_holds
#print axioms interrupt_ne_choose
#print axioms choose_site_lt_base
#print axioms forkRequestOf_value
#print axioms rootRequestOf_value
#print axioms handleOf_handleValue
#print axioms listOf_listValue
#print axioms FiberOp.ofIndex_index

end Effect4.Deep.ForkFlow
