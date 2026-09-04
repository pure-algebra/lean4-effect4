import Effect4.Target.TypeScript.ScriptFlow

/-!
# Target.TypeScript.FiberProfile

Owner: the **fiber profile** as a first-class target profile — the twelve
operations a Flow uses to name a concurrent child, as ordinary `OpSpec` rows,
plus the `Fibers` service they generate.

Ruling 3 of `docs/research/2026-09-03-deep-plan.md:29-36`: *fork is an operation
of the supplied alphabet, not a terminator*, and **the lowering emits a service
call and never `Effect.fork`**. That is a recorded refusal, restated in
`workshop/Deep/fork-lowering.md` §(d). Nothing in this module builds an
`Effect.fork`; it declares rows, and the existing printer
(`Effect4/Target/TypeScript/SkeletonRender.lean:68-71`) spells them.

The rows are spike S3's, transcribed unchanged from `workshop/Deep/ForkFlow.lean`
(`fiberProfile`, `:210-245`; report `docs/research/2026-09-03-spike-s3-fork-flow.md`
§2). S3 verified that `tableAlphabet`
(`Effect4/Target/TypeScript/ScriptFlow.lean:84-108`) builds the `FlowAlphabet`
from them with **no change to `ScriptFlow.lean`**, and this module keeps it so:
it adds data and a `ServiceRow`, and touches no existing definition.

Three facts the rows carry, and the reason each is a field rather than a shape.

* **The error channel is typed.** `join` resumes the child's exit *as an effect*,
  so it declares the child's `errorTy` and a `performCatch` on it binds a value
  of that type (`workshop/Deep/fork-lowering.md:71-81`). `awaitFiber` resumes the
  exit *as a value* and therefore never fails; `interruptFiber` and
  `interruptAll` never fail either.
* **`daemon` and `region` are request fields, not formers.** `region = some n`
  forks a daemon linked to a scope, which is what rc.112's `forkIn`
  (`vendor/effect-4.0.0-rc.112/src/internal/effect.ts:5337`) does anyway, so
  `daemon` is only consulted when `region` is `none` (review finding 14,
  `docs/research/2026-09-03-deep-plan-review.md:524-556`).
* **`await` is a reserved generated binding**, the same refusal
  `Effect4/Concurrency/FiberFamily.lean:68-71` records, so the rows are
  `awaitFiber` and — for symmetry — `interruptFiber`. Every name passes
  `EffectV4.bindingName` (`Effect4/Target/TypeScript/EffectV4.lean:145-147`);
  `Effect4Test/Target/TypeScript/FiberProfileContract.lean` is the receipt.

Nothing here traverses a Lean `String`: the rows concatenate spellings and
compare nothing, so this module stays at the `propext`/`Quot.sound` ceiling and
names no declaration in `Effect4Test/Audit/AxiomGate.lean`. Rendering the rows
crosses, and that happens in the printer, as it does for every other row.
-/

namespace Effect4.Target.EffectV4

/-! ## 1. The operations, by name

A table position is what `tableAlphabet` makes an operation, so the profile's
identity is an index; `FiberOp` is the name that index is read through, and
nothing below reads a position directly (`docs/LOWERING-COVERAGE.md`: identity
by id, never by position). -/

/-- The operations of the fiber profile, in the order `fiberProfile` declares
them. Transcribed from `workshop/Deep/ForkFlow.lean:93-119`; the rc.112
citations are this repository's vendored copy,
`vendor/effect-4.0.0-rc.112/src/internal/effect.ts`. -/
inductive FiberOp where
  /-- `forkUnsafe` (`:5264`), by `daemon`; `forkIn` (`:5337`) when `region` is
  `some`. -/
  | fork
  /-- `forkScoped` (`:5382`): `forkIn` on the ambient scope, which no request
  names. -/
  | forkScoped
  /-- `fiberJoin` (`:814`): the child's exit continues *as an effect*. -/
  | join
  /-- `fiberAwait` (`:767`): the child's exit continues *as a value*. -/
  | awaitFiber
  /-- `fiberInterrupt` (`:857`). -/
  | interruptFiber
  /-- `fiberInterruptAll` (`:888`). -/
  | interruptAll
  /-- `awaitAllChildren`'s snapshot half (`:5314`). -/
  | childrenSnapshot
  /-- `awaitAllChildren`'s exit half: await the children added since the
  snapshot. -/
  | awaitChildren
  /-- `raceAll` (`:1477`): entrants named as declared roots. -/
  | raceAll
  /-- `Effect.uninterruptible` (`:4302`): run a declared root's body masked. -/
  | uninterruptibleIn
  /-- `Effect.interruptible` (`:4331`): run a declared root's body unmasked. -/
  | interruptibleIn
  /-- `Effect.yieldNow` (`:982`): park behind the fiber's own dispatcher. -/
  | yieldNow
deriving DecidableEq, Repr, Inhabited

namespace FiberOp

/-- The profile position of an operation (`ForkFlow.lean:124-136`). -/
def index : FiberOp → Nat
  | fork => 0
  | forkScoped => 1
  | join => 2
  | awaitFiber => 3
  | interruptFiber => 4
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
  | 3 => some awaitFiber
  | 4 => some interruptFiber
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

/-- Every operation, in `index` order. This is the list the `ServiceRow` is
built along, so its order is the profile's and nothing zips by accident. -/
def all : List FiberOp :=
  [fork, forkScoped, join, awaitFiber, interruptFiber, interruptAll, childrenSnapshot,
   awaitChildren, raceAll, uninterruptibleIn, interruptibleIn, yieldNow]

/-- Whether the operation declares a typed failure. Ruling 8 of the deep plan:
`join` carries the child's error, and so do the two shapes that run a declared
root inline; `awaitFiber` answers the exit as a value and never fails, and
neither interrupt row fails. Keyed by the operation rather than by comparing the
`"never"` spelling, so no `String` is traversed here. -/
def fails : FiberOp → Bool
  | join | raceAll | uninterruptibleIn | interruptibleIn => true
  | _ => false

/-- The three rows that compile to a primitive the machine reads *directly* and
therefore have no `WithFiberAction` channel through which to refuse
(`ForkFlow.lean:167-171`, spike report §3). Carried here because the host
service's refusal story differs for them (`fork-lowering.md` §(c), note 4). -/
def direct : FiberOp → Bool
  | join | awaitFiber | yieldNow => true
  | _ => false

end FiberOp

/-! ## 2. The type spellings

`A` is the child's answer spelling and `E` its error spelling, both TypeScript.
A flow has one `resultTy` for every declared root (spike report §8), so `A` is
the flow's result and `E` its error channel. -/

/-- The TypeScript spelling of a fiber handle over a child answering `answerTy`
and failing with `errorTy`: rc.112 `Fiber.Fiber<A, E>`
(`ForkFlow.lean:177-178`). -/
def handleTy (answerTy errorTy : String) : String :=
  "Fiber.Fiber<" ++ answerTy ++ ", " ++ errorTy ++ ">"

/-- The TypeScript spelling of the exit `awaitFiber` answers with. rc.112 has no
`Either`, and `Effect4/Target/TypeScript/EffectV4.lean:49-52` records that an
`Except E A` answer is spelled `Result.Result<A, E>`; on the wire it is the `Val`
of `Effects.Trace.ToVal (Except ε α)`
(`.lake/packages/effects/Effects/Trace.lean:69-70`), namely
`pair (bool true) value` / `pair (bool false) error` (`ForkFlow.lean:185-186`). -/
def exitTy (answerTy errorTy : String) : String :=
  "Result.Result<" ++ answerTy ++ ", " ++ errorTy ++ ">"

/-- A list of handles, the request of `interruptAll` and the answer of
`childrenSnapshot`. -/
def handleListTy (answerTy errorTy : String) : String :=
  "ReadonlyArray<" ++ handleTy answerTy errorTy ++ ">"

/-- The four fields of a fork request: which declared root, the arguments its
parameter list receives, whether the child is a daemon, and the region to link
it to (`ForkFlow.lean:190-192`). The arguments are the wire's untyped `Val`
list, so their spelling is `ReadonlyArray<unknown>` and a root-entry case casts
(`fork-lowering.md` §(b), "Type honesty"). -/
def forkParams : List (String × String) :=
  [("root", "number"), ("args", "ReadonlyArray<unknown>"), ("daemon", "boolean"),
    ("region", "Option.Option<number>")]

/-- The two fields of a plain root reference: which declared root, and its
arguments. What `uninterruptibleIn` and `interruptibleIn` take
(`ForkFlow.lean:196-197`). -/
def rootParams : List (String × String) :=
  [("root", "number"), ("args", "ReadonlyArray<unknown>")]

/-- The request spelling of a fork: the right-nested product `requestSpelling`
builds (`Effect4/Target/TypeScript/ScriptFlow.lean:201-204`), which is exactly
the nesting `Effects.Trace.ToVal` builds from the parameter product. Its four
components are projected back at the call by `Lowering.tupleArgs`
(`SkeletonRender.lean:58-61`) — the converse pair `E4-TARGET-CE-026` pins. -/
def forkRequestTy : String := requestSpelling forkParams

/-- The request spelling of a masked or unmasked body. -/
def rootRequestTy : String := requestSpelling rootParams

/-- A list of root references, the request of `raceAll`. -/
def rootListTy : String := "ReadonlyArray<" ++ rootRequestTy ++ ">"

/-! ## 3. The twelve rows

Ordinary `OpSpec` rows, transcribed from `workshop/Deep/ForkFlow.lean:210-245`.
`tableAlphabet` builds the `FlowAlphabet` from them and `Skeleton.render`
prints them (`SkeletonRender.lean:96-97`); no printer change and no
`ScriptFlow.lean` change is needed for any of the three call shapes the profile
uses (arity four, arity two, arity one, and the one `void`-request row). -/

/-- The profile's rows, in `FiberOp.index` order. -/
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
      requestTy := handleListTy answerTy errorTy,
      answerTy := "void", errorTy := "never",
      params := [("fibers", handleListTy answerTy errorTy)] }
  , { name := "childrenSnapshot", kind := OpKind.family, requestTy := "void",
      answerTy := handleListTy answerTy errorTy, errorTy := "never",
      params := [] }
  , { name := "awaitChildren", kind := OpKind.family,
      requestTy := handleListTy answerTy errorTy,
      answerTy := "void", errorTy := "never",
      params := [("snapshot", handleListTy answerTy errorTy)] }
  , { name := "raceAll", kind := OpKind.family, requestTy := rootListTy,
      answerTy := answerTy, errorTy := errorTy,
      params := [("entrants", rootListTy)] }
  , { name := "uninterruptibleIn", kind := OpKind.family, requestTy := rootRequestTy,
      answerTy := answerTy, errorTy := errorTy, params := rootParams }
  , { name := "interruptibleIn", kind := OpKind.family, requestTy := rootRequestTy,
      answerTy := answerTy, errorTy := errorTy, params := rootParams }
  , { name := "yieldNow", kind := OpKind.family, requestTy := "number",
      answerTy := "void", errorTy := "never", params := [("priority", "number")] }
  ]

theorem fiberProfile_length (answerTy errorTy : String) :
    (fiberProfile answerTy errorTy).length = FiberOp.count := rfl

/-- The row of a profile operation, by name rather than by position. -/
def fiberRow (answerTy errorTy : String) (op : FiberOp) : OpSpec :=
  (fiberProfile answerTy errorTy)[op.index]!

/-! ## 4. The `Fibers` service

One `ServiceRow` per the rows above: the host class the lowered calls land on
(`workshop/Deep/fork-lowering.md` §(c)). The TypeScript face is *taken from the
`OpSpec` rows*, never restated — `familyTable (fibersRows …)` reproduces
`fiberProfile` field for field, and the battery is the receipt — so the only
thing declared here is the Lean face, which the target never reads except for
its parameter count. -/

/-- The Lean binder and carrier spelling of each parameter of a profile row.
The carriers are `workshop/Deep/Fibers.lean`'s: a handle is a `FiberId`, the
argument list is the wire's `List Val`, a region is a `RegionId`. Binders are
the row's own, so the two faces of a parameter agree by name as well as by
position. -/
def fiberLeanParams : FiberOp → List (String × String)
  | .fork | .forkScoped =>
      [("root", "Nat"), ("args", "List Val"), ("daemon", "Bool"),
        ("region", "Option RegionId")]
  | .join | .awaitFiber | .interruptFiber => [("fiber", "FiberId")]
  | .interruptAll => [("fibers", "List FiberId")]
  | .childrenSnapshot => []
  | .awaitChildren => [("snapshot", "List FiberId")]
  | .raceAll => [("entrants", "List (Nat × List Val)")]
  | .uninterruptibleIn | .interruptibleIn => [("root", "Nat"), ("args", "List Val")]
  | .yieldNow => [("priority", "Nat")]

/-- The Lean carrier of each row's answer. -/
def fiberLeanAnswer (answerLean errorLean : String) : FiberOp → String
  | .fork | .forkScoped => "FiberId"
  | .join | .raceAll | .uninterruptibleIn | .interruptibleIn => answerLean
  | .awaitFiber => "Except " ++ errorLean ++ " " ++ answerLean
  | .interruptFiber | .interruptAll | .awaitChildren | .yieldNow => "Unit"
  | .childrenSnapshot => "List FiberId"

/-- What an LLM is told about each row (`ServiceRow.sheet`). -/
def fiberCues : FiberOp → List String
  | .fork => ["start a declared root as a child fiber"]
  | .forkScoped => ["start a declared root in the caller's ambient scope"]
  | .join => ["resume a child's exit as an effect; its failure fails here"]
  | .awaitFiber => ["resume a child's exit as a value"]
  | .interruptFiber => ["interrupt one child and await it"]
  | .interruptAll => ["interrupt every named child, then await them all"]
  | .childrenSnapshot => ["the children this fiber holds right now"]
  | .awaitChildren => ["await the children added since a snapshot"]
  | .raceAll => ["run declared roots against each other; the first settled wins"]
  | .uninterruptibleIn => ["run a declared root's body with interruption masked"]
  | .interruptibleIn => ["run a declared root's body with interruption restored"]
  | .yieldNow => ["park behind this fiber's own dispatcher at a priority"]

/-- One `OpRow` of the `Fibers` service: the TypeScript face read off the
profile's own `OpSpec`, the Lean face declared above. -/
def fiberOpRow (answerLean errorLean : String) (op : FiberOp) (spec : OpSpec) : OpRow :=
  { name := spec.name
    index := op.index
    params := fiberLeanParams op
    tsParams := spec.params
    answer := fiberLeanAnswer answerLean errorLean op
    tsAnswer := spec.answerTy
    cues := fiberCues op
    error := if op.fails then some (errorLean, spec.errorTy) else none }

/-- The `Fibers` service: one method per operation of the fiber profile
(`workshop/Deep/fork-lowering.md` §(c)). `answerTy`/`errorTy` are the flow's
TypeScript result and error spellings; `answerLean`/`errorLean` are their Lean
carriers, which only the row's own documentation and its parameter count read.

`ServiceRow.methodType` gives `join` the aborting reading
`Effect.Effect<A, E>` (`EffectV4.lean:175-179`) and every unfailable row
`Effect.Effect<A>`, and `childrenSnapshot` an Effect *value* rather than a
thunk, because its parameter list is empty — which is exactly what the
`void`-request lowering needs (`fork-lowering.md` §(c), note 3). -/
def fibersRows (answerTy errorTy answerLean errorLean : String) : ServiceRow :=
  { name := "Fibers"
    ops := (FiberOp.all.zip (fiberProfile answerTy errorTy)).map fun (op, spec) =>
      fiberOpRow answerLean errorLean op spec }

/-- The `Fibers` service at the spelling the batteries and the harness use: a
child answering `number` and failing with `number`, carried in Lean by `Nat`. -/
def fibersRowsNat : ServiceRow := fibersRows "number" "number" "Nat" "Nat"

/-- The profile at the same spelling. -/
def fiberProfileNat : List OpSpec := fiberProfile "number" "number"

end Effect4.Target.EffectV4
