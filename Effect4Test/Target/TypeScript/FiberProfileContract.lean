/-
Contract packet: the fiber profile as a target profile, and the one lowering
change it needs (lowering lane L1).

Four things are pinned here.

* **The twelve rows** (`Effect4/Target/TypeScript/FiberProfile.lean`), exactly as
  spike S3 spells them (`workshop/Deep/ForkFlow.lean:210-245`,
  `docs/research/2026-09-03-spike-s3-fork-flow.md` §2): their names pass
  `EffectV4.bindingName`, their arities are the three the printer's three call
  shapes turn on, and their `errorTy` is the typed error channel ruling 8 of
  `docs/research/2026-09-03-deep-plan.md` words -- `join` carries the child's
  error, `awaitFiber` and the two interrupt rows never fail.
* **The `Fibers` service regenerates the rows.** `familyTable (fibersRowsNat)`
  reproduces `fiberProfileNat` field for field, so the service class and the
  flow alphabet are two projections of one declaration and cannot drift.
* **The bytes.** Twelve rendered calls, the service class, and four flows: a
  two-root flow that forks a declared root and joins it, a caught join whose
  failure edge binds the child's typed error, a masked child
  (`uninterruptibleIn`), and a two-root *region* flow that forks outside a region
  and joins inside it — spike S3's programs are `RegionFlow`s, so the entry
  change has to reach that form too. The caught join is single-root, so it is
  also the byte-identity receipt of the entry change: `Flow.lowerRoots` on it is
  `Flow.lowerDispatch` on it, rendered text included
  (`Flow.lowerDispatch_single_root_eq`), and §8a says the same for
  `Region.lowerRoots`, `Region.lowerRootsBest` and `Flow.lowerRootsBest`.
* **The import line.** §9 pins three: a module that names no `effect` namespace,
  the fiber module, and the fiber module with a region. `Spelling.namespacesOf`
  now scans `Exit`, `Fiber`, `Option` and `Result`, and each emitter takes it
  over the rows it declares, so an existing module's import line is what it
  always was and a fiber module imports what it names.

Ruling 3 (`docs/research/2026-09-03-deep-plan.md:29-36`): the lowering emits a
service call and never `Effect.fork`. No string below contains `Effect.fork`, and
the last receipt of §5 says so.

Doc comments cannot precede `#guard`, so the receipts carry line comments. No
definition here renders: a rendered declaration traverses strings and reaches
`Classical.choice`, so every rendering happens inside the `#guard` that reads it,
the way `FlowLowerContract.lean` and `MultiArgContract.lean` do it.
-/

import Effect4.Target.TypeScript.FiberProfile
import Effect4.Target.TypeScript.StructuredLower

namespace Effect4Test.Target.TypeScript.FiberProfileContract

open Effects Effect4.Flow Effect4.Target.EffectV4

#check @Effect4.Target.EffectV4.fiberProfile
#check (@Effect4.Target.EffectV4.fibersRows : String → String → String → String → ServiceRow)
#check @Effect4.Target.EffectV4.FiberOp.ofIndex_index
#check @Effect4.Target.EffectV4.Flow.lowerRoots
#check @Effect4.Target.EffectV4.Flow.lowerEntry
#check @Effect4.Target.EffectV4.Flow.lowerDispatch_single_root_eq

def rows : ServiceRow := fibersRowsNat
def table : List OpSpec := fiberProfileNat
def handle : String := handleTy "number" "number"

/-! ## 1. The twelve rows

`A = number`, `E = number`; `H = Fiber.Fiber<number, number>`,
`X = Result.Result<number, number>`, `R = readonly [number, ReadonlyArray<unknown>]`.
-/

#guard table.length = FiberOp.count
#guard FiberOp.count = 12
#guard FiberOp.all.length = FiberOp.count
#guard FiberOp.all.map FiberOp.index = List.range 12
example (op : FiberOp) : FiberOp.ofIndex op.index = some op := FiberOp.ofIndex_index op

-- The names, in profile order. `await` is a reserved generated binding (the
-- refusal the retired M3 `FiberFamily` (2026-09-04; the fact is `TypeScript.reservedIdentifiers`) records), so the row is
-- `awaitFiber` and `interruptFiber` follows it for symmetry.
#guard table.map (·.name) =
  ["fork", "forkScoped", "join", "awaitFiber", "interruptFiber", "interruptAll",
   "childrenSnapshot", "awaitChildren", "raceAll", "uninterruptibleIn", "interruptibleIn",
   "yieldNow"]
#guard table.all fun row => bindingName row.name
#guard !(table.map (·.name)).contains "await"

-- The three arities the printer's three call shapes turn on, plus the one
-- `void`-request row (`SkeletonRender.lean:68-71`).
#guard table.map OpSpec.arity = [4, 4, 1, 1, 1, 1, 1, 1, 1, 2, 2, 1]
#guard (fiberRow "number" "number" .childrenSnapshot).requestTy = "void"
#guard (table.filter fun row => row.requestTy == "void").length = 1

-- The typed error channel, row by row: `join` and the three shapes that resume a
-- child's failure in this fiber carry `E`; everything else declares `never`.
#guard table.map (·.errorTy) =
  ["never", "never", "number", "never", "never", "never", "never", "never",
   "number", "number", "number", "never"]
#guard FiberOp.all.map FiberOp.fails =
  [false, false, true, false, false, false, false, false, true, true, true, false]
#guard (fiberRow "number" "number" .join).errorTy = "number"
#guard (fiberRow "number" "number" .awaitFiber).errorTy = "never"
#guard (fiberRow "number" "number" .interruptFiber).errorTy = "never"
#guard (fiberRow "number" "number" .interruptAll).errorTy = "never"

-- The spellings. The fork's request is the right-nested product
-- `requestSpelling` builds, which `Lowering.tupleArgs` projects back at the call
-- (`E4-TARGET-CE-026`).
#guard handleTy "number" "number" = "Fiber.Fiber<number, number>"
#guard exitTy "number" "number" = "Result.Result<number, number>"
#guard rootRequestTy = "readonly [number, ReadonlyArray<unknown>]"
#guard forkRequestTy =
  "readonly [number, readonly [ReadonlyArray<unknown>, readonly [boolean, Option.Option<number>]]]"
#guard forkRequestTy = requestSpelling forkParams
#guard rootRequestTy = requestSpelling rootParams
#guard (fiberRow "number" "number" .awaitFiber).answerTy = exitTy "number" "number"
#guard (fiberRow "number" "number" .join).answerTy = "number"
#guard (fiberRow "number" "number" .fork).answerTy = handle

/-! ## 2. `tableAlphabet` builds the alphabet from the rows, unchanged

Spike S3 verified that the profile needs no change to
`Effect4/Target/TypeScript/ScriptFlow.lean`; these receipts keep it so. The
alphabet's operations are table positions, so a row is found by position and read
by name, never the other way round. -/

def alphabet : FlowAlphabet String := tableAlphabet ⟨0⟩ table

#guard (alphabet.lookup ⟨2⟩).map alphabet.answerTy = some "number"
#guard (alphabet.lookup ⟨2⟩).bind alphabet.errorTy = some "number"
#guard (alphabet.lookup ⟨2⟩).map alphabet.requestTy = some (handleTy "number" "number")
#guard (alphabet.lookup ⟨6⟩).map alphabet.requestTy = some "void"
#guard (alphabet.lookup ⟨0⟩).map alphabet.requestTy = some forkRequestTy
#guard (alphabet.lookup ⟨12⟩).isNone
#guard alphabet.boolTy = "boolean"

/-! ## 3. The `Fibers` service is the rows

`familyTable` (`ScriptFlow.lean:210-219`) reads a `ServiceRow` back into
`OpSpec` rows. On the fiber profile it reproduces `fiberProfile` field for field,
which is what "the `ServiceRow` is built from the rows" means operationally: the
service class the host implements and the alphabet the flow runs against cannot
disagree about a name, a request, an answer or an error. `OpSpec` has no `BEq`,
so the comparison is on its five fields. -/

#guard (familyTable rows).map (fun s => (s.name, s.requestTy, s.answerTy, s.errorTy, s.params)) ==
  table.map (fun s => (s.name, s.requestTy, s.answerTy, s.errorTy, s.params))
#guard rows.name = "Fibers"
#guard rows.receiver = "fibers"
#guard rows.ops.length = FiberOp.count
#guard rows.ops.map (·.index) = List.range 12
-- The Lean and TypeScript parameter lists of every row have the same length, the
-- invariant `MultiArgContract.lean` §5 holds every shipped `ServiceRow` to.
#guard rows.ops.all fun row => row.params.length == row.tsParams.length
-- Only the four failing rows carry an error row, so only they get the aborting
-- method type `Effect.Effect<A, E>` (`EffectV4.lean:175-179`).
#guard rows.ops.map (fun row => row.error.isSome) =
  [false, false, true, false, false, false, false, false, true, true, true, false]

/-! ## 4. The twelve calls, spelled

`Skeleton.render` sends a family `perform` to
`[.constYield answer.name (Lowering.callOf rows spec request)]`
(`SkeletonRender.lean:96-97`), and `callOf` picks one of three shapes by the row.
This is the whole of "the existing printer already spells every row": no printer
change, and the fork's four fields destructure at the call site
(`workshop/Deep/fork-lowering.md` §(a)). The request slot is `b1p0` throughout so
the twelve lines read as one table. -/

def rowStatement (op : FiberOp) : Skeleton :=
  Skeleton.perform (.answer ⟨1⟩) ⟨op.index⟩ (fiberRow "number" "number" op) (.param ⟨1⟩ 0)

#guard (FiberOp.all.map fun op =>
    String.intercalate "\n" ((Skeleton.render rows (rowStatement op)).map
      (_root_.TypeScript.Render.stmt _root_.TypeScript.house0 0))) =
  [ "const a1 = yield* fibers.fork(b1p0[0], b1p0[1][0], b1p0[1][1][0], b1p0[1][1][1])"
  , "const a1 = yield* fibers.forkScoped(b1p0[0], b1p0[1][0], b1p0[1][1][0], b1p0[1][1][1])"
  , "const a1 = yield* fibers.join(b1p0)"
  , "const a1 = yield* fibers.awaitFiber(b1p0)"
  , "const a1 = yield* fibers.interruptFiber(b1p0)"
  , "const a1 = yield* fibers.interruptAll(b1p0)"
  , "const a1 = yield* fibers.childrenSnapshot"
  , "const a1 = yield* fibers.awaitChildren(b1p0)"
  , "const a1 = yield* fibers.raceAll(b1p0)"
  , "const a1 = yield* fibers.uninterruptibleIn(b1p0[0], b1p0[1])"
  , "const a1 = yield* fibers.interruptibleIn(b1p0[0], b1p0[1])"
  , "const a1 = yield* fibers.yieldNow(b1p0)" ]

-- The `void`-request row is an Effect *value*, not a call: rc.112 is already
-- lazy, and `ServiceRow.methodType` declares that field as an `Effect`
-- (`workshop/Deep/fork-lowering.md` §(c), note 3).
#guard _root_.TypeScript.Render.expr _root_.TypeScript.house0 0
  (Lowering.callOf rows (fiberRow "number" "number" .childrenSnapshot) (.param ⟨1⟩ 0)) =
  "fibers.childrenSnapshot"

-- The service class the host implements, from the same rows.
#guard _root_.TypeScript.Render.decl _root_.TypeScript.house0 rows.classDecl =
  ("/** Service `Fibers`: one method per operation of the Lean family. */\n" ++
   "export class Fibers extends Context.Service<Fibers, {\n" ++
   "  readonly fork: (root: number, args: ReadonlyArray<unknown>, daemon: boolean, region: Option.Option<number>) => Effect.Effect<Fiber.Fiber<number, number>>\n" ++
   "  readonly forkScoped: (root: number, args: ReadonlyArray<unknown>, daemon: boolean, region: Option.Option<number>) => Effect.Effect<Fiber.Fiber<number, number>>\n" ++
   "  readonly join: (fiber: Fiber.Fiber<number, number>) => Effect.Effect<number, number>\n" ++
   "  readonly awaitFiber: (fiber: Fiber.Fiber<number, number>) => Effect.Effect<Result.Result<number, number>>\n" ++
   "  readonly interruptFiber: (fiber: Fiber.Fiber<number, number>) => Effect.Effect<void>\n" ++
   "  readonly interruptAll: (fibers: ReadonlyArray<Fiber.Fiber<number, number>>) => Effect.Effect<void>\n" ++
   "  readonly childrenSnapshot: Effect.Effect<ReadonlyArray<Fiber.Fiber<number, number>>>\n" ++
   "  readonly awaitChildren: (snapshot: ReadonlyArray<Fiber.Fiber<number, number>>) => Effect.Effect<void>\n" ++
   "  readonly raceAll: (entrants: ReadonlyArray<readonly [number, ReadonlyArray<unknown>]>) => Effect.Effect<number, number>\n" ++
   "  readonly uninterruptibleIn: (root: number, args: ReadonlyArray<unknown>) => Effect.Effect<number, number>\n" ++
   "  readonly interruptibleIn: (root: number, args: ReadonlyArray<unknown>) => Effect.Effect<number, number>\n" ++
   "  readonly yieldNow: (priority: number) => Effect.Effect<void>\n" ++
   "}>()(\"Fibers\") {}\n")

/-! ## 5. Three flows

Each is admitted by `Effects.admit` against `tableAlphabet ⟨0⟩ table` -- no
clause of the eighteen Flow v3 clauses changed, which is the point of ruling 3 --
and lowered by `Flow.lowerRoots`. -/

def program? (name : String) (raw : RawFlow String) : Option FlowProgram :=
  match admit (tableAlphabet ⟨0⟩ table) raw with
  | .ok flow => some { name := name, param := ("n", raw.inputTy), result := raw.resultTy,
                       table := table, flow := flow }
  | .error _ => none

/-- Two roots: the entry forks the declared root `3` and joins it. Block `3` is
the child's body -- one `resultTy` for every declared root, which is the
structural cost spike S3 §8 records. -/
def forkJoinRaw : RawFlow String :=
  { alphabet := ⟨0⟩, roots := [⟨0⟩, ⟨3⟩], entry := ⟨0⟩,
    inputTy := forkRequestTy, resultTy := "number",
    blocks :=
      [ { id := ⟨0⟩, params := [forkRequestTy], term := .perform ⟨0⟩ ⟨0⟩ ⟨1⟩ [] }
      , { id := ⟨1⟩, params := [handle], term := .perform ⟨2⟩ ⟨0⟩ ⟨2⟩ [] }
      , { id := ⟨2⟩, params := ["number"], term := .ret ⟨0⟩ }
      , { id := ⟨3⟩, params := ["number"], term := .ret ⟨0⟩ } ] }

/-- The caught join: the failure edge's last slot binds a value of the *child's*
declared error type, which is why `join` carries a real `errorTy`. One root, so
this flow also witnesses byte identity under the entry change. -/
def caughtJoinRaw : RawFlow String :=
  { alphabet := ⟨0⟩, roots := [⟨0⟩], entry := ⟨0⟩,
    inputTy := forkRequestTy, resultTy := "number",
    blocks :=
      [ { id := ⟨0⟩, params := [forkRequestTy], term := .perform ⟨0⟩ ⟨0⟩ ⟨1⟩ [] }
      , { id := ⟨1⟩, params := [handle], term := .performCatch ⟨2⟩ ⟨0⟩ ⟨2⟩ [] ⟨3⟩ [] }
      , { id := ⟨2⟩, params := ["number"], term := .ret ⟨0⟩ }
      , { id := ⟨3⟩, params := ["number"], term := .ret ⟨0⟩ } ] }

/-- A masked child: `uninterruptibleIn` names the declared root `2` and runs its
body under rc.112's `Effect.uninterruptible`
(`vendor/effect-4.0.0-rc.112/src/internal/effect.ts:4302`). Two slots, so the
call destructures. -/
def maskedChildRaw : RawFlow String :=
  { alphabet := ⟨0⟩, roots := [⟨0⟩, ⟨2⟩], entry := ⟨0⟩,
    inputTy := rootRequestTy, resultTy := "number",
    blocks :=
      [ { id := ⟨0⟩, params := [rootRequestTy], term := .perform ⟨9⟩ ⟨0⟩ ⟨1⟩ [] }
      , { id := ⟨1⟩, params := ["number"], term := .ret ⟨0⟩ }
      , { id := ⟨2⟩, params := ["number"], term := .ret ⟨0⟩ } ] }

def forkJoin? : Option FlowProgram := program? "forkJoin" forkJoinRaw
def caughtJoin? : Option FlowProgram := program? "caughtJoin" caughtJoinRaw
def maskedChild? : Option FlowProgram := program? "maskedChild" maskedChildRaw

#guard forkJoin?.isSome
#guard caughtJoin?.isSome
#guard maskedChild?.isSome

-- The declarations a flow lowers to: one for a single-root flow, and
-- `1 + |roots| + 1` for a multi-root one (the entry, one alias per declared root,
-- and the entry re-export the host layer closes over).
#guard (forkJoin?.bind fun p => (Flow.lowerRoots rows p).map (·.length)) = some 4
#guard (caughtJoin?.bind fun p => (Flow.lowerRoots rows p).map (·.length)) = some 1
#guard (maskedChild?.bind fun p => (Flow.lowerRoots rows p).map (·.length)) = some 4

/-! ### 5a. The two-root flow, byte for byte -/

#guard (forkJoin?.bind fun p => (Flow.lowerRoots rows p).map fun decls =>
    String.intercalate "\n" (decls.map
      (_root_.TypeScript.Render.decl _root_.TypeScript.house0))) = some
  ("/** Lowered from the flow `forkJoin` over `Fibers` (dispatch form, multi-root entry). */\n" ++
   "export const forkJoin__entry = (entry: readonly [number, ReadonlyArray<unknown>]) =>\n" ++
   "  Effect.gen(function* () {\n" ++
   "    const fibers = yield* Fibers\n" ++
   "    let b0p0!: readonly [number, readonly [ReadonlyArray<unknown>, readonly [boolean, Option.Option<number>]]]\n" ++
   "    let b1p0!: Fiber.Fiber<number, number>\n" ++
   "    let b2p0!: number\n" ++
   "    let b3p0!: number\n" ++
   "    let block = entry[0]\n" ++
   "    while (true) {\n" ++
   "      switch (block) {\n" ++
   "        case 1000: {\n" ++
   "          b0p0 = entry[1][0] as readonly [number, readonly [ReadonlyArray<unknown>, readonly [boolean, Option.Option<number>]]]\n" ++
   "          block = 0\n" ++
   "          continue\n" ++
   "        }\n" ++
   "        case 1003: {\n" ++
   "          b3p0 = entry[1][0] as number\n" ++
   "          block = 3\n" ++
   "          continue\n" ++
   "        }\n" ++
   "        case 0: {\n" ++
   "          const a0 = yield* fibers.fork(b0p0[0], b0p0[1][0], b0p0[1][1][0], b0p0[1][1][1])\n" ++
   "          b1p0 = a0\n" ++
   "          block = 1\n" ++
   "          continue\n" ++
   "        }\n" ++
   "        case 1: {\n" ++
   "          const a1 = yield* fibers.join(b1p0)\n" ++
   "          b2p0 = a1\n" ++
   "          block = 2\n" ++
   "          continue\n" ++
   "        }\n" ++
   "        case 2: {\n" ++
   "          return b2p0\n" ++
   "        }\n" ++
   "        case 3: {\n" ++
   "          return b3p0\n" ++
   "        }\n" ++
   "      }\n" ++
   "    }\n" ++
   "  })\n" ++
   "\n" ++
   "/** Enter the flow `forkJoin` at block 0 (dispatch form, multi-root). */\n" ++
   "export const forkJoin: (n: readonly [number, readonly [ReadonlyArray<unknown>, readonly [boolean, Option.Option<number>]]]) => Effect.Effect<number, number, Fibers> = (n) => forkJoin__entry([1000, [n]])\n" ++
   "\n" ++
   "/** Enter the declared root of `forkJoin` at block 3 (dispatch form, multi-root). */\n" ++
   "export const forkJoin__root3: (p0: number) => Effect.Effect<number, number, Fibers> = (p0) => forkJoin__entry([1003, [p0]])\n" ++
   "\n" ++
   "/** The parameterised entry of `forkJoin`: a declared root and its arguments. */\n" ++
   "export const forkJoinEntry = forkJoin__entry\n")

-- The exported name keeps the signature the single-root form gave it, so the
-- type receipt is unchanged: this is the line the pinned compiler must emit.
#guard (forkJoin?.map (Flow.declarationLine rows)) = some
  ("export declare const forkJoin: (n: readonly [number, readonly [ReadonlyArray<unknown>, " ++
   "readonly [boolean, Option.Option<number>]]]) => Effect.Effect<number, number, Fibers>;")

/-! ### 5b. The caught join

`performCatch` of `join` lowers as every caught perform does
(`SkeletonRender.lean:107-111`): rc.112's `Effect.result` turns `Effect<A, E>`
into `Effect<Result<A, E>>`, the value edge reads `a1.success` and the failure
edge reads `a1.failure` -- a value of the *child's* declared error type. That is
why `join` carries a real `errorTy` and `awaitFiber` carries `never`: `join`
resumes the child's exit as an effect, `awaitFiber` as a value
(`workshop/Deep/fork-lowering.md:71-81`).

The flow's own error channel is `never`, because the failure was caught. -/

#guard (caughtJoin?.bind fun p => (Flow.lowerRoots rows p).map fun decls =>
    String.intercalate "\n" (decls.map
      (_root_.TypeScript.Render.decl _root_.TypeScript.house0))) = some
  ("/** Lowered from the flow `caughtJoin` over `Fibers` (dispatch form). */\n" ++
   "export const caughtJoin = (n: readonly [number, readonly [ReadonlyArray<unknown>, readonly [boolean, Option.Option<number>]]]) =>\n" ++
   "  Effect.gen(function* () {\n" ++
   "    const fibers = yield* Fibers\n" ++
   "    let b0p0!: readonly [number, readonly [ReadonlyArray<unknown>, readonly [boolean, Option.Option<number>]]]\n" ++
   "    let b1p0!: Fiber.Fiber<number, number>\n" ++
   "    let b2p0!: number\n" ++
   "    let b3p0!: number\n" ++
   "    b0p0 = n\n" ++
   "    let block = 0\n" ++
   "    while (true) {\n" ++
   "      switch (block) {\n" ++
   "        case 0: {\n" ++
   "          const a0 = yield* fibers.fork(b0p0[0], b0p0[1][0], b0p0[1][1][0], b0p0[1][1][1])\n" ++
   "          b1p0 = a0\n" ++
   "          block = 1\n" ++
   "          continue\n" ++
   "        }\n" ++
   "        case 1: {\n" ++
   "          const a1 = yield* Effect.result(fibers.join(b1p0))\n" ++
   "          if (Result.isSuccess(a1)) {\n" ++
   "            b2p0 = a1.success\n" ++
   "            block = 2\n" ++
   "            continue\n" ++
   "          } else {\n" ++
   "            b3p0 = a1.failure\n" ++
   "            block = 3\n" ++
   "            continue\n" ++
   "          }\n" ++
   "        }\n" ++
   "        case 2: {\n" ++
   "          return b2p0\n" ++
   "        }\n" ++
   "        case 3: {\n" ++
   "          return b3p0\n" ++
   "        }\n" ++
   "      }\n" ++
   "    }\n" ++
   "  })\n")

#guard (caughtJoin?.map (Flow.errorChannel rows)) = some "never"
#guard (forkJoin?.map (Flow.errorChannel rows)) = some "number"

/-! ### 5c. The masked child -/

#guard (maskedChild?.bind fun p => (Flow.lowerRoots rows p).map fun decls =>
    String.intercalate "\n" (decls.map
      (_root_.TypeScript.Render.decl _root_.TypeScript.house0))) = some
  ("/** Lowered from the flow `maskedChild` over `Fibers` (dispatch form, multi-root entry). */\n" ++
   "export const maskedChild__entry = (entry: readonly [number, ReadonlyArray<unknown>]) =>\n" ++
   "  Effect.gen(function* () {\n" ++
   "    const fibers = yield* Fibers\n" ++
   "    let b0p0!: readonly [number, ReadonlyArray<unknown>]\n" ++
   "    let b1p0!: number\n" ++
   "    let b2p0!: number\n" ++
   "    let block = entry[0]\n" ++
   "    while (true) {\n" ++
   "      switch (block) {\n" ++
   "        case 1000: {\n" ++
   "          b0p0 = entry[1][0] as readonly [number, ReadonlyArray<unknown>]\n" ++
   "          block = 0\n" ++
   "          continue\n" ++
   "        }\n" ++
   "        case 1002: {\n" ++
   "          b2p0 = entry[1][0] as number\n" ++
   "          block = 2\n" ++
   "          continue\n" ++
   "        }\n" ++
   "        case 0: {\n" ++
   "          const a0 = yield* fibers.uninterruptibleIn(b0p0[0], b0p0[1])\n" ++
   "          b1p0 = a0\n" ++
   "          block = 1\n" ++
   "          continue\n" ++
   "        }\n" ++
   "        case 1: {\n" ++
   "          return b1p0\n" ++
   "        }\n" ++
   "        case 2: {\n" ++
   "          return b2p0\n" ++
   "        }\n" ++
   "      }\n" ++
   "    }\n" ++
   "  })\n" ++
   "\n" ++
   "/** Enter the flow `maskedChild` at block 0 (dispatch form, multi-root). */\n" ++
   "export const maskedChild: (n: readonly [number, ReadonlyArray<unknown>]) => Effect.Effect<number, number, Fibers> = (n) => maskedChild__entry([1000, [n]])\n" ++
   "\n" ++
   "/** Enter the declared root of `maskedChild` at block 2 (dispatch form, multi-root). */\n" ++
   "export const maskedChild__root2: (p0: number) => Effect.Effect<number, number, Fibers> = (p0) => maskedChild__entry([1002, [p0]])\n" ++
   "\n" ++
   "/** The parameterised entry of `maskedChild`: a declared root and its arguments. */\n" ++
   "export const maskedChildEntry = maskedChild__entry\n")

/-! ### 5d. The refusal, restated as bytes

Ruling 3: the lowered program contains a service call and no `Effect.fork`. -/

-- No lowered declaration of any of the three mentions `Effect.fork`:
-- `splitOn` of a needle that never occurs answers a one-element list.
#guard [forkJoin?, caughtJoin?, maskedChild?].all fun program? =>
  (program?.bind fun p => (Flow.lowerRoots rows p).map fun decls =>
    ((String.intercalate "\n" (decls.map
        (_root_.TypeScript.Render.decl _root_.TypeScript.house0))).splitOn
      "Effect.fork").length == 1) == some true

-- What they contain instead is the service call.
#guard (forkJoin?.bind fun p => (Flow.lowerRoots rows p).map fun decls =>
    decide (1 < ((String.intercalate "\n" (decls.map
        (_root_.TypeScript.Render.decl _root_.TypeScript.house0))).splitOn
      "yield* fibers.fork(").length)) = some true

/-! ## 6. Byte identity under the entry change

`Flow.lowerDispatch_single_root_eq`: a flow with one declared root lowers through
the multi-root emitter to exactly the single `ProgDecl` `Flow.lowerDispatch`
emits. Every flow the four lowering batteries carry has one root, so no existing
golden, contract or harness fixture can move -- and the concrete instance below
compares the rendered text, not just the syntax. -/

example (rowsOf : ServiceRow) (program : FlowProgram)
    (single : (program.flow.erase).roots.length ≤ 1) :
    Flow.lowerRoots rowsOf program =
      (Flow.lowerDispatch rowsOf program).map fun decl => [_root_.TypeScript.Decl.prog decl] :=
  Flow.lowerDispatch_single_root_eq rowsOf program single

#guard (caughtJoin?.map fun p =>
  ((Flow.lowerRoots rows p).map fun decls =>
      decls.map (_root_.TypeScript.Render.decl _root_.TypeScript.house0)) ==
  ((Flow.lowerDispatch rows p).map fun decl =>
      [_root_.TypeScript.Render.decl _root_.TypeScript.house0 (.prog decl)])) = some true

/-! ## 7. The census

`entry-root` is the one rule the entry change adds, appended last to `Rule.all`;
the whole id list is pinned in `FlowLowerContract.lean` and nothing here reads a
position (survey finding H9). The profile's own calls need no rule: they are the
generic `flow-perform` plus `perform-call`/`nullary-value`, and `perform-tuple`
for the rows of arity two or more. -/

#guard Rule.ofId? "entry-root" = some .entryRoot
#guard (Rule.entryRoot).id = "entry-root"
#guard Rule.all.contains .entryRoot

-- A multi-root flow reports it; a single-root flow does not.
#guard (forkJoin?.map fun p => (Flow.ruleSet rows p).contains .entryRoot) = some true
#guard (maskedChild?.map fun p => (Flow.ruleSet rows p).contains .entryRoot) = some true
#guard (caughtJoin?.map fun p => (Flow.ruleSet rows p).contains .entryRoot) = some false

-- The rules the three flows exercise, in first-use order. No rule is new to the
-- profile's calls: `fork` is a `flow-perform` whose four-slot request is a
-- `perform-tuple`, and a caught `join` is a `perform-catch`.
#guard (forkJoin?.map (Flow.ruleSet rows)) =
  some [.serviceAcquire, .dispatchLoop, .blockCase, .entryRoot, .flowPerform, .performCall,
        .performTuple, .paramMove, .flowRet]
#guard (caughtJoin?.map (Flow.ruleSet rows)) =
  some [.serviceAcquire, .dispatchLoop, .blockCase, .flowPerform, .performCall, .performTuple,
        .paramMove, .performCatch, .flowRet]
#guard (maskedChild?.map (Flow.ruleSet rows)) =
  some [.serviceAcquire, .dispatchLoop, .blockCase, .entryRoot, .flowPerform, .performCall,
        .performTuple, .paramMove, .flowRet]

/-! ## 8. Region flows get the same entry

Spike S3's witnesses and its compile are over `RegionFlow`
(`workshop/Deep/ForkFlow.lean`), so a fork that names a declared root names one
of *these* roots. `Region.lowerRoots` is the plain form's change, transcribed:
the same `skeletonCases` call, the entry parameter, one synthetic case per
declared root.

One refusal the plain form cannot need: a declared root must sit **outside**
every region. The top-level dispatch loop runs exactly the blocks whose label is
`none`; a region's blocks live in a nested generator with a block variable of
their own, so a synthetic case at the top level cannot continue at one.
Admission already refuses an *entry* inside a region
(`Effects.RegionClause.entryInside`); `Region.skeletonEntry` refuses the rest. -/

def rregion (id : Nat) (region : Option Nat) (params : List String) (term : RegionTerm) :
    RegionBlock String :=
  { id := ⟨id⟩, region := region.map RegionId.mk, params := params, term := term }

/-- Fork the declared root `5`, then join it *inside* a region: the child's exit
arrives as the region's value, and the region closes with it. Two roots, one
region, the fork outside it. -/
def forkInRegionRaw : RegionFlow String :=
  { alphabet := ⟨0⟩, roots := [⟨0⟩, ⟨5⟩], entry := ⟨0⟩,
    inputTy := forkRequestTy, resultTy := "number",
    regions := [{ id := ⟨1⟩, parent := none, continue_ := ⟨3⟩, resultTy := "number" }],
    blocks :=
      [ rregion 0 none [forkRequestTy] (.plain (.perform ⟨0⟩ ⟨0⟩ ⟨1⟩ []))
      , rregion 1 none [handle] (.enter ⟨1⟩ ⟨2⟩ [⟨0⟩])
      , rregion 2 (some 1) [handle] (.plain (.perform ⟨2⟩ ⟨0⟩ ⟨4⟩ []))
      , rregion 3 none ["number"] (.plain (.ret ⟨0⟩))
      , rregion 4 (some 1) ["number"] (.leave ⟨0⟩)
      , rregion 5 none ["number"] (.plain (.ret ⟨0⟩)) ] }

def regionProgram? (name : String) (raw : RegionFlow String) : Option RegionProgram :=
  match admitRegions (tableAlphabet ⟨0⟩ table) raw with
  | .ok flow => some { name := name, param := ("n", raw.inputTy), result := raw.resultTy,
                       table := table, flow := flow }
  | .error _ => none

def forkInRegion? : Option RegionProgram := regionProgram? "forkInRegion" forkInRegionRaw

/-- The same graph declaring one root: the byte-identity witness. -/
def forkInRegionSingle? : Option RegionProgram :=
  regionProgram? "forkInRegion" { forkInRegionRaw with roots := [⟨0⟩] }

#guard forkInRegion?.isSome
#guard forkInRegionSingle?.isSome
#guard (forkInRegion?.bind fun p => (Region.lowerRoots rows p).map (·.length)) = some 4
#guard (forkInRegionSingle?.bind fun p => (Region.lowerRoots rows p).map (·.length)) = some 1

#guard (forkInRegion?.bind fun p => (Region.lowerRoots rows p).map fun decls =>
    String.intercalate "\n" (decls.map
      (_root_.TypeScript.Render.decl _root_.TypeScript.house0))) = some
  ("/** Lowered from the region flow `forkInRegion` over `Fibers` (dispatch form, multi-root entry, nested scopes). */\n" ++
   "export const forkInRegion__entry = (entry: readonly [number, ReadonlyArray<unknown>]) =>\n" ++
   "  Effect.gen(function* () {\n" ++
   "    const fibers = yield* Fibers\n" ++
   "    const regions = yield* Regions\n" ++
   "    let b0p0!: readonly [number, readonly [ReadonlyArray<unknown>, readonly [boolean, Option.Option<number>]]]\n" ++
   "    let b1p0!: Fiber.Fiber<number, number>\n" ++
   "    let b2p0!: Fiber.Fiber<number, number>\n" ++
   "    let b3p0!: number\n" ++
   "    let b4p0!: number\n" ++
   "    let b5p0!: number\n" ++
   "    let block = entry[0]\n" ++
   "    while (true) {\n" ++
   "      switch (block) {\n" ++
   "        case 1000: {\n" ++
   "          b0p0 = entry[1][0] as readonly [number, readonly [ReadonlyArray<unknown>, readonly [boolean, Option.Option<number>]]]\n" ++
   "          block = 0\n" ++
   "          continue\n" ++
   "        }\n" ++
   "        case 1005: {\n" ++
   "          b5p0 = entry[1][0] as number\n" ++
   "          block = 5\n" ++
   "          continue\n" ++
   "        }\n" ++
   "        case 0: {\n" ++
   "          const a0 = yield* fibers.fork(b0p0[0], b0p0[1][0], b0p0[1][1][0], b0p0[1][1][1])\n" ++
   "          b1p0 = a0\n" ++
   "          block = 1\n" ++
   "          continue\n" ++
   "        }\n" ++
   "        case 1: {\n" ++
   "          b2p0 = b1p0\n" ++
   "          yield* regions.enter(1)\n" ++
   "          const r1 = yield* Effect.scoped(Effect.onExit(Effect.gen(function* () {\n" ++
   "            let block1 = 2\n" ++
   "            while (true) {\n" ++
   "              switch (block1) {\n" ++
   "                case 2: {\n" ++
   "                  const a2 = yield* fibers.join(b2p0)\n" ++
   "                  b4p0 = a2\n" ++
   "                  block1 = 4\n" ++
   "                  continue\n" ++
   "                }\n" ++
   "                case 4: {\n" ++
   "                  return b4p0\n" ++
   "                }\n" ++
   "              }\n" ++
   "            }\n" ++
   "          }), (exit) => regions.leave(1, exit)))\n" ++
   "          b3p0 = r1\n" ++
   "          block = 3\n" ++
   "          continue\n" ++
   "        }\n" ++
   "        case 3: {\n" ++
   "          return b3p0\n" ++
   "        }\n" ++
   "        case 5: {\n" ++
   "          return b5p0\n" ++
   "        }\n" ++
   "      }\n" ++
   "    }\n" ++
   "  })\n" ++
   "\n" ++
   "/** Enter the flow `forkInRegion` at block 0 (dispatch form, multi-root, nested scopes). */\n" ++
   "export const forkInRegion: (n: readonly [number, readonly [ReadonlyArray<unknown>, readonly [boolean, Option.Option<number>]]]) => Effect.Effect<number, number, Fibers | Regions> = (n) => forkInRegion__entry([1000, [n]])\n" ++
   "\n" ++
   "/** Enter the declared root of `forkInRegion` at block 5 (dispatch form, multi-root, nested scopes). */\n" ++
   "export const forkInRegion__root5: (p0: number) => Effect.Effect<number, number, Fibers | Regions> = (p0) => forkInRegion__entry([1005, [p0]])\n" ++
   "\n" ++
   "/** The parameterised entry of `forkInRegion`: a declared root and its arguments. */\n" ++
   "export const forkInRegionEntry = forkInRegion__entry\n")

#guard (forkInRegion?.map (Region.declarationLine rows)) = some
  ("export declare const forkInRegion: (n: readonly [number, readonly [ReadonlyArray<unknown>, " ++
   "readonly [boolean, Option.Option<number>]]]) => Effect.Effect<number, number, Fibers | Regions>;")
#guard (forkInRegion?.map (Region.ruleSet rows)) =
  some [.serviceAcquire, .dispatchLoop, .blockCase, .entryRoot, .flowPerform, .performCall,
        .performTuple, .paramMove, .flowRet, .regionEnter, .regionLeave]

/-! ### 8a. Byte identity for region flows, at both forms -/

example (rowsOf : ServiceRow) (program : RegionProgram)
    (single : (program.flow.flow).roots.length ≤ 1) :
    Region.lowerRoots rowsOf program =
      (Region.lowerDispatch rowsOf program).map fun decl => [_root_.TypeScript.Decl.prog decl] :=
  Region.lowerDispatch_single_root_eq rowsOf program single

example (rowsOf : ServiceRow) (program : RegionProgram)
    (single : (program.flow.flow).roots.length ≤ 1) :
    Region.lowerRootsBest rowsOf program =
      (Region.lowerBest rowsOf program).map fun decl => [_root_.TypeScript.Decl.prog decl] :=
  Region.lowerBest_single_root_eq rowsOf program single

example (rowsOf : ServiceRow) (program : FlowProgram)
    (single : (program.flow.erase).roots.length ≤ 1) :
    Flow.lowerRootsBest rowsOf program =
      (Flow.lowerBest rowsOf program).map fun decl => [_root_.TypeScript.Decl.prog decl] :=
  Flow.lowerBest_single_root_eq rowsOf program single

-- And concretely, on rendered text.
#guard (forkInRegionSingle?.map fun p =>
  ((Region.lowerRoots rows p).map fun decls =>
      decls.map (_root_.TypeScript.Render.decl _root_.TypeScript.house0)) ==
  ((Region.lowerDispatch rows p).map fun decl =>
      [_root_.TypeScript.Render.decl _root_.TypeScript.house0 (.prog decl)])) = some true
#guard (forkInRegionSingle?.map fun p =>
  ((Region.lowerRootsBest rows p).map fun decls =>
      decls.map (_root_.TypeScript.Render.decl _root_.TypeScript.house0)) ==
  ((Region.lowerBest rows p).map fun decl =>
      [_root_.TypeScript.Render.decl _root_.TypeScript.house0 (.prog decl)])) = some true

-- A declared root inside a region has no multi-root lowering: the top-level
-- dispatch loop does not run that block.
def rootInsideRegionRaw : RegionFlow String :=
  { forkInRegionRaw with roots := [⟨0⟩, ⟨4⟩] }

#guard (regionProgram? "rootInside" rootInsideRegionRaw).isSome
#guard ((regionProgram? "rootInside" rootInsideRegionRaw).bind fun p =>
  Region.lowerRoots rows p).isNone

/-! ## 9. The import line is what the module names

`Spelling.namespacesOf` scans a fixed, alphabetical needle list, and each flow
module emitter takes it over the rows it *declares* — the families plus
`Decisions`, `Regions` and `Interrupts` exactly when their classes are emitted.
So `Exit` arrives with the `Regions` class, which is the only row that spells it,
instead of from a hand-written `if regions` at the emitter; and a fiber module
imports `Fiber` and `Option`, which it could not before.

Every existing generated module's import line is unchanged, and these are the
two facts that say why: a row set that names nothing needs nothing, and
`regionsRows` alone yields exactly `["Exit"]`, which is what the old
`if regions then ["Exit"]` produced. -/

#guard Spelling.namespacesOf ["number", "boolean", "void"] = []
#guard Spelling.namespacesOf [handleTy "number" "number"] = ["Fiber"]
#guard Spelling.namespacesOf ["Exit.Exit<unknown, unknown>"] = ["Exit"]
#guard Spelling.namespacesOf regionsRows.spellings = ["Exit"]
#guard Spelling.namespacesOf decisionsRows.spellings = []
#guard Spelling.namespacesOf interruptsRows.spellings = []
-- The order is the needle list's, not the spellings'.
#guard Spelling.namespacesOf
    ["Result.Result<number, number>", "Option.Option<number>",
     "Fiber.Fiber<number, number>", "Exit.Exit<unknown, unknown>"] =
  ["Exit", "Fiber", "Option", "Result"]

#guard moduleNamespaces [decisionsRows] [] = []
#guard moduleNamespaces [regionsRows] [] = ["Exit"]
#guard moduleNamespaces [regionsRows, decisionsRows, interruptsRows] [] = ["Exit"]
#guard moduleNamespaces [rows] [] = ["Fiber", "Option", "Result"]
-- A caller that already binds the names in its own imports subtracts them; this
-- is how the harness's `fiber-fixture` and `deferred-fixture` import them as
-- types only and keep the value import at `Context, Effect`.
#guard moduleNamespaces [rows] [.types ["Fiber", "Option", "Result"] "effect"] = []

-- The `effect` import line of a rendered module is read inline in each receipt:
-- a `def` splitting the rendered text would reach `Classical.choice` through
-- Lean's string folds, and the axiom gate audits battery declarations too,
-- while a `#guard` is a command and leaves none.

-- A family that names no `effect` namespace: `Context` and `Effect`, as before.
#guard (flowModules? [(decisionsRows, [])]).map (fun source =>
    ((source.splitOn "\n").filter fun line =>
      (line.splitOn "from \"effect\"").length > 1).headD "-") =
  some "import { Context, Effect } from \"effect\""

-- The fiber module names `Fiber` (every handle), `Option` (the fork's region
-- field) and `Result` (`awaitFiber`'s exit), and now imports all three.
#guard (forkJoin?.bind fun a => caughtJoin?.bind fun b => maskedChild?.bind fun c =>
    (flowModules? [(rows, [a, b, c])]).map (fun source =>
    ((source.splitOn "\n").filter fun line =>
      (line.splitOn "from \"effect\"").length > 1).headD "-")) =
  some "import { Context, Effect, Fiber, Option, Result } from \"effect\""

-- With a region, `Exit` joins them — carried by the `Regions` class, in the
-- needle list's order.
#guard (forkInRegion?.bind fun p => (regionModules? [(rows, [], [p])]).map (fun source =>
    ((source.splitOn "\n").filter fun line =>
      (line.splitOn "from \"effect\"").length > 1).headD "-")) =
  some "import { Context, Effect, Exit, Fiber, Option, Result } from \"effect\""

end Effect4Test.Target.TypeScript.FiberProfileContract

