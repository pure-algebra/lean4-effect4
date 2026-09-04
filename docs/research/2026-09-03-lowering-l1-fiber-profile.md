# Lowering lane L1: the fiber profile as a target profile, and the multi-root entry

Status: implemented, 2026-09-03. Lane L1 of the lowering packet, plus the two
follow-ups the coordinator asked for after the first integration: the multi-root
entry for **region** flows (spike S3's programs are `RegionFlow`s), and an
`effect` import line computed from the rows a module declares. Sources read, in
the order the brief names them: `docs/research/2026-09-03-deep-plan.md` §0 ruling 3
(`:29-36`), `workshop/Deep/fork-lowering.md` (all four sections),
`docs/research/2026-09-03-spike-s3-fork-flow.md` §2, and the `FiberOp` /
`forkParams` / `OpSpec` rows of `workshop/Deep/ForkFlow.lean:93-262` (read only;
nothing under `workshop/` was edited).

## What builds

```
lake build Effect4.Target.TypeScript.FiberProfile         -> 28 jobs, success
lake build Effect4.Target.TypeScript.FlowLower            -> 37 jobs, success
lake build Effect4.Target.TypeScript.StructureLaws        -> 45 jobs, success
lake build Effect4.Target.TypeScript.SkeletonSemantics    -> 46 jobs, success
lake build Effect4.Target.TypeScript.StructuredLower      -> 39 jobs, success
             (pulls RegionLower, StructureSemantics, StructureOrder)
lake build Effect4Test.Target.TypeScript.FiberProfileContract -> 41 jobs, success
lake build Effect4Test.Flow.DeferredsContract             -> 20 jobs, success
lake build Effect4TestTarget                              -> 98 jobs, success
```

`Effect4TestTarget` passing **unchanged** is the byte-identity evidence: it
contains `FlowLowerContract`, `RegionLowerContract`, `StructuredLowerContract`,
`MultiArgContract`, `AnswerProfileContract`, `StructureLaws*`,
`SkeletonSemantics*` and `LoweringCoverage`, and every rendered-text `#guard` in
them still holds. No `sorry` was written; no golden under `generated/` was
touched.

Two area batteries outside this lane are red and were red before it:
`Effect4TestFlow` (`Effect4Test/Flow/RefsContract.lean:74,85,100,131`, golden
rows and `Refs.rows` spellings) and `Effect4TestCounterexamples`
(`Effect4Test/Counterexamples/Semantics/Layers.lean:137`, the `Layers` operation
list). Both batteries are unmodified in git and both test modules that another
agent has open — `Effect4/Stateful/RefFamily.lean` and
`Effect4/Layer/LayerFamily.lean`, neither of which this lane may touch. Neither
failure reaches a target module.

### Files

| File | Change |
| --- | --- |
| `Effect4/Target/TypeScript/FiberProfile.lean` | **new**: `FiberOp`, the twelve `OpSpec` rows, the spellings, the `Fibers` `ServiceRow` |
| `Effect4/Target/TypeScript/Skeleton.lean` | two `Skeleton` formers; `Lowering.rootEntryBase`, `Lowering.enterAt`, `Lowering.entryRootCase` (`lowering: rule.entry-root`) |
| `Effect4/Target/TypeScript/SkeletonRender.lean` | two printer cases; `Lowering.entryCaseRead`, `Lowering.entryArgRead` |
| `Effect4/Target/TypeScript/Lower.lean` | `Rule.entryRoot`, appended last |
| `Effect4/Target/TypeScript/EffectV4.lean` | `Spelling.namespacesOf` scans `Exit`/`Fiber` as well; new `moduleNamespaces` |
| `Effect4/Target/TypeScript/FlowLower.lean` | `blockCases`, the multi-root entry, `lowerRoots`, `lowerDispatch_single_root_eq`, the shared alias builders; `flowModules?` routes through `lowerRoots` and `moduleNamespaces` |
| `Effect4/Target/TypeScript/RegionLower.lean` | the same entry for region flows: `Region.skeletonEntry`, `lowerEntry`, `rootAlias`, `lowerRoots`, `lowerDispatch_single_root_eq`; `regionModules?` routes through both |
| `Effect4/Target/TypeScript/StructuredLower.lean` | `Flow.lowerRootsBest`, `Region.lowerRootsBest` and their two byte-identity theorems; `structuredModules?` routes through them and `moduleNamespaces` |
| `Effect4/Target/TypeScript/SkeletonSemantics.lean` | one docstring paragraph on `simple?` (why the two new nodes are not simple) |
| `Effect4/Target/TypeScript/StructureLaws.lean` | the two new constructors added to `render_wellScoped`'s label-free alternation |
| `Effect4Test/Target/TypeScript/FiberProfileContract.lean` | **new**: the battery, 611 lines |
| `Effect4Test/Target/TypeScript/FlowLowerContract.lean` | the census id list gains `"entry-root"`; `Rule.all.length` 29 → 30 |
| `Effect4Test/Target/TypeScript/LoweringCoverage.lean` | the `entry-root` ledger row |

`Effect4Test.lean` and `Effect4Test/Audit/AxiomGate.lean` were **not** edited;
§9 lists exactly what they need, including the roots the second round adds to
the three the coordinator has already applied.

---

## 1. The profile as a target profile

`Effect4/Target/TypeScript/FiberProfile.lean` declares the twelve rows exactly as
`workshop/Deep/ForkFlow.lean:210-245` spells them, plus `FiberOp` (the name an
index is read through), the four spellings (`handleTy`, `exitTy`,
`forkParams`/`rootParams`, `forkRequestTy`/`rootRequestTy`) and the `Fibers`
`ServiceRow`.

| # | Name | Request | Answer | `errorTy` | rc.112 (`vendor/effect-4.0.0-rc.112/src/internal/effect.ts`) |
| --- | --- | --- | --- | --- | --- |
| 0 | `fork` | `readonly [number, readonly [ReadonlyArray<unknown>, readonly [boolean, Option.Option<number>]]]` | `H` | `never` | `forkUnsafe` `:5264`; `forkIn` `:5337` when `region` is `some` |
| 1 | `forkScoped` | as `fork` | `H` | `never` | `forkScoped` `:5382` |
| 2 | `join` | `H` | `number` | **`number`** | `fiberJoin` `:814` |
| 3 | `awaitFiber` | `H` | `X` | `never` | `fiberAwait` `:767` |
| 4 | `interruptFiber` | `H` | `void` | `never` | `fiberInterrupt` `:857` |
| 5 | `interruptAll` | `ReadonlyArray<H>` | `void` | `never` | `fiberInterruptAll` `:888` |
| 6 | `childrenSnapshot` | `void` | `ReadonlyArray<H>` | `never` | `awaitAllChildren` `:5314`, snapshot half |
| 7 | `awaitChildren` | `ReadonlyArray<H>` | `void` | `never` | `awaitAllChildren` `:5314`, exit half |
| 8 | `raceAll` | `ReadonlyArray<R>` | `number` | **`number`** | `raceAll` `:1477` |
| 9 | `uninterruptibleIn` | `R` | `number` | **`number`** | `uninterruptible` `:4302` |
| 10 | `interruptibleIn` | `R` | `number` | **`number`** | `interruptible` `:4331` |
| 11 | `yieldNow` | `number` | `void` | `never` | `yieldNowWith` `:982` |

`H = Fiber.Fiber<number, number>`, `X = Result.Result<number, number>`,
`R = readonly [number, ReadonlyArray<unknown>]`, at the spelling
`fiberProfile "number" "number"`.

**A correction to spike S3 §2.** S3's table cites `fiberJoin` at `:5291`,
`fiberAwait` at `:5304`, `fiberInterrupt` at `:859`, `fiberInterruptAll` at
`:895` and `forkIn` at `:5364-5378`. In this repository's vendored rc.112 those
`export const` lines are `:814`, `:767`, `:857`, `:888` and `:5337`. The
citations above are the vendored copy's; S3's numbers land inside or beside the
same definitions but are not their declaration lines. Nothing else in S3's §2
differs from what is implemented.

### The error channel, typed

Ruling 8 of the deep plan, restated as five receipts in the battery §1:
`join` carries the child's `errorTy`, so a `performCatch` on it binds a value of
that type; `awaitFiber` resumes the exit *as a value* and declares `never`;
`interruptFiber` and `interruptAll` declare `never`. `raceAll`,
`uninterruptibleIn` and `interruptibleIn` resume a child's failure *in this
fiber* and therefore carry `E` too. `FiberOp.fails` is the predicate, keyed by
the operation rather than by comparing the `"never"` spelling, so no `String` is
traversed in the profile module.

### The `ServiceRow` is the rows

`fibersRows answerTy errorTy answerLean errorLean` builds the `Fibers`
`ServiceRow` by zipping `FiberOp.all` with `fiberProfile`: the TypeScript face of
every method is *read off the `OpSpec` row*, never restated. The receipt is the
round trip through the existing `familyTable`:

```lean
#guard (familyTable rows).map (fun s => (s.name, s.requestTy, s.answerTy, s.errorTy, s.params)) ==
  table.map (fun s => (s.name, s.requestTy, s.answerTy, s.errorTy, s.params))
```

so the service class the host implements and the alphabet the flow runs against
cannot disagree about a name, a request, an answer or an error.
(`OpSpec` derives no `BEq`, hence the five-field comparison.)

### `tableAlphabet`, unchanged

`Effect4/Target/TypeScript/ScriptFlow.lean` was **not edited**. The battery §2
builds `tableAlphabet ⟨0⟩ fiberProfileNat` and reads five rows back through it,
including `errorTy` as the v0.8.0 `Option` and the out-of-range `lookup ⟨12⟩`.
S3's claim holds as written.

---

## 2. The emitted TypeScript, row by row

Rendered by the battery (§4) from `Skeleton.render rows` of a family `perform`
whose request slot is `b1p0` and whose answer is `a1`. These are the actual
pinned strings, not a transcription:

```ts
const a1 = yield* fibers.fork(b1p0[0], b1p0[1][0], b1p0[1][1][0], b1p0[1][1][1])
const a1 = yield* fibers.forkScoped(b1p0[0], b1p0[1][0], b1p0[1][1][0], b1p0[1][1][1])
const a1 = yield* fibers.join(b1p0)
const a1 = yield* fibers.awaitFiber(b1p0)
const a1 = yield* fibers.interruptFiber(b1p0)
const a1 = yield* fibers.interruptAll(b1p0)
const a1 = yield* fibers.childrenSnapshot
const a1 = yield* fibers.awaitChildren(b1p0)
const a1 = yield* fibers.raceAll(b1p0)
const a1 = yield* fibers.uninterruptibleIn(b1p0[0], b1p0[1])
const a1 = yield* fibers.interruptibleIn(b1p0[0], b1p0[1])
const a1 = yield* fibers.yieldNow(b1p0)
```

**No printer change was needed for any of them.** `Lowering.callOf`
(`SkeletonRender.lean:68-71`) picks all three shapes off the row: the `void`
request of `childrenSnapshot` becomes an Effect *value*, arity one becomes a call
on the slot, arity four and two destructure through `Lowering.tupleArgs`. This is
`fork-lowering.md` §(a) confirmed by execution, and it matches its table row for
row (the doc uses `b0p0` for the two fork rows; the battery uses one slot
throughout so the twelve lines read as a table).

### The `Fibers` service class, from the same rows

```ts
/** Service `Fibers`: one method per operation of the Lean family. */
export class Fibers extends Context.Service<Fibers, {
  readonly fork: (root: number, args: ReadonlyArray<unknown>, daemon: boolean, region: Option.Option<number>) => Effect.Effect<Fiber.Fiber<number, number>>
  readonly forkScoped: (root: number, args: ReadonlyArray<unknown>, daemon: boolean, region: Option.Option<number>) => Effect.Effect<Fiber.Fiber<number, number>>
  readonly join: (fiber: Fiber.Fiber<number, number>) => Effect.Effect<number, number>
  readonly awaitFiber: (fiber: Fiber.Fiber<number, number>) => Effect.Effect<Result.Result<number, number>>
  readonly interruptFiber: (fiber: Fiber.Fiber<number, number>) => Effect.Effect<void>
  readonly interruptAll: (fibers: ReadonlyArray<Fiber.Fiber<number, number>>) => Effect.Effect<void>
  readonly childrenSnapshot: Effect.Effect<ReadonlyArray<Fiber.Fiber<number, number>>>
  readonly awaitChildren: (snapshot: ReadonlyArray<Fiber.Fiber<number, number>>) => Effect.Effect<void>
  readonly raceAll: (entrants: ReadonlyArray<readonly [number, ReadonlyArray<unknown>]>) => Effect.Effect<number, number>
  readonly uninterruptibleIn: (root: number, args: ReadonlyArray<unknown>) => Effect.Effect<number, number>
  readonly interruptibleIn: (root: number, args: ReadonlyArray<unknown>) => Effect.Effect<number, number>
  readonly yieldNow: (priority: number) => Effect.Effect<void>
}>()("Fibers") {}
```

This is `ServiceRow.classDecl` of `fibersRowsNat`, byte for byte, and it agrees
with the hand-written sketch in `fork-lowering.md` §(c) on every method: the four
failing rows get the aborting reading `Effect.Effect<A, E>`
(`EffectV4.lean:175-179`) and `childrenSnapshot` is an Effect *value*, not a
thunk — note 3 of §(c), enforced by `ServiceRow.methodType`.

### The caught join

`performCatch` of `join` lowers as every caught perform does; the failure edge
binds the child's typed error:

```ts
case 1: {
  const a1 = yield* Effect.result(fibers.join(b1p0))
  if (Result.isSuccess(a1)) {
    b2p0 = a1.success
    block = 2
    continue
  } else {
    b3p0 = a1.failure
    block = 3
    continue
  }
}
```

`b3p0` is declared `let b3p0!: number` because Flow v3's `SlotWF` error arm
compares the failure successor's last parameter against the operation's declared
`errorTy` (`.lake/packages/effects/Effects/Flow/Raw.lean:159-168`) — i.e. the
flow is *admitted* only if the failure edge binds the child's error type. That is
the whole reason `join` carries a real `errorTy` and `awaitFiber` carries
`never`.

One consequence worth recording: `Flow.errorChannel` scans `.perform` terms only,
so the caught-join flow's declared error channel is `never` while the uncaught
one's is `number`. Both are pinned in the battery §5b. That is correct — the
catch handles the failure — and it is the first time the distinction has had a
program to show it.

---

## 3. The entry change, before and after

`fork-lowering.md` §(b). The same two-root graph (block `0` forks, block `1`
joins, block `3` is the child's body), lowered before and after.

### Before — one root declared (`roots := [⟨0⟩]`), today's output

```ts
/** Lowered from the flow `forkJoin` over `Fibers` (dispatch form). */
export const forkJoin = (n: readonly [number, readonly [ReadonlyArray<unknown>, readonly [boolean, Option.Option<number>]]]) =>
  Effect.gen(function* () {
    const fibers = yield* Fibers
    let b0p0!: readonly [number, readonly [ReadonlyArray<unknown>, readonly [boolean, Option.Option<number>]]]
    let b1p0!: Fiber.Fiber<number, number>
    let b2p0!: number
    let b3p0!: number
    b0p0 = n
    let block = 0
    while (true) {
      switch (block) {
        case 0: {
          const a0 = yield* fibers.fork(b0p0[0], b0p0[1][0], b0p0[1][1][0], b0p0[1][1][1])
          b1p0 = a0
          block = 1
          continue
        }
        case 1: {
          const a1 = yield* fibers.join(b1p0)
          b2p0 = a1
          block = 2
          continue
        }
        case 2: { return b2p0 }
        case 3: { return b3p0 }
      }
    }
  })
```

Block `3` is emitted but unreachable: nothing can enter it, so the fork it is the
target of has nothing to start.

### After — two roots declared (`roots := [⟨0⟩, ⟨3⟩]`)

```ts
/** Lowered from the flow `forkJoin` over `Fibers` (dispatch form, multi-root entry). */
export const forkJoin__entry = (entry: readonly [number, ReadonlyArray<unknown>]) =>
  Effect.gen(function* () {
    const fibers = yield* Fibers
    let b0p0!: readonly [number, readonly [ReadonlyArray<unknown>, readonly [boolean, Option.Option<number>]]]
    let b1p0!: Fiber.Fiber<number, number>
    let b2p0!: number
    let b3p0!: number
    let block = entry[0]
    while (true) {
      switch (block) {
        case 1000: {
          b0p0 = entry[1][0] as readonly [number, readonly [ReadonlyArray<unknown>, readonly [boolean, Option.Option<number>]]]
          block = 0
          continue
        }
        case 1003: {
          b3p0 = entry[1][0] as number
          block = 3
          continue
        }
        case 0: { /* identical to `before`, byte for byte */ }
        case 1: { /* identical */ }
        case 2: { return b2p0 }
        case 3: { return b3p0 }
      }
    }
  })

/** Enter the flow `forkJoin` at block 0 (dispatch form, multi-root). */
export const forkJoin: (n: readonly [number, readonly [ReadonlyArray<unknown>, readonly [boolean, Option.Option<number>]]]) => Effect.Effect<number, number, Fibers> = (n) => forkJoin__entry([1000, [n]])

/** Enter the declared root of `forkJoin` at block 3 (dispatch form, multi-root). */
export const forkJoin__root3: (p0: number) => Effect.Effect<number, number, Fibers> = (p0) => forkJoin__entry([1003, [p0]])

/** The parameterised entry of `forkJoin`: a declared root and its arguments. */
export const forkJoinEntry = forkJoin__entry
```

Exactly three things moved: `b0p0 = n` and `let block = 0` became one
`let block = entry[0]` plus two synthetic cases, and the module emits
`1 + |roots| + 1` declarations instead of one. Every flow block case is the same
list — `Flow.skeletonEntry` and `Flow.skeletonDispatch` call the *same*
`Flow.blockCases`, so this is a shared definition and not a comparison.

The declaration line the pinned compiler must emit for `forkJoin` is unchanged by
the entry change, and the alias is written at that type rather than leaving it to
inference so the emitted `.d.ts` is byte-equal to it:

```
export declare const forkJoin: (n: readonly [number, readonly [ReadonlyArray<unknown>, readonly [boolean, Option.Option<number>]]]) => Effect.Effect<number, number, Fibers>;
```

The masked-child flow (`uninterruptibleIn`, two roots) is pinned the same way in
battery §5c; its call is `yield* fibers.uninterruptibleIn(b0p0[0], b0p0[1])` and
its second root is exported as `maskedChild__root2`.

### The host side

`fork-lowering.md` §(c)'s `FibersLive(enter, scopes)` closes over `progEntry`,
which is `forkJoinEntry` here, and `fork` builds `enter([1000 + root, args])` —
the same base, `Lowering.rootEntryBase`. Nothing in the emitted module is
`Effect.fork`; battery §5d pins that by `splitOn`, on all three programs. That is
ruling 3 restated as bytes.

### The same entry, for a region flow

Spike S3's witnesses and its compile are over `RegionFlow`
(`workshop/Deep/ForkFlow.lean`), so a fork that names a declared root names one
of *those* roots. `Region.lowerRoots` is the plain form's change transcribed:
the same `Region.skeletonCases` call, the entry parameter, one synthetic case per
declared root. Battery §8 pins a two-root region flow that forks the declared
root `5` outside a region and joins it *inside* one, so the child's exit is the
region's value:

```ts
/** Lowered from the region flow `forkInRegion` over `Fibers` (dispatch form, multi-root entry, nested scopes). */
export const forkInRegion__entry = (entry: readonly [number, ReadonlyArray<unknown>]) =>
  Effect.gen(function* () {
    const fibers = yield* Fibers
    const regions = yield* Regions
    …declarations…
    let block = entry[0]
    while (true) {
      switch (block) {
        case 1000: { b0p0 = entry[1][0] as readonly […]; block = 0; continue }
        case 1005: { b5p0 = entry[1][0] as number; block = 5; continue }
        case 0: { const a0 = yield* fibers.fork(b0p0[0], b0p0[1][0], b0p0[1][1][0], b0p0[1][1][1]); … }
        case 1: {
          b2p0 = b1p0
          yield* regions.enter(1)
          const r1 = yield* Effect.scoped(Effect.onExit(Effect.gen(function* () {
            let block1 = 2
            while (true) {
              switch (block1) {
                case 2: { const a2 = yield* fibers.join(b2p0); b4p0 = a2; block1 = 4; continue }
                case 4: { return b4p0 }
              }
            }
          }), (exit) => regions.leave(1, exit)))
          b3p0 = r1
          block = 3
          continue
        }
        case 3: { return b3p0 }
        case 5: { return b5p0 }
      }
    }
  })

export const forkInRegion: (n: readonly […]) => Effect.Effect<number, number, Fibers | Regions> = (n) => forkInRegion__entry([1000, [n]])
export const forkInRegion__root5: (p0: number) => Effect.Effect<number, number, Fibers | Regions> = (p0) => forkInRegion__entry([1005, [p0]])
export const forkInRegionEntry = forkInRegion__entry
```

The nested region generator is untouched: it keeps its own `block1` variable and
its own cases, because a region's blocks are not in the top-level loop. That is
also the one refusal the plain form cannot need, and it is new here:

> **A declared root must sit outside every region.** The top-level dispatch loop
> runs exactly the blocks whose label is `none`
> (`Region.skeletonCases … none "block"`); a region's blocks live in a nested
> generator with a block variable of their own, so a synthetic case at the top
> level cannot continue at one. Admission already refuses an *entry* inside a
> region (`Effects.RegionClause.entryInside`); `Region.skeletonEntry` returns
> `none` for the rest rather than emitting a case that jumps nowhere. Battery §8a
> pins it: the same graph with `roots := [⟨0⟩, ⟨4⟩]` is admitted and has no
> multi-root lowering.

### `lowerBest`: a multi-root flow keeps the dispatch entry

`Flow.lowerRootsBest` and `Region.lowerRootsBest` are `lowerBest` for one
declared root and the **dispatch** entry for two or more. Entering a chosen root
means entering the dispatch loop at a chosen case, and the structured form has no
case to enter at — its control is labelled blocks with `break`/`continue`. That
is the same trade `dispatch-fallback` already makes for an irreducible graph, and
the census still records it: `ruleSet` reports `entry-root` for any multi-root
flow, and `structuredRuleSet` includes `ruleSet`.

---

## 4. The byte-identity theorem

```lean
/-- **The byte-identity receipt of the entry change.** … -/
theorem lowerDispatch_single_root_eq (rows : ServiceRow) (program : FlowProgram)
    (single : (program.flow.erase).roots.length ≤ 1) :
    lowerRoots rows program = (lowerDispatch rows program).map fun decl => [Decl.prog decl] := by
  simp only [lowerRoots, if_pos single]
```

`Effect4/Target/TypeScript/FlowLower.lean`, in the style of S3's
`compileFork_eq_compileRegion` (`workshop/Deep/ForkFlow.lean:616-666`): the new
path *is* the old path on the old inputs. Every flow in the four lowering
batteries, every program the harness lowers, and every graph in `generated/` has
exactly one declared root, so none of their bytes can move — and
`lake build Effect4TestTarget` says they did not.

The theorem is a statement about the emitter's branch, and that is the honest
shape of the claim: byte identity *requires* the branch, because the entry form
changes the exported name, the parameter and two statements. What the branch is
worth is settled by the concrete instance the battery §6 also pins, which
compares **rendered text**, not syntax:

```lean
#guard (caughtJoin?.map fun p =>
  ((Flow.lowerRoots rows p).map fun decls => decls.map (Render.decl house0)) ==
  ((Flow.lowerDispatch rows p).map fun decl => [Render.decl house0 (.prog decl)])) = some true
```

`lowerDispatch_single_root_eq` reaches `[propext, Classical.choice, Quot.sound]`
because its statement names `lowerDispatch`, a renderer. That is why it is not
the `proof` entry of the `entry-root` ledger row (§5).

### The other three

The same statement holds at each of the three other lowering paths, one theorem
each, all proved the same way:

| Theorem | Module | Says |
| --- | --- | --- |
| `Flow.lowerDispatch_single_root_eq` | `FlowLower.lean` | `Flow.lowerRoots` is `Flow.lowerDispatch` |
| `Flow.lowerBest_single_root_eq` | `StructuredLower.lean` | `Flow.lowerRootsBest` is `Flow.lowerBest` — structured where the graph is reducible, dispatch where it is not |
| `Region.lowerDispatch_single_root_eq` | `RegionLower.lean` | `Region.lowerRoots` is `Region.lowerDispatch` |
| `Region.lowerBest_single_root_eq` | `StructuredLower.lean` | `Region.lowerRootsBest` is `Region.lowerBest` |

Every flow and region flow this library lowered before the fiber profile
declares exactly one root — `FlowLowerContract`, `RegionLowerContract`,
`StructuredLowerContract`, `MultiArgContract`, the harness's `flowFamilies` and
`jobPrograms`, the property corpus — so all four emitters are pinned on their old
inputs. Battery §6 and §8a carry the four generic `example`s plus two concrete
rendered-text comparisons (a plain flow and a region flow).

---

## 5. `Rule.all`: one tag appended, `fiber-call` not needed

**`entry-root` is the only addition.** `Rule.all` goes 29 → 30, appended, never
reordered; every existing id keeps its position, and `FlowLowerContract.lean` —
the one battery that pins the whole list — is the only battery whose census block
changed.

**`fiber-call` is not needed, and here is why.** The profile's twelve calls are
already covered by rules that exist:

| Profile shape | Rules that lower it | Definition |
| --- | --- | --- |
| any of the twelve, as a block terminator | `flow-perform` | `Lowering.flowPerform`, `Skeleton.lean` |
| `join`, `awaitFiber`, `interruptFiber`, `interruptAll`, `awaitChildren`, `raceAll`, `yieldNow` (arity 1) | `perform-call` | `Lowering.performCall`, `EffectV4.lean:354-355` |
| `childrenSnapshot` (`void` request) | `nullary-value` | `Lowering.nullaryValue`, `EffectV4.lean:349-350` |
| `fork`, `forkScoped` (arity 4), `uninterruptibleIn`, `interruptibleIn` (arity 2) | `perform-tuple` | `Lowering.tupleArgs`, `SkeletonRender.lean:58-61` |
| a caught `join` | `perform-catch` | `Lowering.performCatchResult`, `Skeleton.lean` |
| the request-slot moves and the block transfer | `param-move`, `block-case`, `dispatch-loop`, `flow-ret` | unchanged |

The battery §7 pins `Flow.ruleSet` on the three plain programs and §8 pins
`Region.ruleSet` on the region one; `fork` appears as `flow-perform` +
`perform-call` + `perform-tuple` and nothing else, and the region flow adds only
`region-enter` and `region-leave`. `Region.ruleSet` delegates to `Flow.ruleSet`
on the erased graph, so a multi-root *region* flow reports `entry-root` with no
further change. A
`fiber-call` rule would be a second name for `perform-call`, and the ledger's own
rule — "a rule is exactly the code below its tag", one definition per rule
(`docs/LOWERING-COVERAGE.md`, *Rules*) — refuses that: there is no `fiber-call`
definition to tag.

### The ledger row, verbatim

In `Effect4Test/Target/TypeScript/LoweringCoverage.lean`, appended last so the
rows stay in `Rule.all`'s order:

```lean
, { rule := .entryRoot, state := .absent, goldens := [],
    host := false, property := false, typeReceipt := false, proof := none }
```

which `#lowering_coverage` prints as

```
E4LOWCOV	entry-root	absent		0	0	0	-
```

`absent`, and honestly so: no traced program declares two roots yet — the fiber
profile's *runner* face belongs to the fiber-machine packet, not to this one — so
the rule has no golden, no host receipt, no property batch and no type receipt.
Its Lean receipt is `lowerDispatch_single_root_eq`, which is deliberately **not**
a `proof` entry: the ledger checks a `proof` for the `propext`/`Quot.sound`
ceiling, and this one names a renderer.

---

## 6. The import line is what the module names

The first round's §7.4 recorded a gap: a generated fiber module would name
`Fiber.Fiber<…>` and `Option.Option<…>` and import neither, because
`Spelling.namespacesOf` scanned exactly two needles and each flow emitter added
`Result` (and, at the region emitter, `Exit`) by hand. That gap is now closed,
and closed in a way that leaves every existing module's import line alone.

Two changes.

1. **`Spelling.namespacesOf` scans four needles**, `["Exit", "Fiber", "Option",
   "Result"]`, fixed and alphabetical so the import line is a function of the
   spellings and nothing else. The test stays by occurrence — a substring test
   for `"<Name>."` — so a module that does not name a namespace does not import
   it, and a caller that already binds the name subtracts it through the
   existing `neededNamespaces`.
2. **`moduleNamespaces (declared : List ServiceRow) (atoms : List Import)`**
   (`EffectV4.lean`, beside `neededNamespaces`) is what the three flow emitters
   now use. `declared` is every `ServiceRow` the module emits a class for: the
   families, plus `Decisions`, `Regions` and `Interrupts` exactly when they are
   declared. So `Exit` arrives *with the `Regions` class*, which is the only row
   that spells it, instead of from a separate `if regions` at the emitter.

Byte identity, and why it holds. The old rule was `Result` when a family row
mentions `Result.`, plus `Exit` when regions are emitted. The new rule is every
needle any declared row mentions, minus what the atoms bind. They agree because:

```lean
#guard moduleNamespaces [decisionsRows] [] = []
#guard moduleNamespaces [regionsRows] [] = ["Exit"]          -- the old `if regions`
#guard Spelling.namespacesOf decisionsRows.spellings = []
#guard Spelling.namespacesOf interruptsRows.spellings = []
```

and because no module the emitters produce today names `Option.` or `Fiber.` in
a *family* row. That is checked against the artifacts rather than assumed: of the
generated fixtures under `harness/trace/`, the four the changed emitters produce
mention exactly

| Fixture | Emitter | Mentions | Import line |
| --- | --- | --- | --- |
| `flow-fixture.ts` | `regionModules?` | `Exit.` | `import { Context, Effect, Exit } from "effect"` |
| `structured-fixture.ts` | `structuredModules?` | `Exit.` | `import { Context, Effect, Exit } from "effect"` |
| `job-fixture.ts` | `regionModules?` | `Exit.`, `Result.` | `import { Context, Effect, Exit, Result } from "effect"` |

each of which the new rule reproduces exactly. `flowModules?`'s one caller is the
property corpus (`harness/trace/Property.lean:250`) over `Cell.rows`, whose two
rows spell `number` and `void` and name no namespace at all, so its fixture keeps
`import { Context, Effect } from "effect"`. The `module?`/`modules?` fixtures
(`fixture.ts`, `fiber-fixture.ts`, `deferred-fixture.ts`, `ref-fixture.ts`,
`layer-fixture.ts`, `scope-fixture.ts`) went through `neededNamespaces` already;
the two that name `Fiber.` supply `.types ["Fiber", "Option"] "effect"` and the
new needles are subtracted, so their value import stays `Context, Effect`.

The battery pins three import lines directly (§9 of `FiberProfileContract`), so
this is a receipt and not an argument:

```
flowModules?   [(decisionsRows, [])]              -> import { Context, Effect } from "effect"
flowModules?   [(Fibers, [three fiber flows])]    -> import { Context, Effect, Fiber, Option, Result } from "effect"
regionModules? [(Fibers, [], [forkInRegion])]     -> import { Context, Effect, Exit, Fiber, Option, Result } from "effect"
```

`Result` is there because `awaitFiber` answers `Result.Result<A, E>`; `Option`
because the fork's `region` field is `Option.Option<number>`; `Fiber` because
every handle is `Fiber.Fiber<A, E>`; `Exit` because the module declares
`Regions`.

**One consequence to check when its packet lands.** Two in-flight stub fixtures
name a namespace they do not import today and would gain it on the next
regeneration: `harness/trace/layers-fixture.stub.ts` mentions `Fiber.` with no
`Fiber` binding, and `harness/trace/scopes-fixture.stub.ts` mentions `Exit.` with
no `Exit` binding. Both are another agent's untouched work-in-progress; the new
import is a repair (the module names what it now imports), but their digests will
move when they are regenerated.

---

## 7. What the two docs must say at landing

Neither was edited.

### `docs/LOWERING-COVERAGE.md`

1. In *Rules*, the sentence listing the groups gains the multi-root entry:
   `Rule.all` is now the straight-line group, the dispatch group, Flow v3,
   interruption, regions, the structured form, the multi-argument perform, **and
   the multi-root entry**. The count in any prose that quotes it goes 29 → 30.
2. A new section after *Multi-argument operations*, mirroring its shape:

   > ## Declared roots
   >
   > `entry-root` (`Effect4/Target/TypeScript/Skeleton.lean`,
   > `Lowering.entryRootCase`) is what a flow needs when a *declared root* is a
   > callable entry — which is what a fork names
   > (`docs/research/2026-09-03-deep-plan.md:29-36`, ruling 3: fork is an
   > operation, and the lowering emits a service call, never `Effect.fork`). The
   > generator's entry point becomes a parameter,
   > `readonly [number, ReadonlyArray<unknown>]`, and each declared root gets a
   > synthetic dispatch case at `1000 + root` that binds its parameters from the
   > argument array and continues at its own block. The module then exports the
   > entry, one alias per declared root (the entry root keeping the program's own
   > name, signature and declaration line), and the entry re-export the host
   > `Fibers` layer closes over. The same case is emitted for a region flow, at
   > the top-level loop only: a declared root must sit outside every region,
   > because a region's blocks run in a nested generator with a block variable of
   > their own, and `Region.skeletonEntry` refuses a root inside one. At the
   > structured form a multi-root flow keeps the dispatch entry, for the reason
   > `dispatch-fallback` already gives. A flow with one declared root does not
   > take this path at all: the four `*_single_root_eq` theorems say
   > `lowerRoots`/`lowerRootsBest` are `lowerDispatch`/`lowerBest` there, so every
   > program lowered before this rule existed keeps its bytes. It has no golden
   > yet; its bytes are pinned in
   > `Effect4Test/Target/TypeScript/FiberProfileContract.lean`.
3. In *The dispatch form*, note that `flowModules?`, `regionModules?` and
   `structuredModules?` now emit `1 + |roots| + 1` declarations per multi-root
   program and one per single-root program, and that each takes its `effect`
   import from the rows it declares (`moduleNamespaces`) rather than from an
   `if regions` / `usesResult` pair.

### `docs/TYPESCRIPT-TARGET-DAG.md`

1. The *Exact output-text trust boundary* section names the eight new exact
   admissions (§10 below). The wording that already covers `Flow.lowerDispatch`
   covers the five emitters — they are renderers — and needs one sentence for the
   three `*_single_root_eq` theorems, which are the first *theorems* in the
   `Flow`/`Region` namespaces to be admitted: they are receipts about a
   renderer's output, not semantic laws. The IR side stays clean and is worth
   stating: `Lowering.rootEntryBase`, `Lowering.enterAt` and
   `Lowering.entryRootCase` are at no axiom at all, and `Flow.skeletonEntry`,
   `Flow.rootAlias`, `Flow.entryAliasDecl`, `Flow.entryExportDecl`,
   `Flow.effectType`, `Region.skeletonEntry`, `Region.rootAlias`,
   `Region.rootBinders` and `Region.effectType` all stay at
   `propext`/`Quot.sound`.
2. The *Edge ledger* `bridges` row is unchanged (still `required-open`); the
   `coverage` row should mention that the Effect v4 target profile now has a
   second profile beside the family/atom rows — the fiber profile — whose rows
   are data and whose lowering adds one rule.
3. A line for the new module in whatever manifest lists the target modules:
   `Effect4/Target/TypeScript/FiberProfile.lean` — rows and spellings only, no
   renderer, no theorem.
4. One sentence for the import rule, since it is a property of generated text:
   a generated flow module's `effect` import is `Context`, `Effect` and every
   namespace of `["Exit", "Fiber", "Option", "Result"]` its declared rows spell,
   minus the ones its own imports already bind. Before this it was `Context`,
   `Effect`, `Result` when a family row spelled it, and `Exit` when the module
   declared `Regions`; the two agree on every module the emitters produce today,
   which `Effect4TestTarget` and the fixture table in this report's §6 are the
   evidence for.

---

## 8. What the profile cannot lower with the existing `Stmt` formers

Three gaps, in decreasing order of how much they matter; a fourth, the missing
`Fiber` import, was recorded in the first round and is closed in §6. None of the
three blocked the lane.

1. **`TypeScript.Expr` has no type-assertion former.** `entry[1]` is
   `ReadonlyArray<unknown>` — the wire's untyped `Val` list surfacing on the host
   (`fork-lowering.md` §(b) "Type honesty"; packet P7's refusal,
   `docs/research/2026-09-03-deep-plan.md:106-107`) — so each root-entry case must
   read at the parameter's declared type. There is no `Expr.as`. It is spelled
   into the projection by `Lowering.entryArgRead`
   (`.ident (entry ++ "[1][" ++ toString index ++ "] as " ++ type)`), which is the
   same class of spelling `Lowering.tupleArgs` already uses for `b2p0[1][0]` and
   sits behind the same `E4-TARGET-CE-026` argument: projecting off an arbitrary
   expression is not something this fragment can build, so the projection is
   built from a slot's *spelling*. Two alternatives were priced and rejected: a
   generated `cast<T>(x)` helper through `Expr.generic` (adds a runtime helper to
   every module), and typing the entry's arguments `ReadonlyArray<any>` (removes
   the cast, but hides exactly the fact the cast is there to record). If an
   `Expr.assert (target : Expr) (type : String)` is ever added upstream, this is
   its first consumer and the change is one line of the printer.
2. **`Expr.lambda` has no per-parameter type.** `(n: number) => …` is not
   spellable as a lambda. The root aliases therefore carry the type on the
   *constant* instead — `ConstDecl.type`, which the pinned package does have —
   giving `export const forkJoin: (n: T) => Effect.Effect<A, E, R> = (n) => …`.
   This is a deviation from `fork-lowering.md` §(b), which writes
   `export const prog = (n: T) => prog__entry(…)`; the emitted program is more
   typed, not less, and its `.d.ts` line is exactly `Flow.declarationLine`. A
   *nested* typed lambda would have no route at all, which is worth knowing
   before anything tries to emit one.
3. **`Stmt` has no nested-generator former other than `scopedGen` /
   `scopedGenMasked`** (`.lake/packages/typescript/TypeScript/Syntax.lean:127-133`).
   Confirmed. This is §(b)'s own argument for the parameterised entry rather than
   a generator per root, and it holds: a per-root generator would also have to
   redeclare every parameter slot.
*(The fourth, "the generated module would not import `Fiber`", is closed: see
§6. The repair turned out not to need any fixture regenerated, because no module
the emitters produce today names `Option.` or `Fiber.` in a family row.)*

Three smaller notes.

* **A declared root must sit outside every region** (§3). This is not a `Stmt`
  gap but a shape one: the top-level dispatch loop and a region's nested
  generator are two loops with two block variables, and a synthetic case in one
  cannot continue into the other. Emitting a root inside a region would need
  either a second entry parameter threaded into every nested generator or a
  per-root generator — the shape §(b) already priced out. `Region.skeletonEntry`
  refuses instead.

* **`switch` cases are `Nat`-keyed**, so the synthetic cases are an arithmetic
  offset (`Lowering.rootEntryBase = 1000`) rather than a tagged label. A flow with
  a block id at or above the base would collide; `Flow.skeletonEntry` `guard`s it
  and refuses the multi-root lowering rather than emitting a colliding case. The
  guard is on the new path only, so it cannot change an existing output.
* **The two new IR nodes have no denotation.** `Skel.simple?`
  (`SkeletonSemantics.lean`) deliberately does not classify `rootParam` or
  `letBlockIndexFrom`: they read the entry request, and that machine's state is a
  `Slot → Val` with no model of a host argument. They stop it at a `stuck`
  frontier, exactly as the three region nodes do. This is consistent with the
  standing refusal — the emitted program's fork is a host service call, so its
  behaviour is a host receipt and never the subject of a theorem
  (`docs/TRACE-DAG.md` `targets`, `fork-lowering.md` §(d)).

---

## 9. Deviations from `workshop/Deep/fork-lowering.md` §(b), itemised

| §(b) prices | Implemented | Why |
| --- | --- | --- |
| two `Skeleton` formers, `letBlockIndexFrom` / `rootParam` | both, same names | `rootParam` gained a `type` field: the cast needs one |
| one `Rule` tag, `rule.root-entry` | `rule.entry-root` | the lane brief's spelling; the id is what the ledger joins on, so it is fixed here and in the two batteries |
| `const prog__entry = …` (module-private) plus `export const progEntry` | `export const prog__entry` plus `export const progEntry` | `Render.progDecl` always writes `export const`; the re-export is kept because §(c)'s host layer names it |
| `export const prog = (n: T) => …` | typed on the constant, untyped binder | `Expr.lambda` has no typed parameter (§8.2) |
| "one `docs/LOWERING-COVERAGE.md` row" | §7 above; doc not edited | brief says do not edit |
| `flowModules?` emits `1 + |roots|` + the re-export | done, and `regionModules?` / `structuredModules?` too; single-root modules byte-identical | `Flow.lowerRoots`, `Region.lowerRoots`, the two `*Best` variants |
| §(b) says nothing about region flows | the entry is emitted for them too, with the "root outside every region" refusal | spike S3's programs are `RegionFlow`s |

---

## 10. What the coordinator must apply

**`Effect4Test.lean`** — one import, after `MultiArgContract` (line 89), so the
battery joins the green closure. *Applied already:*

```lean
import Effect4Test.Target.TypeScript.FiberProfileContract
```

**`Effect4Test/Audit/AxiomGate.lean`** — exact roots in
`choiceImplementationDeclarations`, beside the lowering-form block that already
holds `Flow.lowerDispatch` (`AxiomGate.lean:187-197`). The first three are
applied; the second round adds five more.

```lean
  -- round 1 (applied)
  , ``Effect4.Target.EffectV4.Flow.lowerEntry
  , ``Effect4.Target.EffectV4.Flow.lowerRoots
  -- The byte-identity receipt of the multi-root entry. A *theorem*, admitted
  -- because its statement names `lowerDispatch`: it says the new emitter is the
  -- old one on a single-root flow, which is a claim about rendered output, not a
  -- semantic law. The three below it are the same claim at the other three
  -- lowering paths.
  , ``Effect4.Target.EffectV4.Flow.lowerDispatch_single_root_eq
  -- round 2: the region entry, the two `best` forms, and the import rule
  , ``Effect4.Target.EffectV4.Region.lowerEntry
  , ``Effect4.Target.EffectV4.Region.lowerRoots
  , ``Effect4.Target.EffectV4.Region.lowerDispatch_single_root_eq
  , ``Effect4.Target.EffectV4.Flow.lowerRootsBest
  , ``Effect4.Target.EffectV4.Flow.lowerBest_single_root_eq
  , ``Effect4.Target.EffectV4.Region.lowerRootsBest
  , ``Effect4.Target.EffectV4.Region.lowerBest_single_root_eq
  -- `moduleNamespaces` is `neededNamespaces` over the rows a module declares;
  -- `neededNamespaces` and `Spelling.namespacesOf` are already on this list.
  , ``Effect4.Target.EffectV4.moduleNamespaces
```

Eleven in total, and no others. Measured by `#print axioms` on every declaration
the two rounds added:

| Declaration | Axioms |
| --- | --- |
| `FiberOp.ofIndex_index` | *none* |
| `Lowering.rootEntryBase`, `Lowering.enterAt`, `Lowering.entryRootCase` | *none* |
| `fiberProfile`, `fibersRows`, `fiberRow`, `fiberOpRow`, `handleTy`, `forkRequestTy` | `propext` |
| `Lowering.entryCaseRead`, `Lowering.entryArgRead`, `Flow.blockCases` | `propext` |
| `Flow.entryAliasDecl`, `Flow.entryExportDecl`, `Flow.rootAliasDoc` | `propext` |
| `Flow.effectType`, `Flow.rootBinders`, `Flow.skeletonEntry`, `Flow.rootAlias`, `Flow.entryAlias` | `propext`, `Quot.sound` |
| `Region.effectType`, `Region.rootBinders`, `Region.skeletonEntry`, `Region.rootAlias` | `propext`, `Quot.sound` |
| **the eleven above** | `propext`, **`Classical.choice`**, `Quot.sound` |

`Skeleton.render` gained two cases and is already admitted by exact name
(`AxiomGate.lean:203`); `Spelling.namespacesOf`, `neededNamespaces`,
`flowModules?`, `regionModules?` and `structuredModules?` were already on the
list and stay there. `Effect4/Target/TypeScript/Skeleton.lean` keeps its property
that **no** declaration in it reaches `Classical.choice`: the two new formers and
the three new `Lowering` definitions are at no axiom at all, and the `String`
crossings live in `SkeletonRender.lean`, which is where the split puts them.

---

## 11. Refusals and open work

* **The refusal row of `fork-lowering.md` §(d)** ("the lowering emits a service
  call for a fork, never `Effect.fork`") is still owed a row in
  `test/counterexamples/REGISTER.md` at the landing. This lane makes it
  executable: battery §5d pins that none of the three lowered programs contains
  the string `Effect.fork`, and that the two-root one contains
  `yield* fibers.fork(`.
* **A declared root inside a region has no lowering.** `Region.skeletonEntry`
  refuses it (battery §8a). Whether the fiber profile ever wants one — a fork
  naming a root that is lexically inside a scope — is a question for the packet
  that writes the `Fibers` layer; the shape it would need is priced in §8.
* **No golden, no host receipt, no property batch** for `entry-root`. The
  multi-root form has never been run: it needs a `Fibers` layer
  (`fork-lowering.md` §(c)) and a tail harness, which is the fiber-machine
  packet's work, and `harness/` is outside this lane.
* **Two in-flight stub fixtures will gain an `effect` import** when their packet
  regenerates them (§6, last paragraph): `layers-fixture.stub.ts` gains `Fiber`,
  `scopes-fixture.stub.ts` gains `Exit`. Both currently name a namespace they do
  not import, so this is a repair, but the digests move.
* **A flow has one `resultTy` for every declared root** (spike S3 §8), so a child
  whose result type differs from its parent's cannot live in the same flow. The
  entry change does not relax this: `Flow.rootAlias` and `Region.rootAlias` type
  every root's alias at `program.result`. Relaxing it is a `RawFlow` change and
  belongs upstream.
* **A multi-root flow never gets the structured form.** `lowerRootsBest` falls
  back to the dispatch entry (§3). Structuring a multi-root graph would mean
  emitting one structured body per root or a labelled entry dispatch in front of
  it; neither is priced anywhere yet.
* **Two area batteries outside this lane are red**, and were before it:
  `Effect4TestFlow` (`RefsContract`) and `Effect4TestCounterexamples`
  (`Counterexamples/Semantics/Layers`). Both test modules another agent has open
  (`Effect4/Stateful/RefFamily.lean`, `Effect4/Layer/LayerFamily.lean`); neither
  failure reaches a target module.
