import { Effect, Option, Ref, Result } from "effect"
import type { MutableRef } from "effect"
import {
  ERefs,
  ERefsRows,
  Refs,
  RefsRows,
  refGetAndSetOld,
  refMakeGet,
  refModifyOld,
  refSetGet,
  refTakeUnderflow,
  refTwoRefs,
  refUpdateTwice
} from "./ref-fixture.ts"
import {
  RefsFull,
  RefsFullRows,
  refModifyPair,
  refPartialNoRewrite,
  refReadBeforeWrite,
  refSetAnswersCell,
  refWriteThenAnswer,
  type PartialUpdate,
  type RefsFullService
} from "./refs-fixture.stub.ts"
import { registerHandle, runTraced, traceService, windowRows, type Event } from "./tracer.ts"

declare const process: { readonly env: Record<string, string | undefined> }

/**
 * The host face of the `Refs` family: rc.112's own `Ref`, wrapped only so the
 * shared alphabet can see it.
 *
 * This tail keeps no store. Every operation is the rc.112 call of the same
 * name, and the handle that crosses the wire is the ref object itself:
 * `registerHandle` brands it and `wire` encodes it as its index in first-seen
 * order, which is the creation order the Lean face numbers cells in.
 *
 *   - `make` is `Ref.make`, whose answer is the `Ref` the tracer indexes.
 *   - `get` is `Ref.get`.
 *   - `set` is `Ref.set`. Declared `Effect<void>`, its runtime answer is the
 *     mutable cell (census `ref.set-void-returns-cell`,
 *     `ref.cell-set-returns-self`). counterexample: E4-SEM-CE-009
 *   - `update` is `Ref.update`. Also declared `Effect<void>`, but its sync
 *     thunk is a block that returns nothing, so its runtime answer is
 *     `undefined` (census `ref.update`). Two `void` operations of one rc.112
 *     module hand back different things; that is why `wireAnswer` reads the
 *     declared spelling and never the value.
 *   - `modify` is `Ref.modify`, whose `f` returns `readonly [answer, newState]`.
 *     Here both components are numbers, so the compiler does not pin their
 *     order and only the golden does. counterexample: E4-SEM-CE-015
 *   - `getAndSet` is `Ref.getAndSet`, answering the previous value.
 *
 * Nothing here works around any of that: the goldens are stated against rc.112
 * as it is.
 */

// The brand rc.112 stamps on every ref (`Ref.ts` TypeId). It is a string key,
// not an exported value, so it is written out here.
const RefTypeId = "~effect/Ref"
// The brand rc.112 stamps on the mutable cell inside a ref (`MutableRef.ts:18`
// TypeId). `Ref.set` succeeds with that cell, so it needs a handle carrier of
// its own; `wire` then encodes it as its allocation index, in first-seen order.
const MutableRefTypeId = "~effect/MutableRef"
registerHandle((value) => RefTypeId in value || MutableRefTypeId in value)

const name = process.env.EFFECT4_PROGRAM ?? "makeGet"
const maxOpsBeforeYield = Number(process.env.EFFECT4_MAX_OPS ?? "1000000")
const budget = Number(process.env.EFFECT4_BUDGET ?? "100000")
const sink: Event[] = []

const live = {
  make: (initial: number) => Ref.make(initial),
  get: (ref: Ref.Ref<number>) => Ref.get(ref),
  set: (ref: Ref.Ref<number>, value: number) => Ref.set(ref, value),
  update: (ref: Ref.Ref<number>, amount: number) => Ref.update(ref, (current) => current + amount),
  modify: (ref: Ref.Ref<number>, amount: number) =>
    Ref.modify(ref, (current): readonly [number, number] => [current, current + amount]),
  getAndSet: (ref: Ref.Ref<number>, value: number) => Ref.getAndSet(ref, value)
}

/** `erefsLive`: a take that would underflow refuses and writes nothing, so the
 * read after it sees exactly what the successful take left. The refusal is an
 * answer of the operation, not an abort of the program. Both components of this
 * `modify` tuple have different types, so here the compiler *does* pin the
 * order — the contrasting half of E4-SEM-CE-015. */
const eliveTryTake = (
  ref: Ref.Ref<number>,
  amount: number
): Effect.Effect<Result.Result<number, string>> =>
  Ref.modify(ref, (current): readonly [Result.Result<number, string>, number] =>
    current >= amount
      ? [Result.succeed(current - amount), current - amount]
      : [Result.fail("underflow"), current])

const elive = {
  make: (initial: number) => Ref.make(initial),
  tryTake: eliveTryTake,
  get: (ref: Ref.Ref<number>) => Ref.get(ref)
}

/**
 * The full rc.112 `Ref` surface: the thirteen Effect-valued operations of
 * `Ref.ts`, each of them that module's own call, with the line the census row
 * cites (`docs/research/2026-09-03-deep-state-models.md` §1.1, §2.1).
 *
 * Every one of them is `Effect.sync` of a single thunk in rc.112 — none is
 * `suspend`, `withFiber`, or a callback — so the whole surface is
 * single-stepped and nothing here parks.
 *
 * The two partial-function operations take a *name* rather than a function
 * (DB-02: canonical content carries no Lean function), and the tail is the
 * interp that gives that name a meaning. `floor` names the partial update
 * `c > floor ? some (c - 1) : none`, so a `floor` above the cell exercises the
 * `None` arm; `amount` names `modifySome`'s pair.
 */
const partialUpdate = (floor: number): PartialUpdate => (current) =>
  current > floor ? Option.some(current - 1) : Option.none()

const fullLive: RefsFullService = {
  // `Ref.make` — `Ref.ts:173`: `Effect.sync(() => makeUnsafe(value))`, and
  // `makeUnsafe` (`:142-146`) allocates a fresh `MutableRef` every evaluation.
  make: (initial) => Ref.make(initial),
  // `Ref.get` — `Ref.ts:200`: a synchronous read of `self.ref.current`.
  get: (ref) => Ref.get(ref),
  // `Ref.set` — `Ref.ts:307`. Declared `Effect<void>`, but the thunk is an
  // expression arrow over `MutableRef.set` (`MutableRef.ts:1067-1070`), which
  // writes `current` and returns the ref itself, so the runtime success value
  // is the cell. The cast reads rc.112's actual answer; nothing is computed
  // here. counterexample: E4-SEM-CE-009
  set: (ref, value) =>
    Ref.set(ref, value) as unknown as Effect.Effect<MutableRef.MutableRef<number>>,
  // `Ref.getAndSet` — `Ref.ts:399-404`: read `current`, assign, return the
  // value read, all inside one sync thunk.
  getAndSet: (ref, value) => Ref.getAndSet(ref, value),
  // `Ref.setAndGet` — `Ref.ts:747`: succeeds with the *assignment expression*,
  // never with a second read of the cell.
  setAndGet: (ref, value) => Ref.setAndGet(ref, value),
  // `Ref.update` — `Ref.ts:1273-1276`: a block-bodied thunk that returns
  // nothing, so this `void`-declared operation answers `undefined` where
  // `set`, also `void`-declared, answers the cell.
  update: (ref, amount) => Ref.update(ref, (current) => current + amount),
  // `Ref.getAndUpdate` — `Ref.ts:496-501`: answers the pre-value.
  getAndUpdate: (ref, amount) => Ref.getAndUpdate(ref, (current) => current + amount),
  // `Ref.updateAndGet` — `Ref.ts:1368`: an expression arrow, so it answers the
  // assignment's value, the same shape as `setAndGet`.
  updateAndGet: (ref, amount) => Ref.updateAndGet(ref, (current) => current + amount),
  // `Ref.updateSome` — `Ref.ts:1502-1508`: block body, assigns only on `Some`.
  updateSome: (ref, floor) => Ref.updateSome(ref, partialUpdate(floor)),
  // `Ref.getAndUpdateSome` — `Ref.ts:635-643`: assigns only on `Some` and
  // answers the value read *before* the write.
  getAndUpdateSome: (ref, floor) => Ref.getAndUpdateSome(ref, partialUpdate(floor)),
  // `Ref.updateSomeAndGet` — `Ref.ts:1639-1646`: assigns only on `Some` and
  // then answers a *fresh read* of `current`. This and `getAndUpdateSome` are
  // the pair the census row `ref.update-some-and-get-reread` contrasts.
  updateSomeAndGet: (ref, floor) => Ref.updateSomeAndGet(ref, partialUpdate(floor)),
  // `Ref.modify` — `Ref.ts:896-901`: the general read-modify-write; the second
  // component is written back and the first is the success value.
  // counterexample: E4-SEM-CE-015
  modify: (ref, amount) =>
    Ref.modify(ref, (current): readonly [number, number] => [current, current + amount]),
  // `Ref.modifySome` — `Ref.ts:1159-1163`: literally `modify`, whose `None`
  // branch writes back `value`, the value `modify` already read at `:898`, and
  // not a re-read of the cell.
  modifySome: (ref, amount) =>
    Ref.modifySome(ref, (current): readonly [number, Option.Option<number>] =>
      current >= amount
        ? [current, Option.some(current - amount)]
        : [current, Option.none()])
}

const refsProgram = (body: (n: number) => Effect.Effect<number, never, Refs>) =>
  Effect.gen(function* () {
    const service = traceService(RefsRows, live, sink)
    sink.push({ kind: "phase", phase: "run" })
    return yield* body(7).pipe(Effect.provideService(Refs, service))
  })

const erefsProgram = (body: (n: number) => Effect.Effect<number, never, ERefs>) =>
  Effect.gen(function* () {
    const service = traceService(ERefsRows, elive, sink)
    sink.push({ kind: "phase", phase: "run" })
    return yield* body(7).pipe(Effect.provideService(ERefs, service))
  })

const fullProgram = (body: (n: number) => Effect.Effect<number, never, RefsFull>) =>
  Effect.gen(function* () {
    const service = traceService(RefsFullRows, fullLive, sink)
    sink.push({ kind: "phase", phase: "run" })
    return yield* body(7).pipe(Effect.provideService(RefsFull, service))
  })

const programs: Record<string, Effect.Effect<number, never, never>> = {
  makeGet: refsProgram(refMakeGet),
  setGet: refsProgram(refSetGet),
  updateTwice: refsProgram(refUpdateTwice),
  modifyOld: refsProgram(refModifyOld),
  getAndSetOld: refsProgram(refGetAndSetOld),
  twoRefs: refsProgram(refTwoRefs),
  takeUnderflow: erefsProgram(refTakeUnderflow),
  setAnswersCell: fullProgram(refSetAnswersCell),
  readBeforeWrite: fullProgram(refReadBeforeWrite),
  writeThenAnswer: fullProgram(refWriteThenAnswer),
  partialNoRewrite: fullProgram(refPartialNoRewrite),
  modifyPair: fullProgram(refModifyPair)
}
const program = programs[name]
if (program === undefined) throw new Error(`unknown program ${name}`)

const report = await runTraced(program, sink, { budget, maxOpsBeforeYield })
sink.push({ kind: "phase", phase: "teardown" })
console.log(JSON.stringify({
  rows: windowRows(report.events),
  frames: report.frames,
  exitTag: report.exitTag,
  primitives: report.primitives,
  yields: report.yields,
  scheduled: report.scheduled,
  tracerDefect: report.tracerDefect,
  maxOpsBeforeYield,
  expectYields: process.env.EFFECT4_EXPECT_YIELDS === "1",
  foreign: ["succ@./atoms.ts"]
}))
