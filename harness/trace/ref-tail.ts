import { Effect, Ref, Result } from "effect"
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
 *     order and only the golden does. counterexample: E4-SEM-CE-013
 *   - `getAndSet` is `Ref.getAndSet`, answering the previous value.
 *
 * Nothing here works around any of that: the goldens are stated against rc.112
 * as it is.
 */

// The brand rc.112 stamps on every ref (`Ref.ts` TypeId). It is a string key,
// not an exported value, so it is written out here.
const RefTypeId = "~effect/Ref"
registerHandle((value) => RefTypeId in value)

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
 * order — the contrasting half of E4-SEM-CE-013. */
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

const programs: Record<string, Effect.Effect<number, never, never>> = {
  makeGet: refsProgram(refMakeGet),
  setGet: refsProgram(refSetGet),
  updateTwice: refsProgram(refUpdateTwice),
  modifyOld: refsProgram(refModifyOld),
  getAndSetOld: refsProgram(refGetAndSetOld),
  twoRefs: refsProgram(refTwoRefs),
  takeUnderflow: erefsProgram(refTakeUnderflow)
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
