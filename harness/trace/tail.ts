import { Effect, Ref, Result } from "effect"
import { Cell, CellRows, ECell, ECellRows, FCell, FCellRows, incr, twice, recover, fallible } from "./fixture.ts"
import { runTraced, traceService, windowRows, type Event } from "./tracer.ts"

declare const process: { readonly env: Record<string, string | undefined> }

/** The patched rc.112 copy (harness/trace/patched) reports frame-level rows
 * through this sink; an unpatched copy never calls it and the report carries
 * an empty list. These rows are recorded, never compared (docs/TRACE-DAG.md). */
const patchedFrames: Array<Record<string, unknown>> = []
;(globalThis as any).__effect4Frame = (row: string, data: Record<string, unknown>) => { patchedFrames.push({ row, ...data }) }

/** Which program to run comes from the harness; the tape is empty for these
 * straight-line programs. Each entry builds its service before the `run`
 * sentinel so construction is outside the compared window. */
const name = process.env.EFFECT4_PROGRAM ?? "incr"
const maxOpsBeforeYield = Number(process.env.EFFECT4_MAX_OPS ?? "1000000")
const budget = Number(process.env.EFFECT4_BUDGET ?? "100000")
const sink: Event[] = []

const cellProgram = (body: (n: number) => Effect.Effect<number, never, Cell>, argument: number, initial: number) =>
  Effect.gen(function* () {
    const ref = yield* Ref.make(initial)
    const service = traceService(CellRows, { get: Ref.get(ref), put: (n: number) => Ref.set(ref, n) }, sink)
    sink.push({ kind: "phase", phase: "run" })
    return yield* body(argument).pipe(Effect.provideService(Cell, service))
  })

/** `ecellLive`: the read returns a left, the write still happens. */
const ecellProgram = (body: (n: number) => Effect.Effect<number, never, ECell>, argument: number, initial: number) =>
  Effect.gen(function* () {
    const ref = yield* Ref.make(initial)
    const service = traceService(ECellRows, {
      tryGet: Effect.succeed(Result.fail("boom") as Result.Result<number, string>),
      put: (n: number) => Ref.set(ref, n)
    }, sink)
    sink.push({ kind: "phase", phase: "run" })
    return yield* body(argument).pipe(Effect.provideService(ECell, service))
  })

/** `fcellLive`: the read aborts with a typed failure; the write before it happens. */
const fcellProgram = (body: (n: number) => Effect.Effect<number, string, FCell>, argument: number, initial: number) =>
  Effect.gen(function* () {
    const ref = yield* Ref.make(initial)
    const service = traceService(FCellRows, {
      get: Effect.fail("boom") as Effect.Effect<number, string>,
      put: (n: number) => Ref.set(ref, n)
    }, sink)
    sink.push({ kind: "phase", phase: "run" })
    return yield* body(argument).pipe(Effect.provideService(FCell, service))
  })

const programs: Record<string, Effect.Effect<number, string, never>> = {
  incr: cellProgram(incr, 0, 41),
  twice: cellProgram(twice, 7, 41),
  recover: ecellProgram(recover, 5, 41),
  fallible: fcellProgram(fallible, 5, 41)
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
  patchedFrames,
  foreign: ["succ@./atoms.ts", "orZero@./atoms.ts"]
}))
