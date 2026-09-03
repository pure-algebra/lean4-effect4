import { Effect, Ref } from "effect"
import { Cell, CellRows, incr, twice } from "./fixture.ts"
import { runTraced, traceService, windowRows, type Event } from "./tracer.ts"

declare const process: { readonly env: Record<string, string | undefined> }

/** Which program to run and its argument come from the harness; the tape is
 * empty for these straight-line programs. */
const name = process.env.EFFECT4_PROGRAM ?? "incr"
const maxOpsBeforeYield = Number(process.env.EFFECT4_MAX_OPS ?? "1000000")
const budget = Number(process.env.EFFECT4_BUDGET ?? "100000")
const initial = 41
const argument = name === "twice" ? 7 : 0
const chosen = name === "twice" ? twice : incr

const sink: Event[] = []

/** `Cell.Service (StateT number Id)` as a `Ref`, every method traced. Built
 * before the `run` sentinel so construction is outside the compared window. */
const program = Effect.gen(function* () {
  const ref = yield* Ref.make(initial)
  const service = traceService(CellRows, { get: Ref.get(ref), put: (n: number) => Ref.set(ref, n) }, sink)
  sink.push({ kind: "phase", phase: "run" })
  const result = yield* chosen(argument).pipe(Effect.provideService(Cell, service))
  return result
})

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
