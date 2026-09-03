import { Effect, Ref } from "effect"
import { Cell, CellRows, Decisions, incr, twice, chooser, swap } from "./flow-fixture.ts"
import { runTraced, traceService, decisionsFromTape, windowRows, type Event } from "./tracer.ts"

declare const process: { readonly env: Record<string, string | undefined> }

/** The dispatch-form programs, run against the same traced Cell service as the
 * straight-line tail and a Decisions service answering from the golden's tape
 * (`EFFECT4_TAPE`, `site:1` for true and `site:0` for false, comma separated). */
const name = process.env.EFFECT4_PROGRAM ?? "incr"
const maxOpsBeforeYield = Number(process.env.EFFECT4_MAX_OPS ?? "1000000")
const budget = Number(process.env.EFFECT4_BUDGET ?? "100000")
const tape: Array<readonly [number, boolean]> = (process.env.EFFECT4_TAPE ?? "")
  .split(",")
  .filter((entry) => entry.length > 0)
  .map((entry) => {
    const [site, branch] = entry.split(":")
    return [Number(site), branch === "1"] as const
  })
const sink: Event[] = []
const decisions = decisionsFromTape(tape, sink)

const cellProgram = (
  body: (n: number) => Effect.Effect<number, never, Cell | Decisions>,
  argument: number,
  initial: number
) =>
  Effect.gen(function* () {
    const ref = yield* Ref.make(initial)
    const service = traceService(CellRows, { get: Ref.get(ref), put: (n: number) => Ref.set(ref, n) }, sink)
    sink.push({ kind: "phase", phase: "run" })
    return yield* body(argument).pipe(
      Effect.provideService(Cell, service),
      Effect.provideService(Decisions, decisions)
    )
  })

const programs: Record<string, Effect.Effect<number, never, never>> = {
  incr: cellProgram(incr, 0, 41),
  twice: cellProgram(twice, 7, 41),
  chooser: cellProgram(chooser, 5, 41),
  swap: cellProgram(swap, 5, 41)
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
