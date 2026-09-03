import { Effect, Ref, type Exit } from "effect"
import { Cell, CellRows, Decisions, Regions, RCell, RCellRows, incr, twice, chooser, swap, irreducible } from "./structured-fixture.ts"
import * as fixture from "./structured-fixture.ts"
import { runTraced, traceService, decisionsFromTape, outcomeWire, windowRows, type Event } from "./tracer.ts"

declare const process: { readonly env: Record<string, string | undefined> }

/** The patched rc.112 copy (harness/trace/patched) reports frame-level rows
 * through this sink; an unpatched copy never calls it and the report carries
 * an empty list. These rows are recorded, never compared (docs/TRACE-DAG.md). */
const patchedFrames: Array<Record<string, unknown>> = []
;(globalThis as any).__effect4Frame = (row: string, data: Record<string, unknown>) => { patchedFrames.push({ row, ...data }) }

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

/** The regions service: every region event is pushed as the run observes it,
 * with the exit `onExit` or the release saw, rendered as the outcome wire. */
const regions = {
  enter: (region: number) => Effect.sync(() => { sink.push({ kind: "enter", region }) }),
  leave: (region: number, exit: Exit.Exit<unknown, unknown>) =>
    Effect.sync(() => { sink.push({ kind: "leave", region, outcome: outcomeWire(exit as any) }) }),
  finalizer: (region: number, exit: Exit.Exit<unknown, unknown>) =>
    Effect.sync(() => { sink.push({ kind: "finalizer", region, outcome: outcomeWire(exit as any) }) })
}

/** `RCell`: resources are their numbers, `boom` and `releaseBoom` fail. */
const rcellProgram = (
  body: (n: number) => Effect.Effect<number, string, RCell | Regions | Decisions>,
  argument: number,
  initial: number
) =>
  Effect.gen(function* () {
    const ref = yield* Ref.make(initial)
    const service = traceService(RCellRows, {
      get: Ref.get(ref),
      put: (n: number) => Ref.set(ref, n),
      acquire: (n: number) => Effect.succeed(n),
      release: (_n: number) => Effect.void,
      boom: (_n: number) => Effect.fail("boom") as Effect.Effect<number, string>,
      releaseBoom: (_n: number) => Effect.fail("boom") as Effect.Effect<void, string>
    }, sink)
    sink.push({ kind: "phase", phase: "run" })
    return yield* body(argument).pipe(
      Effect.provideService(RCell, service),
      Effect.provideService(Regions, regions),
      Effect.provideService(Decisions, decisions)
    )
  })

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

const regionPrograms = fixture as unknown as Record<string, (n: number) => Effect.Effect<number, string, RCell | Regions | Decisions>>
const programs: Record<string, Effect.Effect<number, string, never>> = {
  incr: cellProgram(incr, 0, 41),
  twice: cellProgram(twice, 7, 41),
  chooser: cellProgram(chooser, 5, 41),
  swap: cellProgram(swap, 5, 41),
  irreducible: cellProgram(irreducible, 5, 41),
  regionNested: rcellProgram(regionPrograms.regionNested!, 5, 41),
  regionTwoFail: rcellProgram(regionPrograms.regionTwoFail!, 5, 41),
  regionBothSucceed: rcellProgram(regionPrograms.regionBothSucceed!, 5, 41)
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
  foreign: ["succ@./atoms.ts"]
}))
