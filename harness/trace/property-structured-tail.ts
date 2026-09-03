import { readFileSync } from "node:fs"
import { Effect, Ref } from "effect"
import * as fixture from "./property-structured-fixture.ts"
import { runTraced, traceService, decisionsFromTape, windowRows, type Event } from "./tracer.ts"

declare const process: { readonly env: Record<string, string | undefined> }

/** The patched rc.112 copy (harness/trace/patched) reports frame-level rows
 * through this sink; an unpatched copy never calls it and the report carries
 * an empty list. These rows are recorded, never compared (docs/TRACE-DAG.md). */
const patchedFrames: Array<Record<string, unknown>> = []
;(globalThis as any).__effect4Frame = (row: string, data: Record<string, unknown>) => { patchedFrames.push({ row, ...data }) }

/** The batch tail: every (program, tape) of the manifest in `EFFECT4_BATCH`
 * runs once in this process against a fresh traced Cell service and a
 * Decisions service answering from its tape; one JSON report per case. */
const maxOpsBeforeYield = Number(process.env.EFFECT4_MAX_OPS ?? "1000000")
const budget = Number(process.env.EFFECT4_BUDGET ?? "100000")
const manifestPath = process.env.EFFECT4_BATCH ?? "batch.json"
const manifest: Array<{ program: string; tape: string }> = JSON.parse(readFileSync(manifestPath, "utf8"))

const parseTape = (text: string): Array<readonly [number, boolean]> =>
  text.split(",").filter((entry) => entry.length > 0).map((entry) => {
    const [site, branch] = entry.split(":")
    return [Number(site), branch === "1"] as const
  })

const programs = fixture as unknown as Record<string, (n: number) => Effect.Effect<number, never, any>>
const reports: unknown[] = []
for (const entry of manifest) {
  const body = programs[entry.program]
  if (typeof body !== "function") throw new Error(`unknown program ${entry.program}`)
  const sink: Event[] = []
  const decisions = decisionsFromTape(parseTape(entry.tape), sink)
  const program = Effect.gen(function* () {
    const ref = yield* Ref.make(41)
    const service = traceService(fixture.CellRows, { get: Ref.get(ref), put: (n: number) => Ref.set(ref, n) }, sink)
    sink.push({ kind: "phase", phase: "run" })
    return yield* body(5).pipe(
      Effect.provideService(fixture.Cell, service),
      Effect.provideService(fixture.Decisions, decisions)
    )
  }) as Effect.Effect<number, never, never>
  const report = await runTraced(program, sink, { budget, maxOpsBeforeYield })
  sink.push({ kind: "phase", phase: "teardown" })
  reports.push({
    program: entry.program, tape: entry.tape,
    rows: windowRows(report.events), frames: report.frames.length, exitTag: report.exitTag,
    primitives: report.primitives, yields: report.yields, tracerDefect: report.tracerDefect,
    maxOpsBeforeYield, expectYields: process.env.EFFECT4_EXPECT_YIELDS === "1",
    patchedFrames: patchedFrames.splice(0)
  })
}
console.log(JSON.stringify(reports))
