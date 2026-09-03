/**
 * The host tail of packet M2: interruption as decisions.
 *
 * The lowered program asks `interrupts.point(site)` at every interruptible
 * point — before every `perform` and at every region `leave`. This tail is the
 * interruptor. It answers the point from the interrupt tape exactly as the Lean
 * runner does (`Effect4.Flow.interruptRead`: the head entry is consumed only
 * when it names this site, and exhaustion answers "not delivered"), pushes the
 * same `decide` row, folds the answer into a pending flag, and — when the run
 * is not masked — calls `fiber.interruptUnsafe()`, the same rc.112 idiom
 * `tracer.ts` uses on the budget path.
 *
 * Deferral is the tail's own bookkeeping, not rc.112's `uninterruptibleMask`:
 * the mask is a model fact of the flow (`RegionProgram.masked`), the lowering
 * emits no `Effect.uninterruptible`, and what the golden checks is that the
 * *rows* land where the Lean runner puts them. Which rc.112 primitive would
 * carry the mask is an open lowering question, recorded in docs/TRACE-DAG.md.
 *
 * `EFFECT4_TAPE` carries the interrupt tape (`site:1` for delivered), taken
 * from the golden's `tape` header by the driver.
 */
import { Effect, Ref, type Exit } from "effect"
import { RCell, RCellRows, Decisions, Regions, Interrupts } from "./flow-fixture.ts"
import * as fixture from "./flow-fixture.ts"
import { runTraced, traceService, decisionsFromTape, outcomeWire, windowRows, type Event } from "./tracer.ts"

declare const process: { readonly env: Record<string, string | undefined> }

const patchedFrames: Array<Record<string, unknown>> = []
;(globalThis as any).__effect4Frame = (row: string, data: Record<string, unknown>) => { patchedFrames.push({ row, ...data }) }

const name = process.env.EFFECT4_PROGRAM ?? "interruptUnmasked"
const maxOpsBeforeYield = Number(process.env.EFFECT4_MAX_OPS ?? "1000000")
const budget = Number(process.env.EFFECT4_BUDGET ?? "100000")

/** The interrupt tape: `<site>:1` entries, in the order the run meets them. */
const tape: Array<readonly [number, boolean]> = (process.env.EFFECT4_TAPE ?? "")
  .split(",")
  .filter((entry) => entry.length > 0)
  .map((entry) => {
    const [site, branch] = entry.split(":")
    return [Number(site), branch === "1"] as const
  })

/** The uninterruptible regions of each program, mirroring the `masked` field
 * of `interruptEntries` in `harness/trace/Generate.lean`. */
const maskedRegions: Record<string, ReadonlyArray<number>> = {
  interruptUnmasked: [],
  interruptMasked: [1],
  interruptFinalizer: []
}

const sink: Event[] = []
const decisions = decisionsFromTape([], sink)

/** The regions currently open, innermost last. `enter` pushes, `leave` pops;
 * an interrupt point at a region's own `leave` still sees that region open,
 * which is what `Effect4.Flow.isMasked` says of the runner's frame stack. */
const openRegions: number[] = []
const masked = () => openRegions.some((region) => (maskedRegions[name] ?? []).includes(region))

const regions = {
  enter: (region: number) => Effect.sync(() => { openRegions.push(region); sink.push({ kind: "enter", region }) }),
  leave: (region: number, exit: Exit.Exit<unknown, unknown>) =>
    Effect.sync(() => {
      const at = openRegions.lastIndexOf(region)
      if (at >= 0) openRegions.splice(at, 1)
      sink.push({ kind: "leave", region, outcome: outcomeWire(exit as any) })
    }),
  finalizer: (region: number, exit: Exit.Exit<unknown, unknown>) =>
    Effect.sync(() => { sink.push({ kind: "finalizer", region, outcome: outcomeWire(exit as any) }) })
}

/** The interrupt tape, consumed by occurrence with a site check. */
let cursor = 0
let pending = false
const readTape = (site: number): boolean => {
  const entry = tape[cursor]
  if (entry === undefined) return false
  if (entry[0] !== site) return false
  cursor += 1
  return entry[1]
}

const interrupts = {
  point: (site: number) =>
    Effect.withFiber((fiber: any) => {
      const answered = readTape(site)
      sink.push({ kind: "decide", site, branch: answered })
      pending = pending || answered
      if (!masked() && pending) {
        pending = false
        fiber.interruptUnsafe()
      }
      return Effect.void
    })
}

const interruptProgram = (
  body: (n: number) => Effect.Effect<number, string, RCell | Regions | Decisions | Interrupts>,
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
      Effect.provideService(Decisions, decisions),
      Effect.provideService(Interrupts, interrupts)
    )
  })

const lowered = fixture as unknown as
  Record<string, (n: number) => Effect.Effect<number, string, RCell | Regions | Decisions | Interrupts>>
const body = lowered[name]
if (body === undefined) throw new Error(`unknown program ${name}`)

const report = await runTraced(interruptProgram(body, 5, 41), sink, { budget, maxOpsBeforeYield })
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
