import { Effect } from "effect"
import { runTraced, windowRows, type Event } from "./tracer.ts"

declare const process: { readonly env: Record<string, string | undefined> }

/**
 * Three programs that exist only to be shot at, by
 * `scripts/test-trace-goldens-gate.sh`. None of them has a committed golden and
 * none is part of `check-trace-host.sh`: each names one wire fact that no
 * program of the corpus reaches, so the only way to keep the fact under a gate
 * is to plant it.
 *
 * - `control` succeeds with a string carrying a raw U+0001. `JSON.stringify`
 *   escapes it `\u0001`, and the Lean renderer now does too
 *   (`Effect4/Target/TypeScript/Trace.lean` `escape`). A golden holding the raw
 *   character must diverge. E4-TARGET-CE-014
 * - `overflow` succeeds with 2^53, which a JavaScript number cannot carry
 *   exactly. `wire` refuses it, so the run is INVALID, never pass or fail.
 *   E4-TARGET-CE-015
 * - `die` dies. A defect used to render `{"failure":[]}`, byte-identical to a
 *   unit failure; it renders `{"defect":d}` now, so a golden still claiming the
 *   old form must diverge. E4-TARGET-CE-017
 */
const name = process.env.EFFECT4_PROGRAM ?? "control"
const maxOpsBeforeYield = Number(process.env.EFFECT4_MAX_OPS ?? "1000000")
const budget = Number(process.env.EFFECT4_BUDGET ?? "100000")
const sink: Event[] = []

const after = <A>(body: Effect.Effect<A, never, never>): Effect.Effect<A, never, never> =>
  Effect.suspend(() => {
    sink.push({ kind: "phase", phase: "run" })
    return body
  })

const programs: Record<string, Effect.Effect<unknown, never, never>> = {
  control: after(Effect.succeed(`a${String.fromCharCode(1)}b`)),
  overflow: after(Effect.succeed(2 ** 53)),
  die: after(Effect.die("boom"))
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
  foreign: []
}))
