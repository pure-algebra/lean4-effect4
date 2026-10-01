// Seat J2, step 1b: both engines' verdicts on shapes in program position that DI-72 (763187e1) rules
// on, on the orderings the deferred refusal exists for, and on the residual shapes outside DI-72.
// One line per case: `same` or `DIFF`, then each engine's verdicts (unit=code:detail or lifted).
//   bun docs/research/2026-10-01-landing/seat-J2/probes/bare-shapes.ts
import * as ck from "../../../../../ts/eff/ingest/ck.ts"
import * as oxc from "../../../../../ts/eff/ingest/oxc.ts"
const header = 'import { Effect, Layer, Context, Ref, Option } from "effect"\n'
const cases: Record<string, string> = {
  // DI-72's four shapes
  nat: "const p = 7", str: 'const p = "s"', bool: "const p = true", undef: "const p = undefined",
  binderBody: "const p = Effect.flatMap(Effect.succeed(1), (x) => x)",
  binderYield: "const p = Effect.gen(function* () { const x = yield* Effect.succeed(1); yield* x; return 1 })",
  yieldLit: "const p = Effect.gen(function* () { yield* 7; return 1 })",
  atomApp: "const p = succ(1)", atomAppBody: "const p = Effect.flatMap(Effect.succeed(1), (x) => succ(x))",
  // refusals the walk gives before any DI-72 shape
  nul: "const p = null", noncanon: "const p = 0x10", unknownCall: "const p = Effect.foo(1)",
  retryBare: "const p = Effect.retry(1)",
  bareThenUnknown: "const p = Effect.flatMap(Effect.succeed(1), (x) => x).pipe(Effect.retry(3))",
  unknownThenBare: "const p = Effect.retry(Effect.flatMap(Effect.succeed(1), (x) => x), 3)",
  layerBare: "const L = Layer.effectDiscard(Effect.flatMap(Effect.succeed(1), (x) => x)); const p = Effect.provide(Effect.succeed(1), L)",
  layerBareDirect: "const L = Layer.effectDiscard(7)",
  declBare: "const q = Effect.flatMap(Effect.succeed(1), (x) => x); const p = Effect.flatMap(q, (y) => Effect.succeed(y))",
  entryBare: "Effect.runPromise(Effect.flatMap(Effect.succeed(1), (x) => x))",
  defaultBare: "export default Effect.flatMap(Effect.succeed(1), (x) => x)",
  failLit: "const p = Effect.fail(7)",
  // residual, outside DI-72 (measured, not repaired)
  neg: "const p = -1", unknownMember: "const p = Effect.foo", never: "const p = Effect.never",
}
let diff = 0
for (const [name, body] of Object.entries(cases)) {
  const show = (vs: readonly { kind: string; unit: { name: string }; code?: string; detail?: string }[]) =>
    vs.map(v => `${v.unit.name}=` + (v.kind === "refusal" ? `${v.code}:${v.detail}` : "lifted"))
  const l = show(ck.recognizeSource(header + body, name + ".ts")), r = show(oxc.recognizeSource(header + body, name + ".ts"))
  const same = JSON.stringify(l) === JSON.stringify(r)
  if (!same) diff++
  console.log(`${same ? "same" : "DIFF"} ${name.padEnd(16)} ck ${JSON.stringify(l)} | oxc ${JSON.stringify(r)}`)
}
console.log(`${Object.keys(cases).length} cases, ${diff} differ`)
