import { expect, test } from "bun:test"
import { recognizeSource as ck } from "../ck.ts"
import { recognizeSource as oxc } from "../oxc.ts"
import { compareVerdicts } from "../gate.ts"

test("the agreement comparison includes the entire lifted record", () => {
  const source = 'import { Effect } from "effect"; const p = Effect.succeed(1);'
  const a = ck(source, "p.ts"), b = oxc(source, "p.ts")
  expect(compareVerdicts(a, b)).toEqual({ status: "agree", count: 1 })
  const v = b[0]!
  expect(compareVerdicts(a, [{ ...v, unit: { ...v.unit, span: { ...v.unit.span, start: v.unit.span.start + 1 } } }])).toEqual({ status: "disagree", indices: [0] })
})

test("a missing engine result is not agreement", () => {
  expect(compareVerdicts([], undefined)).toEqual({ status: "not-run" })
})

test("source-edit equality excludes only source locations", async () => {
  const { canonJson, sourceEditKey } = await import("../contract.ts")
  const source = 'import { Effect } from "effect"; const p = Effect.succeed(1);'
  for (const recognize of [ck, oxc]) {
    const a = recognize(source, "p.ts")[0]!, b = recognize('// comment\n' + source, "p.ts")[0]!
    expect(canonJson(sourceEditKey(a))).toBe(canonJson(sourceEditKey(b)))
    expect(canonJson(sourceEditKey(a))).not.toBe(canonJson(sourceEditKey({ ...b, unit: { ...b.unit, name: "different" } })))
  }
})
