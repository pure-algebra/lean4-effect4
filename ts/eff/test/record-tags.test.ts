import { describe, expect, test } from "bun:test"
import { Result } from "effect"
import { readTypeScript } from "../read.ts"
import { readPrintedSource as ck } from "../ingest/ck.ts"
import { readPrintedSource as oxc } from "../ingest/oxc.ts"

// These controls exercise the printed-source profile; checked program typing is separate.
const selected = 'caseTagR("raw", "Found", a0 => Effect.succeed(a0), a0 => Effect.succeed(a0))'
const expected = {
  _tag: "select", scrutinee: { _tag: "lit", value: { _tag: "str", value: "raw" } },
  decision: { _tag: "recordTag", tag: "Found" },
  arm0: { _tag: "succeed", value: { _tag: "var", index: 0 } },
  arm1: { _tag: "succeed", value: { _tag: "var", index: 0 } }
} as const

describe("record-tag printed-source selection", () => {
  test("both printed-source walks retain the decision and both whole-value binders", () => {
    const direct = readTypeScript(selected)
    expect(Result.isSuccess(direct) && direct.success).toEqual(expected)
    const source = `export const program = ${selected}`
    expect(ck(source)).toEqual(expected)
    expect(oxc(source)).toEqual(expected)
  })
  test("legacy pair selection keeps its distinct stored decision", () => {
    const result = readTypeScript(selected.replace("caseTagR", "caseTag"))
    expect(Result.isSuccess(result) && result.success).toEqual({ ...expected,
      decision: { _tag: "tag", tag: "Found" } })
  })
  test("malformed record selections refuse", () => {
    for (const expression of [
      selected.replace('"Found"', "7"),
      selected.replace("a0 =>", "() =>"),
      selected.replace("caseTagR(", "caseTagR<string>("),
      selected.slice(0, -1) + ", 0)"
    ]) {
      expect(Result.isFailure(readTypeScript(expression))).toBe(true)
      expect(() => ck(`export const program = ${expression}`)).toThrow()
      expect(() => oxc(`export const program = ${expression}`)).toThrow()
    }
  })
})
