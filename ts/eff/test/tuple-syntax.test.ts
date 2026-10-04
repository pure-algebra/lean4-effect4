import { describe, expect, test } from "bun:test"
import { Result } from "effect"
import { readTypeScript } from "../read.ts"
import { readTupleIndex } from "../tuple-index.ts"
import { readPrintedSource as ck } from "../ingest/ck.ts"
import { readPrintedSource as oxc } from "../ingest/oxc.ts"

const project = (key: string, marker = key, target = 'tuple(7, "x", true)') =>
  `Effect.succeed(tupleAt<${JSON.stringify(marker)}>(${JSON.stringify(key)})(${target}))`

describe("exact tuple source syntax", () => {
  test("both source walks retain the static index and ordinary tuple atom", () => {
    const source = project("2")
    const expected = { _tag: "succeed", value: { _tag: "tupleAt", index: 2,
      target: { _tag: "app", atom: "tuple", args: [
        { _tag: "lit", value: { _tag: "nat", value: 7 } },
        { _tag: "lit", value: { _tag: "str", value: "x" } },
        { _tag: "lit", value: { _tag: "bool", value: true } }
      ] } } } as const
    const direct = readTypeScript(source)
    expect(Result.isSuccess(direct) && direct.success).toEqual(expected)
    expect(ck(`export const program = ${source}`)).toEqual(expected)
    expect(oxc(`export const program = ${source}`)).toEqual(expected)
  })
  test("raw empty and singleton constructions remain available", () => {
    for (const source of ["Effect.succeed(tuple())", "Effect.succeed(tuple(7))", project("0", "0", "tuple(7)")]) {
      expect(Result.isSuccess(readTypeScript(source))).toBe(true)
      expect(ck(`export const program = ${source}`)).toEqual(oxc(`export const program = ${source}`))
    }
  })
  test("ordinary atom calls remain distinct from the marked projection", () => {
    const parsed = readTypeScript("Effect.succeed(tupleAt())")
    expect(Result.isSuccess(parsed) && parsed.success).toEqual({ _tag: "succeed", value: { _tag: "app", atom: "tupleAt", args: [] } })
  })
  test("safe index boundary is explicit", () => {
    expect(readTupleIndex("9007199254740991")).toBe(Number.MAX_SAFE_INTEGER)
    expect(readTupleIndex("9007199254740992")).toBeUndefined()
    expect(readTupleIndex("9007199254740993")).toBeUndefined()
    expect(readTupleIndex("123456789012345678901234567890")).toBeUndefined()
    expect(Result.isSuccess(readTypeScript(project("9007199254740991")))).toBe(true)
  })
  test("malformed markers and host-unrepresentable indices refuse in both walks", () => {
    const malformed = [
      project("0", "1"), ...["", "00", "01", "+1", "-0", "-1", "1e3", " 1", "１", "9007199254740992", "9007199254740993", "123456789012345678901234567890"].map(key => project(key)),
      'Effect.succeed(tupleAt<"0">(0)(tuple(7)))',
      'Effect.succeed(tupleAt<"0">("0")())',
      'Effect.succeed(tupleAt<"0">("0")(tuple(7), tuple(8)))',
      'Effect.succeed(tupleAt<"0", "1">("0")(tuple(7)))',
      'Effect.succeed(tupleAt<"0">("0")<never>(tuple(7)))'
    ]
    for (const source of malformed) {
      expect(Result.isFailure(readTypeScript(source))).toBe(true)
      expect(() => ck(`export const program = ${source}`)).toThrow()
      expect(() => oxc(`export const program = ${source}`)).toThrow()
    }
  })
})
