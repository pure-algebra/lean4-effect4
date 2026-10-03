// Structural parser controls. These checks do not establish typing or execution agreement.
import { describe, expect, test } from "bun:test"
import { Result } from "effect"
import { parseSync } from "oxc-parser"
import { exprOf, readTypeScript, type Expr } from "../read.ts"

const parse = (source: string) => {
  const parsed = parseSync("record.ts", source, { sourceType: "module", lang: "ts" })
  expect(parsed.errors).toEqual([])
  const statement = parsed.program.body[0]
  if (statement?.type !== "ExpressionStatement") throw new Error("Expected one expression")
  return exprOf(statement.expression as unknown as Parameters<typeof exprOf>[0])
}
const fragment = (source: string): Expr => {
  const result = parse(source)
  if (Result.isFailure(result)) throw new Error(JSON.stringify(result.failure))
  return result.success
}
const ident = (name: string): Expr => ({ _tag: "ident", name })
const int = (value: number): Expr => ({ _tag: "int", value })
const str = (value: string): Expr => ({ _tag: "str", value })

describe("record target syntax", () => {
  test("keeps optionality, readonly fields, arbitrary names and tuple types", () => {
    expect(fragment('recordValue<{ readonly nickname?: string; readonly "a-b": readonly [number, string] }>([], {})'))
      .toEqual({ _tag: "call", fn: { _tag: "generic", fn: ident("recordValue"), typeArgs: [
        '{ readonly nickname?: string; readonly "a-b": readonly [number, string] }',
      ] }, args: [{ _tag: "arr", items: [] }, { _tag: "object", fields: [] }] })
  })
  test("keeps literal, union and nested generic type arguments", () => {
    expect(fragment('recordOptional<"nickname" | "a-b", Option.Option<undefined>>("nickname")'))
      .toEqual({ _tag: "call", fn: { _tag: "generic", fn: ident("recordOptional"),
        typeArgs: ['"nickname" | "a-b"', "Option.Option<undefined>"] }, args: [str("nickname")] })
  })
  test("keeps escaped literal type text in the renderer's spelling", () => {
    const quoted = JSON.stringify('line\n"\\\t')
    expect(fragment(`field<${quoted}>()`)).toEqual({ _tag: "call",
      fn: { _tag: "generic", fn: ident("field"), typeArgs: [quoted] }, args: [] })
  })
  test("keeps plain, quoted and computed object keys distinct", () => {
    expect(fragment("({ x: 1 })")).toEqual({ _tag: "object", fields: [["x", int(1)]] })
    expect(fragment('({ "x": 1 })')).toEqual({ _tag: "objectWith", keys: "quoted",
      entries: [{ _tag: "property", name: "x", value: int(1) }] })
    expect(fragment('({ ["__proto__"]: 1, ["x"]: 2 })')).toEqual({ _tag: "objectWith", keys: "computed",
      entries: [{ _tag: "property", name: "__proto__", value: int(1) }, { _tag: "property", name: "x", value: int(2) }] })
  })
  test("keeps spread position and overwrite order", () => {
    expect(fragment('({ ...a0, "a-b": 1, ...a1, "a-b": 2 })')).toEqual({ _tag: "objectWith", keys: "quoted",
      entries: [{ _tag: "spread", value: ident("a0") }, { _tag: "property", name: "a-b", value: int(1) },
        { _tag: "spread", value: ident("a1") }, { _tag: "property", name: "a-b", value: int(2) }] })
  })
  test("keeps element access separate from member access", () => {
    expect(fragment('a0["a-b"]')).toEqual({ _tag: "index", base: ident("a0"), key: str("a-b") })
    expect(fragment("a0.nickname")).toEqual({ _tag: "member", base: ident("a0"), name: "nickname" })
  })
  test("keeps typed construction and null as structural syntax", () => {
    expect(fragment("new Box<string>(null)")).toEqual({ _tag: "new",
      callee: { _tag: "generic", fn: ident("Box"), typeArgs: ["string"] }, args: [{ _tag: "jsNull" }] })
  })
  for (const source of [
    '({ x: 1, "y": 2 })', '({ ["x"]: 1, y: 2 })', "({ [a0]: 1 })",
    "({ get x() { return 1 } })", "({ x() { return 1 } })", "({ x })",
    "a0?.x", 'a0?.["x"]', "new Box(...a0)",
    "field<{ method(): string }>()", "field<{ [x: string]: number }>()",
    "field<{ [a0]: string }>()", "field<string[]>()", "field<readonly string[]>()",
  ]) test(`refuses unsupported syntax: ${source}`, () => expect(Result.isFailure(parse(source))).toBe(true))

  for (const value of ['({ "x": 1 })', '({ ["__proto__"]: 1 })', 'a0["x"]', "new Box<string>(null)", "null"]) {
    test(`structural parsing alone does not admit a term: ${value}`, () => {
      expect(Result.isFailure(readTypeScript(`Effect.succeed(${value})`))).toBe(true)
    })
  }
})
