import { describe, expect, test } from "bun:test"
import { Result, Schema } from "effect"
import { parseSync } from "oxc-parser"
import { Ty, type Term } from "../eff.gen.ts"
import { exprOf, readTypeScript, type Expr } from "../read.ts"
import { readTypeMetadata } from "../metadata.ts"
import { key, normalize, targetType, legacyType } from "../target-types.ts"
import { readPrintedSource as ck } from "../ingest/ck.ts"
import { readPrintedSource as oxc } from "../ingest/oxc.ts"
import fixtures from "./type-projection.gen.json"

const expression = (source: string): Expr => {
  const parsed = parseSync("metadata.ts", source, { sourceType: "module", lang: "ts" })
  expect(parsed.errors).toEqual([])
  const statement = parsed.program.body[0]
  if (statement?.type !== "ExpressionStatement") throw new Error("expression expected")
  const result = exprOf({ ...statement.expression })
  if (Result.isFailure(result)) throw new Error(JSON.stringify(result.failure))
  return result.success
}
const decodeType = Schema.decodeUnknownSync(Ty)
const term = (source: string): Term => {
  const result = readTypeScript(`Effect.succeed(${source})`)
  if (Result.isFailure(result)) throw new Error(JSON.stringify(result.failure))
  if (result.success._tag !== "succeed") throw new Error("succeed expected")
  return result.success.value
}
const refused = (source: string) => expect(Result.isFailure(readTypeScript(`Effect.succeed(${source})`))).toBe(true)
const person = fixtures.cases.find(item => item.raw._tag === "record" && "fields" in item.raw && item.raw.fields?.[0]?.[0] === "nickname")!
const special = fixtures.cases.find(item => item.raw._tag === "record" && "fields" in item.raw && item.raw.fields?.[0]?.[0] === "__proto__")!
const personType = decodeType(person.raw)
if (personType._tag !== "record") throw new Error("record fixture expected")
const constructor = `recordValue<${person.annotation}>(${person.metadata}, { id: 1 })`

describe("generated finite type projection controls", () => {
  for (const [index, fixture] of fixtures.cases.entries()) test(`${index}: ${fixture.raw._tag}`, () => {
    const raw = decodeType(fixture.raw)
    expect(key(raw)).toEqual(fixture.key)
    expect(normalize(raw)).toEqual(decodeType(fixture.normal))
    expect(targetType(raw, legacyType) ?? null).toEqual(fixture.annotation)
    expect(readTypeMetadata(expression(fixture.metadata))).toEqual(raw)
  })
  test("metadata rejects malformed frames and inexact carrier values", () => {
    for (const source of ["[10, [0], []]", "[10, [255], []]", "[10, [], [1]]", "[10, [2, 256], []]", "[10, [20], [[2, [32, 0, 0, 0, 0, 0, 0]]]]", '[10, [6], [[3, "\\uD800"]]]']) {
      expect(readTypeMetadata(expression(source))).toBeUndefined()
    }
  })
})

describe("named record term source reading", () => {
  test("retains raw declaration order and supplied presence", () => {
    expect(term(constructor)).toEqual({ _tag: "record", fields: personType.fields,
      presentNames: ["id"], values: [{ _tag: "lit", value: { _tag: "nat", value: 1 } }] })
  })
  test("required access, optional access and overwrite remain distinct", () => {
    const record = term(constructor)
    expect(term(`${constructor}.id`)).toEqual({ _tag: "field", mode: "required", target: record, name: "id" })
    expect(term(`recordOptional<"nickname">("nickname")(${constructor})`)).toEqual({ _tag: "field", mode: "optional", target: record, name: "nickname" })
    expect(term(`recordSet<"nickname">()({ ...${constructor}, nickname: "Ada" })`)).toEqual({ _tag: "recordSet", target: record, name: "nickname", value: { _tag: "lit", value: { _tag: "str", value: "Ada" } } })
  })
  test("computed prototype keys and bracket reads retain field names", () => {
    const made = `recordValue<${special.annotation}>(${special.metadata}, { ["__proto__"]: undefined })`
    const record = term(made)
    expect(record._tag === "record" && record.presentNames).toEqual(["__proto__"])
    expect(term(`${made}["a-b"]`)).toEqual({ _tag: "field", mode: "required", target: record, name: "a-b" })
    expect(term(`recordSet<"__proto__">()({ ...${constructor}, ["__proto__"]: 7 })`)._tag).toBe("recordSet")
  })
  test("raw fallback is readable only when the canonical writer requires it", () => {
    expect(term(`recordRaw<unknown>(${person.metadata}, ["id"], [])`)._tag).toBe("record")
    refused(`recordRaw<unknown>(${person.metadata}, ["id"], [1])`)
  })
  test("refuses changed metadata, annotation, keys, order and extra properties", () => {
    for (const source of [
      `recordValue<unknown>(${person.metadata}, { id: 1 })`,
      `recordValue<${person.annotation}>(${person.metadata}, { "id": 1 })`,
      `recordValue<${person.annotation}>(${person.metadata}, { ...${constructor} })`,
      `recordValue<${special.annotation}>(${special.metadata}, { "__proto__": undefined })`,
      `${constructor}["id"]`,
      `recordOptional<"id">("nickname")(${constructor})`,
      `recordSet<"id">()({ id: 1, ...${constructor} })`,
      `recordSet<"id">()({ ...${constructor}, id: 1, nickname: "Ada" })`,
      `recordSet<"nickname">()({ ...${constructor}, id: 1 })`
    ]) refused(source)
  })
  test("both printed-source walks reconstruct the same record terms", () => {
    for (const value of [constructor, `${constructor}.id`,
      `recordOptional<"nickname">("nickname")(${constructor})`,
      `recordSet<"nickname">()({ ...${constructor}, nickname: "Ada" })`,
      `recordRaw<unknown>(${person.metadata}, ["id"], [])`]) {
      const source = `export const program = Effect.succeed(${value})`
      const expected = { _tag: "succeed" as const, value: term(value) }
      expect(ck(source)).toEqual(expected)
      expect(oxc(source)).toEqual(expected)
    }
  })
  test("every admitted legacy primitive survives an absent optional field", () => {
    for (const name of ["any", "object", "symbol", "bigint", "number"]) {
      const metadata = `[10,[20],[[4,[[5,[3,"x"],[5,[1,true],[10,[6],[[3,"${name}"]]]]]]]]]`
      const value = `recordValue<{ readonly x?: ${name} }>(${metadata}, {})`
      const source = `export const program = Effect.succeed(${value})`
      const expected = { _tag: "succeed" as const, value: term(value) }
      expect(ck(source)).toEqual(expected)
      expect(oxc(source)).toEqual(expected)
    }
  })
  test("ordinary atom calls keep their existing spelling", () => {
    expect(term("recordValue(1)")).toEqual({ _tag: "app", atom: "recordValue", args: [{ _tag: "lit", value: { _tag: "nat", value: 1 } }] })
  })
})
