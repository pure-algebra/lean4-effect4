import { describe, expect, test } from "bun:test"
import { Option } from "effect"
import { recordOptional, recordSet, recordValue } from "./records.ts"

describe("record target helpers", () => {
  test("absence, present undefined, and nested none remain distinct", () => {
    type Fields = { readonly nickname?: string | undefined; readonly nested?: Option.Option<string> }
    const absent = recordValue<Fields>([], {})
    const present = recordValue<Fields>([], { nickname: undefined, nested: Option.none() })
    expect(recordOptional("nickname")(absent)).toEqual(Option.none())
    expect(recordOptional("nickname")(present)).toEqual(Option.some(undefined))
    expect(recordOptional("nested")(present)).toEqual(Option.some(Option.none()))
  })

  test("presence ignores the prototype and handles shadowed property methods", () => {
    const inherited: { x?: number } = Object.create({ x: 4 })
    expect(recordOptional("x")(inherited)).toEqual(Option.none())
    const value = { ["__proto__"]: 1, hasOwnProperty: false, ["a-b"]: "yes" }
    expect(recordOptional("__proto__")(value)).toEqual(Option.some(1))
    expect(recordOptional("hasOwnProperty")(value)).toEqual(Option.some(false))
    expect(recordOptional("a-b")(value)).toEqual(Option.some("yes"))
    expect(Object.getPrototypeOf(value)).toBe(Object.prototype)
  })

  test("update evaluates each operand once in source order and leaves its input intact", () => {
    const calls: string[] = []
    const original = { id: 1, nickname: "old" }
    const target = () => { calls.push("target"); return original }
    const replacement = () => { calls.push("replacement"); return 7 }
    const result = recordSet<"nickname">()({ ...target(), nickname: replacement() })
    expect(calls).toEqual(["target", "replacement"])
    expect(result).toEqual({ id: 1, nickname: 7 })
    expect(original).toEqual({ id: 1, nickname: "old" })
  })

  test("computed prototype updates create an own value without changing the prototype", () => {
    const result = recordSet<"__proto__">()({ ...{ x: 1 }, ["__proto__"]: { x: 2 } })
    expect(Object.getPrototypeOf(result)).toBe(Object.prototype)
    expect(Object.hasOwn(result, "__proto__")).toBe(true)
    expect(result["__proto__"]).toEqual({ x: 2 })
  })
})
