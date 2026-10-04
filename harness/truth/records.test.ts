import { describe, expect, test } from "bun:test"
import { Effect, Option } from "effect"
import { caseTagR, recordRequired, recordOptional, recordSet, recordValue } from "./records.ts"

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
    const result = recordSet<"nickname">("nickname")(target())(replacement())
    expect(calls).toEqual(["target", "replacement"])
    expect(result).toEqual({ id: 1, nickname: 7 })
    expect(original).toEqual({ id: 1, nickname: "old" })
  })

  test("computed prototype updates create an own value without changing the prototype", () => {
    const result = recordSet<"__proto__">("__proto__")({ x: 1 })({ x: 2 })
    expect(Object.getPrototypeOf(result)).toBe(Object.prototype)
    expect(Object.hasOwn(result, "__proto__")).toBe(true)
    expect(result["__proto__"]).toEqual({ x: 2 })
  })
})


describe("whole-record tag selection", () => {
  test("binds the original object and constructs only the chosen callback when run", async () => {
    const value = { _tag: "Found" as const, id: 7, hasOwnProperty: false }
    const calls: string[] = []
    const scrutinee = () => { calls.push("scrutinee"); return value }
    const program = caseTagR(scrutinee(), "Found", record => {
      calls.push("hit")
      expect(record).toBe(value)
      return Effect.succeed(record.id)
    }, () => { calls.push("miss"); return Effect.succeed(0) })
    expect(calls).toEqual(["scrutinee"])
    expect(await Effect.runPromise(program)).toBe(7)
    expect(calls).toEqual(["scrutinee", "hit"])
  })

  test("the miss branch retains the whole object and inherited tags do not match", async () => {
    const value = { _tag: "Missing" as const, query: "Ada" }
    expect(await Effect.runPromise(caseTagR(value, "Found", () => Effect.succeed(null),
      record => Effect.succeed(record)))).toBe(value)
    const inherited: { readonly _tag?: string } = Object.create({ _tag: "Found" })
    expect(await Effect.runPromise(caseTagR(inherited, "Found", () => Effect.succeed("hit"),
      record => { expect(record).toBe(inherited); return Effect.succeed("miss") }))).toBe("miss")
  })

  test("literal tags include ordinary prototype names", async () => {
    const value = { _tag: "__proto__" as const, ["__proto__"]: 9 }
    expect(await Effect.runPromise(caseTagR(value, "__proto__",
      record => Effect.succeed(record["__proto__"]), () => Effect.succeed(0)))).toBe(9)
  })
})


test("record overwrite copies before the replacement and each impossible branch stays dormant", async () => {
  const calls: string[] = []
  const original = { get old() { calls.push("copy"); return 1 } }
  const target = () => { calls.push("target"); return original }
  const replacement = () => { calls.push("replacement"); return 2 }
  const result = recordSet("__proto__")(target())(replacement())
  expect(calls).toEqual(["target", "copy", "replacement"])
  expect(Object.hasOwn(result, "__proto__")).toBe(true)
  expect(Object.getPrototypeOf(result)).toBe(Object.prototype)
  const input = { _tag: "Found" as const, id: 7 }
  const programs: readonly Effect.Effect<number>[] = [
    caseTagR(input, "Absent", hit => Effect.succeed(recordRequired("id")(hit)), miss => Effect.succeed(miss.id)),
    caseTagR(input, "Absent", hit => Effect.succeed(recordOptional("id")(hit)), miss => Effect.succeed(miss.id)),
    caseTagR(input, "Absent", hit => Effect.succeed(recordSet("id")(hit)(8)), miss => Effect.succeed(miss.id)),
    caseTagR(input, "Absent", hit => Effect.succeed(recordRequired("extra")(recordSet("extra")(recordRequired("child")(hit))(1))), miss => Effect.succeed(miss.id))
  ]
  for (const program of programs) expect(await Effect.runPromise(program)).toBe(7)
})
