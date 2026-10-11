import { describe, expect, test } from "bun:test"
import { Data, Effect, Exit, Option } from "effect"
import { KeyValueStore } from "effect/unstable/persistence"
import { canonicalJson, pairOf, payloadOf, toPair, UnsupportedHostFailure } from "./prelude.ts"
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


// Decisions row 120, part E2: the classes a printed module declares, as rc.112 builds them.
class NotFound extends Data.TaggedError("NotFound")<{ readonly id: number }> {}
class Wrapped extends Data.TaggedError("Wrapped")<{ readonly cause: string }> {}
class Coded extends Data.TaggedError("Coded")<{ readonly message: string; readonly code: number }> {}
class MessageOnly extends Data.TaggedError("MessageOnly")<{ readonly message: string }> {}

describe("payload classes: one image, never a pair (decisions row 120, part E2)", () => {
  test("a class with data beyond its message is a payload, wired whole with sorted keys", () => {
    expect(pairOf(new NotFound({ id: 9 }))).toBeNull()
    expect(JSON.stringify(payloadOf(new NotFound({ id: 9 })))).toBe('{"_tag":"NotFound","id":9}')
    expect(JSON.stringify(payloadOf(new Coded({ message: "m", code: 1 })))).toBe('{"_tag":"Coded","code":1,"message":"m"}')
  })

  test("a cause the instance holds unenumerable is still its data", () => {
    const disk = new Wrapped({ cause: "disk" })
    expect(Object.keys(disk)).toEqual(["_tag"])
    expect(JSON.stringify(payloadOf(disk))).toBe('{"_tag":"Wrapped","cause":"disk"}')
    const empty = new Wrapped({ cause: "" })
    expect(Object.keys(empty)).toEqual(["cause", "_tag"])
    expect(JSON.stringify(payloadOf(empty))).toBe('{"_tag":"Wrapped","cause":""}')
  })

  test("a message-only class stays the pair (ruling (c)); a pair and a plain value are no payload", () => {
    expect(pairOf(new MessageOnly({ message: "m" }))).toEqual(["MessageOnly", "m"])
    expect(payloadOf(new MessageOnly({ message: "m" }))).toBeNull()
    expect(payloadOf(["SqlError", "boom"])).toBeNull()
    expect(payloadOf({ _tag: "NotFound", id: 9 })).toBeNull()
  })

  test("a host failure with data beyond its message is a defect at the adapter, not a pair", async () => {
    const error = new KeyValueStore.KeyValueStoreError({ message: "m", method: "get", key: "k" })
    expect(pairOf(error)).toBeNull()
    expect(() => toPair(error)).toThrow(UnsupportedHostFailure)
    const exit = await Effect.runPromiseExit(Effect.mapError(Effect.fail(error), toPair))
    expect(Exit.isFailure(exit) && exit.cause.reasons.map((reason) => reason._tag)).toEqual(["Die"])
  })

  test("keys sort by code point, which is UTF-8 byte order, not UTF-16 order", () => {
    const sorted = canonicalJson({ "😀": 3, "\uffff": 4, "é": 1, z: 2, _tag: "x", nested: { b: 1, a: [{ d: 1, c: 2 }] } })
    expect(Object.keys(sorted as object)).toEqual(["_tag", "nested", "z", "é", "\uffff", "😀"])
    expect(JSON.stringify((sorted as { nested: unknown }).nested)).toBe('{"a":[{"c":2,"d":1}],"b":1}')
  })
})
