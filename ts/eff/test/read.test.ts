// Pinned readings: the shapes the spike found ambiguous at the grammar and the row table
// decides, the binder discipline, and the refusals by name. The corpus check (`check.ts`) is
// the receipt over 400 generated and the wire-corpus programs; these are the cases worth
// reading.

import { describe, expect, test } from "bun:test"
import { Result } from "effect"
import { isEff } from "../eff.gen.ts"
import { toJson } from "../json.gen.ts"
import { heads, rows } from "../profile.gen.ts"
import { readTypeScript, type Refusal } from "../read.ts"

const json = (source: string): string => {
  const r = readTypeScript(source)
  if (Result.isFailure(r)) throw new Error(`refused: ${JSON.stringify(r.failure)}`)
  return toJson(r.success)
}

const refusal = (source: string): Refusal => {
  const r = readTypeScript(source)
  if (Result.isSuccess(r)) throw new Error(`accepted: ${toJson(r.success)}`)
  return r.failure
}

describe("the profile", () => {
  test("has the reader's 37 heads and one entry per NativeOp value", () => {
    expect(heads.length).toBe(37)
    expect(rows.length).toBe(53)
    expect(new Set(rows.map((e) => e.row.spelling)).size).toBe(20)
    expect(new Set(rows.map((e) => JSON.stringify(e.op))).size).toBe(53)
  })
})

describe("exits and literals", () => {
  test("Effect.succeed(42) is the wire golden p42", () => {
    expect(json("Effect.succeed(42)")).toBe('["succeed",["lit",["nat",42]]]')
  })
  test("a bare literal is a yielded error", () => {
    expect(json("2")).toBe('["yieldError",["lit",["nat",2]]]')
    expect(json('"hi"')).toBe('["yieldError",["lit",["str","hi"]]]')
    expect(json("undefined")).toBe('["yieldError",["lit",["unit"]]]')
  })
  test("Effect.fiberId is the getId action", () => {
    expect(json("Effect.fiberId")).toBe('["withFiber",["getId"]]')
  })
  test("a negative number never arrives as a literal", () => {
    expect(refusal("Effect.succeed(-1)")._tag).toBe("node")
  })
})

describe("rows: the shape the grammar could not decide", () => {
  test('Scope.make("parallel") is the unit-request row with a trailing name', () => {
    expect(json('Scope.make("parallel")')).toBe('["perform",["scopeMake",["parallel"]],["lit",["unit"]]]')
    expect(json("Scope.make()")).toBe('["perform",["scopeMake",["sequential"]],["lit",["unit"]]]')
  })
  test('Ref.get("hi") is a row with a string request', () => {
    expect(json('Ref.get("hi")')).toBe('["perform",["refGet"],["lit",["str","hi"]]]')
  })
  test('Scope.make("hi") is refused, not read into the wrong row', () => {
    expect(refusal('Scope.make("hi")')).toEqual({ _tag: "arity", head: "Scope.make" })
  })
  test("a read-modify-write row carries its pure function in the operation", () => {
    expect(json("Effect.flatMap(Ref.make(0), (a0) => Ref.update(a0, incr))")).toBe(
      '["bind",["perform",["refMake"],["lit",["nat",0]]],["perform",["refUpdate",["incr"]],["var",0]]]',
    )
  })
  test("an async row reads back as callback", () => {
    expect(json("Effect.flatMap(Deferred.make(), (a0) => Deferred.await(a0))")).toBe(
      '["bind",["perform",["deferredMake"],["lit",["unit"]]],["callback",["deferredAwait"],["var",0]]]',
    )
  })
  test("an unknown call whose arguments are all terms is an atom application, yielded", () => {
    expect(json("add(1, 2)")).toBe('["yieldError",["app","add",["cons",["lit",["nat",1]],["cons",["lit",["nat",2]],["nil"]]]]]')
    expect(json("Effect.map(1)")).toBe('["yieldError",["app","Effect.map",["cons",["lit",["nat",1]],["nil"]]]]')
  })
})

describe("binders are depths", () => {
  test("the continuation of flatMap binds a<n>", () => {
    expect(json("Effect.flatMap(Effect.succeed(1), (a0) => Effect.succeed(a0))")).toBe(
      '["bind",["succeed",["lit",["nat",1]]],["succeed",["var",0]]]',
    )
  })
  test("a wrong binder name is refused by the name expected", () => {
    expect(refusal("Effect.flatMap(Effect.succeed(1), (b) => Effect.succeed(b))")).toEqual({ _tag: "binder", expected: "a0" })
  })
  test("a variable out of scope is an unknown identifier", () => {
    expect(refusal("Effect.succeed(a0)")).toEqual({ _tag: "unknownIdent", name: "a0" })
  })
  test("acquireRelease binds the resource and the exit", () => {
    expect(json("Effect.acquireRelease(Effect.succeed(1), (a0, a1) => Effect.succeed(a1))")).toBe(
      '["acquireRelease",["succeed",["lit",["nat",1]]],["succeed",["var",1]]]',
    )
  })
})

describe("heads out of position", () => {
  test("Effect.whileLoop outside its suspend", () => {
    expect(refusal("Effect.whileLoop({})")).toEqual({ _tag: "unknownHead", name: "Effect.whileLoop" })
  })
  test("Cause.fail outside a cause", () => {
    expect(refusal("Cause.fail(1)")).toEqual({ _tag: "unknownHead", name: "Cause.fail" })
  })
  test("an unknown Effect export is tried as an atom application, so its lambda refuses as a term", () => {
    expect(refusal("Effect.map(Effect.succeed(1), (a0) => a0)")).toEqual({ _tag: "shape", what: "term" })
  })
})

describe("program files", () => {
  test("the truth files' export form reads as the bare expression", () => {
    const bare = json("Effect.succeed(42)")
    const exported = json(['import { Effect } from "effect"', "export const main: Effect.Effect<number, never> = Effect.succeed(42)"].join("\n"))
    expect(exported).toBe(bare)
  })
  test("two statements are not one program", () => {
    expect(refusal("Effect.succeed(1)\nEffect.succeed(2)")._tag).toBe("program")
  })
  test("what is read is a node of the schema", () => {
    const r = readTypeScript("Effect.gen(function* () {\n  const a0 = yield* Effect.succeed(1)\n  return a0\n})")
    expect(Result.isSuccess(r) && isEff(r.success)).toBe(true)
  })
})
