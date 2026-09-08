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
  test("has the reader's 50 heads and one entry per NativeOp value", () => {
    expect(heads.length).toBe(50)
    expect(rows.length).toBe(55)
    expect(new Set(rows.map((e) => e.row.spelling)).size).toBe(22)
    expect(new Set(rows.map((e) => JSON.stringify(e.op))).size).toBe(55)
  })
  test("only the five product-request exports use tuple calls", () => {
    expect(rows.filter((e) => e.row.shape === "tupleCall").map((e) => e.row.name)).toEqual([
      "refSet", "refGetAndSet", "refSetAndGet", "deferredSucceed", "deferredFail",
    ])
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
    expect(json("Effect.flatMap(Deferred.make<number, number>(), (a0) => Deferred.await(a0))")).toBe(
      '["bind",["perform",["deferredMake"],["lit",["unit"]]],["callback",["deferredAwait"],["var",0]]]',
    )
  })
  // E4-CHECK-CE-013: a row that declares type arguments is read at exactly that spelling
  // (`Deferred.make<number, number>()`); a bare call, the wrong arguments, a row that declares
  // none, and a reserved head carrying any are refused, as the Lean reader refuses them.
  test("Deferred.make<number, number>() is the row with its declared type arguments", () => {
    expect(json("Deferred.make<number, number>()")).toBe('["perform",["deferredMake"],["lit",["unit"]]]')
  })
  test("Deferred.make() without its type arguments is refused", () => {
    expect(refusal("Deferred.make()")).toEqual({ _tag: "arity", head: "Deferred.make" })
  })
  test("Deferred.make<string, number>() with the wrong type arguments is refused", () => {
    expect(refusal("Deferred.make<string, number>()")).toEqual({ _tag: "arity", head: "Deferred.make" })
  })
  test("Ref.make<number>(0) carries type arguments its row does not declare", () => {
    expect(refusal("Ref.make<number>(0)")).toEqual({ _tag: "arity", head: "Ref.make" })
  })
  test("a reserved head with type arguments is not a row call", () => {
    expect(refusal("Effect.succeed<number>(1)")).toEqual({ _tag: "unknownHead", name: "Effect.succeed" })
  })
  test("an unknown call whose arguments are all terms is an atom application, yielded", () => {
    expect(json("add(1, 2)")).toBe('["yieldError",["app","add",["cons",["lit",["nat",1]],["cons",["lit",["nat",2]],["nil"]]]]]')
    expect(json("Effect.map(1)")).toBe('["yieldError",["app","Effect.map",["cons",["lit",["nat",1]],["nil"]]]]')
  })
})

describe("tuple calls", () => {
  const tupleRows = [
    ["Ref.set", "refSet"],
    ["Ref.getAndSet", "refGetAndSet"],
    ["Ref.setAndGet", "refSetAndGet"],
    ["Deferred.succeed", "deferredSucceed"],
    ["Deferred.fail", "deferredFail"],
  ] as const
  const pair = ["app", "pair", ["cons", ["lit", ["nat", 1]], ["cons", ["lit", ["nat", 7]], ["nil"]]]]

  for (const [spelling, op] of tupleRows) {
    test(`${spelling} reads its two arguments into its operation and pair request`, () => {
      expect(JSON.parse(json(`${spelling}(1, 7)`))).toEqual(["perform", [op], pair])
    })
    test(`${spelling} refuses its former one-request call`, () => {
      expect(refusal(`${spelling}(pair(1, 7))`)).toEqual({ _tag: "arity", head: spelling })
    })
    test(`${spelling} refuses the former Reflect.apply wrapper`, () => {
      expect(refusal(`Reflect.apply(${spelling}, undefined, pair(1, 7))`)).toEqual({ _tag: "unknownIdent", name: spelling })
    })
  }

  test("a saved tuple request reads its two component reads as the same bound variable", () => {
    expect(JSON.parse(json("Effect.flatMap(Effect.succeed(pair(1, 7)), (a0) => Ref.set(fst(a0), snd(a0)))"))).toEqual([
      "bind", ["succeed", pair], ["perform", ["refSet"], ["var", 0]],
    ])
  })
  test("components of two different identifiers are an ordinary pair", () => {
    expect(JSON.parse(json("Effect.flatMap(Effect.succeed(pair(1, 7)), (a0) => Effect.flatMap(Effect.succeed(pair(2, 8)), (a1) => Ref.set(fst(a0), snd(a1))))"))).toEqual([
      "bind", ["succeed", pair],
      ["bind", ["succeed", ["app", "pair", ["cons", ["lit", ["nat", 2]], ["cons", ["lit", ["nat", 8]], ["nil"]]]]],
        ["perform", ["refSet"], ["app", "pair", ["cons", ["app", "fst", ["cons", ["var", 0], ["nil"]]], ["cons", ["app", "snd", ["cons", ["var", 1], ["nil"]]], ["nil"]]]]]],
    ])
  })
  test("tuple requests retain ordinary scope checks", () => {
    expect(refusal("Ref.set(fst(a0), snd(a0))")).toEqual({ _tag: "unknownIdent", name: "a0" })
    expect(refusal("Ref.set(a0, 7)")).toEqual({ _tag: "unknownIdent", name: "a0" })
  })
  test("a call row does not accept the tuple reading", () => {
    expect(refusal("Ref.get(1, 2)")).toEqual({ _tag: "arity", head: "Ref.get" })
  })
  test("three plain arguments are an atom application, not a row", () => {
    expect(JSON.parse(json("Ref.set(1, 7, 8)"))).toEqual([
      "yieldError", ["app", "Ref.set", ["cons", ["lit", ["nat", 1]], ["cons", ["lit", ["nat", 7]], ["cons", ["lit", ["nat", 8]], ["nil"]]]]],
    ])
  })
  test("Reflect.apply is no head: a bare mention is an unknown identifier", () => {
    expect(refusal("Reflect.apply")).toEqual({ _tag: "unknownIdent", name: "Reflect.apply" })
  })
  test("ordinary dotted atom calls retain their existing reading", () => {
    expect(JSON.parse(json("foo.concat(1)"))).toEqual([
      "yieldError", ["app", "foo.concat", ["cons", ["lit", ["nat", 1]], ["nil"]]],
    ])
  })
})

describe("the synchronous runIn adapter", () => {
  test("its callback adds no binder and returns the runIn action", () => {
    expect(JSON.parse(json("Effect.flatMap(Effect.succeed(1), (a0) => Effect.flatMap(Effect.succeed(2), (a1) => Effect.withFiber(() => { Fiber.runIn(a0, a1); return Effect.void })))"))).toEqual([
      "bind", ["succeed", ["lit", ["nat", 1]]],
      ["bind", ["succeed", ["lit", ["nat", 2]]], ["withFiber", ["runIn", ["var", 0], ["var", 1]]]],
    ])
  })
  test("the former raw synchronous call stays reserved and refused", () => {
    expect(refusal("Fiber.runIn(1, 2)")).toEqual({ _tag: "arity", head: "Fiber.runIn" })
  })
  test("the wrapper preserves scope checking", () => {
    expect(refusal("Effect.withFiber(() => { Fiber.runIn(a0, 2); return Effect.void })")).toEqual({ _tag: "unknownIdent", name: "a0" })
    expect(refusal("Effect.withFiber(() => { Fiber.runIn(1, a0); return Effect.void })")).toEqual({ _tag: "unknownIdent", name: "a0" })
  })
  for (const callback of [
    "(a0) => { Fiber.runIn(1, 2); return Effect.void }",
    "() => { Fiber.runIn(1, 2); Fiber.runIn(1, 2); return Effect.void }",
    "() => { Fiber.runIn(1, 2); return Effect.succeed(undefined) }",
    "() => { Fiber.interrupt(1, 2); return Effect.void }",
    "() => { Fiber.runIn(1); return Effect.void }",
    "() => { return Effect.void; Fiber.runIn(1, 2) }",
    "() => { return Effect.void }",
    "() => Fiber.runIn(1, 2)",
    "() => { Fiber.runIn(1, 2); return Effect.void }, 0",
  ]) {
    test(`refuses a different callback shape: ${callback}`, () => {
      expect(refusal(`Effect.withFiber(${callback})`)).toEqual({ _tag: "shape", what: "runIn" })
    })
  }
  test("adding expression statements does not admit them in a generator", () => {
    expect(refusal("Effect.gen(function* () { Fiber.runIn(1, 2); return 0 })")).toEqual({ _tag: "unsupportedStmt" })
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

describe("the join", () => {
  const key = 'Context.Service<number>("k4_4")'
  const leaf = `Layer.succeed(${key}, 7)`
  test("reads a service with both numeric fields", () => {
    expect(json(`Effect.service(${key})`)).toBe('["service",{"name":{"value":4},"service":{"value":4}}]')
  })
  test("reads provided values and both local options", () => {
    expect(json(`Effect.provideService(Effect.service(${key}), ${key}, 7)`)).toBe(
      '["provideService",{"name":{"value":4},"service":{"value":4}},["lit",["nat",7]],["service",{"name":{"value":4},"service":{"value":4}}]]',
    )
    for (const options of ["", ", { local: true }"]) {
      const result = readTypeScript(`Effect.provide(Effect.service(${key}), ${leaf}${options})`)
      expect(Result.isSuccess(result)).toBe(true)
      if (Result.isSuccess(result)) {
        expect(result.success._tag).toBe("provideLayer")
        if (result.success._tag === "provideLayer") expect(result.success.isLocal).toBe(options !== "")
      }
    }
  })
  test.each([
    [leaf, "succeed"],
    [`Layer.effect(${key}, Effect.succeed(7))`, "effect"],
    ["Layer.effectDiscard(Effect.succeed(7))", "effectDiscard"],
    [`${leaf}.pipe(Layer.provide(${leaf}))`, "provide"],
    [`${leaf}.pipe(Layer.provideMerge(${leaf}))`, "provideMerge"],
    [`Layer.merge(${leaf}, ${leaf})`, "merge"],
    [`Layer.fresh(${leaf})`, "fresh"],
    [`Layer.orDie(${leaf})`, "orDie"],
  ] as const)("reads layer %s", (layer, tag) => {
    const result = readTypeScript(`Effect.provide(Effect.succeed(7), ${layer})`)
    expect(Result.isSuccess(result)).toBe(true)
    if (Result.isSuccess(result) && result.success._tag === "provideLayer") {
      expect(result.success.layer._tag).toBe(tag)
    }
  })
  test("layer bodies have their own empty binder environment", () => {
    const result = readTypeScript(`Effect.flatMap(Effect.succeed(1), (a0) => Effect.provide(
      Effect.succeed(a0), Layer.effect(${key}, Effect.flatMap(Effect.succeed(2), (a0) => Effect.succeed(a0)))))`)
    expect(Result.isSuccess(result)).toBe(true)
    expect(refusal(`Effect.flatMap(Effect.succeed(1), (a0) => Effect.provide(
      Effect.succeed(a0), Layer.effect(${key}, Effect.succeed(a0))))`)).toEqual(
      { _tag: "unknownIdent", name: "a0" },
    )
  })
  test.each([
    'Context.Service<boolean>("k4_4")',
    'Context.Service<number>("k04_4")',
    'Context.Service<number>("k4_04")',
    'Context.Service<number>("k4_4_")',
    'Context.Service("k4_4")',
    'Context.Service<number, number>("k4_4")',
  ])("rejects a noncanonical key %s", (invalid) => {
    expect(refusal(`Effect.service(${invalid})`)).toEqual({ _tag: "shape", what: "service key" })
  })
  test("checks reserved and untyped keys against the native signature", () => {
    expect(json('Effect.service(Context.Service<Scope.Scope>("k0_0"))')).toBe('["service",{"name":{"value":0},"service":{"value":0}}]')
    expect(json('Effect.service(Context.Service<Ref.Ref<number>>("k4_7"))')).toBe(
      '["service",{"name":{"value":4},"service":{"value":7}}]',
    )
    expect(json('Effect.service(Context.Service("k1_4"))')).toBe('["service",{"name":{"value":1},"service":{"value":4}}]')
    expect(refusal('Effect.service(Context.Service<number>("k1_4"))')).toEqual({ _tag: "shape", what: "service key" })
  })
  test("keeps service keys exact at the JavaScript integer boundary", () => {
    expect(json('Effect.service(Context.Service<number>("k9007199254740991_4"))')).toBe(
      '["service",{"name":{"value":9007199254740991},"service":{"value":4}}]',
    )
    for (const key of ['Context.Service<number>("k9007199254740992_4")',
      'Context.Service("k4_9007199254740993")']) {
      expect(refusal(`Effect.service(${key})`)).toEqual({ _tag: "shape", what: "service key" })
    }
  })
  test("rejects local false and nonliteral Layer.succeed values", () => {
    expect(refusal(`Effect.provide(Effect.succeed(7), ${leaf}, { local: false })`)._tag).toBe("arity")
    expect(refusal(`Effect.provide(Effect.succeed(7), Layer.succeed(${key}, add(1, 2)))`)).toEqual({ _tag: "shape", what: "literal" })
  })
})
