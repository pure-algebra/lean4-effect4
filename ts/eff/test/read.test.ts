// Pinned readings: the shapes the spike found ambiguous at the grammar and the row table
// decides, the binder discipline, and the refusals by name. The corpus check (`check.ts`) is
// the receipt over 400 generated and the wire-corpus programs; these are the cases worth
// reading.

import { describe, expect, test } from "bun:test"
import { Result } from "effect"
import { isEff, type Eff, type LayerTerm, type Row, type Term, type Ty } from "../eff.gen.ts"
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
  test("has the reader's 53 heads and one entry per NativeOp value", () => {
    expect(heads.length).toBe(53)
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
  test("checks the external service handle spellings at codes 8 and 9", () => {
    expect(json('Effect.service(Context.Service<SqlClient.SqlClient>("k4_8"))')).toBe(
      '["service",{"name":{"value":4},"service":{"value":8}}]',
    )
    expect(json('Effect.service(Context.Service<KeyValueStore.KeyValueStore>("k5_9"))')).toBe(
      '["service",{"name":{"value":5},"service":{"value":9}}]',
    )
    expect(refusal('Effect.service(Context.Service<KeyValueStore.KeyValueStore>("k4_8"))')).toEqual(
      { _tag: "shape", what: "service key" },
    )
  })
  test("rejects local false and nonliteral Layer.succeed values", () => {
    expect(refusal(`Effect.provide(Effect.succeed(7), ${leaf}, { local: false })`)._tag).toBe("arity")
    expect(refusal(`Effect.provide(Effect.succeed(7), Layer.succeed(${key}, add(1, 2)))`)).toEqual({ _tag: "shape", what: "literal" })
  })
})

// The host rows slice (2026-09-08): the n-ary merge, and a layer named by its path. A
// program with references prints as a declaration block (`printModule`), and reading it back
// must give the IR the printer started from: the site at the target's path is the layer
// itself, every later site a `ref` to it (`readModule`, `Refs.lean`).
describe("the n-ary merge", () => {
  const key = 'Context.Service<number>("k4_4")'
  const leaf = `Layer.succeed(${key}, 7)`

  /** The layer of `Effect.provide(Effect.succeed(7), <layer>)`. */
  const layerOf = (layer: string): LayerTerm => {
    const result = readTypeScript(`Effect.provide(Effect.succeed(7), ${layer})`)
    if (Result.isFailure(result)) throw new Error(`refused: ${JSON.stringify(result.failure)}`)
    if (result.success._tag !== "provideLayer") throw new Error(`not a provideLayer: ${result.success._tag}`)
    return result.success.layer
  }

  test("Layer.mergeAll(a, b, c) keeps its three layers in order", () => {
    const layer = layerOf(`Layer.mergeAll(${leaf}, Layer.fresh(${leaf}), Layer.orDie(${leaf}))`)
    expect(layer._tag).toBe("mergeAll")
    if (layer._tag === "mergeAll") expect(layer.layers.map((l) => l._tag)).toEqual(["succeed", "fresh", "orDie"])
  })
  test("Layer.mergeAll() is the empty spine", () => {
    const layer = layerOf("Layer.mergeAll()")
    expect(layer._tag).toBe("mergeAll")
    if (layer._tag === "mergeAll") expect(layer.layers).toEqual([])
    expect(json("Effect.provide(Effect.succeed(7), Layer.mergeAll())")).toContain('["mergeAll",["nil"]]')
  })
  test("Layer.merge is never read as the n-ary one", () => {
    expect(layerOf(`Layer.merge(${leaf}, ${leaf})`)._tag).toBe("merge")
  })
  test("Layer.mergeAll does not stand alone in program position", () => {
    expect(refusal(`Layer.mergeAll(${leaf})`)).toEqual({ _tag: "unknownHead", name: "Layer.mergeAll" })
  })
})

describe("layer references", () => {
  const key = 'Context.Service<number>("k4_4")'
  const kRef = 'Context.Service<Ref.Ref<number>>("k6_7")'
  const k44 = { name: { value: 4 }, service: { value: 4 } }
  const k67 = { name: { value: 6 }, service: { value: 7 } }

  test("L_1_0_0_0_0 in layer position is a reference to that path", () => {
    const result = readTypeScript("Effect.provide(Effect.succeed(7), L_1_0_0_0_0)")
    expect(Result.isSuccess(result)).toBe(true)
    if (Result.isSuccess(result) && result.success._tag === "provideLayer") {
      expect(result.success.layer).toEqual({ _tag: "ref", target: [1, 0, 0, 0, 0] })
    }
  })
  test.each(["L_01", "L_1_", "L_", "L_1__0", "L_x", "L1", "a0"])(
    "refuses the non-canonical layer name %s",
    (name) => {
      expect(refusal(`Effect.provide(Effect.succeed(7), ${name})`)).toEqual({ _tag: "shape", what: "layer" })
    },
  )

  // pDiamond of `harness/truth/Truth.lean`: one layer, provided twice through a `merge`. The
  // merge's left child is at [1, 0, 0, 0, 0] — root bind → child 1 provideService → child 0
  // bind → child 0 provideLayer → child 0 merge → child 0 — so that is the hoisted target.
  const diamond = [
    'import { Context, Effect, Layer, Ref } from "effect"',
    `export const L_1_0_0_0_0 = Layer.effect(${key}, Effect.succeed(5))`,
    `export const main: Effect.Effect<number, never> = Effect.flatMap(Ref.make(0), (a0) => ` +
      `Effect.provideService(Effect.flatMap(Effect.provide(Effect.service(${key}), ` +
      `Layer.merge(L_1_0_0_0_0, L_1_0_0_0_0)), (a1) => Ref.get(a0)), ${kRef}, a0))`,
  ].join("\n")

  test("a two-declaration module puts the layer back at its path and leaves the second site a ref", () => {
    expect(JSON.parse(json(diamond))).toEqual([
      "bind",
      ["perform", ["refMake"], ["lit", ["nat", 0]]],
      ["provideService", k67, ["var", 0], [
        "bind",
        ["provideLayer",
          ["merge", ["effect", k44, ["succeed", ["lit", ["nat", 5]]]], ["ref", [1, 0, 0, 0, 0]]],
          false,
          ["service", k44]],
        ["perform", ["refGet"], ["var", 0]],
      ]],
    ])
  })
  test("the same block without its declaration leaves both sites references", () => {
    const both = JSON.parse(json(diamond.split("\n").filter((line) => !line.startsWith("export const L_")).join("\n")))
    expect(both[2][3][1][1][1]).toEqual(["ref", [1, 0, 0, 0, 0]])
    expect(both[2][3][1][1][2]).toEqual(["ref", [1, 0, 0, 0, 0]])
  })
  test("a declaration whose name is no path spelling is not a module", () => {
    expect(refusal(`export const helper = Layer.succeed(${key}, 7)\nexport const main = Effect.succeed(1)`))
      .toEqual({ _tag: "shape", what: "module" })
  })
  test("a declaration whose path names no layer is not a module", () => {
    expect(refusal(`export const L_0 = Layer.succeed(${key}, 7)\nexport const main = Effect.succeed(1)`))
      .toEqual({ _tag: "shape", what: "module" })
  })
  test("one declaration and no reference still reads as the bare program", () => {
    expect(json(`const L_0 = Layer.succeed(${key}, 7)\nEffect.provide(Effect.succeed(7), L_0)`))
      .toBe(json(`Effect.provide(Effect.succeed(7), Layer.succeed(${key}, 7))`))
  })
  // A spine's element i at child c of p is at p ++ [c] ++ [1]*i ++ [0]: the first layer of
  // this mergeAll is at [0, 0, 0] and the third at [0, 0, 1, 1, 0].
  test("a target inside a mergeAll spine lands on the right element", () => {
    const source = [
      `export const L_0_0_0 = Layer.succeed(${key}, 7)`,
      `export const main = Effect.provide(Effect.succeed(7), ` +
        `Layer.mergeAll(L_0_0_0, Layer.orDie(Layer.succeed(${key}, 9)), L_0_0_0))`,
    ].join("\n")
    expect(JSON.parse(json(source))[1]).toEqual([
      "mergeAll",
      ["cons", ["succeed", k44, ["nat", 7]],
        ["cons", ["orDie", ["succeed", k44, ["nat", 9]]],
          ["cons", ["ref", [0, 0, 0]], ["nil"]]]],
    ])
  })
  // Declarations go back ancestors first, so a target inside another target has a site by
  // the time its turn comes (`Eff.restoreAll`); `printModule` emits them the other way round.
  test("a target nested in another is restored inside it", () => {
    const source = [
      `export const L_0_0 = Layer.succeed(${key}, 7)`,
      `export const L_0 = Layer.merge(L_0_0, L_0_0)`,
      `export const main = Effect.provide(Effect.provide(Effect.succeed(7), L_0), L_0)`,
    ].join("\n")
    const read = JSON.parse(json(source))
    expect(read[1]).toEqual(["merge", ["succeed", k44, ["nat", 7]], ["ref", [0, 0]]])
    expect(read[3][1]).toEqual(["ref", [0]])
  })
})

// The host rows slice (2026-09-09): a supplied row table beside the 55 built-ins. Its rows are
// the external operations by position (`nativeSpell`, never parsed from an identifier); a
// `method` row's receiver is the first component of its request and prints as
// `receiver.spelling(args)` (`printMethod`, `readRowMethod`). The tables and programs mirror
// `Test/Api/ExternalContract.lean` and `Test/Api/AcquireHandleContract.lean`.
describe("supplied tables and method rows", () => {
  const never: Ty = { _tag: "never" }
  const unit: Ty = { _tag: "unit" }
  const nat: Ty = { _tag: "nat" }
  const str: Ty = { _tag: "string" }
  const handle = (target: string): Ty => ({ _tag: "handle", target })
  const prod = (left: Ty, right: Ty): Ty => ({ _tag: "prod", left, right })
  const row = (name: string, spelling: string, shape: Row["shape"], request: Ty, answer: Ty, typeArgs: ReadonlyArray<string> = []): Row => ({
    name, spelling, shape, trailing: [], kind: "async", request, answer, error: never, requires: [], cite: "", typeArgs, registration: "external",
  })
  const methodTable: ReadonlyArray<Row> = [
    row("stop", "stop", "method", prod(nat, unit), nat),
    row("read", "read", "method", prod(nat, nat), nat),
    row("write", "write", "method", prod(nat, prod(nat, str)), nat),
    row("lookup", "lookup", "method", prod(nat, nat), nat, ["number"]),
    row("ping", "ping", "call", nat, nat),
  ]
  const resource = handle("Host.Resource")
  const acquireTable: ReadonlyArray<Row> = [
    row("acquire", "Host.acquire", "call", unit, resource),
    row("close", "Host.close", "call", resource, unit),
    row("read", "Host.read", "call", resource, nat),
  ]
  const readWith = (source: string, table: ReadonlyArray<Row>): string => {
    const r = readTypeScript(source, "program.ts", table)
    if (Result.isFailure(r)) throw new Error(`refused: ${JSON.stringify(r.failure)}`)
    return toJson(r.success)
  }
  const refusalWith = (source: string, table: ReadonlyArray<Row>): Refusal => {
    const r = readTypeScript(source, "program.ts", table)
    if (Result.isSuccess(r)) throw new Error(`accepted: ${toJson(r.success)}`)
    return r.failure
  }
  const v = (index: number): Term => ({ _tag: "var", index })
  const natLit = (value: number): Term => ({ _tag: "lit", value: { _tag: "nat", value } })
  const unitLit: Term = { _tag: "lit", value: { _tag: "unit" } }
  const pair = (a: Term, b: Term): Term => ({ _tag: "app", atom: "pair", args: [a, b] })
  const external = (index: number, request: Term): Eff => ({ _tag: "callback", register: { _tag: "external", index }, request })
  const after9 = (rest: Eff): Eff => ({ _tag: "bind", first: { _tag: "succeed", value: natLit(9) }, rest })

  test("zero, one and two arguments, and explicit type arguments (Lean methodPrograms)", () => {
    const method = (call: string): string => readWith(`Effect.flatMap(Effect.succeed(9), (a0) => ${call})`, methodTable)
    expect(method("a0.stop()")).toBe(toJson(after9(external(0, pair(v(0), unitLit)))))
    expect(method("a0.read(3)")).toBe(toJson(after9(external(1, pair(v(0), natLit(3))))))
    expect(method('a0.write(3, "x")')).toBe(toJson(after9(external(2, pair(v(0), pair(natLit(3), { _tag: "lit", value: { _tag: "str", value: "x" } }))))))
    expect(method("a0.lookup<number>(3)")).toBe(toJson(after9(external(3, pair(v(0), natLit(3))))))
  })
  test("the type arguments must be exactly the row's", () => {
    expect(refusalWith("Effect.flatMap(Effect.succeed(9), (a0) => a0.lookup(3))", methodTable)).toEqual({ _tag: "arity", head: "lookup" })
    expect(refusalWith("Effect.flatMap(Effect.succeed(9), (a0) => a0.read<number>(3))", methodTable)).toEqual({ _tag: "arity", head: "read" })
  })
  test("a method spelled as a call, and a call row spelled with a receiver, are refused", () => {
    expect(refusalWith("Effect.flatMap(Effect.succeed(9), (a0) => read(a0, 3))", methodTable)).toEqual({ _tag: "arity", head: "read" })
    expect(refusalWith("Effect.flatMap(Effect.succeed(9), (a0) => a0.ping())", methodTable)).toEqual({ _tag: "arity", head: "ping" })
  })
  test("under the empty table the same spellings are no rows", () => {
    expect(refusal("Effect.flatMap(Effect.succeed(9), (a0) => a0.read(3))")).toEqual({ _tag: "unknownHead", name: "read" })
    // A dotted call that no table names falls to the atom-application reading, as in Lean
    // (`readEff`'s last arm): a different program from the table's, which is why the corpus
    // gate must read a truth fixture under its own table.
    expect(json("Host.acquire()")).toBe('["yieldError",["app","Host.acquire",["nil"]]]')
  })
  test("the truth fixture pAcquireHandle reads to Lean's program under its table", () => {
    const source =
      "Effect.flatMap(Effect.scoped(Effect.acquireRelease(Host.acquire(), (a0, a1) => Host.close(a0))), " +
      "(a0) => Effect.flatMap(Host.read(a0), (a1) => Effect.succeed(pair(a0, a1))))"
    const expected: Eff = {
      _tag: "bind",
      first: { _tag: "scoped", body: { _tag: "acquireRelease", acquire: external(0, unitLit), release: external(1, v(0)) } },
      rest: { _tag: "bind", first: external(2, v(0)), rest: { _tag: "succeed", value: pair(v(0), v(1)) } },
    }
    expect(readWith(source, acquireTable)).toBe(toJson(expected))
  })
  test("a dotted head is never a receiver, and a member off a binder is not a program", () => {
    expect(json("Effect.succeed(1)")).toBe(json("Effect.succeed(1)"))
    expect(refusalWith("Effect.flatMap(Effect.succeed(9), (a0) => a0.read)", methodTable)).toEqual({ _tag: "shape", what: "expression" })
  })
})


describe("conditional handlers", () => {
  test("canonical catch binds the first error", () => {
    expect(json("Effect.catch(Effect.fail(7), (a0) => Effect.succeed(a0))")).toBe(
      '["catchIf",["lit",["bool",true]],["fail",["lit",["nat",7]]],["succeed",["var",0]]]')
  })
  test("predicate and handler both see only their own binder", () => {
    const source = "Effect.catchIf(Effect.fail(7), (a0) => eq(a0, 7), (a0) => Effect.succeed(a0), undefined)"
    expect(JSON.parse(json(source))[0]).toBe("catchIf")
    expect(refusal(source.replace("(a0) => eq", "(a1) => eq"))._tag).toBe("binder")
    expect(refusal(source.replace("(a0) => Effect.succeed", "(a1) => Effect.succeed"))._tag).toBe("binder")
  })
  test("the exact reader requires an absent fallback", () => {
    expect(refusal("Effect.catchIf(Effect.fail(7), (a0) => false, (a0) => Effect.succeed(a0))")._tag).toBe("arity")
    expect(refusal("Effect.catchIf(Effect.fail(7), (a0) => false, (a0) => Effect.succeed(a0), extra)")._tag).toBe("shape")
  })
  test("the noncanonical unconditional spelling stays outside the exact print image", () => {
    expect(refusal("Effect.catchIf(Effect.fail(7), (a0) => true, (a0) => Effect.succeed(a0), undefined)")._tag).toBe("shape")
  })
})
