import { expect, test } from "bun:test"
import { Result } from "effect"
import type { Eff } from "../../eff.gen.ts"
import { readTypeScript } from "../../read.ts"
import { recognizeSource as ck, readPrintedSource as printedCk } from "../ck.ts"
import { recognizeSource as oxc, readPrintedSource as printedOxc } from "../oxc.ts"

const header = 'import { Context, Effect } from "effect"; import { SqlClient } from "effect/unstable/sql";'
const sharedId = "effect/sql/SqlClient"

for (const [name, recognize] of [["ck", ck], ["oxc", oxc]] as const) {
  test(`${name}: explicit literal identity agrees with the runtime key before normalization`, () => {
    for (const identity of ['"alpha"', "'alpha'", '"\\u0061lpha"']) {
      const source = `${header} const K = Context.Service<${identity}, number>("alpha"); const main = Effect.service(K);`
      const result = recognize(source, "literal-service.ts").find(row => row.unit.name === "main")
      expect(result?.kind).toBe("lifted")
      if (result?.kind !== "lifted") throw new Error(JSON.stringify(result))
      expect(result.keys).toEqual([{ ordinal: 4, service: 4, sourceId: "alpha" }])
      expect(result.eff).toEqual({ _tag: "service", key: { name: { value: 4 }, service: { value: 4 } } })
    }
  })

  test(`${name}: different literal identities keep distinct keys with the same carrier`, () => {
    const source = `${header} const A = Context.Service<"alpha", number>("alpha"); const B = Context.Service<"beta", number>("beta");` +
      "const main = Effect.provideService(Effect.service(A), B, 1);"
    const result = recognize(source, "distinct-service.ts").find(row => row.unit.name === "main")
    expect(result?.kind).toBe("lifted")
    if (result?.kind !== "lifted") throw new Error(JSON.stringify(result))
    expect(result.keys).toEqual([
      { ordinal: 4, service: 4, sourceId: "alpha" },
      { ordinal: 5, service: 4, sourceId: "beta" },
    ])
    expect(result.eff).toEqual({ _tag: "provideService",
      body: { _tag: "service", key: { name: { value: 4 }, service: { value: 4 } } },
      key: { name: { value: 5 }, service: { value: 4 } }, value: { _tag: "lit", value: { _tag: "nat", value: 1 } } })
  })

  test(`${name}: an explicit Identifier cannot disagree with or hide the runtime identity`, () => {
    for (const args of ['"other", number', 'string, number', 'number, number', '"alpha", boolean, number']) {
      const source = `${header} const K = Context.Service<${args}>("alpha"); const main = Effect.service(K);`
      const result = recognize(source, "mismatched-service.ts").find(row => row.unit.name === "main")
      expect(result?.kind).toBe("refusal")
      if (result?.kind !== "refusal") throw new Error(JSON.stringify(result))
      expect(result.code).toBe("E-TYPE-PARAM")
    }
  })

  test(`${name}: class-style Self remains a separate admitted foreign spelling`, () => {
    const source = `${header} class K extends Context.Service<K, number>()("alpha") {} const main = Effect.service(K);`
    const result = recognize(source, "class-service.ts").find(row => row.unit.name === "main")
    expect(result?.kind).toBe("lifted")
    if (result?.kind !== "lifted") throw new Error(JSON.stringify(result))
    expect(result.keys).toEqual([{ ordinal: 4, service: 4, sourceId: "alpha" }])
  })

  test(`${name}: the native scope service is not a user key with the old reserved spelling`, () => {
    const source = `${header} import { Scope } from "effect"; const K = Context.Service<"k0_0", number>("k0_0");` +
      "const main = Effect.andThen(Effect.service(Scope.Scope), Effect.service(K));"
    const result = recognize(source, "scope-service.ts").find(row => row.unit.name === "main")
    expect(result?.kind).toBe("lifted")
    if (result?.kind !== "lifted") throw new Error(JSON.stringify(result))
    expect(result.keys).toEqual([{ ordinal: 4, service: 4, sourceId: "k0_0" }])
    expect(result.eff).toEqual({ _tag: "bind",
      first: { _tag: "service", key: { name: { value: 0 }, service: { value: 0 } } },
      rest: { _tag: "service", key: { name: { value: 4 }, service: { value: 4 } } } })
  })

  test(`${name}: restoring a referenced layer does not renumber the native scope service`, () => {
    const source = `${header} import { Scope, Layer } from "effect"; const Live = Layer.effectDiscard(Effect.service(Scope.Scope));` +
      "const main = Effect.provide(Effect.provide(Effect.succeed(1), Live), Live);"
    const result = recognize(source, "scope-layer.ts").find(row => row.unit.name === "main")
    expect(result?.kind).toBe("lifted")
    if (result?.kind !== "lifted") throw new Error(JSON.stringify(result))
    expect(result.keys).toEqual([])
    expect(JSON.stringify(result.eff)).toContain('"name":{"value":0},"service":{"value":0}')
  })

  test(`${name}: native scope aliases must remain unshadowed at the use`, () => {
    for (const [imports, root, scope] of [
      ['import { Scope } from "effect";', "Scope", "Scope.Scope"],
      ['import { Scope as S } from "effect";', "S", "S.Scope"],
      ['import * as Fx from "effect";', "Fx", "Fx.Scope.Scope"],
    ]) {
      const prefix = `${header} import { Layer } from "effect"; ${imports}`
      const positive = recognize(`${prefix} const main = Effect.flatMap(Effect.succeed(1), (_) => Effect.service(${scope}));`, "scope-alias.ts")
        .find(row => row.unit.name === "main")
      expect(positive?.kind).toBe("lifted")
      for (const body of [
        `Effect.service(${scope})`,
        `Effect.provide(Effect.succeed(1), Layer.effectDiscard(Effect.service(${scope})))`,
        `Effect.succeed(1).pipe(Effect.provide(Layer.effectDiscard(Effect.service(${scope}))))`,
      ]) {
        const negative = recognize(`${prefix} const main = Effect.flatMap(Effect.succeed(1), (${root}) => ${body});`, "scope-shadow.ts")
          .find(row => row.unit.name === "main")
        expect(negative?.kind).toBe("refusal")
        if (negative?.kind !== "refusal") throw new Error(JSON.stringify(negative))
        expect(negative.code).toBe("E-OP-RECEIVER")
      }
      // This layer was defined before the callback: its scope use refers to the
      // import, even when a later callback shadows that spelling.
      const declared = recognize(`${prefix} const Live = Layer.effectDiscard(Effect.service(${scope}));` +
        `const main = Effect.flatMap(Effect.succeed(1), (${root}) => Effect.provide(Effect.succeed(1), Live));`, "scope-layer-binding.ts")
        .find(row => row.unit.name === "main")
      expect(declared?.kind).toBe("lifted")
    }
  })

  // Adapted from vendor/effect-4.0.0-rc.112/src/Context.ts:864-868: the Port
  // service/provision pattern, replacing its object carrier with supported number.
  test(`${name}: pinned Port example, adapted scalar carrier, retains value checks`, () => {
    const prefix = `${header} const Port = Context.Service<number>("Port");`
    const positive = recognize(`${prefix} const main = Effect.provideService(Effect.service(Port), Port, 8080);`, "vendor-port-adapted.ts")
      .find(row => row.unit.name === "main")
    expect(positive?.kind).toBe("lifted")
    if (positive?.kind !== "lifted") throw new Error(JSON.stringify(positive))
    expect(positive.keys).toEqual([{ ordinal: 4, service: 4, sourceId: "Port" }])
    const negative = recognize(`${prefix} const main = Effect.provideService(Effect.service(Port), Port, true);`, "vendor-port-wrong-carrier.ts")
      .find(row => row.unit.name === "main")
    expect(negative?.kind).toBe("refusal")
    if (negative?.kind === "refusal") expect(negative.code).toBe("E-ARG-DYNAMIC")
  })

  // Adapted from vendor/effect-4.0.0-rc.112/src/Context.ts:183-185: the
  // two-stage class factory is unchanged; { port: number } becomes number.
  test(`${name}: pinned Config class example, adapted carrier, does not admit callbacks`, () => {
    const prefix = `${header} class Config extends Context.Service<Config, number>()("Config") {}`
    const positive = recognize(`${prefix} const main = Effect.provideService(Effect.service(Config), Config, 8080);`, "vendor-config-adapted.ts")
      .find(row => row.unit.name === "main")
    expect(positive?.kind).toBe("lifted")
    if (positive?.kind !== "lifted") throw new Error(JSON.stringify(positive))
    expect(positive.keys).toEqual([{ ordinal: 4, service: 4, sourceId: "Config" }])
    const negative = recognize(`${prefix} const main = Effect.provideService(Effect.service(Config), Config, () => 8080);`, "vendor-config-callback.ts")
      .find(row => row.unit.name === "main")
    expect(negative?.kind).toBe("refusal")
    if (negative?.kind === "refusal") expect(negative.code).toBe("E-ARG-DYNAMIC")
  })

  // Adapted from vendor/effect-4.0.0-rc.112/src/unstable/sql/SqlClient.ts:12,95:
  // keep its key string and carrier, use package imports and namespace aliases.
  // This recognizes the declaration and service reads, not the SQL implementation.
  test(`${name}: pinned SqlClient key through aliases retains its package identity`, () => {
    const prefix = 'import * as C from "effect/Context"; import { Effect } from "effect"; import { SqlClient as SQL } from "effect/unstable/sql";'
    const body = 'const main = Effect.andThen(Effect.service(Db), Effect.service(SQL.SqlClient));'
    const positive = recognize(`${prefix} const Db = C.Service<SQL.SqlClient>("effect/sql/SqlClient"); ${body}`, "vendor-sql-key-adapted.ts")
      .find(row => row.unit.name === "main")
    expect(positive?.kind).toBe("lifted")
    if (positive?.kind !== "lifted") throw new Error(JSON.stringify(positive))
    expect(positive.keys).toEqual([{ ordinal: 4, service: 8, sourceId: "effect/sql/SqlClient" }])
    const negative = recognize(`${prefix} const Db = C.Service<number>("effect/sql/SqlClient"); ${body}`, "vendor-sql-key-conflict.ts")
      .find(row => row.unit.name === "main")
    expect(negative?.kind).toBe("refusal")
    if (negative?.kind === "refusal") expect(negative.code).toBe("E-TYPE-PARAM")
  })

  // The unadapted callback carrier in Context.ts:178-180 remains outside the
  // admitted service-type profile. The examples above do not widen that profile.
  test(`${name}: the pinned Database callback carrier still refuses by type`, () => {
    const source = `${header} const Database = Context.Service<{ query: (sql: string) => string }>("Database"); const main = Effect.service(Database);`
    const result = recognize(source, "vendor-database-unadapted.ts").find(row => row.unit.name === "main")
    expect(result?.kind).toBe("refusal")
    if (result?.kind === "refusal") expect(result.code).toBe("E-TYPE-PARAM")
  })

  for (const packageFirst of [false, true]) {
    const order = packageFirst ? "package first" : "declaration first"
    const sequence = (declared: string, packaged: string) => packageFirst
      ? `Effect.andThen(${packaged}, ${declared})` : `Effect.andThen(${declared}, ${packaged})`

    test(`${name}: conflicting package and declared service types refuse, ${order}`, () => {
      const source = `${header} const K = Context.Service<number>("${sharedId}"); const main = ` +
        sequence("Effect.service(K)", "Effect.service(SqlClient.SqlClient)") + ";"
      const result = recognize(source, "conflicting-services.ts").find(row => row.unit.name === "main")
      expect(result?.kind).toBe("refusal")
      if (result?.kind !== "refusal") throw new Error(JSON.stringify(result))
      expect(result.code).toBe("E-TYPE-PARAM")
      expect(result.detail).toBe("type parameter: service identity has conflicting shapes")
    })

    test(`${name}: same-shape package alias reuses one key, ${order}`, () => {
      const source = `${header} const K = Context.Service<SqlClient.SqlClient>("${sharedId}"); const main = ` +
        sequence("Effect.service(K)", "Effect.service(SqlClient.SqlClient)") + ";"
      const result = recognize(source, "same-service.ts").find(row => row.unit.name === "main")
      expect(result?.kind).toBe("lifted")
      if (result?.kind !== "lifted") throw new Error(JSON.stringify(result))
      expect(result.keys).toEqual([{ ordinal: 4, service: 8, sourceId: sharedId }])
      const service: Eff = { _tag: "service", key: { name: { value: 4 }, service: { value: 8 } } }
      expect(result.eff).toEqual({ _tag: "bind", first: service, rest: service })
    })
  }

  test(`${name}: ordinary declared keys also refuse conflicting shapes in either order`, () => {
    const declarations = `${header} const A = Context.Service<number>("same"); const B = Context.Service<boolean>("same");`
    for (const [first, second] of [["A", "B"], ["B", "A"]]) {
      const source = `${declarations} const main = Effect.andThen(Effect.service(${first}), Effect.service(${second}));`
      const result = recognize(source, "declared-conflict.ts").find(row => row.unit.name === "main")
      expect(result?.kind).toBe("refusal")
      if (result?.kind !== "refusal") throw new Error(JSON.stringify(result))
      expect(result.code).toBe("E-TYPE-PARAM")
    }
  })
}

const printedReaders = [
  ["ck", printedCk], ["oxc", printedOxc],
  ["fragment", (source: string) => {
    const result = readTypeScript(source)
    if (Result.isFailure(result)) throw new Error(JSON.stringify(result.failure))
    return result.success
  }],
] as const

for (const [name, read] of printedReaders) {
  test(`${name}: the printed key retains both fields of its identity`, () => {
    for (const [key, carrier, expected] of [
      ["k10_4", "number", { name: { value: 10 }, service: { value: 4 } }],
      ["k11_7", "Ref.Ref<number>", { name: { value: 11 }, service: { value: 7 } }],
    ] as const) {
      expect(read(`Effect.service(Context.Service<${JSON.stringify(key)}, ${carrier}>(${JSON.stringify(key)}))`))
        .toEqual({ _tag: "service", key: expected })
    }
  })

  test(`${name}: printed reserved Scope keeps its native Identifier and unknown keys stay bare`, () => {
    expect(read('Effect.service(Scope.Scope)'))
      .toEqual({ _tag: "service", key: { name: { value: 0 }, service: { value: 0 } } })
    expect(read('Effect.service(Context.Service("k1_4"))'))
      .toEqual({ _tag: "service", key: { name: { value: 1 }, service: { value: 4 } } })
  })

  test(`${name}: the printed reader refuses noncanonical identity or carrier`, () => {
    for (const key of [
      'Context.Service<"k11_4", number>("k10_4")',
      'Context.Service<"k10_5", number>("k10_4")',
      'Context.Service<"k10_4", boolean>("k10_4")',
      'Context.Service<number>("k10_4")',
      'Context.Service<string, number>("k10_4")',
      'Context.Service<"k10_4", number, number>("k10_4")',
      'Context.Service<"k010_4", number>("k010_4")',
      'Context.Service<"k9007199254740992_4", number>("k9007199254740992_4")',
      'Context.Service<"k0_0", Scope.Scope>("k0_0")',
      'Context.Service<Scope.Scope, Scope.Scope>("k0_0")',
      'Context.Service<Scope.Scope>("k0_0")',
      'Context.Service("k0_0")',
      'Context.Service<Scope.Scope, number>("k0_0")',
      'Context.Service<Scope.Scope, number>("k10_4")',
      'Context.Service<"k1_4", number>("k1_4")',
    ]) expect(() => read(`Effect.service(${key})`)).toThrow()
  })
}
