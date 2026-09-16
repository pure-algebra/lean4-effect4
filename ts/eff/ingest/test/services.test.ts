import { expect, test } from "bun:test"
import type { Eff } from "../../eff.gen.ts"
import { recognizeSource as ck } from "../ck.ts"
import { recognizeSource as oxc } from "../oxc.ts"

const header = 'import { Context, Effect } from "effect"; import { SqlClient } from "effect/unstable/sql";'
const sharedId = "effect/sql/SqlClient"

for (const [name, recognize] of [["ck", ck], ["oxc", oxc]] as const) {
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
