import { expect, test } from "bun:test"
import { recognizeSource as ck } from "../ck.ts"
import { recognizeSource as oxc } from "../oxc.ts"

for (const recognizeSource of [ck, oxc]) {

test("foreign keys start at four independently of their source identifier", () => {
  const source = 'import { Effect, Context } from "effect"; const K = Context.Service<number>("k10_4"); export const program = Effect.service(K);'
  const result = recognizeSource(source, "key.ts")
  expect(result).toHaveLength(1)
  const v = result[0]!
  expect(v.kind).toBe("lifted")
  if (v.kind === "lifted") {
    expect(v.eff).toEqual({ _tag: "service", key: { name: { value: 4 }, service: { value: 4 } } })
    expect(v.keys).toEqual([{ ordinal: 4, service: 4, sourceId: "k10_4" }])
  }
})

test("foreign provision refuses a boolean for a number-shaped service", () => {
  const [v] = recognizeSource('import { Effect, Context } from "effect"; const K = Context.Service<number>("K"); const p = Effect.provideService(Effect.succeed(0), K, true);', "shape.ts")
  expect(v?.kind).toBe("refusal")
  if (v?.kind === "refusal") expect(v.code).toBe("E-ARG-DYNAMIC")
})

test("foreign failures admit literals and refuse primitive-valued nonliteral terms", () => {
  const vs = recognizeSource('import { Effect } from "effect"; const a = Effect.fail(1); const b = Effect.fail(succ(1));', "failure.ts")
  expect(vs.map(v => v.kind === "refusal" ? v.code : v.kind)).toEqual(["lifted", "E-FAIL-NOT-DOCUMENTED"])
})

}

for (const recognize of [ck, oxc]) {
  test("nested eta binders may shadow an outer eta binder", () => {
    const [v] = recognize('import { Effect } from "effect"; const p = Effect.succeed(1).pipe((_self) => Effect.flatMap(_self, (a) => Effect.succeed(a).pipe((_self) => Effect.as(_self, 2))));', "eta.ts")
    expect(v?.kind).toBe("lifted")
  })
}

for (const recognize of [ck, oxc]) {
  test("default and entry-call expressions are ingestion roots", () => {
    const source = 'import { Effect } from "effect"; export default Effect.succeed(1); Effect.runSync(Effect.succeed(2));'
    expect(recognize(source, "roots.ts").map(v => [v.unit.name, v.kind])).toEqual([["default", "lifted"], ["Effect.runSync#0", "lifted"]])
  })
  test("functions and generic declarations are classified", () => {
    const source = 'import { Effect } from "effect"; function p() { return Effect.succeed(1) }; function q<T>(x: T) { return x };'
    expect(recognize(source, "functions.ts").map(v => v.kind === "refusal" ? v.code : v.kind)).toEqual(["E-PARAM-SHAPE", "E-TYPE-PARAM"])
  })
}

for (const recognize of [ck, oxc]) {
  test("an earlier refused declaration cannot become admitted through a later unit", () => {
    const source = 'import { Effect } from "effect"; const q = later; const later = Effect.succeed(1); const p = q;'
    const v = recognize(source, "forward.ts").find(v => v.unit.name === "p")
    expect(v?.kind).toBe("refusal")
    if (v?.kind === "refusal") { expect(v.code).toBe("E-REF-UNBOUND"); expect(v.detail).toContain("E-REF-FORWARD") }
  })
}

for (const recognize of [ck, oxc]) {
  test("a class service declaration supplies its literal identity and shape", () => {
    const source = 'import { Effect, Context } from "effect"; class K extends Context.Service<K, number>()("Service") {} const p = Effect.service(K);'
    const vs = recognize(source, "class.ts")
    expect(vs).toHaveLength(1)
    const v = vs[0]!
    expect(v.kind).toBe("lifted")
    if (v.kind === "lifted") expect(v.keys).toEqual([{ ordinal: 4, service: 4, sourceId: "Service" }])
  })
}

for (const recognize of [ck, oxc]) {
  test("map admits a term body and refuses an arbitrary closure", () => {
    const source = 'import { Effect } from "effect"; const p = Effect.succeed(1).pipe(Effect.map((x) => x)); const q = Effect.map(Effect.succeed(1), (x) => x * 2 + 1);'
    const vs = recognize(source, "map.ts")
    expect(vs[0]?.kind).toBe("lifted")
    const v = vs[1]
    expect(v?.kind).toBe("refusal")
    if (v?.kind === "refusal") expect(v.code).toBe("E-ARG-CLOSURE")
  })
}
