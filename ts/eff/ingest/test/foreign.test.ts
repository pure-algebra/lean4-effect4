import { expect, test } from "bun:test"
import { recognizeSource as ck } from "../ck.ts"
import { recognizeSource as oxc } from "../oxc.ts"
import { compareVerdicts } from "../gate.ts"

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

const layerHeader = 'import { Effect, Layer, Context } from "effect"; '
const layerValue = 'Layer.succeed(Context.Service<number>("K"), 7)'

test("foreign layer declarations retain one defining occurrence and later references", () => {
  const source = layerHeader + `const Live = ${layerValue}; const p = Effect.provide(Effect.succeed(7), Layer.mergeAll(Live, Live, Live));`
  const left = ck(source, "layers.ts"), right = oxc(source, "layers.ts")
  expect(compareVerdicts(left, right).status).toBe("agree")
  for (const result of [left, right]) {
    expect(result).toHaveLength(1)
    const v = result[0]!
    expect(v.kind).toBe("lifted")
    if (v.kind !== "lifted" || v.eff._tag !== "provideLayer") throw new Error("expected provision")
    expect(v.eff.layer).toEqual({ _tag: "mergeAll", layers: [
      { _tag: "succeed", key: { name: { value: 4 }, service: { value: 4 } }, value: { _tag: "nat", value: 7 } },
      { _tag: "ref", target: [0, 0, 0] }, { _tag: "ref", target: [0, 0, 0] },
    ] })
    expect(v.layers).toEqual([{ sourceName: "Live", target: [0, 0, 0] }])
  }
})

test("nested layer definitions are shared across an inlined program and later provisions", () => {
  const source = layerHeader + `const Base = ${layerValue}; const Live = Layer.merge(Base, Base); const q = Effect.provide(Effect.succeed(7), Live); const p = Effect.flatMap(q, (_) => Effect.provide(Effect.succeed(8), Base));`
  const left = ck(source, "nested.ts"), right = oxc(source, "nested.ts")
  expect(compareVerdicts(left, right).status).toBe("agree")
  const v = left.find(v => v.unit.name === "p")
  expect(v?.kind).toBe("lifted")
  if (v?.kind !== "lifted" || v.eff._tag !== "bind" || v.eff.rest._tag !== "provideLayer") throw new Error("expected bind")
  expect(v.eff.rest.layer).toEqual({ _tag: "ref", target: [0, 0, 0] })
})

test("layer definitions use program path order while keys retain their existing reading order", () => {
  const source = layerHeader + `const Live = Layer.effectDiscard(Effect.service(Context.Service<number>("A"))); const p = Effect.provide(Effect.flatMap(Effect.provide(Effect.succeed(1), Live), (_) => Effect.service(Context.Service<number>("B"))), Live);`
  const left = ck(source, "order.ts"), right = oxc(source, "order.ts")
  expect(compareVerdicts(left, right).status).toBe("agree")
  const v = left[0]
  expect(v?.kind).toBe("lifted")
  if (v?.kind !== "lifted" || v.eff._tag !== "provideLayer" || v.eff.body._tag !== "bind" || v.eff.body.first._tag !== "provideLayer") throw new Error("expected provision")
  expect(v.eff.body.first.layer).toEqual({ _tag: "ref", target: [0] })
  expect(v.keys).toEqual([{ ordinal: 4, service: 4, sourceId: "B" }, { ordinal: 5, service: 4, sourceId: "A" }])
})

test("a layer alias retains the original identity regardless of which name occurs first", () => {
  for (const uses of ["Base, Alias, Alias", "Alias, Base, Alias"]) {
    const source = layerHeader + `const Base = ${layerValue}; const Alias = Base; const p = Effect.provide(Effect.succeed(7), Layer.mergeAll(${uses}));`
    const left = ck(source, "alias.ts"), right = oxc(source, "alias.ts")
    expect(compareVerdicts(left, right).status).toBe("agree")
    const v = left[0]
    if (v?.kind !== "lifted" || v.eff._tag !== "provideLayer" || v.eff.layer._tag !== "mergeAll") throw new Error("expected mergeAll")
    expect(v.eff.layer.layers.slice(1)).toEqual([{ _tag: "ref", target: [0, 0, 0] }, { _tag: "ref", target: [0, 0, 0] }])
    expect(v.layers?.map(l => l.target)).toEqual([[0, 0, 0], [0, 0, 0]])
    expect(compareVerdicts(left, [{ ...v, layers: [{ sourceName: "changed", target: [0] }] }]).status).toBe("disagree")
  }
})

test("unbound and forward layer references remain refusals in both foreign readers", () => {
  for (const [source, code] of [
    [layerHeader + 'const p = Effect.provide(Effect.succeed(7), L_0);', "E-REF-UNBOUND"],
    [layerHeader + `const p = Effect.provide(Effect.succeed(7), Live); const Live = ${layerValue};`, "E-REF-FORWARD"],
    [layerHeader + `const Early = Later; const Later = ${layerValue}; const p = Effect.provide(Effect.succeed(7), Early);`, "E-REF-UNBOUND"],
  ] as const) {
    const left = ck(source!, "refused-layer.ts"), right = oxc(source!, "refused-layer.ts")
    expect(compareVerdicts(left, right).status).toBe("agree")
    for (const result of [left, right]) {
      const v = result.find(v => v.unit.name === "p")
      expect(v?.kind).toBe("refusal")
      if (v?.kind === "refusal") expect(v.code).toBe(code!)
    }
  }
})

test("a layer reference cannot turn a program or a malformed layer into a definition", () => {
  for (const value of ['Effect.succeed(7)', 'Layer.succeed(Context.Service<number>("K"), 7, 8)']) {
    const source = layerHeader + `const Live = ${value}; const p = Effect.provide(Effect.succeed(7), Live);`
    const left = ck(source, "bad-layer.ts"), right = oxc(source, "bad-layer.ts")
    expect(compareVerdicts(left, right).status).toBe("agree")
    const v = left.find(v => v.unit.name === "p")
    expect(v?.kind).toBe("refusal")
    if (v?.kind === "refusal") expect(v.code).toBe("E-REF-UNBOUND")
  }
})

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
