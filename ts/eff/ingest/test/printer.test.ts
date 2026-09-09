import { expect, test } from "bun:test"
import { readFileSync } from "node:fs"
import { readPrintedSource as ck } from "../ck.ts"
import { readPrintedSource as oxc } from "../oxc.ts"
import { effJson } from "../../json.gen.ts"

for (const readPrintedSource of [ck, oxc]) {
test("the compiler reader recovers the original printed program", () => {
  expect(readPrintedSource("Effect.succeed(12)")).toEqual({ _tag: "succeed", value: { _tag: "lit", value: { _tag: "nat", value: 12 } } })
})

test("printed service identifiers are preserved by the separate printer entrypoint", () => {
  expect(readPrintedSource('Effect.service(Context.Service<number>("k10_4"))')).toEqual({ _tag: "service", key: { name: { value: 10 }, service: { value: 4 } } })
})

const key = 'Context.Service<number>("k4_4")'
const layer = `Layer.succeed(${key}, 7)`
const k44 = { name: { value: 4 }, service: { value: 4 } }

test("the printed n-ary merge keeps zero, one, and three layers", () => {
  for (const count of [0, 1, 3]) {
    const source = `Effect.provide(Effect.succeed(7), Layer.mergeAll(${Array(count).fill(layer).join(", ")}))`
    const program = readPrintedSource(source)
    expect(program._tag).toBe("provideLayer")
    if (program._tag !== "provideLayer") throw new Error("expected provision")
    expect(program.layer).toEqual({ _tag: "mergeAll", layers: Array(count).fill({ _tag: "succeed", key: { name: { value: 4 }, service: { value: 4 } }, value: { _tag: "nat", value: 7 } }) })
  }
})

test("the printed diamond recovers the original Lean golden including its defining path", () => {
  const source = `export const L_0_0 = Layer.effect(${key}, Effect.succeed(7)); export const main = Effect.provide(Effect.service(${key}), Layer.merge(L_0_0, L_0_0))`
  const expected = JSON.parse(readFileSync(new URL("../../../../ocaml/eff/goldens/pDiamond.json", import.meta.url), "utf8"))
  expect(effJson(readPrintedSource(source))).toEqual(expected)
})

test("the layer definition is restored at its named position inside a mergeAll spine", () => {
  const source = `const L_0_0_1_0 = ${layer}; Effect.provide(Effect.succeed(7), Layer.mergeAll(L_0_0_1_0, L_0_0_1_0, L_0_0_1_0))`
  expect(effJson(readPrintedSource(source))).toEqual([
    "provideLayer", ["mergeAll", ["cons", ["ref", [0, 0, 1, 0]],
      ["cons", ["succeed", k44, ["nat", 7]], ["cons", ["ref", [0, 0, 1, 0]], ["nil"]]]]],
    false, ["succeed", ["lit", ["nat", 7]]],
  ])
})

test("nested layer declarations restore ancestors before their children", () => {
  const source = `export const L_0_0 = ${layer}; export const L_0 = Layer.merge(L_0_0, L_0_0); export const main = Effect.provide(Effect.provide(Effect.succeed(7), L_0), L_0)`
  expect(effJson(readPrintedSource(source))).toEqual([
    "provideLayer", ["merge", ["succeed", k44, ["nat", 7]], ["ref", [0, 0]]], false,
    ["provideLayer", ["ref", [0]], false, ["succeed", ["lit", ["nat", 7]]]],
  ])
})

test("a layer identifier without a declaration stays a reference", () => {
  expect(effJson(readPrintedSource("Effect.provide(Effect.succeed(7), L_0)"))).toEqual([
    "provideLayer", ["ref", [0]], false, ["succeed", ["lit", ["nat", 7]]],
  ])
})

test("only canonical path names, leading const layers, and one main program are accepted", () => {
  for (const name of ["helper", "L_", "L_01", "L_1_", "L_1__0"]) {
    expect(() => readPrintedSource(`const ${name} = ${layer}; Effect.provide(Effect.succeed(7), ${name})`)).toThrow()
    expect(() => readPrintedSource(`Effect.provide(Effect.succeed(7), ${name})`)).toThrow()
  }
  for (const source of [
    `const L_0 = ${layer}; Effect.succeed(7)`,
    "const L_0 = Effect.succeed(7); Effect.provide(Effect.succeed(7), L_0)",
    `let L_0 = ${layer}; Effect.provide(Effect.succeed(7), L_0)`,
    `const L_0 = ${layer}, extra = ${layer}; Effect.provide(Effect.succeed(7), L_0)`,
    "Effect.succeed(7); Effect.succeed(8)",
    `Effect.provide(Effect.succeed(7), L_0); const L_0 = ${layer}`,
  ]) expect(() => readPrintedSource(source)).toThrow()
})
}

test("the compiler reader refuses paths whose components exceed exact integers", () => {
  expect(() => ck("Effect.provide(Effect.succeed(7), L_9007199254740992)")).toThrow()
})
