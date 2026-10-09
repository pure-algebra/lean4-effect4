import { expect, test } from "bun:test"
import { readFileSync } from "node:fs"
import { readPrintedSource as ck, recognizeSource as foreignCk } from "../ck.ts"
import { readPrintedSource as oxc, recognizeSource as foreignOxc } from "../oxc.ts"
import { effJson } from "../../json.gen.ts"

for (const readPrintedSource of [ck, oxc]) {
test("the compiler reader recovers the original printed program", () => {
  expect(readPrintedSource("Effect.succeed(12)")).toEqual({ _tag: "succeed", value: { _tag: "lit", value: { _tag: "nat", value: 12 } } })
})

test("the printed boolean thunks capture the caller without adding a binder", () => {
  const source = "Effect.flatMap(Effect.succeed(true), (a0) => ifCase(() => a0, () => Effect.succeed(a0), () => Effect.fail(a0)))"
  expect(effJson(readPrintedSource(source))).toEqual([
    "bind", ["succeed", ["lit", ["bool", true]]],
    ["select", ["var", 0], ["bool"], ["succeed", ["var", 0]], ["fail", ["var", 0]]],
  ])
})

test("the printed boolean row refuses noncanonical calls and thunks", () => {
  const bodies = ["a0", "Effect.succeed(a0)", "Effect.fail(a0)"]
  const thunks = bodies.map(body => `() => ${body}`)
  const call = (args: readonly string[], head = "ifCase") =>
    `Effect.flatMap(Effect.succeed(true), (a0) => ${head}(${args.join(", ")}))`
  for (const source of [
    call(thunks.slice(0, 2)), call([...thunks, "0"]), call(thunks, "ifCase<number>"), call(thunks, "ifCase?."),
    "Effect.suspend(() => true ? Effect.succeed(1) : Effect.succeed(2))",
    "Effect.flatMap(Effect.succeed(true), (ifCase) => ifCase(() => ifCase, () => Effect.succeed(ifCase), () => Effect.succeed(ifCase)))",
  ]) expect(() => readPrintedSource(source)).toThrow()
  for (let index = 0; index < thunks.length; index++) {
    for (const malformed of [
      `a1 => ${bodies[index]}`, `(): unknown => ${bodies[index]}`, `async () => ${bodies[index]}`,
      `<T>() => ${bodies[index]}`, `() => { return ${bodies[index]} }`, "function* () { yield 1 }",
    ]) {
      const args = [...thunks]; args[index] = malformed
      expect(() => readPrintedSource(call(args))).toThrow()
    }
  }
  for (let index = 0; index < thunks.length; index++) {
    const args = [...thunks]; args[index] = thunks[index]!.replaceAll("a0", "a1")
    expect(() => readPrintedSource(call(args))).toThrow()
  }
})

test("printed service identifiers are preserved by the separate printer entrypoint", () => {
  expect(readPrintedSource('Effect.service(Context.Service<"k10_4", number>("k10_4"))')).toEqual({ _tag: "service", key: { name: { value: 10 }, service: { value: 4 } } })
})

const key = 'Context.Service<"k4_4", number>("k4_4")'
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

// The mask that restores (decisions rows 244 to 246). The getter prints as the mask that answers
// its own parameter, and a restore site as `pipe(body, saved)` (`Codegen/Templates.lean`). The
// oracles are Lean's goldens: one restore site around a wait, two masks, a saved state used
// outside its mask, and a saved term that is no saved state.
test("the printed mask recovers the original Lean goldens", () => {
  const getter = (n: number) => `Effect.uninterruptibleMask((a${n}) => Effect.succeed(a${n}))`
  for (const [golden, source] of [
    ["pMask", `Effect.flatMap(Deferred.make<number, number>(), (a0) => Effect.flatMap(Deferred.succeed(a0, 7), (a1) => ` +
      `Effect.flatMap(${getter(2)}, (a2) => Effect.uninterruptible(pipe(Deferred.await(a0), a2)))))`],
    ["pMaskNested", `Effect.flatMap(${getter(0)}, (a0) => Effect.uninterruptible(Effect.flatMap(${getter(1)}, (a1) => ` +
      `Effect.uninterruptible(Effect.flatMap(pipe(Effect.succeed(1), a1), (a2) => pipe(Effect.succeed(a2), a0))))))`],
    ["pMaskEscape", `Effect.flatMap(Effect.flatMap(${getter(0)}, (a0) => Effect.uninterruptible(Effect.succeed(a0))), ` +
      `(a0) => pipe(Effect.succeed(3), a0))`],
    ["pIllRestoreBool", "pipe(Effect.succeed(1), true)"],
  ] as const) {
    const expected = JSON.parse(readFileSync(new URL(`../../../../ocaml/eff/goldens/${golden}.json`, import.meta.url), "utf8"))
    expect(effJson(readPrintedSource(source))).toEqual(expected)
  }
})

test("a mask whose callback does not answer its own parameter is no printed image", () => {
  for (const source of [
    "Effect.uninterruptibleMask((a0) => Effect.succeed(1))",
    "Effect.uninterruptibleMask((a0) => pipe(Effect.succeed(1), a0))",
    "Effect.uninterruptibleMask(Effect.succeed(1))",
    "pipe(Effect.succeed(1))",
  ]) expect(() => readPrintedSource(source)).toThrow()
})

test("a printed getter refuses an Effect head shadowed by a callback binder", () => {
  for (const source of [
    'Effect.uninterruptibleMask((Effect) => Effect.succeed(Effect))',
    'Effect.flatMap(Effect.succeed(0), (Effect) => Effect.uninterruptibleMask((r) => Effect.succeed(r)))',
    'Effect.flatMap(Effect.succeed(0), (Effect) => Effect.flatMap(Effect.succeed(1), (a1) => Effect.uninterruptibleMask((r) => Effect.succeed(r))))',
  ]) expect(() => readPrintedSource(source)).toThrow()
})
}

test("the compiler reader refuses paths whose components exceed exact integers", () => {
  expect(() => ck("Effect.provide(Effect.succeed(7), L_9007199254740992)")).toThrow()
})

// The two source profiles stay separate: only the printed profile changes its boolean image.
for (const recognizeSource of [foreignCk, foreignOxc]) {
  test("foreign recognition retains its former suspended conditional", () => {
    const source = 'import { Effect } from "effect"\nexport const main = Effect.flatMap(Effect.succeed(true), (flag) => Effect.suspend(() => flag ? Effect.succeed(1) : Effect.succeed(2)))'
    const verdicts = recognizeSource(source, "legacy-boolean.ts")
    expect(verdicts.length).toBe(1)
    const verdict = verdicts[0]!
    expect(verdict.kind).toBe("lifted")
    if (verdict.kind !== "lifted") throw new Error("expected retained foreign conditional")
    expect(effJson(verdict.eff)).toEqual([
      "bind", ["succeed", ["lit", ["bool", true]]],
      ["select", ["var", 0], ["bool"], ["succeed", ["lit", ["nat", 1]]], ["succeed", ["lit", ["nat", 2]]]],
    ])
  })
  test("foreign recognition still refuses malformed suspended conditionals", () => {
    for (const body of [
      "Effect.suspend(flag => flag ? Effect.succeed(1) : Effect.succeed(2))",
      "Effect.suspend(() => missing ? Effect.succeed(1) : Effect.succeed(2))",
      "true ? Effect.succeed(1) : Effect.succeed(2)",
    ]) {
      const verdicts = recognizeSource(`import { Effect } from "effect"\nexport const main = ${body}`, "legacy-boolean-refusal.ts")
      expect(verdicts.length).toBe(1)
      expect(verdicts[0]!.kind).toBe("refusal")
    }
  })
  test("foreign recognition does not acquire the printed helper", () => {
    const source = 'import { Effect } from "effect"\nexport const main = ifCase(() => true, () => Effect.succeed(1), () => Effect.succeed(2))'
    const verdicts = recognizeSource(source, "printed-boolean-foreign.ts")
    expect(verdicts.length).toBe(1)
    expect(verdicts[0]!.kind).toBe("refusal")
  })
}
