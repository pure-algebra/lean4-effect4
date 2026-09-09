import { expect, test } from "bun:test"
import { recognizeSource as ck } from "../ck.ts"
import { recognizeSource as oxc } from "../oxc.ts"
import { compareVerdicts } from "../gate.ts"
import { canonJson, sourceEditKey } from "../contract.ts"
import { parseSync } from "oxc-parser"

test("T4 generated programs and adversarial form edits retain engine agreement", () => {
  for (let seed = 0; seed < 64; seed++) {
    const term = String((seed * 17 + 5) % 97)
    const expression = `Effect.flatMap(Effect.succeed(${term}), (x) => Effect.succeed(x))`
    for (const edited of [expression, `(${expression})`, `(${expression}) as any`, expression.replace("Effect.flatMap", "Effect?.flatMap"), expression.replace(term, "0x10")]) {
      const source = `import { Effect } from "effect"; const p = ${edited};`
      expect(compareVerdicts(ck(source, "generated.ts"), oxc(source, "generated.ts")).status).toBe("agree")
    }
  }
})

test("T5 declared result mutants are detected by the actual agreement primitive", () => {
  const source = 'import { Effect, Context } from "effect"; const K = Context.Service<number>("K"); const p = Effect.service(K);'
  const original = ck(source, "mutants.ts"), v = original[0]!
  expect(v.kind).toBe("lifted")
  if (v.kind !== "lifted") return
  for (const mutant of [{ ...v, wireHex: v.wireHex + "00" }, { ...v, keys: [] }, { ...v, unit: { ...v.unit, name: "changed" } }, { ...v, eff: { _tag: "succeed" as const, value: { _tag: "lit" as const, value: { _tag: "unit" as const } } } }]) {
    expect(compareVerdicts(original, [mutant]).status).toBe("disagree")
  }
  expect(compareVerdicts(original, []).status).toBe("disagree")
})

test("T6 recognition depends on the source rather than prior calls", () => {
  const source = 'import { Effect } from "effect"; const p = Effect.succeed(1);'
  for (const engine of [ck, oxc]) {
    const before = canonJson(engine(source, "pure.ts").map(sourceEditKey))
    engine('import { Effect, Context } from "effect"; const K = Context.Service<number>("K"); const p = Effect.service(K);', "other.ts")
    expect(canonJson(engine(source, "pure.ts").map(sourceEditKey))).toBe(before)
  }
})

test("T8 audits the pinned parser's nonstandard wrappers and import metadata", () => {
  const p = parseSync("shapes.ts", 'import type { Effect as T } from "effect"; import * as E from "effect/Effect"; (E.succeed(1)); E?.succeed(1); E!.succeed(1);', { lang: "ts", sourceType: "module" })
  expect(p.errors).toHaveLength(0)
  const statements = p.program.body.filter(s => s.type === "ExpressionStatement")
  expect(statements.map(s => s.expression.type)).toEqual(["ParenthesizedExpression", "ChainExpression", "CallExpression"])
  expect(p.module.staticImports[0]?.entries[0]?.isType).toBe(true)
  expect(String(p.module.staticImports[1]?.entries[0]?.importName.kind)).toBe("NamespaceObject")
})
