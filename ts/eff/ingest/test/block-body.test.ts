import { expect, test } from "bun:test"
import { recognizeSource as ck } from "../ck.ts"
import { recognizeSource as oxc } from "../oxc.ts"
import { compareVerdicts } from "../gate.ts"
import { taxonomy } from "../../taxonomy.gen.ts"

// A statement body of `if` and `while (true)` inside `Effect.gen` is a block, or both readers
// refuse it. The oxc reader once read a body that was no block as an empty list, so
// `if (held) return 1047` lifted to an `ifElse` with an empty branch, and the program answered
// the fall-through value. The compiler reader refused it, so the two disagreed.
// Fixtures: docs/research/2026-10-16-dogfood-data/ts/foreign-if/ (the dogfood note, §6).

const gen = (body: string) =>
  `import { Effect } from "effect"\nexport const main = Effect.gen(function* () {\n  const held = yield* Effect.succeed(true)\n  ${body}\n})\n`
const nodeDetail = (value: string) =>
  taxonomy.find(t => t.code === "E-NODE")!.detail.replace("{value}", value)

for (const [name, body, value] of [
  ["a then branch with no braces", "if (held) return 1047\n  return 0", "if body"],
  ["a then branch that returns a yield, with no braces", "if (held) return yield* Effect.succeed(1047)\n  return 0", "if body"],
  ["an else branch with no braces", "if (held) { return 1047 } else return 0", "if body"],
  ["an else if", "if (held) { return 1047 } else if (held) { return 1 } else { return 0 }", "if body"],
  ["a loop body with no braces", "while (true) yield* Effect.succeed(1)\n  return 0", "statement"],
] as const) {
  test(`both readers refuse ${name}, with one refusal`, () => {
    const source = gen(body)
    const left = ck(source, "body.ts"), right = oxc(source, "body.ts")
    expect(compareVerdicts(left, right).status).toBe("agree")
    for (const verdicts of [left, right]) {
      expect(verdicts).toHaveLength(1)
      const verdict = verdicts[0]!
      expect(verdict.kind).toBe("refusal")
      if (verdict.kind !== "refusal") throw new Error(JSON.stringify(verdict))
      expect(verdict.code).toBe("E-NODE")
      expect(verdict.detail).toBe(nodeDetail(value))
    }
  })
}

test("control: both readers lift a then branch in braces, and the branch holds its return", () => {
  const source = gen("if (held) { return 1047 }\n  return 0")
  const left = ck(source, "braced.ts"), right = oxc(source, "braced.ts")
  expect(compareVerdicts(left, right).status).toBe("agree")
  const verdict = right[0]!
  expect(verdict.kind).toBe("lifted")
  if (verdict.kind !== "lifted") throw new Error(JSON.stringify(verdict))
  expect(JSON.stringify(verdict.eff)).toContain('"thenB":[{"_tag":"ret","value":{"_tag":"lit","value":{"_tag":"nat","value":1047}}}]')
})
