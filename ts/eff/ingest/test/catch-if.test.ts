import { expect, test } from "bun:test"
import { recognizeSource as ck } from "../ck.ts"
import { recognizeSource as oxc } from "../oxc.ts"
import { compareVerdicts } from "../gate.ts"

const header = 'import { Effect } from "effect"; '
for (const [name, expression] of [
  ["catch", "Effect.catch(Effect.fail(7), error => Effect.succeed(error))"],
  ["true", "Effect.catchIf(Effect.fail(7), error => true, value => Effect.succeed(value))"],
  ["predicate", "Effect.catchIf(Effect.fail(7), error => eq(error, 7), value => Effect.succeed(value))"],
  ["absent fallback", "Effect.catchIf(Effect.fail(7), error => eq(error, 7), value => Effect.succeed(value), undefined)"],
  ["pipe", "Effect.fail(7).pipe(Effect.catchIf(error => eq(error, 7), value => Effect.succeed(value)))"],
] as const) {
  test(`S3 both readers admit ${name} with separate callback scopes`, () => {
    const source = `${header}const program = ${expression};`
    const left = ck(source, `${name}.ts`), right = oxc(source, `${name}.ts`)
    expect(compareVerdicts(left, right).status).toBe("agree")
    for (const verdicts of [left, right]) {
      expect(verdicts).toHaveLength(1)
      const verdict = verdicts[0]!
      expect(verdict.kind).toBe("lifted")
      if (verdict.kind !== "lifted") throw new Error(JSON.stringify(verdict))
      expect(verdict.eff._tag).toBe("catchIf")
      if (verdict.eff._tag !== "catchIf") throw new Error("expected catchIf")
      expect(verdict.eff.handler).toEqual({ _tag: "succeed", value: { _tag: "var", index: 0 } })
      if (name === "true" || name === "catch") {
        expect(verdict.eff.test).toEqual({ _tag: "lit", value: { _tag: "bool", value: true } })
      }
    }
  })
}

test("S3 a predicate binder does not leak into the handler", () => {
  const source = header + 'const program = Effect.catchIf(Effect.fail(7), error => false, value => Effect.succeed(error));'
  for (const recognize of [ck, oxc]) {
    const [verdict] = recognize(source, "escaping.ts")
    expect(verdict?.kind).toBe("refusal")
  }
})


test("S3 a supplied fallback is outside the admitted conditional handler", () => {
  const source = header + 'const program = Effect.catchIf(Effect.fail(7), error => false, value => Effect.succeed(value), value => Effect.succeed(value));'
  for (const recognize of [ck, oxc]) {
    const [verdict] = recognize(source, "fallback.ts")
    expect(verdict?.kind).toBe("refusal")
  }
})
