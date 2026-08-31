/**
 * CAS-004 binding: the canonical value encoding, bound to the model.
 *
 * The Lean model computes each structure's canonical bytes through its
 * compact renderer; this suite reproduces them through `canonicalJson`
 * byte-for-byte — codepoint key order, integer-only numbers, and the
 * exact `JSON.stringify` escape set are all model-pinned, so a second
 * writer cannot split a value's content identity. The refusals the
 * model makes unrepresentable (fractional and unsafe numbers) are
 * asserted TypeScript-side.
 *
 * The printer is imported from `src/internal/canonicalJson.ts` — the
 * module the bytes are actually computed in — and NOT through the
 * `src/cas/Value.ts` re-export it used to arrive by. That import path
 * is the binding: the store computes a value node's address over these
 * bytes, so the module that writes them is the one the model's vectors
 * have to hold, and a suite that only ever reached it through a
 * re-export was one refactor away from leaving it unbound. The
 * re-export is asserted separately, as an identity, so the public door
 * and these bytes cannot fork either.
 *
 * Two anchors, because the printer answers to two model generations:
 *
 * - CAS-004's known-answer rows (`archive/lean-model-0.3/conformance/
 *   manifest/CAS-004.json`), which state the encoding as bytes for the
 *   cases that decide it — astral keys, the escape set, the safe-integer
 *   bounds, nesting.
 * - the LIVE emitted corpus (`library/cas/vectors/`), whose schema-sort
 *   node carries 2,539 bytes of the current model's own `renderCompact`
 *   output. Nothing is hand-written there: the assertion re-renders the
 *   payload's parsed value and demands the same bytes back.
 */
import { expect, it } from "@effect/vitest"
import { Effect, Encoding, Schema } from "effect"
import { canonicalJson } from "../src/internal/canonicalJson.ts"
import { SchemaKindTag } from "../src/internal/kindTags.ts"
import { canonicalJson as reExportedCanonicalJson } from "../src/cas/Value.ts"
import { loadVectors } from "./fixtures/vectors.ts"
import {
  assertFamilyRows,
  ManifestModel,
  type FamilyBinding,
} from "./conformance/harness.ts"

const Cas004Row = Schema.Struct({
  case: Schema.String,
  expect: Schema.Struct({ bytes: Schema.Array(Schema.Natural) }),
  input: Schema.Struct({ value: Schema.Unknown }),
})

const binding: FamilyBinding<"CAS-004", typeof Cas004Row> = {
  family: "CAS-004",
  model: ManifestModel,
  row: Cas004Row,
  hasOracle: false,
}

it.effect("CAS-004 consumes every ratified canonical-encoding row structurally", () =>
  assertFamilyRows(binding, (row) => Effect.sync(() => ({
    bytes: Array.from(new TextEncoder().encode(canonicalJson(row.input.value))),
  }))))

it.effect("the live emitted vectors' own canonical bytes re-render identically", () =>
  Effect.gen(function* () {
    const { vectors } = yield* loadVectors
    // The schema sort is the one emitted sort whose payload IS a
    // canonical rendering (the `{revision, value}` envelope); every
    // other sort's payload is a binary frame or opaque content. The
    // selection is asserted non-empty because an empty one would make
    // the loop below pass by doing nothing.
    const rendered = vectors.flatMap((vector) =>
      vector.word
        .filter((node) => node.node.tag === SchemaKindTag)
        .map((node) => ({ vector: vector.name, payload: node.node.payload }))
    )
    expect(rendered.length).toBeGreaterThan(0)
    for (const { vector, payload } of rendered) {
      const parsed: unknown = JSON.parse(
        new TextDecoder("utf-8", { fatal: true }).decode(payload),
      )
      expect(`${vector}: ${Encoding.encodeHex(
        new TextEncoder().encode(canonicalJson(parsed)),
      )}`).toBe(`${vector}: ${Encoding.encodeHex(payload)}`)
    }
  }))

it.effect("`Cas.Value` re-exports this printer instead of spelling a second one", () =>
  Effect.sync(() => {
    // `Value.ts` says it re-exports the one spelling. An identity check
    // is what makes that a fact: were it ever to wrap or reimplement
    // the printer, the public door would answer bytes the vectors above
    // never held to the model.
    expect(reExportedCanonicalJson).toBe(canonicalJson)
  }))

it.effect("numbers outside the safe-integer domain are refused, not formatted", () =>
  Effect.sync(() => {
    expect(() => canonicalJson(1.5)).toThrow(TypeError)
    expect(() => canonicalJson(0.1)).toThrow(TypeError)
    expect(() => canonicalJson(Number.MAX_SAFE_INTEGER + 1)).toThrow(TypeError)
    expect(() => canonicalJson(Number.NaN)).toThrow(TypeError)
    expect(() => canonicalJson(Number.POSITIVE_INFINITY)).toThrow(TypeError)
    // The safe bounds themselves encode.
    expect(canonicalJson(Number.MAX_SAFE_INTEGER)).toBe("9007199254740991")
    expect(canonicalJson(Number.MIN_SAFE_INTEGER)).toBe("-9007199254740991")
  }))
