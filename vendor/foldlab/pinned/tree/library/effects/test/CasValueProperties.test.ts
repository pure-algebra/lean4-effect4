/**
 * Deterministic generative checks at the public value-projection seam.
 * Deviant Unicode must round-trip by value; malformed text and arbitrary
 * invalid UTF-8 must fail through the typed projection error, never defect.
 */
import { expect, it } from "@effect/vitest"
import { cast, Effect, Schema } from "effect"
import { Cas } from "../src/index.ts"
import { CasNodeInput } from "../src/cas/Node.ts"
import { CasStore, layerMemoryWith } from "../src/cas/Store.ts"
import { deterministicAddress } from "./fixtures/address.ts"

const TextValue = Cas.value({
  kindTag: 0x73,
  revision: 0,
  schema: Schema.String,
})

const makeRandom = (seed: number): (() => number) => {
  let state = seed >>> 0
  return () => {
    state ^= state << 13
    state ^= state >>> 17
    state ^= state << 5
    return state >>> 0
  }
}

const deviantCodeUnits = [
  0x0000,
  0x0008,
  0x0009,
  0x000a,
  0x000d,
  0x001f,
  0x0022,
  0x005c,
  0x007f,
  0x0085,
  0x034f,
  0x061c,
  0x200b,
  0x200d,
  0x2028,
  0x2029,
  0x202e,
  0x2066,
  0xd800,
  0xdbff,
  0xdc00,
  0xdfff,
  0xfffd,
  0xfffe,
  0xffff,
] as const

const generatedString = (random: () => number, maximumLength = 48): string => {
  const length = random() % (maximumLength + 1)
  const units: Array<number> = []
  for (let index = 0; index < length; index += 1) {
    units.push(random() % 3 === 0
      ? deviantCodeUnits[random() % deviantCodeUnits.length]!
      : random() & 0xffff)
  }
  return String.fromCharCode(...units)
}

it.effect("deviant Unicode strings round-trip with stable content identity", () =>
  Effect.gen(function* () {
    const random = makeRandom(0xc45a_11ce)
    for (let sample = 0; sample < 256; sample += 1) {
      const value = generatedString(random)
      const first = yield* TextValue.put(value)
      const second = yield* TextValue.put(value)
      const decoded = yield* TextValue.get(first)
      expect({ sample, decoded, stable: second === first }).toEqual({
        sample,
        decoded: value,
        stable: true,
      })
    }
  }).pipe(Effect.provide(layerMemoryWith(deterministicAddress()))))

it.effect("nonsense text and invalid UTF-8 always reject as typed projection failures", () =>
  Effect.gen(function* () {
    const random = makeRandom(0xbad0_c0de)
    const encoder = new TextEncoder()
    const store = yield* CasStore

    for (let sample = 0; sample < 128; sample += 1) {
      const tailLength = random() % 32
      const invalidUtf8 = new Uint8Array(tailLength + 1)
      invalidUtf8[0] = 0xff
      for (let index = 1; index < invalidUtf8.length; index += 1) {
        invalidUtf8[index] = random() & 0xff
      }
      const nonsenseText = encoder.encode(`nonsense:${generatedString(random)}`)
      const wrongJsonShape = encoder.encode(JSON.stringify(generatedString(random)))

      for (const payload of [invalidUtf8, nonsenseText, wrongJsonShape]) {
        const id = yield* store.put(CasNodeInput.make({
          kind: { version: 0, tag: TextValue.kindTag },
          payload,
          refs: [],
        }))
        const result = yield* TextValue.get(cast(id)).pipe(Effect.result)
        expect({ sample, resultTag: result._tag }).toEqual({
          sample,
          resultTag: "Failure",
        })
        if (result._tag === "Failure") {
          expect(result.failure._tag).toBe("ProjectionCodecFailure")
        }
      }
    }
  }).pipe(Effect.provide(layerMemoryWith(deterministicAddress()))))
