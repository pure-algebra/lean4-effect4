/** Property checks for hostile text and native codec boundaries. */
import { expect, it } from "@effect/vitest"
import { Effect, Encoding, Equal, Hash, Option, Schema } from "effect"
import { Cas } from "../src/index.ts"
import { WrongKindReference } from "../src/cas/Node.ts"
import {
  BlobManifestPayload,
  Uint32,
  Uint64,
} from "../src/internal/blobGraph.ts"
import { decodeValidatedHex } from "../src/internal/bytes.ts"
import { decide, type WireFacts } from "../src/server/Protocol.ts"

const reserved = new Set([
  "con",
  "prn",
  "aux",
  "nul",
  ...Array.from({ length: 9 }, (_, index) => `com${index + 1}`),
  ...Array.from({ length: 9 }, (_, index) => `lpt${index + 1}`),
])

const isPortableStem = (candidate: string): boolean => {
  if (candidate.length === 0 || reserved.has(candidate)) return false
  return candidate.split("-").every((part) => part.length > 0
    && [...part].every((character) =>
      (character >= "a" && character <= "z")
      || (character >= "0" && character <= "9")))
}

it.effect.prop(
  "manifest names accept exactly the portable ASCII language",
  [Schema.String],
  ([candidate]) => Effect.sync(() => {
    const name = Schema.decodeOption(Cas.ConformanceVector.ManifestName)(candidate)
    const file = Schema.decodeOption(Cas.ConformanceVector.ManifestFileName)(candidate)
    expect(Option.isSome(name)).toBe(isPortableStem(candidate))
    expect(Option.isSome(file)).toBe(
      candidate.endsWith(".json")
      && isPortableStem(candidate.slice(0, -".json".length)),
    )
  }),
  { fastCheck: { numRuns: 512 } },
)

it("manifest names reject traversal, controls, confusables, and reserved devices", () => {
  const deviants = [
    "../x.json",
    "..\\x.json",
    "/x.json",
    "x/y.json",
    "x\\y.json",
    "x\0.json",
    "x\n.json",
    "x\r.json",
    "x\u202e.json",
    "x\u200d.json",
    "ｘ.json",
    "x😀.json",
    "X.json",
    "x--y.json",
    "x-.json",
    ".json",
    "con.json",
    "lpt9.json",
  ]
  for (const candidate of deviants) {
    expect({
      candidate,
      accepted: Option.isSome(
        Schema.decodeOption(Cas.ConformanceVector.ManifestFileName)(candidate),
      ),
    }).toEqual({ candidate, accepted: false })
  }
})

const openPolicy = { maxBatchKeys: 8, maxNodeBytes: 4096 }
const wireFacts = (path: string): WireFacts => ({
  authorization: undefined,
  body: new Uint8Array(0),
  contentType: "application/octet-stream",
  method: "GET",
  path,
  profile: "cas-http/0",
})

it.effect.prop(
  "resource paths never admit deviant text around a content identifier",
  [Schema.String],
  ([path]) => Effect.sync(() => {
    const decision = decide(openPolicy, wireFacts(path))
    const expected = path.length === 69
      && path.startsWith("/cas/")
      && Option.isSome(Schema.decodeOption(Cas.ContentId)(path.slice(5)))
    expect(decision._tag === "Accepted").toBe(expected)
  }),
  { fastCheck: { numRuns: 512 } },
)

it.effect.prop(
  "Effect's native hex codec round-trips arbitrary bytes",
  [Schema.Uint8Array],
  ([bytes]) => Effect.sync(() => {
    const encoded = Encoding.encodeHex(bytes)
    expect(decodeValidatedHex(encoded)).toEqual(bytes)
  }),
  { fastCheck: { numRuns: 256 } },
)

it.effect.prop(
  "the exact manifest codec round-trips native uint32 and uint64 domains",
  [Uint32, Uint64, Uint32],
  ([recipeId, totalBytes, leafCount]) => Effect.gen(function* () {
    const value = { recipeId, totalBytes, leafCount }
    const encoded = yield* Schema.encodeEffect(BlobManifestPayload)(value)
    expect(encoded).toHaveLength(16)
    expect(yield* Schema.decodeEffect(BlobManifestPayload)(encoded)).toEqual(value)
  }),
  { fastCheck: { numRuns: 256 } },
)

it("Schema tagged errors already provide Effect structural equality and hashing", () => {
  const id = Cas.ContentId.make("ab".repeat(32))
  const left = new WrongKindReference({ ref: id, expectedTag: 1, actualTag: 2 })
  const right = new WrongKindReference({ ref: id, expectedTag: 1, actualTag: 2 })
  expect(Equal.equals(left, right)).toBe(true)
  expect(Hash.hash(left)).toBe(Hash.hash(right))
})
