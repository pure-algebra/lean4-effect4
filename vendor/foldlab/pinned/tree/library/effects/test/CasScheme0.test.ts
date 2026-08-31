/**
 * Scheme-0 addressing under the shipped SHA-256 path.
 *
 * These are production-path observations: the committed known-answer fixture
 * regenerates through the same builder that wrote it, the two published
 * FIPS 180-2 digests anchor the scheme outside this implementation, and the
 * in-memory store's roots are the full digests of exactly the canonical
 * encodings it admitted.
 */
import { expect, it } from "@effect/vitest"
import { Crypto, Effect, Encoding, Layer, Schema } from "effect"
import { Cas } from "../src/index.ts"
import { CasNodeInput, ContentId } from "../src/cas/Node.ts"
import {
  AddressScheme,
  CasStore,
  encodeCasNode,
  layerMemory,
} from "../src/cas/Store.ts"
import { layerDiskFs } from "./fixtures/diskFs.ts"
import { readFixtureString } from "./fixtures/read.ts"
import {
  buildCasKatFixture,
  casKatFixturePath,
  productionCrypto,
  renderCasKatFixture,
} from "./fixtures/casScheme0.ts"

/** The in-memory store over the production digest path, with the digest itself
 * visible so a test can address bytes directly. */
const production = layerMemory.pipe(
  Layer.provideMerge(AddressScheme.layerSha256),
  Layer.provideMerge(productionCrypto),
)

/** Published in FIPS 180-2; the fixture is anchored on these rather than on
 * whatever this implementation happens to produce. */
const fips180_2 = {
  empty: "e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855",
  abc: "ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad",
} as const

const Snapshot = Schema.Struct({
  label: Schema.String,
  counts: Schema.Array(Schema.Number),
})

const digestHex = (bytes: Uint8Array) =>
  Crypto.Crypto.use((platform) => platform.digest("SHA-256", bytes)).pipe(
    Effect.map((digest) => Encoding.encodeHex(digest)),
    Effect.orDie,
  )

it.effect("the shipped digest path reproduces the published FIPS 180-2 vectors", () =>
  Effect.gen(function* () {
    expect(yield* digestHex(new Uint8Array())).toBe(fips180_2.empty)
    expect(yield* digestHex(new TextEncoder().encode("abc"))).toBe(fips180_2.abc)
  }).pipe(Effect.provide(productionCrypto)))

it.effect("the committed known-answer fixture regenerates from the shipped digest path", () =>
  Effect.gen(function* () {
    const regenerated = renderCasKatFixture(yield* buildCasKatFixture)
    const committed = yield* readFixtureString(casKatFixturePath).pipe(
      Effect.orDie,
      Effect.provide(layerDiskFs),
    )
    // Compared byte for byte, less the carriage returns a Windows checkout
    // introduces: no vector, address, or field can drift undetected.
    expect(committed.replaceAll("\r\n", "\n")).toBe(regenerated)
  }).pipe(Effect.provide(productionCrypto)))

it.effect("every committed address is the full digest, lowercase and unprefixed", () =>
  Effect.gen(function* () {
    const fixture = yield* buildCasKatFixture
    expect(fixture.vectors.length).toBeGreaterThan(0)
    for (const vector of fixture.vectors) {
      const bytes = Encoding.decodeHex(vector.bytes)
      if (bytes._tag === "Failure") throw new Error(`${vector.case} carries invalid hex`)
      expect({ case: vector.case, address: vector.address }).toEqual({
        case: vector.case,
        address: yield* digestHex(bytes.success),
      })
      expect(vector.address).toMatch(/^[0-9a-f]{64}$/)
      expect(vector.address.length).toBe(fixture.addressBytes * 2)
    }
  }).pipe(Effect.provide(productionCrypto)))

it.effect("a production put-get-put returns the same root across a reference edge", () =>
  Effect.gen(function* () {
    const store = yield* CasStore
    const child = CasNodeInput.make({
      kind: { version: 0, tag: 0x21 },
      payload: Uint8Array.from([1, 2, 3, 4]),
      refs: [],
    })
    const childId = yield* store.put(child)
    const parent = CasNodeInput.make({
      kind: { version: 0, tag: 0x22 },
      payload: Uint8Array.from([5, 6]),
      refs: [{ id: childId, expectedTag: 0x21 }],
    })

    const first = yield* store.put(parent)
    const loaded = yield* store.load(first)
    const second = yield* store.put(loaded)
    expect(second).toBe(first)

    // Scheme 0: the root is the digest of exactly the canonical encoding.
    expect(first).toBe(ContentId.make(yield* digestHex(encodeCasNode(parent))))
    expect(childId).toBe(ContentId.make(yield* digestHex(encodeCasNode(child))))
  }).pipe(Effect.provide(production)))

it.effect("a production projection put-get-put returns the same root", () =>
  Effect.gen(function* () {
    const projection = Cas.value({ kindTag: 0x23, revision: 1, schema: Snapshot })
    const input = { label: "scheme-0", counts: [3, 1, 4] }

    const first = yield* projection.put(input)
    const restored = yield* projection.get(first)
    expect(restored).toEqual(input)
    expect(yield* projection.put(restored)).toBe(first)
  }).pipe(Effect.provide(production)))
