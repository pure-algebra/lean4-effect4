/**
 * Known-answer vectors for scheme-0 addressing: byte strings and the full
 * thirty-two-byte addresses they carry.
 *
 * The vector set is computed, never typed. Its raw pre-images are anchored on
 * the published FIPS 180-2 digests, and its node pre-images are the canonical
 * encodings of the ratified CAS-001 codec rows — read from the manifest and
 * re-encoded here, never copied from it. The generator script and the test
 * suite build the fixture through this one module, so a committed file that
 * drifts from the shipped SHA-256 path fails the gate.
 */
import { Crypto, Effect, Encoding, Schema } from "effect"
import { layerDiskFs } from "./diskFs.ts"
import { readFixtureString } from "./read.ts"
import { Byte, CasNodeInput, ContentId, type StoreFailure } from "../../src/cas/Node.ts"
import { encodeCasNode, makeSha256Address } from "../../src/cas/Store.ts"

/** The committed fixture: written by the generator, read by the suite.
 * URL form for the generator script; package-root-relative path for
 * service reads. */
export const casKatFixtureUrl = new URL("./cas-scheme-0-kat.json", import.meta.url)
export const casKatFixturePath = "test/fixtures/cas-scheme-0-kat.json"

const codecManifestPath =
  "archive/lean-model-0.3/conformance/manifest/CAS-001.json"

/**
 * The production digest path now ships in the package as
 * `Cas.layerCryptoWebCrypto`; the fixture re-exports it so this gate keeps
 * proving the shipped layer against the known-answer vectors.
 */
export { layerCryptoWebCrypto as productionCrypto } from "../../src/cas/Store.ts"

const AddressBytes = Schema.Array(Byte).check(Schema.isLengthBetween(32, 32))

const ManifestNode = Schema.Struct({
  payload: Schema.Array(Byte),
  refs: Schema.Array(Schema.Struct({ addr: AddressBytes, expectedTag: Byte })),
  tag: Byte,
  version: Byte,
})
type ManifestNode = typeof ManifestNode.Type

const CodecManifest = Schema.Struct({
  rows: Schema.Array(Schema.Union([
    Schema.Struct({
      case: Schema.String,
      input: Schema.Struct({ node: ManifestNode }),
    }),
    Schema.Struct({
      case: Schema.String,
      input: Schema.Struct({ bytes: Schema.Array(Byte) }),
    }),
  ])),
})

export interface CasKatVector {
  /** Vector name: the plane it came from, then its case. */
  readonly case: string
  /** Lowercase hex of the digest pre-image — exactly the bytes hashed. */
  readonly bytes: string
  /** Lowercase hex of the full digest: the scheme-0 address. */
  readonly address: ContentId
}

export interface CasKatFixture {
  readonly _provenance: string
  readonly scheme: string
  readonly digest: string
  readonly addressBytes: number
  readonly meaning: string
  readonly vectors: ReadonlyArray<CasKatVector>
}

const ascii = (text: string): Uint8Array => new TextEncoder().encode(text)

/**
 * Raw pre-images. The first two are the FIPS 180-2 published vectors, which
 * anchor the fixture outside this implementation; the rest exercise the empty
 * input, every octet value, and a two-block message.
 */
const rawPreImages: ReadonlyArray<readonly [string, Uint8Array]> = [
  ["raw/empty", new Uint8Array()],
  ["raw/abc", ascii("abc")],
  ["raw/two-block", ascii("abcdbcdecdefdefgefghfghighijhijkijkljklmklmnlmnomnopnopq")],
  ["raw/every-byte-value", Uint8Array.from({ length: 256 }, (_, value) => value)],
  ["raw/profile-name", ascii("cas-http/0")],
]

const casNodeFromManifest = (node: ManifestNode): Effect.Effect<CasNodeInput> =>
  CasNodeInput.makeEffect({
    kind: { version: node.version, tag: node.tag },
    payload: Uint8Array.from(node.payload),
    refs: node.refs.map((ref) => ({
      id: ContentId.make(Encoding.encodeHex(Uint8Array.from(ref.addr))),
      expectedTag: ref.expectedTag,
    })),
  }).pipe(Effect.orDie)

/** Canonical encodings of the ratified codec rows that carry a node. */
const nodePreImages: Effect.Effect<ReadonlyArray<readonly [string, Uint8Array]>> =
  Effect.gen(function* () {
    const text = yield* readFixtureString(codecManifestPath).pipe(
      Effect.orDie,
      Effect.provide(layerDiskFs),
    )
    const manifest = yield* Schema.decodeUnknownEffect(CodecManifest)(
      JSON.parse(text) as unknown,
    ).pipe(Effect.orDie)

    const preImages: Array<readonly [string, Uint8Array]> = []
    for (const row of manifest.rows) {
      if (!("node" in row.input)) continue
      const node = yield* casNodeFromManifest(row.input.node)
      preImages.push([`node/${row.case}`, encodeCasNode(node)])
    }
    return preImages
  })

/**
 * Build the fixture through the shipped address function. Every address here
 * is the full digest of exactly its pre-image bytes: nothing prepended,
 * nothing truncated, lowercase hex.
 */
export const buildCasKatFixture: Effect.Effect<
  CasKatFixture,
  StoreFailure,
  Crypto.Crypto
> = Effect.gen(function* () {
  const address = yield* makeSha256Address
  const preImages = [...rawPreImages, ...yield* nodePreImages]
    .sort(([left], [right]) => left < right ? -1 : left > right ? 1 : 0)

  const vectors: Array<CasKatVector> = []
  for (const [name, bytes] of preImages) {
    vectors.push({
      case: name,
      bytes: Encoding.encodeHex(bytes),
      address: yield* address.digest(bytes),
    })
  }

  return {
    _provenance: "generated by scripts/generate-cas-kat.ts",
    scheme: "cas-scheme-0",
    digest: "SHA-256",
    addressBytes: 32,
    meaning:
      "The scheme-0 address of a byte string is the full thirty-two-byte "
      + "SHA-256 digest of exactly those bytes, lowercase hex — nothing "
      + "prepended, never truncated, no per-address scheme prefix.",
    vectors,
  }
})

/** The one serialization both the generator and the suite produce. */
export const renderCasKatFixture = (fixture: CasKatFixture): string =>
  `${JSON.stringify(fixture, undefined, 2)}\n`
