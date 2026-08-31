/**
 * The conformance vector — the registered replay surface, TypeScript
 * twin of `library/cas/Cas/Vectors/Vectors.lean`.
 *
 * A conformance vector is a store word with a name: a replayable
 * admission history the Lean model emits (`lake exe vectors`) and any
 * runtime replays binding by binding, recomputing every address and
 * re-running admission. These schemas hand-mirror the Lean emitter and
 * are the drift tripwire between the two: a fixture the schemas refuse
 * is a red suite, never a fix-up.
 *
 * The vector registry lives on the Lean side (one list the emitter,
 * the byte-identity gate, and the `index.json` manifest all iterate);
 * this module is the consuming type — it never writes, regenerates,
 * or repairs a fixture (generated-vectors law).
 *
 * The format is DESCRIBED: `vectorSchema`/`indexSchema` are generated
 * Effect Schemas mirroring the Lean codes, and the richer runtime Schemas
 * carry their native persistent representations through the annotation API.
 * The runtime codec is the carrier and the generated representation is the
 * content-addressed identity. On the Lean
 * side the same codes drive the generic codec, whose proved forward
 * and exactness theorems ARE the format's validator.
 */
import { Schema } from "effect"
import * as CanonicalSchema from "./CanonicalSchema.ts"
import { Byte, CasNodeInput, ContentId } from "./Node.ts"
import { indexSchema, vectorSchema } from "./generated/ConformanceVectorSchema.ts"

const manifestStemPattern = /^[a-z0-9]+(?:-[a-z0-9]+)*$(?![\s\S])/u
const manifestFilePattern = /^[a-z0-9]+(?:-[a-z0-9]+)*\.json$(?![\s\S])/u
const reservedPortableStem = /^(?:con|prn|aux|nul|com[1-9]|lpt[1-9])$/u
const portableStem = Schema.makeFilter<string>(
  (input) => reservedPortableStem.test(input)
    ? "manifest name is reserved on Windows"
    : undefined,
  { expected: "a portable manifest name" },
)

/** Portable manifest key: lowercase ASCII words separated by one hyphen. */
export const ManifestName = Schema.String.check(
  Schema.isPattern(manifestStemPattern),
  portableStem,
)

/** Portable manifest filename. Separators, traversal, controls, confusables,
 * and platform-specific spellings are outside the accepted language. */
export const ManifestFileName = Schema.String.check(
  Schema.isPattern(manifestFilePattern),
  Schema.makeFilter((input) => {
    const stem = input.slice(0, -".json".length)
    return reservedPortableStem.test(stem)
      ? "manifest filename is reserved on Windows"
      : undefined
  }, { expected: "a portable manifest filename" }),
)

/** The vector wire schema version this consumer understands. */
export const SchemaVersion = 1

/** The digest scheme the fixtures declare: scheme-0 SHA-256. */
export const DigestScheme = "sha256-scheme0"

/** The vector format as canonical schema — GENERATED mirrors of the
 * Lean codes (`lake exe emitwire`, byte-identity-gated): the
 * content-addressed identity of the file format itself. */
export * from "./generated/ConformanceVectorSchema.ts"

/** One typed reference: the expected kind tag and the hex address. */
export const VectorRef = Schema.Struct({
  expectedTag: Byte,
  id: ContentId,
})
export type VectorRef = typeof VectorRef.Type

/** One node: scalar header fields, hex payload, ordered references. */
export const VectorNode = Schema.Struct({
  version: Byte,
  tag: Byte,
  payload: Schema.Uint8ArrayFromHex,
  refs: Schema.Array(VectorRef),
})
export type VectorNode = typeof VectorNode.Type

/** One binding: the Lean-computed address and the node it binds. */
export const VectorBinding = Schema.Struct({
  address: ContentId,
  node: VectorNode,
})
export type VectorBinding = typeof VectorBinding.Type

/** A registered conformance vector: metadata plus the store word in
 * admission order. Carries `vectorSchema` — the format's canonical,
 * content-addressed identity — through the annotation API. */
export const ConformanceVector = Schema.Struct({
  schemaVersion: Schema.Literal(SchemaVersion),
  digest: Schema.Literal(DigestScheme),
  name: ManifestName,
  description: Schema.String,
  word: Schema.Array(VectorBinding),
}).pipe(CanonicalSchema.annotate(vectorSchema))
export type ConformanceVector = typeof ConformanceVector.Type

/** One index row: where a fixture lives and what its word binds. */
export const IndexEntry = Schema.Struct({
  name: ManifestName,
  file: ManifestFileName,
  description: Schema.String,
  bindings: Schema.Int,
  root: ContentId,
})
export type IndexEntry = typeof IndexEntry.Type

/** The `index.json` manifest — the tracking surface over the Lean
 * registry, carrying `indexSchema` as its canonical identity. */
export const VectorIndex = Schema.Struct({
  schemaVersion: Schema.Literal(SchemaVersion),
  digest: Schema.Literal(DigestScheme),
  vectors: Schema.Array(IndexEntry),
}).pipe(CanonicalSchema.annotate(indexSchema))
export type VectorIndex = typeof VectorIndex.Type

/** Project a vector node onto the store's boundary shape — what
 * `CasStore.put` admits during a replay. */
export const toNodeInput = (node: VectorNode): CasNodeInput =>
  CasNodeInput.make({
    kind: { version: node.version, tag: node.tag },
    payload: node.payload,
    refs: node.refs.map((ref) => ({ id: ref.id, expectedTag: ref.expectedTag })),
  })
