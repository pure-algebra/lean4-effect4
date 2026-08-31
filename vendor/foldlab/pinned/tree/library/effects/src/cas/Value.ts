/**
 * Typed values projected through the content-addressed store.
 *
 * The digest payload is canonical JSON of the Schema's Encoded form inside
 * the exact envelope `{ revision, value }`. Object keys are ordered by
 * Unicode codepoint (equal to UTF-8 byte order) at every depth, array order
 * is preserved, only safe integers are admitted as numbers, and the
 * resulting text is UTF-8 encoded.
 * The kind tag and revision together version this projection: the kind tag is
 * the CAS node tag and the revision is carried in the payload envelope.
 *
 * Typed references (CAS-005): a schema field built with `ref` holds a
 * `Root<B>` — a typed content id, decoded lazily, never a loaded
 * child. On the wire the field is a positional `{"$ref": k}` marker in
 * the payload and the k-th entry of the node's reference array, so the
 * store's admission law checks every typed edge (`WrongKindReference`)
 * with no projection-side machinery. Construction is leaf-up: putting
 * a value whose references are not yet admitted fails with the store's
 * `DanglingReference`.
 *
 * This is a runtime projection contract only. It makes no canonicality or
 * equivalence claim about the independent Lean printer.
 */
import {
  cast,
  Effect,
  Option,
  Predicate,
  Result,
  Schema,
  SchemaGetter,
  SchemaIssue,
  SchemaRepresentation,
} from "effect"
// Type-only: the arbitrary hooks are handed their own `fc`, so nothing
// test-shaped enters the library's runtime graph.
import type * as FastCheck from "effect/testing/FastCheck"
import {
  Byte,
  CasNodeInput,
  ContentId,
  UnknownKind,
  type CasError,
  type ContentId as ContentIdType,
} from "./Node.ts"
import { CasLoader, CasSchemeVersion, CasStore } from "./Store.ts"
import { bytesEqual } from "../internal/bytes.ts"
import { ReservedKindTags } from "../internal/kindTags.ts"
import {
  markerize,
  RefSentinelKey,
  resolveMarkers,
  violationReason,
} from "../internal/refMarkers.ts"

declare const RootTypeId: unique symbol

/** A content root whose decoded value is tracked phantasmally. The runtime
 * descriptor still checks the resident node kind before decoding. */
export type Root<A> = ContentIdType & {
  readonly [RootTypeId]: {
    readonly value: (value: A) => A
    readonly expectedKindTag: Byte
  }
}

export class ProjectionCodecFailure
  extends Schema.TaggedError<ProjectionCodecFailure>()(
    "ProjectionCodecFailure",
    {
      direction: Schema.Literals(["encode", "decode"]),
      id: Schema.optionalKey(ContentId),
      issue: Schema.String,
    },
  ) {}

export type ProjectionError = CasError | ProjectionCodecFailure

/** A projection revision: a non-negative safe integer, validated by
 * schema at construction. */
export const Revision = Schema.Int.check(
  Schema.isBetween({ minimum: 0, maximum: Number.MAX_SAFE_INTEGER }),
)
export type Revision = typeof Revision.Type

const ProjectionEnvelope = Schema.Struct({
  revision: Revision,
  value: Schema.Json,
})

export interface DecodedEnvelope {
  readonly revision: Revision
  readonly value: Schema.Json
}

export interface ValueOptions<A> {
  readonly kindTag: Byte
  readonly revision: Revision
  readonly schema: Schema.Codec<A, Schema.Json, never, never>
}

export interface CasValue<A> {
  /** The projection's CAS node tag — what a typed reference to this
   * projection expects at its target. */
  readonly kindTag: Byte
  readonly put: (value: A) => Effect.Effect<Root<A>, ProjectionError, CasStore>
  /** Reads require only the load law, so typed values decode over
   * read-only compositions — a path-reader host included. */
  readonly get: (root: Root<A>) => Effect.Effect<A, ProjectionError, CasLoader>
}

const utf8Encoder = new TextEncoder()
const utf8Decoder = new TextDecoder("utf-8", { fatal: true })

const projectionFailure = (
  direction: "encode" | "decode",
  issue: string,
  id?: ContentIdType,
): ProjectionCodecFailure =>
  new ProjectionCodecFailure(
    id === undefined ? { direction, issue } : { direction, issue, id },
  )

/** The canonical value encoding (CAS-004) — one spelling, MOVED to
 * `../internal/canonicalJson.ts` so seams below the store law (the
 * word log) can speak it without importing this module, and
 * re-exported here so every existing consumer keeps its door. */
export { canonicalJson } from "../internal/canonicalJson.ts"
import { canonicalJson } from "../internal/canonicalJson.ts"

const payloadFor = (
  revision: number,
  encoded: Schema.Json,
): Effect.Effect<Uint8Array, ProjectionCodecFailure> =>
  Effect.try({
    try: () => utf8Encoder.encode(canonicalJson({ revision, value: encoded })),
    catch: (issue) => projectionFailure("encode", String(issue)),
  })

/** Decode and re-verify one canonical `{revision, value}` envelope —
 * shared with the schema plane; not part of the front door. The address
 * is the failure's provenance and nothing else, so it is optional: a
 * caller holding payload bytes whose address is not yet computed still
 * gets the same decode and the same refusals. */
export const decodedVersionedEnvelope = (
  payload: Uint8Array,
  id?: ContentIdType,
): Effect.Effect<DecodedEnvelope, ProjectionCodecFailure> =>
  Effect.try({
    try: () => {
      const text = utf8Decoder.decode(payload)
      const parsed: unknown = JSON.parse(text)
      const canonical = utf8Encoder.encode(canonicalJson(parsed))
      if (!bytesEqual(canonical, payload)) {
        throw new TypeError("Projection payload is not canonical JSON")
      }
      return parsed
    },
    catch: (issue) => projectionFailure("decode", String(issue), id),
  }).pipe(
    Effect.flatMap((parsed) =>
      Schema.decodeUnknownEffect(ProjectionEnvelope, {
        onExcessProperty: "error",
      })(parsed).pipe(
        Effect.mapError((issue) =>
          projectionFailure("decode", String(issue), id)
        ),
      )
    ),
  )

/** Decode and re-verify one canonical envelope at an expected revision. */
export const decodedEnvelope = (
  payload: Uint8Array,
  revision: number,
  id: ContentIdType,
): Effect.Effect<Schema.Json, ProjectionCodecFailure> =>
  decodedVersionedEnvelope(payload, id).pipe(
    Effect.flatMap((envelope) => envelope.revision === revision
      ? Effect.succeed(envelope.value)
      : Effect.fail(projectionFailure(
          "decode",
          `Projection revision does not match ${revision}`,
          id,
        ))),
  )

const makeRoot = <A>(id: ContentIdType): Root<A> => cast(id)

/** The wire shape of a typed reference before marker assignment. */
const sentinelSchema = Schema.Struct({
  [RefSentinelKey]: Schema.Struct({ id: ContentId, tag: Byte }),
})

/** The decoded shape of an encoded typed reference: the sentinel a
 * `foldlab/cas/ref` declaration admits, before marker assignment. Named
 * because generated code has to spell it. */
export type ReferenceSentinel = typeof sentinelSchema.Type

/** Stable Effect Schema persistence identity for a typed CAS reference. */
export const ReferenceRepresentationId = "foldlab/cas/ref"

const strictOptions = {
  onExcessProperty: "error",
} satisfies import("effect/SchemaAST").ParseOptions

/** The one import generated code needs to name the estate's own reference
 * constructor. The package exports a single entry point, so both the
 * constructor and the sentinel type are reached through `Cas`. */
const referenceImportDeclaration = `import { Cas } from "@foldlab/cas"`

/** Lowercase hex, the alphabet `ContentId` admits. */
const hexDigits = [..."0123456789abcdef"]

/** An address-shaped generator: 64 lowercase hex digits, the exact shape
 * `ContentId` checks. Written against the hook's own `fc` so no test-only
 * module is pulled into the library's runtime graph. */
const arbitraryContentId = (fc: typeof FastCheck): FastCheck.Arbitrary<ContentIdType> =>
  fc.array(fc.constantFrom(...hexDigits), { maxLength: 64, minLength: 64 })
    .map((digits) => ContentId.make(digits.join("")))

/** The encoded reference declaration used by canonical schema identity.
 *
 * It ships the whole declaration contract, so a foldlab reference is
 * indistinguishable from a built-in across persistence (`representation`),
 * revival (`referenceRepresentationReviver`), code generation (`toCode`),
 * and instance generation (`toArbitrary`). */
export const referenceRepresentation = (
  expectedTag: Byte,
): Schema.declare<ReferenceSentinel> =>
  Schema.declare<ReferenceSentinel>(
    (candidate): candidate is ReferenceSentinel =>
      Option.isSome(
        Schema.decodeUnknownOption(sentinelSchema, strictOptions)(candidate),
      ),
    {
      representation: {
        id: ReferenceRepresentationId,
        payload: expectedTag,
      },
      toArbitrary: () => (fc) =>
        arbitraryContentId(fc).map((id) => ({
          [RefSentinelKey]: { id, tag: expectedTag },
        })),
      toCode: () => ({
        importDeclarations: [referenceImportDeclaration],
        runtime: `Cas.CanonicalSchema.ref(${expectedTag})`,
        Type: "Cas.ReferenceSentinel",
      }),
    },
  )

/** Reconstruct the encoded reference declaration from persisted identity. */
export const referenceRepresentationReviver =
  SchemaRepresentation.makeDeclarationReviver(
    ReferenceRepresentationId,
    Byte,
    ({ payload }) => refWithTag(Byte.make(payload)),
  )

/** The one reference-codec law: sentinel on the wire, `Root` in the
 * value, the expected kind tag stamped at encode and demanded at
 * decode. The encoded side arrives already built, because only the
 * thunked entry point needs to defer it: `Suspend` is a representation
 * node of its own, so suspending a tag that is already data would put a
 * `Suspend` wrapper into the persisted identity and revival would no
 * longer answer the bytes it was revived from. The tag stays a thunk
 * because the thunked entry point still needs it lazily. */
const refCodec = <B>(
  reference: Schema.Codec<ReferenceSentinel, typeof sentinelSchema.Encoded>,
  expectedTag: () => Byte,
): Schema.Codec<Root<B>, typeof sentinelSchema.Encoded> =>
  reference.pipe(Schema.decodeTo(
    Schema.declare<Root<B>>(
      (candidate): candidate is Root<B> => Predicate.isString(candidate),
      // The decoded side of a reference is an address. Generation derives
      // through it rather than throwing on an opaque declaration; the
      // codec's own encode stamps the expected tag, so a generated root
      // round-trips.
      { toArbitrary: () => (fc) => cast(arbitraryContentId(fc)) },
    ),
    {
      decode: SchemaGetter.transformOrFail((sentinel, options) => {
        const expected = expectedTag()
        return sentinel[RefSentinelKey].tag === expected
          ? Effect.succeed(makeRoot<B>(sentinel[RefSentinelKey].id))
          : Effect.fail(new SchemaIssue.InvalidValue(
              { message: `reference expects kind tag ${expected}, node carries ${sentinel[RefSentinelKey].tag}` },
              sentinel,
              options,
            ))
      }),
      encode: SchemaGetter.transform((root: Root<B>) => ({
        [RefSentinelKey]: { id: ContentId.make(root), tag: expectedTag() },
      })),
    },
  ))

/** A typed-reference field: `Root<B>` in the decoded value, a
 * positional marker plus a reference-array entry on the wire. The
 * target projection arrives as a thunk so self- and mutual reference
 * elaborate; its kind tag is stamped into the reference at encode and
 * demanded of it at decode. */
export const ref = <B>(
  target: () => CasValue<B>,
): Schema.Codec<Root<B>, typeof sentinelSchema.Encoded> =>
  refCodec<B>(
    Schema.suspend(() => referenceRepresentation(target().kindTag)),
    () => target().kindTag,
  )

/** A typed-reference field pinned to a kind tag directly — the form a
 * canonical schema's `Ref` compiles to, where the tag is data and no
 * target projection exists yet. The decoded root's value type stays
 * `unknown` until references carry their target schema's address (a
 * schema-commission item). This is also what the reviver rebuilds, so
 * it lowers back to the bare declaration it was revived from. */
export const refWithTag = (
  tag: Byte,
): Schema.Codec<Root<unknown>, typeof sentinelSchema.Encoded> =>
  refCodec<unknown>(referenceRepresentation(tag), () => tag)

/** The projection constructor WITHOUT the reserved-tag door — the
 * library's own way of reading a plane it owns.
 *
 * The door on `value` below exists to stop a CALLER-DEFINED projection
 * from giving a registry row a second public interpretation. A plane the
 * library itself owns is the opposite case: `Cas.CanonicalSchema` reads
 * the `schema` row (0x53) and `Cas.Annotations` reads the `annotation`
 * row (0x41), and each is the ONE interpretation of its row rather than
 * a second one. Before decision 40 the annotation plane rode a working
 * tag and needed no exception; ratifying that tag as a registry row is
 * what made the distinction have to be spelled.
 *
 * NOT exported from the package. A caller reaching a reserved row goes
 * through the module that owns it, which is the whole content of the
 * rule. */
export const libraryValue = <A>(options: ValueOptions<A>): CasValue<A> => {
  const kindTag = Byte.make(options.kindTag)
  const revision = Revision.make(options.revision)

  const put: CasValue<A>["put"] = Effect.fn("CasValue.put")(
    function* (input) {
      const store = yield* CasStore
      const encoded = yield* Schema.encodeUnknownEffect(options.schema)(input).pipe(
        Effect.mapError((issue) => projectionFailure("encode", String(issue))),
      )
      // Reference sentinels become positional markers (CAS-005): the
      // k-th marker in canonical byte order carries index k, and the
      // references ride the node, where admission checks their kinds.
      const markerized = markerize(encoded)
      if (Result.isFailure(markerized)) {
        return yield* projectionFailure(
          "encode",
          violationReason(markerized.failure),
        )
      }
      const payload = yield* payloadFor(
        revision,
        markerized.success.payload,
      )
      const id = yield* store.put(CasNodeInput.make({
        kind: { version: CasSchemeVersion, tag: kindTag },
        payload,
        refs: markerized.success.refs,
      }))
      return makeRoot<A>(id)
    },
  )

  const get: CasValue<A>["get"] = Effect.fn("CasValue.get")(
    function* (root) {
      const loader = yield* CasLoader
      const node = yield* loader.load(root)
      if (node.kind.tag !== kindTag) {
        return yield* new UnknownKind(node.kind)
      }
      const encoded = yield* decodedEnvelope(node.payload, revision, root)
      // The exact inverse walk: forced marker indexes verified against
      // the node's reference array, markers restored to sentinels.
      const resolved = resolveMarkers(encoded, node.refs)
      if (Result.isFailure(resolved)) {
        return yield* projectionFailure(
          "decode",
          violationReason(resolved.failure),
          root,
        )
      }
      return yield* Schema.decodeEffect(options.schema)(resolved.success).pipe(
        Effect.mapError((issue) => projectionFailure("decode", String(issue), root)),
      )
    },
  )

  return { get, kindTag, put }
}

/** Construct a typed value projection over the in-memory CAS service.
 *
 * The whole library-owned registry is refused, not just the replay tags
 * — a caller-defined projection aliasing a registry row would give one
 * kind plane two public interpretations. The set is generated from
 * `Cas.Grammar.manifestV0`, so this door widens with the grammar: the
 * day a sort is ratified in Lean, the next regeneration closes the door
 * on its tag, and the byte gate says so until that regeneration has
 * run. Decision 40 widened it by four rows.
 *
 * A plane the library OWNS is read through the module that owns it —
 * `Cas.CanonicalSchema` for the schema row, `Cas.Annotations` for the
 * annotation row — which is `libraryValue` above and not an escape from
 * this rule. */
export const value = <A>(options: ValueOptions<A>): CasValue<A> => {
  const kindTag = Byte.make(options.kindTag)
  if (ReservedKindTags.has(kindTag)) {
    throw new TypeError(`Projection kind tag 0x${kindTag.toString(16)} is reserved`)
  }
  return libraryValue(options)
}
