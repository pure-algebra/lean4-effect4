import { Effect, Equal, Option, Schema } from "effect"
import { Recipe, type Bytes } from "../../src/internal/merkleChunk.ts"
import {
  type VerifyConsistencyInput,
  verifyConsistency,
} from "../../src/internal/merkleConsistency.ts"
import {
  dstep,
  initState,
  type DDecision,
  type DInput,
  type DStepFunction,
} from "../../src/internal/merkleDecoder.ts"
import {
  decodeOpening,
  decodeStream,
  encodeNat32,
  encodeOpening,
  encodeStream,
  type OpeningDoc,
  type StreamDoc,
} from "../../src/internal/merkleProofCodec.ts"
import { type HP, type Pre, root } from "../../src/internal/merkleTree.ts"
import {
  type VerifyInclusionInput,
  verifyInclusion,
} from "../../src/internal/merkleVerify.ts"
import { feedAll, type FramerResult } from "../../src/internal/proofFramer.ts"
import { ManifestModel } from "../conformance/harness.ts"

export type MerkleAddress = ReadonlyArray<number>

const ByteSchema = Schema.Int.check(Schema.isBetween({ minimum: 0, maximum: 0xff }))
const BytesSchema = Schema.Array(ByteSchema)
const AddressSchema = BytesSchema.check(Schema.isLengthBetween(32, 32))
const UInt32Schema = Schema.Int.check(Schema.isBetween({ minimum: 0, maximum: 0xffff_ffff }))

const ParentNodeSchema = Schema.Struct({
  _tag: Schema.Literal("ParentNode"),
  left: AddressSchema,
  right: AddressSchema,
})
const ChunkNodeSchema = Schema.Struct({
  _tag: Schema.Literal("ChunkNode"),
  bytes: BytesSchema,
})
const SkipNodeSchema = Schema.Struct({ _tag: Schema.Literal("SkipNode") })
export const DInputSchema = Schema.Union([
  ParentNodeSchema,
  ChunkNodeSchema,
  SkipNodeSchema,
])

const DDecisionSchema = Schema.Union([
  Schema.Struct({ _tag: Schema.Literal("Emitted"), index: UInt32Schema, bytes: BytesSchema }),
  Schema.Struct({ _tag: Schema.Literal("LengthValidated") }),
  Schema.Struct({ _tag: Schema.Literal("RejectedNode") }),
])

export const ChunkRowSchema = Schema.Struct({
  case: Schema.String,
  expect: Schema.Struct({
    chunks: Schema.Array(BytesSchema),
    root: AddressSchema,
  }),
  input: Schema.Struct({
    bytes: BytesSchema,
    chunkSize: UInt32Schema.check(Schema.isGreaterThan(0)),
  }),
})
export type ChunkRow = typeof ChunkRowSchema.Type

export const DecoderRowSchema = Schema.Struct({
  case: Schema.String,
  expect: Schema.Struct({
    decisions: Schema.Array(DDecisionSchema),
    status: Schema.Literals(["active", "done", "rejected"]),
  }),
  input: Schema.Struct({
    root: AddressSchema,
    total: UInt32Schema,
    lo: UInt32Schema,
    hi: UInt32Schema,
    inputs: Schema.Array(DInputSchema),
  }),
})
export type DecoderRow = typeof DecoderRowSchema.Type

export const InclusionRowSchema = Schema.Struct({
  case: Schema.String,
  expect: Schema.Struct({ accepted: Schema.Boolean }),
  input: Schema.Struct({
    index: UInt32Schema,
    count: UInt32Schema,
    bytes: BytesSchema,
    siblings: Schema.Array(AddressSchema),
    root: AddressSchema,
  }),
})
export type InclusionRow = typeof InclusionRowSchema.Type

export const ConsistencyRowSchema = Schema.Struct({
  case: Schema.String,
  expect: Schema.Struct({ accepted: Schema.Boolean }),
  input: Schema.Struct({
    oldSize: UInt32Schema,
    newSize: UInt32Schema,
    oldRoot: AddressSchema,
    newRoot: AddressSchema,
    proof: Schema.Array(AddressSchema),
  }),
})
export type ConsistencyRow = typeof ConsistencyRowSchema.Type

const OpeningDocSchema = Schema.Struct({
  index: UInt32Schema,
  total: UInt32Schema,
  leaf: BytesSchema,
  siblings: Schema.Array(AddressSchema),
})
const OpeningResultSchema = Schema.Union([
  Schema.Struct({ _tag: Schema.Literal("Decoded"), doc: OpeningDocSchema }),
  Schema.Struct({ _tag: Schema.Literal("Rejected") }),
])
export const OpeningRowSchema = Schema.Struct({
  case: Schema.String,
  expect: OpeningResultSchema,
  input: Schema.Struct({ bytes: BytesSchema }),
})
export type OpeningRow = typeof OpeningRowSchema.Type

const StreamResultSchema = Schema.Union([
  Schema.Struct({
    _tag: Schema.Literal("Decoded"),
    header: Schema.Struct({ total: UInt32Schema, lo: UInt32Schema, hi: UInt32Schema }),
    items: Schema.Array(DInputSchema),
  }),
  Schema.Struct({ _tag: Schema.Literal("Rejected") }),
])
export const StreamRowSchema = Schema.Struct({
  case: Schema.String,
  expect: StreamResultSchema,
  input: Schema.Struct({ bytes: BytesSchema }),
})
export type StreamRow = typeof StreamRowSchema.Type

const FramerResultSchema = Schema.Union([
  Schema.Struct({
    _tag: Schema.Literal("Parsed"),
    items: Schema.Array(DInputSchema),
    remainder: BytesSchema,
  }),
  Schema.Struct({ _tag: Schema.Literal("Malformed") }),
])

export const FramerRowSchema = Schema.Struct({
  case: Schema.String,
  expect: FramerResultSchema,
  input: Schema.Struct({ fragments: Schema.Array(BytesSchema) }),
})
export type FramerRow = typeof FramerRowSchema.Type

export const MerkleOracle = "Addresses are 32-byte toy digests (the declared 32-lane byte fold, not cryptographic) over structural pre-image encodings — a tag byte for leaf or parent, the leaf's absolute index and bytes, the parent's two child addresses — so domain separation and position binding live in the pre-image exactly as the model states them; the tie to a production hash arrives with the implementation slice."
export const FramerOracle = "Fragments are transport-level splits of proof-stream frame bodies — a skip tag, a length-prefixed chunk, a parent carrying two 32-byte addresses (toy digests, the declared 32-lane byte fold, not cryptographic) — so an implementation binds its incremental framer with the fragments replayed verbatim: identical items and remainder across every fragmentation of one body, a nonempty remainder on truncation, malformed on an unknown tag."

const binding = <Family extends string, Row extends Schema.Top & {
  readonly DecodingServices: never
  readonly EncodingServices: never
}>(family: Family, row: Row) => ({
  family,
  model: ManifestModel,
  row,
  hasOracle: true as const,
  oracle: MerkleOracle,
})

export const mrk001Binding = binding("MRK-001", ChunkRowSchema)
export const mrk002Binding = binding("MRK-002", DecoderRowSchema)
export const mrk003Binding = binding("MRK-003", DecoderRowSchema)
export const mrk005Binding = binding("MRK-005", DecoderRowSchema)
export const mrk006Binding = binding("MRK-006", InclusionRowSchema)
export const mrk007Binding = binding("MRK-007", ConsistencyRowSchema)
export const mrk011Binding = binding("MRK-011", OpeningRowSchema)
export const mrk012Binding = binding("MRK-012", StreamRowSchema)
export const mrk015Binding = {
  family: "MRK-015",
  model: ManifestModel,
  row: FramerRowSchema,
  hasOracle: true as const,
  oracle: FramerOracle,
}

/** The manifest-declared 32-lane toy digest. Test-side only. */
export const toyAddress = (bytes: Bytes): MerkleAddress =>
  Array.from({ length: 32 }, (_, lane) => {
    let accumulator = lane + bytes.length
    for (const byte of bytes) accumulator += byte * (lane + 3)
    return accumulator % 256
  })

const encodePreimage = (preimage: Pre<MerkleAddress>): Bytes => {
  switch (preimage._tag) {
    case "Leaf":
      return [0, ...encodeNat32(preimage.index), ...preimage.bytes]
    case "Parent":
      return [1, ...preimage.left, ...preimage.right]
  }
}

export const merkleH: HP<MerkleAddress> = {
  H: (preimage) => toyAddress(encodePreimage(preimage)),
}

export type ChunkFunction = (
  recipe: Recipe,
  bytes: Bytes,
) => ReadonlyArray<Bytes>
export type InclusionFunction = (
  input: VerifyInclusionInput<MerkleAddress>,
) => boolean
export type ConsistencyFunction = (
  input: VerifyConsistencyInput<MerkleAddress>,
) => boolean
export type OpeningDecodeFunction = (bytes: Bytes) => Option.Option<OpeningDoc>
export type StreamDecodeFunction = (bytes: Bytes) => Option.Option<StreamDoc>

export const runChunkRow = (
  chunk: ChunkFunction,
  row: ChunkRow,
) => Effect.gen(function* () {
  const recipe = Recipe.make(row.input.chunkSize)
  if (Option.isNone(recipe)) {
    return yield* Effect.die(new Error(`${row.case}: invalid committed chunk recipe`))
  }
  const chunks = chunk(recipe.value, row.input.bytes)
  return { chunks, root: root(merkleH, 0, chunks) }
})

export const runDecoderRow = (
  step: DStepFunction<MerkleAddress>,
  row: DecoderRow,
) => Effect.sync(() => {
  const params = {
    P: merkleH,
    total: row.input.total,
    expectedRoot: row.input.root,
    lo: row.input.lo,
    hi: row.input.hi,
  }
  let state = initState(params)
  const decisions: Array<DDecision> = []
  for (const input of row.input.inputs) {
    const output = step(params, state, input)
    state = output.state
    decisions.push(...output.decisions)
  }
  return { decisions, status: state.status }
})

export const runInclusionRow = (
  verify: InclusionFunction,
  row: InclusionRow,
) => Effect.sync(() => ({
  accepted: verify({
    P: merkleH,
    index: row.input.index,
    count: row.input.count,
    bytes: row.input.bytes,
    siblings: row.input.siblings,
    expectedRoot: row.input.root,
  }),
}))

export const runConsistencyRow = (
  verify: ConsistencyFunction,
  row: ConsistencyRow,
) => Effect.sync(() => ({
  accepted: verify({
    P: merkleH,
    oldSize: row.input.oldSize,
    newSize: row.input.newSize,
    oldRoot: row.input.oldRoot,
    newRoot: row.input.newRoot,
    proof: row.input.proof,
  }),
}))

export const runOpeningRow = (
  decode: OpeningDecodeFunction,
  row: OpeningRow,
) => Effect.gen(function* () {
  const decoded = decode(row.input.bytes)
  if (Option.isNone(decoded)) return { _tag: "Rejected" as const }
  const canonical = encodeOpening(decoded.value)
  const roundTrip = decode(canonical)
  if (!Equal.equals(canonical, row.input.bytes)
    || Option.isNone(roundTrip)
    || !Equal.equals(roundTrip.value, decoded.value)) {
    return yield* Effect.die(new Error(`${row.case}: opening codec violated canonical exactness`))
  }
  return { _tag: "Decoded" as const, doc: decoded.value }
})

/** Render a mutant result without imposing the real codec's exactness law. */
export const runOpeningMutantRow = (
  decode: OpeningDecodeFunction,
  row: OpeningRow,
) => Effect.sync(() => Option.match(decode(row.input.bytes), {
  onNone: () => ({ _tag: "Rejected" as const }),
  onSome: (doc) => ({ _tag: "Decoded" as const, doc }),
}))

export const runStreamRow = (
  decode: StreamDecodeFunction,
  row: StreamRow,
) => Effect.gen(function* () {
  const decoded = decode(row.input.bytes)
  if (Option.isNone(decoded)) return { _tag: "Rejected" as const }
  const canonical = encodeStream(decoded.value)
  const roundTrip = decode(canonical)
  if (!Equal.equals(canonical, row.input.bytes)
    || Option.isNone(roundTrip)
    || !Equal.equals(roundTrip.value, decoded.value)) {
    return yield* Effect.die(new Error(`${row.case}: stream codec violated canonical exactness`))
  }
  return { _tag: "Decoded" as const, ...decoded.value }
})

/** Render a mutant result without imposing the real codec's exactness law. */
export const runStreamMutantRow = (
  decode: StreamDecodeFunction,
  row: StreamRow,
) => Effect.sync(() => Option.match(decode(row.input.bytes), {
  onNone: () => ({ _tag: "Rejected" as const }),
  onSome: (doc) => ({ _tag: "Decoded" as const, ...doc }),
}))

export const realChunk: ChunkFunction = (recipe, bytes) => recipe.chunk(bytes)
export const realStep: DStepFunction<MerkleAddress> = dstep
export const realInclusion: InclusionFunction = verifyInclusion
export const realConsistency: ConsistencyFunction = verifyConsistency
export const realOpeningDecode: OpeningDecodeFunction = decodeOpening
export const realStreamDecode: StreamDecodeFunction = decodeStream

export const runFramerRow = (
  parse: (fragments: ReadonlyArray<ReadonlyArray<number>>) => FramerResult,
  row: FramerRow,
) => Effect.sync(() => parse(row.input.fragments))

export const realFeedAll = feedAll
