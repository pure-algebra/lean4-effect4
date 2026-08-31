/**
 * SRV-001: the model server ran every scripted session and wrote down
 * what happened — outcomes and the reified storage transcript. This
 * binding replays the same scripts through the implementation's
 * semantic core over a recording backend, under the vector digest, and
 * must reproduce both, in order. The transcript is law: a skipped
 * admission check, an extra load, or a reordered negotiation is a red
 * row here, never a benchmark.
 *
 * The row schemas decode INTO the protocol vocabulary: addresses are
 * the branded `ContentId` schema itself, node bytes come through the
 * stock hex codec, and a decoded request IS a `CasRequest` — it feeds
 * `serve` directly, with no translation layer anywhere.
 */
import { it } from "@effect/vitest"
import { Effect, Option, Schema } from "effect"
import {
  ByteReader,
  ByteWriter,
  RootStore,
  type ByteReaderShape,
  type ByteWriterShape,
  type RootStoreShape,
} from "../../src/cas/Backend.ts"
import { ContentId } from "../../src/cas/Node.ts"
import type { CasAddress } from "../../src/cas/Store.ts"
import { makeCasServerCore } from "../../src/server/Core.ts"
import {
  CasOutcome,
  Principal,
  type CasRequest,
} from "../../src/server/Protocol.ts"
import { toyAddr } from "../fixtures/toyAddress.ts"
import { assertFamilyRows, ManifestModel } from "../conformance/harness.ts"

const Address = ContentId
const NodeBytes = Schema.Uint8ArrayFromHex
const Status = Schema.Literals(["present", "missing", "failed"])

/** Decodes to exactly the protocol's request algebra: a decoded row
 * request IS a `CasRequest`, checked below with no cast. */
const Request = Schema.Union([
  Schema.Struct({ _tag: Schema.Literal("ReadCapabilities") }),
  Schema.Struct({
    _tag: Schema.Literal("QueryPresence"),
    keys: Schema.Array(Address),
  }),
  Schema.Struct({ _tag: Schema.Literal("LoadNode"), id: Address }),
  Schema.Struct({
    _tag: Schema.Literal("UploadNode"),
    bytes: NodeBytes,
    id: Address,
  }),
  Schema.Struct({
    _tag: Schema.Literal("PublishRoot"),
    closure: Schema.Array(Address),
    root: Address,
  }),
])
const _requestsAreProtocol: (decoded: typeof Request.Type) => CasRequest =
  (decoded) => decoded
void _requestsAreProtocol

const Outcome = Schema.Union([
  Schema.Struct({
    _tag: Schema.Literal("Capabilities"),
    maxBatchKeys: Schema.Number,
    maxNodeBytes: Schema.Number,
  }),
  Schema.Struct({
    _tag: Schema.Literal("Presence"),
    statuses: Schema.Array(Status),
  }),
  Schema.Struct({ _tag: Schema.Literal("NodeBytes"), bytes: NodeBytes }),
  Schema.Struct({ _tag: Schema.Literal("NodeAbsent") }),
  Schema.Struct({ _tag: Schema.Literal("Admitted") }),
  Schema.Struct({ _tag: Schema.Literal("AlreadyAdmitted") }),
  Schema.Struct({ _tag: Schema.Literal("AdmissionRefused") }),
  Schema.Struct({ _tag: Schema.Literal("DigestMismatch") }),
  Schema.Struct({ _tag: Schema.Literal("NodeBudgetExceeded") }),
  Schema.Struct({ _tag: Schema.Literal("BatchBudgetExceeded") }),
  Schema.Struct({ _tag: Schema.Literal("Published") }),
  Schema.Struct({ _tag: Schema.Literal("ClosureUnverified") }),
])

const StorageEvent = Schema.Union([
  Schema.Struct({
    _tag: Schema.Literal("LoadBytes"),
    address: Address,
    answer: Schema.Union([Schema.Null, NodeBytes]),
  }),
  Schema.Struct({
    _tag: Schema.Literal("PutBytes"),
    address: Address,
    bytes: NodeBytes,
  }),
  Schema.Struct({
    _tag: Schema.Literal("Presence"),
    addresses: Schema.Array(Address),
    answer: Schema.Array(Status),
  }),
  Schema.Struct({ _tag: Schema.Literal("PublishRoot"), root: Address }),
])
type StorageEvent = typeof StorageEvent.Type

const Row = Schema.Struct({
  case: Schema.String,
  expect: Schema.Struct({
    events: Schema.Array(StorageEvent),
    outcomes: Schema.Array(Outcome),
  }),
  input: Schema.Struct({ requests: Schema.Array(Request) }),
})

const binding = {
  family: "SRV-001" as const,
  hasOracle: false as const,
  model: ManifestModel,
  row: Row,
}

/** The vector digest, mirroring the model's declared toy address. */
const toyAddress: CasAddress = {
  digest: (bytes) => Effect.sync(() => ContentId.make(
    toyAddr(Array.from(bytes))
      .map((byte) => byte.toString(16).padStart(2, "0"))
      .join(""),
  )),
}

/** A memory backend that also reifies every storage event, in the row
 * vocabulary — the implementation-side mirror of the model's traced
 * handler, answering all three seams over one shared state. */
const makeRecordingBackend = () => {
  const nodes = new Map<ContentId, Uint8Array>()
  const published = new Set<ContentId>()
  const events: Array<StorageEvent> = []
  const reader: ByteReaderShape = {
    loadBytes: (address) => Effect.sync(() => {
      const resident = nodes.get(address)
      events.push({
        _tag: "LoadBytes",
        address,
        answer: resident === undefined ? null : resident.slice(),
      })
      return resident === undefined
        ? Option.none()
        : Option.some(resident.slice())
    }),
    presence: (addresses) => Effect.sync(() => {
      const answer = addresses.map((address) =>
        nodes.has(address) ? "present" as const : "missing" as const)
      events.push({ _tag: "Presence", addresses, answer })
      return answer
    }),
  }
  const writer: ByteWriterShape = {
    putBytes: (address, bytes) => Effect.sync(() => {
      events.push({ _tag: "PutBytes", address, bytes: bytes.slice() })
      if (!nodes.has(address)) nodes.set(address, bytes.slice())
    }),
  }
  const roots: RootStoreShape = {
    publish: (root) => Effect.sync(() => {
      events.push({ _tag: "PublishRoot", root })
      published.add(root)
    }),
    list: Effect.sync(() => [...published]),
  }
  return { events, reader, writer, roots }
}

/** Project an implementation outcome onto the row vocabulary — the
 * model collapses refusal detail, so the verdict is dropped. */
const outcomeView = CasOutcome.$match({
  AdmissionRefused: () => ({ _tag: "AdmissionRefused" }) as const,
  Admitted: () => ({ _tag: "Admitted" }) as const,
  AlreadyAdmitted: () => ({ _tag: "AlreadyAdmitted" }) as const,
  BackendUnavailable: () => ({ _tag: "BackendUnavailable" }) as const,
  BatchBudgetExceeded: () => ({ _tag: "BatchBudgetExceeded" }) as const,
  Capabilities: ({ maxBatchKeys, maxNodeBytes }) =>
    ({ _tag: "Capabilities", maxBatchKeys, maxNodeBytes }) as const,
  ClosureUnverified: () => ({ _tag: "ClosureUnverified" }) as const,
  DigestMismatch: () => ({ _tag: "DigestMismatch" }) as const,
  NodeAbsent: () => ({ _tag: "NodeAbsent" }) as const,
  NodeBudgetExceeded: () => ({ _tag: "NodeBudgetExceeded" }) as const,
  NodeBytes: ({ bytes }) => ({ _tag: "NodeBytes", bytes }) as const,
  Presence: ({ statuses }) => ({ _tag: "Presence", statuses }) as const,
  Published: () => ({ _tag: "Published" }) as const,
  RootAbsent: () => ({ _tag: "RootAbsent" }) as const,
  RootPublished: () => ({ _tag: "RootPublished" }) as const,
})

it.effect("SRV-001 replays every scripted session through the semantic core", () =>
  assertFamilyRows(binding, (row) => Effect.gen(function* () {
    const recording = makeRecordingBackend()
    const core = yield* makeCasServerCore(
      { maxBatchKeys: 4, maxNodeBytes: 128 },
      toyAddress,
    ).pipe(
      Effect.provideService(ByteReader, recording.reader),
      Effect.provideService(ByteWriter, recording.writer),
      Effect.provideService(RootStore, recording.roots),
    )

    const outcomes = []
    for (const request of row.input.requests) {
      outcomes.push(outcomeView(
        yield* core.serve(Principal.Anonymous(), request),
      ))
    }
    return { events: recording.events, outcomes }
  })))
