import { expect, it, layer } from "@effect/vitest"
import {
  Channel,
  Crypto,
  Deferred,
  Effect,
  Fiber,
  HashMap,
  HashSet,
  Layer,
  Redacted,
  Ref,
  Stream,
} from "effect"
import { TestClock } from "effect/testing"
import * as FetchHttpClient from "effect/unstable/http/FetchHttpClient"
import * as HttpClient from "effect/unstable/http/HttpClient"
import * as HttpClientError from "effect/unstable/http/HttpClientError"
import * as HttpClientRequest from "effect/unstable/http/HttpClientRequest"
import * as HttpClientResponse from "effect/unstable/http/HttpClientResponse"
import { createHash, randomBytes } from "node:crypto"
import * as Cas from "../../src/Cas.ts"
import {
  CasNodeInput,
  ContentId,
  RemoteFailure,
} from "../../src/cas/Node.ts"
import { CasStore } from "../../src/cas/Store.ts"
import {
  CasRemoteConfig,
  RemoteAuthority,
  remoteConfig,
} from "../../src/cas/Remote.ts"
import {
  encodeCasNode,
  makeMemoryCasStore,
  makeSha256Address,
  type CasAddress,
} from "../../src/cas/Store.ts"
import { CasTransfer } from "../../src/cas/Transfer.ts"
import {
  makeRemoteAdapter,
  type RemoteAdapter,
  type TaggedTranscriptDecision,
} from "../../src/internal/remote.ts"
import { encodeCapabilityDocument } from "../../src/internal/remoteControl.ts"
import {
  classifyTransportFailure,
  makeRemoteHttp,
} from "../../src/internal/remoteHttp.ts"
import {
  initialMachineState,
  step,
  type MInput,
  type TaggedDecision,
} from "../../src/internal/remoteMachine.ts"
import type {
  CompletionWitness,
  RemoteCasTransport,
  RemoteWireEvent,
} from "../../src/internal/remoteTransport.ts"
import { HostilePeer, type HostileFault } from "./harness/HostilePeer.ts"
import { ReferencePeer } from "./harness/ReferencePeer.ts"
import { serveGatedPeer } from "./harness/GatedPeer.ts"
import { awaitPeerSocketsReleased } from "./harness/ConformancePeer.ts"
import { admitGraphBottomUp } from "./fixtures/Graph.ts"
import { freshPush } from "./fixtures/Profiles.ts"
import { buildScenario } from "./fixtures/Sync.ts"
import {
  remoteStepLayer,
  type RemoteBytes,
  type RemoteKey,
  RemoteStepSUT,
} from "../conformance/harness.ts"
import { deterministicAddress } from "../fixtures/address.ts"

const digest = (bytes: Uint8Array): ContentId =>
  ContentId.make(createHash("sha256").update(bytes).digest("hex"))

const keyBytes = (id: ContentId): RemoteKey => Array.from(Buffer.from(id, "hex"))

const normalizeInput = (
  input: MInput<ContentId, Uint8Array>,
): MInput<RemoteKey, RemoteBytes> => {
  if (input._tag === "Request") {
    switch (input.op._tag) {
      case "Load":
        return { _tag: "Request", id: input.id, op: { _tag: "Load", key: keyBytes(input.op.key) } }
      case "FindMissing":
        return {
          _tag: "Request",
          id: input.id,
          op: { _tag: "FindMissing", keys: input.op.keys.map(keyBytes) },
        }
      case "Upload":
        return {
        _tag: "Request",
        id: input.id,
        op: {
          _tag: "Upload",
          key: keyBytes(input.op.key),
          bytes: Array.from(input.op.bytes),
        },
      }
      case "PublishRoot":
        return {
          _tag: "Request",
          id: input.id,
          op: {
            _tag: "PublishRoot",
            key: keyBytes(input.op.key),
            closure: input.op.closure.map(keyBytes),
          },
        }
      case "Attest":
        return {
          _tag: "Request",
          id: input.id,
          op: {
            _tag: "Attest",
            key: keyBytes(input.op.key),
            bytes: Array.from(input.op.bytes),
          },
        }
    }
  }
  if (input.event._tag === "Ok") {
    return {
      _tag: "FromWire",
      id: input.id,
      event: {
        _tag: "Ok",
        declared: input.event.declared,
        bytes: Array.from(input.event.bytes),
      },
    }
  }
  if (input.event._tag === "IntegrityMismatch") {
    return { _tag: "FromWire", id: input.id, event: { _tag: "IntegrityMismatch" } }
  }
  throw new Error(`differential scenario contains unsupported event ${input.event._tag}`)
}

const normalizeDecision = (
  tagged: TaggedTranscriptDecision,
) => {
  const decision = tagged.decision
  if (decision._tag === "Issued") {
    const command = decision.command
    if (command._tag === "Load") {
      return { op: tagged.op, decision: { _tag: "Issued" as const, command: {
        _tag: "Load" as const,
        key: keyBytes(command.key),
      } } }
    }
    if (command._tag === "Upload") {
      return { op: tagged.op, decision: { _tag: "Issued" as const, command: {
        _tag: "Upload" as const,
        key: keyBytes(command.key),
        byteLength: command.byteLength,
      } } }
    }
    if (command._tag === "FindMissing") {
      return { op: tagged.op, decision: { _tag: "Issued" as const, command: {
        _tag: "FindMissing" as const,
        keys: command.keys.map(keyBytes),
      } } }
    }
    if (command._tag === "PublishRoot") {
      return { op: tagged.op, decision: { _tag: "Issued" as const, command: {
        _tag: "PublishRoot" as const,
        key: keyBytes(command.key),
      } } }
    }
    throw new Error(`differential scenario contains unsupported command ${command._tag}`)
  }
  if (decision._tag === "PresenceNoted") {
    return {
      op: tagged.op,
      decision: {
        _tag: "PresenceNoted" as const,
        found: decision.found.map(keyBytes),
        missing: decision.missing.map(keyBytes),
      },
    }
  }
  if (decision._tag === "BatchRejected" || decision._tag === "BatchGaveUp") {
    return { op: tagged.op, decision: { _tag: decision._tag } }
  }
  return {
    op: tagged.op,
    decision: { _tag: decision._tag, key: keyBytes(decision.key) },
  }
}

const TestCrypto = Layer.succeed(Crypto.Crypto, Crypto.make({
  randomBytes: (size) => new Uint8Array(randomBytes(size)),
  digest: (algorithm, bytes) => Effect.sync(() => {
    const name = algorithm.toLowerCase().replace("-", "")
    return new Uint8Array(createHash(name).update(bytes).digest())
  }),
}))

const HttpRuntime = Layer.mergeAll(
  FetchHttpClient.layer,
  TestCrypto,
)

const config = (
  authority: string,
  overrides: Partial<{
    readonly maxEncodedBytes: number
    readonly maxDecodedBytes: number
    readonly maxDecompressedBytes: number
    readonly maxQueuedBytes: number
    readonly maxAttempts: number
    readonly operationDeadlineMs: number
    readonly decisionTranscriptCapacity: number
    readonly capabilityProbe: "eager" | "lazy"
  }> = {},
) => new CasRemoteConfig({
  authority: RemoteAuthority.make(authority),
  authorityMode: "remote-authoritative",
  maxEncodedBytes: overrides.maxEncodedBytes ?? 4096,
  maxDecodedBytes: overrides.maxDecodedBytes ?? 4096,
  maxDecompressedBytes: overrides.maxDecompressedBytes ?? 4096,
  maxQueuedBytes: overrides.maxQueuedBytes ?? 4096,
  maxAttempts: overrides.maxAttempts ?? 1,
  operationDeadlineMs: overrides.operationDeadlineMs ?? 5_000,
  ...(overrides.decisionTranscriptCapacity === undefined
    ? {}
    : { decisionTranscriptCapacity: overrides.decisionTranscriptCapacity }),
  ...(overrides.capabilityProbe === undefined
    ? {}
    : { capabilityProbe: overrides.capabilityProbe }),
  redirectPolicy: { maxRedirects: 0, crossOrigin: "deny" },
})

const node = (payload: ReadonlyArray<number>, tag = 3) => CasNodeInput.make({
  kind: { version: 0, tag },
  payload: Uint8Array.from(payload),
  refs: [],
})

const remoteLayer = (remoteConfig: CasRemoteConfig) =>
  Cas.layerRemote(remoteConfig).pipe(Layer.provideMerge(HttpRuntime))

it.effect("reference cas-http/0 shares admission state across CasStore and CasTransfer", () =>
  Effect.scoped(Effect.gen(function* () {
    const resident = node([1, 2, 3, 4])
    const residentBytes = encodeCasNode(resident)
    const residentId = digest(residentBytes)
    const endpoint = yield* ReferencePeer.serve({
      nodes: new Map([[residentId, residentBytes]]),
    })

    yield* Effect.gen(function* () {
      const store = yield* CasStore
      const transfer = yield* CasTransfer

      const loaded = yield* store.load(residentId)
      expect(Array.from(loaded.payload)).toEqual([1, 2, 3, 4])

      const streamed = yield* transfer.loadStream(residentId)
      const chunks = yield* Stream.runCollect(streamed)
      expect(chunks).toHaveLength(1)
      expect(Array.from(chunks[0] ?? [])).toEqual(Array.from(residentBytes))

      const uploaded = node([9, 8, 7], 4)
      const first = yield* store.put(uploaded)
      const second = yield* store.put(uploaded)
      expect(second).toBe(first)
      expect(endpoint.observe().puts).toBe(1)

      const projected = yield* transfer.putStream(
        Cas.restartable(() => Stream.make(Uint8Array.from([5, 4]), Uint8Array.from([3]))),
        { kind: { version: 0, tag: 5 }, refs: [] },
      )
      expect(projected).toMatch(/^[0-9a-f]{64}$/)
      expect(endpoint.observe().puts).toBe(2)
      yield* awaitPeerSocketsReleased(endpoint)
      expect(endpoint.observe().openSockets).toBe(0)
    }).pipe(Effect.provide(remoteLayer(config(endpoint.authority))))
  })))

it.effect("remote snapshots retain a bounded decision tail and dropped count", () =>
  Effect.scoped(Effect.gen(function* () {
    const endpoint = yield* ReferencePeer.serve({})
    const remoteConfig = config(endpoint.authority, {
      decisionTranscriptCapacity: 3,
    })
    const address = yield* makeSha256Address
    const adapter = yield* makeRemoteAdapter(
      remoteConfig,
      yield* makeRemoteHttp(remoteConfig),
      address,
    )

    for (let value = 0; value < 5; value += 1) {
      yield* adapter.store.put(node([value], 80 + value))
    }
    const snapshot = yield* adapter.snapshot
    expect(snapshot.decisions).toHaveLength(3)
    expect(snapshot.droppedDecisions).toBeGreaterThan(0)
    expect(snapshot.decisions.at(-1)?.op).toBe(6)
    const upload = snapshot.decisions.find((entry) =>
      entry.decision._tag === "Issued"
      && entry.decision.command._tag === "Upload")
    expect(upload).toBeDefined()
    if (upload?.decision._tag === "Issued"
      && upload.decision.command._tag === "Upload") {
      expect(upload.decision.command.byteLength).toBeGreaterThan(0)
      expect("bytes" in upload.decision.command).toBe(false)
    }
    yield* awaitPeerSocketsReleased(endpoint)
    expect(endpoint.observe().openSockets).toBe(0)
  }).pipe(Effect.provide(TestCrypto))))

it.effect("encoded key-list budget rejects before transport and clears in-flight state", () =>
  Effect.gen(function* () {
    const underlying = scriptedTransport([])
    let controlCalls = 0
    const transport: RemoteCasTransport = {
      issue: (operationId, attempt, request) => {
        if (request.command._tag !== "ProbeCapabilities") controlCalls += 1
        return underlying.issue(operationId, attempt, request)
      },
    }
    const remoteConfig = config("http://127.0.0.1:1", { maxEncodedBytes: 35 })
    const address = yield* makeSha256Address
    const adapter = yield* makeRemoteAdapter(remoteConfig, transport, address)
    const error = yield* adapter.transfer.missing([
      ContentId.make("12".repeat(32)),
    ]).pipe(Effect.flip)
    expect(error).toMatchObject({
      _tag: "CasRemoteError/Budget",
      stage: "encoded",
      observed: 36,
      bound: 35,
    })
    expect(controlCalls).toBe(0)
    expect((yield* adapter.snapshot).inFlightSize).toBe(0)
  }).pipe(Effect.provide(TestCrypto)))

it.effect("RMT-002 rejects a declared oversize before any response body is read or admitted", () =>
  Effect.scoped(Effect.gen(function* () {
    const bytes = encodeCasNode(node([1, 2, 3]))
    const id = digest(bytes)
    const endpoint = yield* HostilePeer.serve({
      fault: "declaredOversize",
      body: bytes,
      declared: 512,
    })

    yield* Effect.gen(function* () {
      const store = yield* CasStore
      const first = yield* store.load(id).pipe(Effect.flip)
      expect(first).toBeInstanceOf(RemoteFailure)
      if (first._tag === "CasError/RemoteFailure") {
        expect(first.cause).toMatchObject({
          _tag: "CasRemoteError/Budget",
          stage: "decoded",
          observed: 512,
          bound: 32,
        })
      }
      expect(endpoint.observe().bodyBytesWritten).toBe(0)

      yield* store.load(id).pipe(Effect.flip)
      expect(endpoint.observe().gets).toBe(2)
      yield* awaitPeerSocketsReleased(endpoint)
      expect(endpoint.observe().openSockets).toBe(0)
    }).pipe(Effect.provide(remoteLayer(config(endpoint.authority, {
      maxDecodedBytes: 32,
      maxQueuedBytes: 32,
    }))))
  })))

it.effect("RMT-002 cuts off a chunked body at the decoded-byte bound without admitting it", () =>
  Effect.scoped(Effect.gen(function* () {
      const bytes = encodeCasNode(node(Array.from({ length: 48 }, (_, index) => index)))
      const id = digest(bytes)
      const endpoint = yield* HostilePeer.serve({ fault: "chunkedOversize", body: bytes })

      yield* Effect.gen(function* () {
        const store = yield* CasStore
        const first = yield* store.load(id).pipe(Effect.flip)
        expect(first._tag).toBe("CasError/RemoteFailure")
        if (first._tag === "CasError/RemoteFailure") {
          expect(first.cause).toMatchObject({
            _tag: "CasRemoteError/Budget",
            stage: "decoded",
            observed: bytes.length,
            bound: 24,
          })
        }

        yield* store.load(id).pipe(Effect.flip)
        expect(endpoint.observe().gets).toBe(2)
        yield* awaitPeerSocketsReleased(endpoint)
        expect(endpoint.observe().openSockets).toBe(0)
      }).pipe(Effect.provide(remoteLayer(config(endpoint.authority, {
        maxDecodedBytes: 24,
      }))))
    })))

it.effect("RMT-002 enforces the queued-byte bound on the consumer side without admitting", () =>
  Effect.scoped(Effect.gen(function* () {
    const bytes = encodeCasNode(node([1, 3, 3, 7]))
    const endpoint = yield* HostilePeer.serve({ fault: "complete", body: bytes })
    yield* CasStore.use((store) => Effect.gen(function* () {
      const error = yield* store.load(digest(bytes)).pipe(Effect.flip)
      expect(error._tag).toBe("CasError/RemoteFailure")
      if (error._tag === "CasError/RemoteFailure") {
        expect(error.cause).toMatchObject({
          _tag: "CasRemoteError/Budget",
          stage: "queued",
          observed: bytes.length,
          bound: 1,
        })
      }

      yield* store.load(digest(bytes)).pipe(Effect.flip)
      expect(endpoint.observe().gets).toBe(2)
      yield* awaitPeerSocketsReleased(endpoint)
      expect(endpoint.observe().openSockets).toBe(0)
    })).pipe(
      Effect.provide(remoteLayer(config(endpoint.authority, { maxQueuedBytes: 1 }))),
    )
  })))

it.effect("the decompressed-byte budget is enforced independently of decoded bytes", () =>
  Effect.scoped(Effect.gen(function* () {
    const bytes = encodeCasNode(node([2, 7, 1, 8]))
    const endpoint = yield* HostilePeer.serve({ fault: "complete", body: bytes })
    const error = yield* CasStore.use((store) => store.load(digest(bytes))).pipe(
      Effect.flip,
      Effect.provide(remoteLayer(config(endpoint.authority, {
        maxDecodedBytes: 4096,
        maxDecompressedBytes: 1,
      }))),
    )
    expect(error._tag).toBe("CasError/RemoteFailure")
    if (error._tag === "CasError/RemoteFailure") {
      expect(error.cause).toMatchObject({
        _tag: "CasRemoteError/Budget",
        stage: "decompressed",
        observed: bytes.length,
        bound: 1,
      })
    }
    yield* awaitPeerSocketsReleased(endpoint)
    expect(endpoint.observe().openSockets).toBe(0)
  })))

it.effect("hostile cas-http/0 admits a complete content-length response and reuses it locally", () =>
  Effect.scoped(Effect.gen(function* () {
      const bytes = encodeCasNode(node([6, 2, 6]))
      const id = digest(bytes)
      const endpoint = yield* HostilePeer.serve({ fault: "complete", body: bytes })

      yield* CasStore.use((store) => Effect.gen(function* () {
        yield* store.load(id)
        yield* store.load(id)
      })).pipe(Effect.provide(remoteLayer(config(endpoint.authority))))
      expect(endpoint.observe().gets).toBe(1)
      yield* awaitPeerSocketsReleased(endpoint)
      expect(endpoint.observe().openSockets).toBe(0)
    })))

const hostileCases: ReadonlyArray<readonly [HostileFault, string, string, string]> = [
  ["truncated", "truncated fixed-length response", "CasRemoteError/Protocol", "truncatedBody"],
  ["contentLengthLarger", "overstated content length", "CasRemoteError/Protocol", "truncatedBody"],
  ["underreportedOversize", "understated content length", "CasRemoteError/Integrity", "nonCanonicalBytes"],
  ["wrongBytes", "substituted bytes", "CasRemoteError/Integrity", "addressMismatch"],
  ["resetMidBody", "connection reset mid-body", "CasRemoteError/Protocol", "truncatedBody"],
]

for (const [fault, title, expectedTag, expectedCode] of hostileCases) {
  it.effect(`hostile cas-http/0 ${title} fails typed, admits nothing, and releases its socket`, () =>
      Effect.scoped(Effect.gen(function* () {
        const bytes = encodeCasNode(node([7, 7, 7, 7]))
        const id = digest(bytes)
        const endpoint = yield* HostilePeer.serve({ fault, body: bytes })

        yield* Effect.gen(function* () {
          const store = yield* CasStore
          const first = yield* store.load(id).pipe(Effect.flip)
          expect(first._tag).toBe("CasError/RemoteFailure")
          if (first._tag === "CasError/RemoteFailure") {
            expect(first.cause._tag).toBe(expectedTag)
            if (!("code" in first.cause)) {
              return yield* Effect.die(`hostile case ${fault} returned no typed code`)
            }
            expect(first.cause.code).toBe(expectedCode)
            if ("completion" in first.cause) {
              expect(first.cause.completion).toBe("possiblyProcessed")
            }
          }

          yield* store.load(id).pipe(Effect.flip)
          expect(endpoint.observe().gets).toBe(2)
          yield* awaitPeerSocketsReleased(endpoint)
          expect(endpoint.observe().openSockets).toBe(0)
        }).pipe(Effect.provide(remoteLayer(config(endpoint.authority))))
      })))
}

for (const fault of ["contentEncoding", "contentEncodingAck", "contentEncodingAck204"] as const) {
  it.effect(`hostile cas-http/0 rejects non-identity content-encoding on ${fault === "contentEncoding" ? "loads" : fault === "contentEncodingAck204" ? "204 acknowledgements" : "acknowledgements"}`, () =>
    Effect.scoped(Effect.gen(function* () {
      const resident = node([4, 2, 4, 2])
      const bytes = encodeCasNode(resident)
      const endpoint = yield* HostilePeer.serve({ fault, body: bytes })
      const error = fault === "contentEncoding"
        ? yield* CasStore.use((store) => store.load(digest(bytes))).pipe(
            Effect.flip,
            Effect.provide(remoteLayer(config(endpoint.authority))),
          )
        : yield* CasStore.use((store) => store.put(resident)).pipe(
            Effect.flip,
            Effect.provide(remoteLayer(config(endpoint.authority))),
          )
      expect(error).toMatchObject({
        _tag: "CasError/RemoteFailure",
        cause: { _tag: "CasRemoteError/Protocol", code: "invalidHeaders" },
      })
      yield* awaitPeerSocketsReleased(endpoint)
      expect(endpoint.observe().openSockets).toBe(0)
    })))
}

for (const fixture of [
  { fault: "rateLimitedAbsent" as const, retryAfter: undefined },
  { fault: "rateLimitedDate" as const, retryAfter: undefined },
  { fault: "rateLimitedNumeric" as const, retryAfter: 17 },
]) {
  it.effect(`rate-limit ${fixture.fault} preserves only delta-seconds retry evidence`, () =>
    Effect.scoped(Effect.gen(function* () {
      const bytes = encodeCasNode(node([4, 2, 9]))
      const endpoint = yield* HostilePeer.serve({ fault: fixture.fault, body: bytes })
      const error = yield* CasStore.use((store) => store.load(digest(bytes))).pipe(
        Effect.flip,
        Effect.provide(remoteLayer(config(endpoint.authority))),
      )
      expect(error).toMatchObject({
        _tag: "CasError/RemoteFailure",
        cause: { _tag: "CasRemoteError/Unavailable", code: "rateLimited" },
      })
      if (error._tag === "CasError/RemoteFailure"
        && error.cause._tag === "CasRemoteError/Unavailable") {
        expect(error.cause.retryAfter).toBe(fixture.retryAfter)
      }
      yield* awaitPeerSocketsReleased(endpoint)
      expect(endpoint.observe().openSockets).toBe(0)
    })))
}

it.effect("hostile cas-http/0 maps 404 to ContentNotFound without remote fallback", () =>
  Effect.scoped(Effect.gen(function* () {
    const bytes = encodeCasNode(node([2]))
    const endpoint = yield* HostilePeer.serve({ fault: "notFound", body: bytes })
    const error = yield* CasStore.use((store) => store.load(digest(bytes))).pipe(
      Effect.flip,
      Effect.provide(remoteLayer(config(endpoint.authority))),
    )
    expect(error._tag).toBe("CasError/ContentNotFound")
    expect(endpoint.observe().gets).toBe(1)
    yield* awaitPeerSocketsReleased(endpoint)
    expect(endpoint.observe().openSockets).toBe(0)
  })))

it.effect("plain FetchHttpClient wiring keeps every redirect as a denied machine event", () =>
  Effect.scoped(Effect.gen(function* () {
    const bytes = encodeCasNode(node([3, 0, 2]))
    const endpoint = yield* HostilePeer.serve({ fault: "redirect", body: bytes })
    const error = yield* CasStore.use((store) => store.load(digest(bytes))).pipe(
      Effect.flip,
      Effect.provide(remoteLayer(config(endpoint.authority))),
    )
    expect(error).toMatchObject({
      _tag: "CasError/RemoteFailure",
      cause: {
        _tag: "CasRemoteError/Policy",
        code: "redirectDenied",
      },
    })
    expect(endpoint.observe().gets).toBe(1)
    yield* awaitPeerSocketsReleased(endpoint)
    expect(endpoint.observe().openSockets).toBe(0)
  })))

it.effect("queued admission budgeting is invariant under one-chunk and many-chunk sources", () =>
  Effect.scoped(Effect.gen(function* () {
    const endpoint = yield* HostilePeer.serve({ fault: "complete", body: new Uint8Array() })
    const outcomes = yield* CasTransfer.use((transfer) => Effect.forEach([
      Cas.restartable(() => Stream.succeed(Uint8Array.from([1, 2, 3, 4]))),
      Cas.restartable(() => Stream.make(
        Uint8Array.of(1),
        Uint8Array.of(2),
        Uint8Array.of(3),
        Uint8Array.of(4),
      )),
    ], (source) => transfer.putStream(source, {
      kind: { version: 0, tag: 9 },
      refs: [],
    }).pipe(
      Effect.flip,
      Effect.map((error) => ({
        _tag: error._tag,
        stage: "stage" in error ? error.stage : undefined,
        observed: "observed" in error ? error.observed : undefined,
        bound: "bound" in error ? error.bound : undefined,
        attemptId: "attemptId" in error ? error.attemptId : undefined,
      })),
    ))).pipe(Effect.provide(remoteLayer(config(endpoint.authority, {
      maxQueuedBytes: 3,
    }))))
    expect(outcomes).toEqual([
      {
        _tag: "CasRemoteError/Budget",
        stage: "queued",
        observed: 4,
        bound: 3,
        attemptId: undefined,
      },
      {
        _tag: "CasRemoteError/Budget",
        stage: "queued",
        observed: 4,
        bound: 3,
        attemptId: undefined,
      },
    ])
    // Layer acquisition performs the required capability probe; the rejected
    // uploads themselves still issue no wire request.
    expect(endpoint.observe().requests).toBe(1)
    yield* awaitPeerSocketsReleased(endpoint)
    expect(endpoint.observe().openSockets).toBe(0)
  })))

it.effect("capability acquisition is mandatory and capability documents fail closed", () =>
  Effect.scoped(Effect.gen(function* () {
    for (const fixture of [
      { fault: "capabilitiesMissing" as const, code: "invalidStatus" as const },
      { fault: "capabilitiesTruncated" as const, code: "invalidFraming" as const },
    ]) {
      const endpoint = yield* HostilePeer.serve({ fault: fixture.fault })
      const error = yield* CasTransfer.use((transfer) => transfer.capabilities).pipe(
        Effect.provide(remoteLayer(config(endpoint.authority))),
        Effect.flip,
      )
      expect(error).toMatchObject({
        _tag: "CasRemoteError/Protocol",
        code: fixture.code,
      })
      yield* awaitPeerSocketsReleased(endpoint)
      expect(endpoint.observe().openSockets).toBe(0)
    }
  })))

it.effect("capabilities and find-missing remain planning data only", () =>
  Effect.scoped(Effect.gen(function* () {
    const resident = node([2, 3, 5, 7], 31)
    const residentBytes = encodeCasNode(resident)
    const residentId = digest(residentBytes)
    const absent = node([11, 13], 32)
    const absentId = digest(encodeCasNode(absent))
    const endpoint = yield* ReferencePeer.serve({
      nodes: new Map([[residentId, residentBytes]]),
    })

    yield* Effect.gen(function* () {
      const transfer = yield* CasTransfer
      const store = yield* CasStore

      expect(yield* transfer.capabilities).toEqual({
        maxBatchKeys: 4,
        maxBlobBytes: 4_096,
      })
      expect(yield* transfer.missing([residentId, absentId])).toEqual({
        present: [residentId],
        missing: [absentId],
        failed: [],
      })
      expect(endpoint.observe()).toMatchObject({ requests: 2, gets: 0 })

      const refused = yield* transfer.publish(residentId, []).pipe(Effect.flip)
      expect(refused).toMatchObject({
        _tag: "CasRemoteError/Policy",
        code: "publishUnconfirmed",
      })
      expect(endpoint.observe().requests).toBe(2)

      expect(yield* store.load(residentId)).toEqual(resident)
      expect(endpoint.observe().gets).toBe(1)
      yield* transfer.publish(residentId, [])

      for (let attempt = 0; attempt < 2; attempt += 1) {
        const notFound = yield* store.load(absentId).pipe(Effect.flip)
        expect(notFound).toMatchObject({
          _tag: "CasError/ContentNotFound",
          id: absentId,
        })
      }
      expect(endpoint.observe().gets).toBe(3)
    }).pipe(Effect.provide(remoteLayer(config(endpoint.authority))))

    yield* awaitPeerSocketsReleased(endpoint)
    expect(endpoint.observe().openSockets).toBe(0)
  })))

it.effect("find-missing rejects the probed key budget before issue", () =>
  Effect.scoped(Effect.gen(function* () {
    const endpoint = yield* ReferencePeer.serve({})
    const keys = [0, 1, 2, 3, 4].map((value) =>
      digest(encodeCasNode(node([value], 40 + value))))

    const error = yield* CasTransfer.use((transfer) => transfer.missing(keys)).pipe(
      Effect.provide(remoteLayer(config(endpoint.authority))),
      Effect.flip,
    )
    expect(error).toMatchObject({
      _tag: "CasRemoteError/Budget",
      stage: "keys",
      observed: 5,
      bound: 4,
    })
    expect(endpoint.observe().requests).toBe(1)
    yield* awaitPeerSocketsReleased(endpoint)
    expect(endpoint.observe().openSockets).toBe(0)
  })))

it.effect("malformed positional presence fails the whole batch closed", () =>
  Effect.scoped(Effect.gen(function* () {
    const endpoint = yield* HostilePeer.serve({ fault: "missingMalformed" })
    const id = digest(encodeCasNode(node([89], 51)))
    const error = yield* CasTransfer.use((transfer) => transfer.missing([id])).pipe(
      Effect.provide(remoteLayer(config(endpoint.authority))),
      Effect.flip,
    )
    expect(error).toMatchObject({
      _tag: "CasRemoteError/Protocol",
      code: "invalidFraming",
    })
    yield* awaitPeerSocketsReleased(endpoint)
    expect(endpoint.observe().openSockets).toBe(0)
  })))

it.effect("push negotiates a complete graph children-first and publishes last", () =>
  Effect.scoped(Effect.gen(function* () {
    const endpoint = yield* ReferencePeer.serve({})
    const child = node([1, 2, 3], 61)
    const childId = digest(encodeCasNode(child))
    const parent = CasNodeInput.make({
      kind: { version: 0, tag: 62 },
      payload: Uint8Array.of(5, 8, 13),
      refs: [{ id: childId, expectedTag: child.kind.tag }],
    })
    const parentId = digest(encodeCasNode(parent))

    yield* Effect.gen(function* () {
      const store = yield* CasStore
      const transfer = yield* CasTransfer
      const putOffset = endpoint.observe().putIds?.length ?? 0
      const eventOffset = endpoint.observe().events?.length ?? 0
      expect(yield* store.put(child)).toBe(childId)
      expect(yield* store.put(parent)).toBe(parentId)

      expect(yield* transfer.push(parentId)).toEqual({
        transferred: [],
        alreadyPresent: [childId, parentId],
      })
      expect(endpoint.observe()).toMatchObject({
        requests: 5,
        gets: 0,
        puts: 2,
      })
      expect(endpoint.observe().putIds?.slice(putOffset)).toEqual([childId, parentId])
      expect(endpoint.observe().events?.slice(eventOffset)).toEqual([
        `put:${childId}`,
        `put:${parentId}`,
        "missing:2",
        `publish:${parentId}`,
      ])

      // The registry PUT is idempotent for an identical root and closure.
      yield* transfer.publish(parentId, [childId])
      expect(endpoint.observe().requests).toBe(6)
    }).pipe(Effect.provide(remoteLayer(config(endpoint.authority))))

    yield* awaitPeerSocketsReleased(endpoint)
    expect(endpoint.observe().openSockets).toBe(0)
  })))

it.effect("push rejects a later oversized node before negotiation or upload", () =>
  Effect.scoped(Effect.gen(function* () {
    const child = node([1], 91)
    const childBytes = encodeCasNode(child)
    const childId = digest(childBytes)
    const parent = CasNodeInput.make({
      kind: { version: 0, tag: 92 },
      payload: Uint8Array.from({ length: 128 }, (_, index) => index),
      refs: [{ id: childId, expectedTag: child.kind.tag }],
    })
    const parentBytes = encodeCasNode(parent)
    const endpoint = yield* ReferencePeer.serve({
      capabilities: { maxBatchKeys: 1, maxBlobBytes: childBytes.length },
    })
    const remoteConfig = config(endpoint.authority)
    const address = yield* makeSha256Address
    const localStore = yield* makeMemoryCasStore(address)
    yield* localStore.put(child)
    const parentId = yield* localStore.put(parent)
    const adapter = yield* makeRemoteAdapter(
      remoteConfig,
      yield* makeRemoteHttp(remoteConfig),
      address,
      { localStore },
    )

    const error = yield* adapter.transfer.push(parentId).pipe(Effect.flip)
    expect(error).toMatchObject({
      _tag: "CasRemoteError/Budget",
      stage: "encoded",
      observed: parentBytes.length,
      bound: childBytes.length,
    })
    if (error._tag === "CasRemoteError/Budget") {
      expect(error.attemptId).toBeUndefined()
      expect(error.opId).toBeUndefined()
    }
    expect(endpoint.observe()).toMatchObject({ requests: 1, gets: 0, puts: 0 })
    expect(endpoint.observe().events).toEqual([])
  }).pipe(Effect.provide(TestCrypto))))

it.effect("push attests locally-held present nodes without loading or caching them", () =>
  Effect.scoped(Effect.gen(function* () {
    const resident = node([8, 9, 10], 93)
    const bytes = encodeCasNode(resident)
    const id = digest(bytes)
    const endpoint = yield* ReferencePeer.serve({ nodes: new Map([[id, bytes]]) })
    const remoteConfig = config(endpoint.authority)
    const address = yield* makeSha256Address
    const localStore = yield* makeMemoryCasStore(address)
    yield* localStore.put(resident)
    const adapter = yield* makeRemoteAdapter(
      remoteConfig,
      yield* makeRemoteHttp(remoteConfig),
      address,
      { localStore },
    )

    expect(yield* adapter.transfer.push(id)).toEqual({
      transferred: [],
      alreadyPresent: [id],
    })
    expect(endpoint.observe()).toMatchObject({ requests: 3, gets: 0, puts: 0 })
    expect(yield* adapter.snapshot).toMatchObject({
      cacheSize: 0,
      confirmedSize: 1,
      publishedSize: 1,
    })
  }).pipe(Effect.provide(TestCrypto))))

it.effect("a refused local attestation is a typed policy failure with no attempt evidence", () =>
  Effect.scoped(Effect.gen(function* () {
    const base = deterministicAddress()
    let digestCalls = 0
    const address: CasAddress = {
      digest: (bytes) => {
        digestCalls += 1
        return digestCalls === 4
          ? Effect.succeed(ContentId.make("ff".repeat(32)))
          : base.digest(bytes)
      },
    }
    const localStore = yield* makeMemoryCasStore(address)
    const resident = node([13, 21, 34], 94)
    const id = yield* localStore.put(resident)
    const bytes = encodeCasNode(resident)
    const endpoint = yield* ReferencePeer.serve({ nodes: new Map([[id, bytes]]) })
    const remoteConfig = config(endpoint.authority)
    const adapter = yield* makeRemoteAdapter(
      remoteConfig,
      yield* makeRemoteHttp(remoteConfig),
      address,
      { localStore },
    )

    const error = yield* adapter.transfer.push(id).pipe(Effect.flip)
    expect(error).toMatchObject({
      _tag: "CasRemoteError/Policy",
      code: "attestRefused",
      receivedBytes: 0,
      sentBytes: 0,
    })
    if (error._tag === "CasRemoteError/Policy") {
      expect(error.attemptId).toBeUndefined()
    }
    expect(endpoint.observe()).toMatchObject({ requests: 2, gets: 0, puts: 0 })
    expect(yield* adapter.snapshot).toMatchObject({ cacheSize: 0, confirmedSize: 0 })
  }).pipe(Effect.provide(TestCrypto))))

it.effect("push uploads an early batch before the final batch is materialized", () =>
  Effect.scoped(Effect.gen(function* () {
    const scenario = buildScenario(freshPush)
    const endpoint = yield* ReferencePeer.serve({})
    const remoteConfig = config(endpoint.authority)
    const address = yield* makeSha256Address
    const localStore = yield* makeMemoryCasStore(address)
    const ids = yield* admitGraphBottomUp(localStore, scenario.graph)
    const root = ids[scenario.graph.root]
    if (root === undefined) return yield* Effect.die("seeded graph has no root")
    const transport = yield* makeRemoteHttp(remoteConfig)
    const adapter = yield* makeRemoteAdapter(
      remoteConfig,
      transport,
      address,
      { localStore },
    )

    const report = yield* adapter.transfer.push(root)
    expect(report.transferred).toEqual(ids)
    expect(report.alreadyPresent).toEqual([])

    const events = endpoint.observe().events ?? []
    const firstUpload = events.findIndex((event) => event.startsWith("put:"))
    const finalNegotiation = events.findLastIndex((event) => event.startsWith("missing:"))
    expect(firstUpload).toBeGreaterThanOrEqual(0)
    expect(finalNegotiation).toBeGreaterThan(firstUpload)
    expect(events.at(-1)).toBe(`publish:${root}`)
    expect(endpoint.observe().putIds).toEqual(ids)
    yield* awaitPeerSocketsReleased(endpoint)
    expect(endpoint.observe().openSockets).toBe(0)
  }).pipe(Effect.provide(TestCrypto))))

it.effect("push fails closed when a missing plan contradicts machine confirmation", () =>
  Effect.scoped(Effect.gen(function* () {
    const child = node([2, 3, 5], 63)
    const childId = digest(encodeCasNode(child))
    const parent = CasNodeInput.make({
      kind: { version: 0, tag: 64 },
      payload: Uint8Array.of(8, 13, 21),
      refs: [{ id: childId, expectedTag: child.kind.tag }],
    })
    const parentId = digest(encodeCasNode(parent))
    const endpoint = yield* ReferencePeer.serve({
      reportedMissing: new Set([childId]),
    })

    yield* Effect.gen(function* () {
      const store = yield* CasStore
      const transfer = yield* CasTransfer
      yield* store.put(child)
      yield* store.put(parent)

      const error = yield* transfer.push(parentId).pipe(Effect.flip)
      expect(error).toMatchObject({
        _tag: "CasRemoteError/Integrity",
        code: "remoteRejected",
      })
      expect(endpoint.observe()).toMatchObject({
        requests: 4,
        gets: 0,
        puts: 2,
      })
    }).pipe(Effect.provide(remoteLayer(config(endpoint.authority))))

    yield* awaitPeerSocketsReleased(endpoint)
    expect(endpoint.observe().openSockets).toBe(0)
  })))

it.effect("upload acknowledgements reject trailing octets", () =>
  Effect.scoped(Effect.gen(function* () {
    const endpoint = yield* ReferencePeer.serve({
      uploadAcknowledgementBody: Uint8Array.of(0),
    })
    const error = yield* CasStore.use((store) => store.put(node([1, 6, 1, 8], 65))).pipe(
      Effect.flip,
      Effect.provide(remoteLayer(config(endpoint.authority))),
    )
    expect(error).toMatchObject({
      _tag: "CasError/RemoteFailure",
      cause: {
        _tag: "CasRemoteError/Protocol",
        code: "unexpectedBody",
      },
    })
    yield* awaitPeerSocketsReleased(endpoint)
    expect(endpoint.observe().openSockets).toBe(0)
  })))

it.effect("upload acknowledgements reject a non-binary media type", () =>
  Effect.scoped(Effect.gen(function* () {
    const endpoint = yield* ReferencePeer.serve({
      acknowledgementContentType: "text/plain",
      uploadAcknowledgementBody: new Uint8Array(),
    })
    const error = yield* CasStore.use((store) => store.put(node([2, 7, 1, 8], 69))).pipe(
      Effect.flip,
      Effect.provide(remoteLayer(config(endpoint.authority))),
    )
    expect(error).toMatchObject({
      _tag: "CasError/RemoteFailure",
      cause: {
        _tag: "CasRemoteError/Protocol",
        code: "invalidHeaders",
      },
    })
    yield* awaitPeerSocketsReleased(endpoint)
    expect(endpoint.observe().openSockets).toBe(0)
  })))

it.effect("publish acknowledgements reject trailing octets", () =>
  Effect.scoped(Effect.gen(function* () {
    const endpoint = yield* ReferencePeer.serve({
      publishAcknowledgementBody: Uint8Array.of(0),
    })
    yield* Effect.gen(function* () {
      const store = yield* CasStore
      const transfer = yield* CasTransfer
      const root = yield* store.put(node([3, 4, 5], 66))
      const error = yield* transfer.publish(root, []).pipe(Effect.flip)
      expect(error).toMatchObject({
        _tag: "CasRemoteError/Protocol",
        code: "unexpectedBody",
      })
    }).pipe(Effect.provide(remoteLayer(config(endpoint.authority))))
    yield* awaitPeerSocketsReleased(endpoint)
    expect(endpoint.observe().openSockets).toBe(0)
  })))

it.effect("a cold reference-carrying parent load is the deferred closure-pull boundary", () =>
  Effect.scoped(Effect.gen(function* () {
    const child = node([1, 1, 2, 3], 10)
    const childId = digest(encodeCasNode(child))
    const parent = CasNodeInput.make({
      kind: { version: 0, tag: 11 },
      payload: Uint8Array.of(5, 8),
      refs: [{ id: childId, expectedTag: child.kind.tag }],
    })
    const parentBytes = encodeCasNode(parent)
    const parentId = digest(parentBytes)
    const endpoint = yield* ReferencePeer.serve({ nodes: new Map([[parentId, parentBytes]]) })
    const error = yield* CasStore.use((store) => store.load(parentId)).pipe(
      Effect.flip,
      Effect.provide(remoteLayer(config(endpoint.authority))),
    )
    expect(error).toMatchObject({
      _tag: "CasError/RemoteFailure",
      cause: { _tag: "CasError/DanglingReference", missing: childId },
    })
    expect(endpoint.observe().gets).toBe(1)
    yield* awaitPeerSocketsReleased(endpoint)
    expect(endpoint.observe().openSockets).toBe(0)
  })))

it.effect("a mid-download deadline surfaces typed completion evidence and releases its socket", () =>
  Effect.scoped(Effect.gen(function* () {
      const bytes = encodeCasNode(node([4, 4, 4, 4]))
      const endpoint = yield* serveGatedPeer(bytes)
      const layer = remoteLayer(config(endpoint.authority))
      yield* CasStore.use((store) => Effect.gen(function* () {
        const first = yield* store.load(digest(bytes)).pipe(Effect.flip, Effect.forkScoped)
        yield* endpoint.awaitRequest(1)
        yield* TestClock.adjust(5_001)
        const error = yield* Fiber.join(first)
        yield* endpoint.awaitClosed(1)
        expect(error._tag).toBe("CasError/RemoteFailure")
        if (error._tag === "CasError/RemoteFailure") {
          expect(error.cause).toMatchObject({
            _tag: "CasRemoteError/Unavailable",
            code: "timeout",
            completion: "possiblyProcessed",
            receivedBytes: Math.max(1, Math.floor(bytes.length / 2)),
          })
        }

        const second = yield* store.load(digest(bytes)).pipe(Effect.flip, Effect.forkScoped)
        yield* endpoint.awaitRequest(2)
        yield* TestClock.adjust(5_001)
        yield* Fiber.join(second)
        yield* endpoint.awaitClosed(2)
        expect(endpoint.observe().gets).toBe(2)
        yield* awaitPeerSocketsReleased(endpoint)
        expect(endpoint.observe().openSockets).toBe(0)
      })).pipe(Effect.provide(layer))
    })))

it.effect("caller interruption mid-body releases the socket and clears machine state", () =>
  Effect.scoped(Effect.gen(function* () {
    const bytes = encodeCasNode(node([4, 2, 4, 2]))
    const endpoint = yield* serveGatedPeer(bytes)
    const remoteConfig = config(endpoint.authority)

    yield* Effect.gen(function* () {
      const transport = yield* makeRemoteHttp(remoteConfig)
      const address = yield* makeSha256Address
      const adapter = yield* makeRemoteAdapter(remoteConfig, transport, address)
      const loading = yield* adapter.store.load(digest(bytes)).pipe(Effect.forkScoped)
      yield* endpoint.awaitRequest(1)
      yield* Fiber.interrupt(loading)
      yield* endpoint.awaitClosed(1)

      const snapshot = yield* adapter.snapshot
      expect(snapshot.inFlightSize).toBe(0)
      expect(snapshot.cacheSize).toBe(0)
      expect(endpoint.observe().gets).toBe(1)
      expect(endpoint.observe().openSockets).toBe(0)
    }).pipe(Effect.provide(HttpRuntime))
  })))

it.effect("a one-shot upload reset is never retried and carries indeterminate completion evidence", () =>
  Effect.scoped(Effect.gen(function* () {
      const uploaded = node([9, 9, 1], 7)
      const bytes = encodeCasNode(uploaded)
      const id = digest(bytes)
      const endpoint = yield* HostilePeer.serve({ fault: "cancellationMidUpload", body: bytes })

      yield* Effect.gen(function* () {
        const transfer = yield* CasTransfer
        const store = yield* CasStore
        const error = yield* transfer.putStream(
          Cas.oneShot(Stream.succeed(uploaded.payload)),
          { kind: uploaded.kind, refs: [], expected: id },
        ).pipe(Effect.flip)
        expect(error._tag).toBe("CasRemoteError/Policy")
        if (error._tag === "CasRemoteError/Policy") {
          expect(error).toMatchObject({
            code: "oneShotRetryRefused",
            completion: "possiblyProcessed",
            receivedBytes: 0,
            sentBytes: bytes.length,
            cause: {
              _tag: "CasRemoteError/Unavailable",
              receivedBytes: 0,
              sentBytes: bytes.length,
            },
          })
        }
        expect(endpoint.observe().puts).toBe(1)

        yield* store.load(id)
        expect(endpoint.observe().gets).toBe(1)
        yield* awaitPeerSocketsReleased(endpoint)
        expect(endpoint.observe().openSockets).toBe(0)
      }).pipe(Effect.provide(remoteLayer(config(endpoint.authority, { maxAttempts: 3 }))))
    })))

it.effect("a restartable upload reacquires and rechecks its source before a bounded retry", () =>
  Effect.scoped(Effect.gen(function* () {
      const uploaded = node([3, 1, 4], 8)
      const bytes = encodeCasNode(uploaded)
      const id = digest(bytes)
      const endpoint = yield* HostilePeer.serve({ fault: "cancellationMidUpload", body: bytes })
      let sourceRuns = 0
      const source = Stream.fromEffect(Effect.sync(() => {
        sourceRuns += 1
        return uploaded.payload
      }))

      yield* Effect.gen(function* () {
        const transfer = yield* CasTransfer
        const store = yield* CasStore
        const admitted = yield* transfer.putStream(
          Cas.restartable(() => source),
          { kind: uploaded.kind, refs: [], expected: id },
        )
        expect(admitted).toBe(id)
        expect(sourceRuns).toBe(2)
        expect(endpoint.observe().puts).toBe(2)

        yield* store.load(id)
        expect(endpoint.observe().puts).toBe(2)
        yield* awaitPeerSocketsReleased(endpoint)
        expect(endpoint.observe().openSockets).toBe(0)
      }).pipe(Effect.provide(remoteLayer(config(endpoint.authority, { maxAttempts: 2 }))))
    })))

interface ScriptedExchange {
  readonly events: ReadonlyArray<RemoteWireEvent>
  readonly witness: CompletionWitness
}

const scriptedTransport = (script: ReadonlyArray<ScriptedExchange>): RemoteCasTransport => {
  let cursor = 0
  return {
    issue: (_operationId, _attempt, request) => {
      const command = request.command
      if (command._tag === "ProbeCapabilities") {
        const bytes = encodeCapabilityDocument({ maxBatchKeys: 4, maxBlobBytes: 4_096 })
        return Channel.fromArray<RemoteWireEvent>([
          { _tag: "ResponseStarted", declared: bytes.length },
          { _tag: "BodyChunk", bytes },
        ]).pipe(
          Channel.concatWith(() => Channel.fromEffectDone(Effect.succeed({
            receivedBytes: bytes.length,
            sentBytes: 0,
            terminalFraming: "complete" as const,
          }))),
        )
      }
      const exchange = script[cursor]
      cursor += 1
      if (exchange === undefined) {
        return Channel.fromEffectDone(Effect.die(new Error("unexpected differential transfer")))
      }
      return Channel.fromArray(exchange.events).pipe(
        Channel.concatWith(() => Channel.fromEffectDone(Effect.succeed(exchange.witness))),
      )
    },
  }
}

type BlockedControlCommand = "ProbeCapabilities" | "FindMissing" | "PublishRoot"

const makeBlockingTransport = (
  blocked: BlockedControlCommand,
): Effect.Effect<{
  readonly transport: RemoteCasTransport
  readonly started: Deferred.Deferred<void>
  readonly restarted: Deferred.Deferred<void>
  readonly finalized: Ref.Ref<boolean>
  readonly blockedIssues: () => number
}> => Effect.gen(function* () {
  const started = yield* Deferred.make<void>()
  const restarted = yield* Deferred.make<void>()
  const finalized = yield* Ref.make(false)
  let blockedIssues = 0
  const capabilityBytes = encodeCapabilityDocument({ maxBatchKeys: 4, maxBlobBytes: 4_096 })
  const complete = (
    events: ReadonlyArray<RemoteWireEvent>,
    sentBytes: number,
  ): Channel.Channel<RemoteWireEvent, never, CompletionWitness> =>
    Channel.fromArray(events).pipe(
      Channel.concatWith(() => Channel.fromEffectDone(Effect.succeed({
        receivedBytes: 0,
        sentBytes,
        terminalFraming: "complete" as const,
      }))),
    )

  const transport: RemoteCasTransport = {
    issue: (_operationId, _attempt, request) => {
      const command = request.command
      if (command._tag === blocked) {
        blockedIssues += 1
        return Channel.fromEffectDone(
          Deferred.succeed(blockedIssues === 1 ? started : restarted, undefined).pipe(
            Effect.andThen(Effect.never),
            Effect.ensuring(Ref.set(finalized, true)),
          ),
        )
      }
      if (command._tag === "ProbeCapabilities") {
        return complete([
          { _tag: "ResponseStarted", declared: capabilityBytes.length },
          { _tag: "BodyChunk", bytes: capabilityBytes },
        ], 0)
      }
      if (command._tag === "Upload" || command._tag === "PublishRoot") {
        return complete([{
          _tag: "Event",
          event: { _tag: "Ok", declared: 0, bytes: new Uint8Array() },
        }], command._tag === "Upload" ? command.bytes.length : 4)
      }
      return Channel.fromEffectDone(Effect.die(
        new Error(`unexpected ${command._tag} command in interruption fixture`),
      ))
    },
  }
  return { transport, started, restarted, finalized, blockedIssues: () => blockedIssues }
})

it.effect("capability probe interruption finalizes its transport", () =>
  Effect.scoped(Effect.gen(function* () {
    const fixture = yield* makeBlockingTransport("ProbeCapabilities")
    const address = yield* makeSha256Address
    const acquiring = yield* makeRemoteAdapter(
      config("http://127.0.0.1:1"),
      fixture.transport,
      address,
    ).pipe(Effect.forkScoped)
    yield* Deferred.await(fixture.started)
    yield* Fiber.interrupt(acquiring)
    expect(yield* Ref.get(fixture.finalized)).toBe(true)
  }).pipe(Effect.provide(TestCrypto))))

it.effect("lazy capability probing lets the adapter acquire degraded", () =>
  Effect.scoped(Effect.gen(function* () {
    const endpoint = yield* HostilePeer.serve({ fault: "capabilitiesMissing" })
    const remoteConfig = config(endpoint.authority, { capabilityProbe: "lazy" })
    const address = yield* makeSha256Address
    const adapter = yield* makeRemoteAdapter(
      remoteConfig,
      yield* makeRemoteHttp(remoteConfig),
      address,
    )
    expect(endpoint.observe().requests).toBe(0)

    const error = yield* adapter.store.load(ContentId.make("11".repeat(32))).pipe(Effect.flip)
    expect(error).toMatchObject({
      _tag: "CasError/RemoteFailure",
      cause: { _tag: "CasRemoteError/Protocol", code: "invalidStatus" },
    })
    expect(endpoint.observe().requests).toBe(1)
    yield* awaitPeerSocketsReleased(endpoint)
    expect(endpoint.observe().openSockets).toBe(0)
  }).pipe(Effect.provide(TestCrypto))))

it.effect("lazy capability probing is memoized once per acquired adapter", () =>
  Effect.scoped(Effect.gen(function* () {
    const endpoint = yield* ReferencePeer.serve({})
    const remoteConfig = config(endpoint.authority, { capabilityProbe: "lazy" })
    const address = yield* makeSha256Address
    const adapter = yield* makeRemoteAdapter(
      remoteConfig,
      yield* makeRemoteHttp(remoteConfig),
      address,
    )
    expect(endpoint.observe().requests).toBe(0)
    yield* adapter.transfer.capabilities
    yield* adapter.transfer.capabilities
    expect(endpoint.observe().requests).toBe(1)
    yield* awaitPeerSocketsReleased(endpoint)
    expect(endpoint.observe().openSockets).toBe(0)
  }).pipe(Effect.provide(TestCrypto))))

it.effect("lazy capability probing remains deadline bounded", () =>
  Effect.scoped(Effect.gen(function* () {
    const fixture = yield* makeBlockingTransport("ProbeCapabilities")
    const remoteConfig = config("http://127.0.0.1:1", {
      capabilityProbe: "lazy",
      operationDeadlineMs: 100,
    })
    const address = yield* makeSha256Address
    const adapter = yield* makeRemoteAdapter(remoteConfig, fixture.transport, address)
    const probing = yield* adapter.transfer.capabilities.pipe(Effect.flip, Effect.forkScoped)
    yield* Deferred.await(fixture.started)
    yield* TestClock.adjust(101)

    expect(yield* Fiber.join(probing)).toMatchObject({
      _tag: "CasRemoteError/Unavailable",
      code: "timeout",
      completion: "possiblyProcessed",
    })
    expect(yield* Ref.get(fixture.finalized)).toBe(true)
  }).pipe(Effect.provide(TestCrypto))))

it.effect("interrupting the first lazy capability probe does not poison its cache", () =>
  Effect.scoped(Effect.gen(function* () {
    const fixture = yield* makeBlockingTransport("ProbeCapabilities")
    const remoteConfig = config("http://127.0.0.1:1", { capabilityProbe: "lazy" })
    const address = yield* makeSha256Address
    const adapter = yield* makeRemoteAdapter(remoteConfig, fixture.transport, address)

    const first = yield* adapter.transfer.capabilities.pipe(Effect.forkScoped)
    yield* Deferred.await(fixture.started)
    yield* Fiber.interrupt(first)
    expect(fixture.blockedIssues()).toBe(1)

    const second = yield* adapter.transfer.capabilities.pipe(Effect.forkScoped)
    yield* Deferred.await(fixture.restarted)
    expect(fixture.blockedIssues()).toBe(2)
    yield* Fiber.interrupt(second)
  }).pipe(Effect.provide(TestCrypto))))

it.effect("a retryable lazy capability failure is invalidated for the next call", () =>
  Effect.gen(function* () {
    let probes = 0
    const limits = { maxBatchKeys: 7, maxBlobBytes: 8_192 }
    const bytes = encodeCapabilityDocument(limits)
    const transport: RemoteCasTransport = {
      issue: () => {
        probes += 1
        if (probes === 1) {
          return Channel.fromEffectDone(Effect.fail({
            _tag: "RemoteTransportFailure" as const,
            code: "connectionFailed" as const,
            completion: "knownUnprocessed" as const,
            receivedBytes: 0,
            sentBytes: 0,
          }))
        }
        return Channel.fromArray<RemoteWireEvent>([
          { _tag: "ResponseStarted", declared: bytes.length },
          { _tag: "BodyChunk", bytes },
        ]).pipe(Channel.concatWith(() => Channel.fromEffectDone(Effect.succeed({
          receivedBytes: bytes.length,
          sentBytes: 0,
          terminalFraming: "complete" as const,
        }))))
      },
    }
    const adapter = yield* makeRemoteAdapter(
      config("http://127.0.0.1:1", { capabilityProbe: "lazy" }),
      transport,
      yield* makeSha256Address,
    )

    expect(yield* adapter.transfer.capabilities.pipe(Effect.flip)).toMatchObject({
      _tag: "CasRemoteError/Unavailable",
      code: "connectionFailed",
    })
    expect(yield* adapter.transfer.capabilities).toEqual(limits)
    expect(probes).toBe(2)
  }).pipe(Effect.provide(TestCrypto)))

it.effect("find-missing interruption finalizes transport and clears in-flight state", () =>
  Effect.scoped(Effect.gen(function* () {
    const fixture = yield* makeBlockingTransport("FindMissing")
    const address = yield* makeSha256Address
    const adapter = yield* makeRemoteAdapter(
      config("http://127.0.0.1:1"),
      fixture.transport,
      address,
    )
    const id = digest(encodeCasNode(node([1, 0, 1], 67)))
    const running = yield* adapter.transfer.missing([id]).pipe(Effect.forkScoped)
    yield* Deferred.await(fixture.started)
    yield* Fiber.interrupt(running)
    expect(yield* Ref.get(fixture.finalized)).toBe(true)
    expect(yield* adapter.snapshot).toMatchObject({ inFlightSize: 0 })
  }).pipe(Effect.provide(TestCrypto))))

it.effect("publish interruption finalizes transport and clears in-flight state", () =>
  Effect.scoped(Effect.gen(function* () {
    const fixture = yield* makeBlockingTransport("PublishRoot")
    const address = yield* makeSha256Address
    const adapter = yield* makeRemoteAdapter(
      config("http://127.0.0.1:1"),
      fixture.transport,
      address,
    )
    const root = yield* adapter.store.put(node([2, 0, 2], 68))
    const running = yield* adapter.transfer.publish(root, []).pipe(Effect.forkScoped)
    yield* Deferred.await(fixture.started)
    yield* Fiber.interrupt(running)
    expect(yield* Ref.get(fixture.finalized)).toBe(true)
    expect(yield* adapter.snapshot).toMatchObject({
      inFlightSize: 0,
      confirmedSize: 1,
      publishedSize: 0,
    })
  }).pipe(Effect.provide(TestCrypto))))

layer(remoteStepLayer(step))("remote adapter differential mirror lane", (it) => {
  it.effect("the adapter and pure mirror agree across the shared differential scenario table", () =>
    Effect.gen(function* () {
    const sut = yield* RemoteStepSUT
    const resident = node([8, 6, 7, 5, 3, 0, 9])
    const bytes = encodeCasNode(resident)
    const id = digest(bytes)
    const complete = (events: ReadonlyArray<RemoteWireEvent>, sentBytes = 0): ScriptedExchange => ({
      events,
      witness: { receivedBytes: bytes.length, sentBytes, terminalFraming: "complete" },
    })
    const loadExchange = complete([
      { _tag: "ResponseStarted", declared: bytes.length },
      { _tag: "BodyChunk", bytes },
    ])
    const uploadAck = complete([{
      _tag: "Event",
      event: { _tag: "Ok", declared: 0, bytes: new Uint8Array() },
    }], bytes.length)
    const uploadMismatch = complete([{
      _tag: "Event",
      event: { _tag: "IntegrityMismatch" },
    }], bytes.length)
    const loadInput = (op: number): MInput<ContentId, Uint8Array> => ({
      _tag: "Request",
      id: op,
      op: { _tag: "Load", key: id },
    })
    const loadAnswer = (op: number): MInput<ContentId, Uint8Array> => ({
      _tag: "FromWire",
      id: op,
      event: { _tag: "Ok", declared: bytes.length, bytes },
    })
    const uploadInput = (op: number): MInput<ContentId, Uint8Array> => ({
      _tag: "Request",
      id: op,
      op: { _tag: "Upload", key: id, bytes },
    })
    const uploadAnswer = (
      op: number,
      event: "Ok" | "IntegrityMismatch" = "Ok",
    ): MInput<ContentId, Uint8Array> => ({
      _tag: "FromWire",
      id: op,
      event: event === "Ok"
        ? { _tag: "Ok", declared: 0, bytes: new Uint8Array() }
        : { _tag: "IntegrityMismatch" },
    })

    const scenarios: ReadonlyArray<{
      readonly name: string
      readonly overrides?: Parameters<typeof config>[1]
      readonly script: ReadonlyArray<ScriptedExchange>
      readonly inputs: ReadonlyArray<MInput<ContentId, Uint8Array>>
      readonly execute: (adapter: RemoteAdapter) => Effect.Effect<unknown, unknown>
    }> = [
      {
        name: "verified load",
        script: [loadExchange],
        inputs: [loadInput(1), loadAnswer(1)],
        execute: (adapter) => adapter.store.load(id),
      },
      {
        name: "upload acknowledgement",
        script: [uploadAck],
        inputs: [uploadInput(1), uploadAnswer(1)],
        execute: (adapter) => adapter.store.put(resident),
      },
      {
        name: "deduplicated upload after load",
        script: [loadExchange],
        inputs: [loadInput(1), loadAnswer(1), uploadInput(2)],
        execute: (adapter) => Effect.gen(function* () {
          yield* adapter.store.load(id)
          yield* adapter.store.put(resident)
        }),
      },
      {
        name: "deduplicated upload after acknowledgement",
        script: [uploadAck],
        inputs: [uploadInput(1), uploadAnswer(1), uploadInput(2)],
        execute: (adapter) => Effect.gen(function* () {
          yield* adapter.store.put(resident)
          yield* adapter.store.put(resident)
        }),
      },
      {
        name: "rejected repeat after integrity mismatch",
        script: [uploadMismatch],
        inputs: [uploadInput(1), uploadAnswer(1, "IntegrityMismatch"), uploadInput(2)],
        execute: (adapter) => Effect.gen(function* () {
          yield* adapter.store.put(resident).pipe(Effect.result)
          yield* adapter.store.put(resident).pipe(Effect.result)
        }),
      },
      {
        name: "oversize upload",
        overrides: { maxEncodedBytes: bytes.length - 1 },
        script: [],
        inputs: [uploadInput(1)],
        execute: (adapter) => adapter.store.put(resident).pipe(Effect.result),
      },
      {
        name: "declared oversize load",
        overrides: { maxDecodedBytes: bytes.length - 1 },
        script: [complete([{ _tag: "ResponseStarted", declared: bytes.length }])],
        inputs: [
          loadInput(1),
          {
            _tag: "FromWire",
            id: 1,
            event: { _tag: "Ok", declared: bytes.length, bytes: new Uint8Array() },
          },
        ],
        execute: (adapter) => adapter.store.load(id).pipe(Effect.result),
      },
    ]

    const address = yield* makeSha256Address
    for (const scenario of scenarios) {
      const remoteConfig = config("http://127.0.0.1:1", scenario.overrides)
      const adapter = yield* makeRemoteAdapter(
        remoteConfig,
        scriptedTransport(scenario.script),
        address,
      )
      yield* scenario.execute(adapter)
      const observed = yield* adapter.snapshot
      const params = {
        budgets: {
          maxBytes: scenario.name.includes("upload") || scenario.name.includes("repeat")
            ? remoteConfig.maxEncodedBytes
            : remoteConfig.maxDecodedBytes,
          maxKeys: 1,
        },
        size: (value: RemoteBytes) => value.length,
        verify: (key: RemoteKey, value: RemoteBytes) => {
          const actual = keyBytes(digest(Uint8Array.from(value)))
          return actual.every((byte, index) => key[index] === byte)
        },
      }
      let expectedState = initialMachineState<RemoteKey, RemoteBytes>()
      const expectedDecisions: Array<TaggedDecision<RemoteKey, RemoteBytes>> = []
      for (const input of scenario.inputs) {
        const output = sut.step(params, expectedState, normalizeInput(input))
        expectedState = output.state
        expectedDecisions.push(...output.decisions)
      }
      const expectedFirstOp = expectedDecisions[0]?.op ?? 0
      const observedFirstOp = observed.decisions[0]?.op ?? expectedFirstOp
      const operationIdOffset = observedFirstOp - expectedFirstOp
      const redactedExpectedDecisions = expectedDecisions.map((tagged) =>
        tagged.decision._tag === "Issued" && tagged.decision.command._tag === "Upload"
          ? {
            op: tagged.op,
            decision: {
              _tag: "Issued" as const,
              command: {
                _tag: "Upload" as const,
                key: tagged.decision.command.key,
                byteLength: tagged.decision.command.bytes.length,
              },
            },
          }
          : tagged)
      expect({
        scenario: scenario.name,
        decisions: observed.decisions.map((tagged) => {
          const normalized = normalizeDecision(tagged)
          return { ...normalized, op: normalized.op - operationIdOffset }
        }),
        state: {
          cacheSize: observed.cacheSize,
          confirmedSize: observed.confirmedSize,
          inFlightSize: observed.inFlightSize,
          publishedSize: observed.publishedSize,
          rejectedSize: observed.rejectedSize,
          reportedMissingSize: observed.reportedMissingSize,
          reportedPresentSize: observed.reportedPresentSize,
        },
      }).toEqual({
        scenario: scenario.name,
        decisions: redactedExpectedDecisions,
        state: {
          cacheSize: HashSet.size(expectedState.cache),
          confirmedSize: HashSet.size(expectedState.confirmed),
          inFlightSize: HashMap.size(expectedState.inFlight),
          publishedSize: HashSet.size(expectedState.published),
          rejectedSize: HashSet.size(expectedState.rejected),
          reportedMissingSize: HashSet.size(expectedState.reportedMissing),
          reportedPresentSize: HashSet.size(expectedState.reportedPresent),
        },
      })
    }
    }).pipe(Effect.provide(TestCrypto)))
})

it.effect("an invalid upload acknowledgement clears the correlated in-flight operation", () =>
  Effect.gen(function* () {
    const uploaded = node([1, 4, 1, 4], 12)
    const bytes = encodeCasNode(uploaded)
    const remoteConfig = config("http://127.0.0.1:1")
    const address = yield* makeSha256Address
    const adapter = yield* makeRemoteAdapter(remoteConfig, scriptedTransport([{
      events: [],
      witness: {
        receivedBytes: 0,
        sentBytes: bytes.length,
        terminalFraming: "complete",
      },
    }]), address)
    const error = yield* adapter.store.put(uploaded).pipe(Effect.flip)
    expect(error).toMatchObject({
      _tag: "CasError/RemoteFailure",
      cause: { _tag: "CasRemoteError/Protocol", code: "invalidAcknowledgement" },
    })
    const snapshot = yield* adapter.snapshot
    expect(snapshot.inFlightSize).toBe(0)
  }).pipe(Effect.provide(TestCrypto)))

it.effect("rate-limit evidence retains the Schema-decoded retry-after value", () =>
  Effect.gen(function* () {
    const resident = node([2, 7, 1, 8], 13)
    const bytes = encodeCasNode(resident)
    const id = digest(bytes)
    const remoteConfig = config("http://127.0.0.1:1")
    const address = yield* makeSha256Address
    const adapter = yield* makeRemoteAdapter(remoteConfig, scriptedTransport([{
      events: [{ _tag: "Event", event: { _tag: "RateLimited", retryAfter: 17 } }],
      witness: { receivedBytes: 0, sentBytes: 0, terminalFraming: "complete" },
    }]), address)
    const error = yield* adapter.store.load(id).pipe(Effect.flip)
    expect(error).toMatchObject({
      _tag: "CasError/RemoteFailure",
      cause: {
        _tag: "CasRemoteError/Unavailable",
        code: "rateLimited",
        retryAfter: 17,
      },
    })
  }).pipe(Effect.provide(TestCrypto)))

it("nested fetch causes retain connection-reset classification", () => {
  const request = HttpClientRequest.get("http://127.0.0.1:1/control/capabilities")
  const error = new HttpClientError.HttpClientError({
    reason: new HttpClientError.TransportError({
      request,
      cause: Object.assign(new TypeError("fetch failed"), {
        cause: { code: "ECONNRESET" },
      }),
    }),
  })
  expect(classifyTransportFailure(error, 0)).toMatchObject({
    _tag: "RemoteTransportFailure",
    code: "connectionReset",
  })
})

it("remoteConfig validates schemes, accepts ordinary Redacted credentials, and applies named defaults", () => {
  expect(() => remoteConfig("ftp://example.com")).toThrow()
  const built = remoteConfig("https://example.com", {
    maxAttempts: 3,
    credentials: Redacted.make("secret"),
  })
  expect(built).toMatchObject({
    authority: "https://example.com",
    authorityMode: "remote-authoritative",
    maxAttempts: 3,
    capabilityProbe: "eager",
    redirectPolicy: { maxRedirects: 0, crossOrigin: "deny" },
  })
  expect(built.maxEncodedBytes).toBeGreaterThan(0)
  expect(built.operationDeadlineMs).toBeGreaterThan(0)
})

it.effect("offline puts are observably distinct from local-authoritative admission", () => {
  const authority = RemoteAuthority.make("http://127.0.0.1:1")
  const makeModeConfig = (authorityMode: "offline" | "local-authoritative") =>
    new CasRemoteConfig({
      authority,
      authorityMode,
      maxEncodedBytes: 4096,
      maxDecodedBytes: 4096,
      maxDecompressedBytes: 4096,
      maxQueuedBytes: 4096,
      maxAttempts: 1,
      operationDeadlineMs: 5_000,
      redirectPolicy: { maxRedirects: 0, crossOrigin: "deny" },
    })
  const uploaded = node([6, 6, 6], 14)
  return Effect.gen(function* () {
    const offline = yield* CasStore.use((store) => store.put(uploaded)).pipe(
      Effect.flip,
      Effect.provide(remoteLayer(makeModeConfig("offline"))),
    )
    expect(offline).toMatchObject({
      _tag: "CasError/RemoteFailure",
      cause: { _tag: "CasRemoteError/Policy", code: "offline" },
    })
    const local = yield* CasStore.use((store) => store.put(uploaded)).pipe(
      Effect.provide(remoteLayer(makeModeConfig("local-authoritative"))),
    )
    expect(local).toBe(digest(encodeCasNode(uploaded)))
  })
})
