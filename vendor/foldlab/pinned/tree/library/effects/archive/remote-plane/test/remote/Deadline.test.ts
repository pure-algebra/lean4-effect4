/**
 * The cas-http/0 deadline clause at the two gate positions the mid-download
 * case in `RemoteAdapter.test.ts` does not reach: a peer that never writes
 * response headers at all, and a peer that answers completely inside the
 * deadline. Expiry is the machine's ordinary Silence event with the typed
 * `timeout` reason — no new alphabet, no shell-side retry, and in-flight
 * state cleared exactly as any silence clears it.
 */
import { expect, it } from "@effect/vitest"
import { Crypto, Effect, Fiber, Layer } from "effect"
import { TestClock } from "effect/testing"
import * as FetchHttpClient from "effect/unstable/http/FetchHttpClient"
import { createHash, randomBytes } from "node:crypto"
import { CasNodeInput, ContentId } from "../../src/cas/Node.ts"
import { CasRemoteConfig, RemoteAuthority } from "../../src/cas/Remote.ts"
import { encodeCasNode, makeSha256Address } from "../../src/cas/Store.ts"
import { makeRemoteAdapter } from "../../src/internal/remote.ts"
import { makeRemoteHttp } from "../../src/internal/remoteHttp.ts"
import { awaitPeerSocketsReleased } from "./harness/ConformancePeer.ts"
import { serveGatedPeer } from "./harness/GatedPeer.ts"

const TestCrypto = Layer.succeed(Crypto.Crypto, Crypto.make({
  randomBytes: (size) => new Uint8Array(randomBytes(size)),
  digest: (algorithm, bytes) => Effect.sync(() => {
    const name = algorithm.toLowerCase().replace("-", "")
    return new Uint8Array(createHash(name).update(bytes).digest())
  }),
}))

const HttpRuntime = Layer.mergeAll(FetchHttpClient.layer, TestCrypto)

const digest = (bytes: Uint8Array): ContentId =>
  ContentId.make(createHash("sha256").update(bytes).digest("hex"))

const config = (authority: string, maxAttempts = 1) => new CasRemoteConfig({
  authority: RemoteAuthority.make(authority),
  authorityMode: "remote-authoritative",
  maxEncodedBytes: 4096,
  maxDecodedBytes: 4096,
  maxDecompressedBytes: 4096,
  maxQueuedBytes: 4096,
  maxAttempts,
  operationDeadlineMs: 5_000,
  redirectPolicy: { maxRedirects: 0, crossOrigin: "deny" },
})

const node = CasNodeInput.make({
  kind: { version: 0, tag: 3 },
  payload: Uint8Array.from([6, 1, 8, 0]),
  refs: [],
})

const adapterOver = (authority: string, maxAttempts = 1) =>
  Effect.gen(function* () {
    const remoteConfig = config(authority, maxAttempts)
    const transport = yield* makeRemoteHttp(remoteConfig)
    const address = yield* makeSha256Address
    return yield* makeRemoteAdapter(remoteConfig, transport, address)
  })

it.effect("a peer silent before its response headers expires as a Silence event", () =>
  Effect.scoped(Effect.gen(function* () {
    const bytes = encodeCasNode(node)
    const endpoint = yield* serveGatedPeer(bytes, "beforeHeaders")

    yield* Effect.gen(function* () {
      // Three attempts are budgeted; a deadline must spend none of them.
      const adapter = yield* adapterOver(endpoint.authority, 3)
      const loading = yield* adapter.store.load(digest(bytes)).pipe(
        Effect.flip,
        Effect.forkScoped,
      )
      yield* endpoint.awaitRequest(1)
      yield* TestClock.adjust(5_001)

      const error = yield* Fiber.join(loading)
      expect(error).toMatchObject({
        _tag: "CasError/RemoteFailure",
        cause: {
          _tag: "CasRemoteError/Unavailable",
          code: "timeout",
          completion: "possiblyProcessed",
        },
      })

      yield* endpoint.awaitClosed(1)
      expect(yield* adapter.snapshot).toMatchObject({ inFlightSize: 0, cacheSize: 0 })
      expect(endpoint.observe().gets).toBe(1)
      yield* awaitPeerSocketsReleased(endpoint)
      expect(endpoint.observe().openSockets).toBe(0)
    }).pipe(Effect.provide(HttpRuntime))
  })))

it.effect("a response completed inside the deadline is admitted and leaves no in-flight state", () =>
  Effect.scoped(Effect.gen(function* () {
    const bytes = encodeCasNode(node)
    const endpoint = yield* serveGatedPeer(bytes, "none")

    yield* Effect.gen(function* () {
      const adapter = yield* adapterOver(endpoint.authority)
      // The clock never advances: the deadline cannot be what resolves this.
      const loaded = yield* adapter.store.load(digest(bytes))
      expect(Array.from(loaded.payload)).toEqual(Array.from(node.payload))
      expect(yield* adapter.snapshot).toMatchObject({ inFlightSize: 0 })
      expect(endpoint.observe().gets).toBe(1)
      yield* awaitPeerSocketsReleased(endpoint)
      expect(endpoint.observe().openSockets).toBe(0)
    }).pipe(Effect.provide(HttpRuntime))
  })))
