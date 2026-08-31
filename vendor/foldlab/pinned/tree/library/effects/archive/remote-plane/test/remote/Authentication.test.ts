/**
 * The cas-http/0 credential clause: one opaque bearer credential per
 * authority, presented on every request there and structurally absent from
 * everything the library renders. A `401` is terminal for its operation —
 * there is no challenge negotiation at `/0` and nothing retries.
 */
import { expect, it } from "@effect/vitest"
import { Crypto, Effect, Layer, Redacted } from "effect"
import * as FetchHttpClient from "effect/unstable/http/FetchHttpClient"
import { createHash, randomBytes } from "node:crypto"
import * as Cas from "../../src/Cas.ts"
import { CasNodeInput, ContentId } from "../../src/cas/Node.ts"
import { CasRemoteConfig, RemoteAuthority } from "../../src/cas/Remote.ts"
import { CasStore, encodeCasNode, makeSha256Address } from "../../src/cas/Store.ts"
import { CasTransfer } from "../../src/cas/Transfer.ts"
import { makeRemoteAdapter } from "../../src/internal/remote.ts"
import { makeRemoteHttp } from "../../src/internal/remoteHttp.ts"
import { serveCredentialPeer } from "./harness/CredentialPeer.ts"

/** The one credential these tests configure. Nothing the library renders may
 * contain it. */
const secret = "s3cr3t-cas-credential-e2e"

/** The configuration schema validates a credential against its declared
 * label, so a credential must be minted under that same label. */
const credential = Redacted.make(secret, { label: "CAS credentials" })

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

const config = (
  authority: string,
  overrides: {
    readonly credentials?: Redacted.Redacted<string>
    readonly maxAttempts?: number
  } = {},
) => new CasRemoteConfig({
  authority: RemoteAuthority.make(authority),
  authorityMode: "remote-authoritative",
  maxEncodedBytes: 4096,
  maxDecodedBytes: 4096,
  maxDecompressedBytes: 4096,
  maxQueuedBytes: 4096,
  maxAttempts: overrides.maxAttempts ?? 1,
  operationDeadlineMs: 5_000,
  redirectPolicy: { maxRedirects: 0, crossOrigin: "deny" },
  ...(overrides.credentials === undefined ? {} : { credentials: overrides.credentials }),
})

const node = (payload: ReadonlyArray<number>, tag = 3) => CasNodeInput.make({
  kind: { version: 0, tag },
  payload: Uint8Array.from(payload),
  refs: [],
})

const remoteLayer = (remoteConfig: CasRemoteConfig) =>
  Cas.layerRemote(remoteConfig).pipe(Layer.provideMerge(HttpRuntime))

/** Every rendering a caller might reach for, joined into one string. */
const renderings = (values: ReadonlyArray<unknown>): string =>
  values.map((value) => {
    try {
      return `${String(value)} ${JSON.stringify(value)}`
    } catch {
      return String(value)
    }
  }).join(" ")

it.effect("a configured credential accompanies every request to its authority", () =>
  Effect.scoped(Effect.gen(function* () {
    const residentBytes = encodeCasNode(node([1, 2, 3]))
    const endpoint = yield* serveCredentialPeer({
      nodes: new Map([[digest(residentBytes), residentBytes]]),
    })

    yield* Effect.gen(function* () {
      const store = yield* CasStore
      const transfer = yield* CasTransfer
      yield* store.load(digest(residentBytes))
      yield* transfer.missing([digest(residentBytes)])
      yield* store.put(node([4, 5, 6], 4))
    }).pipe(Effect.provide(remoteLayer(config(endpoint.authority, { credentials: credential }))))

    const observed = endpoint.observe()
    // The capability probe, the load, the batch, and the upload.
    expect(observed.requests).toBe(4)
    expect(observed.authorizations).toEqual(
      Array.from({ length: observed.requests }, () => `Bearer ${secret}`),
    )
  })))

it.effect("configuration without a credential sends no Authorization header", () =>
  Effect.scoped(Effect.gen(function* () {
    const residentBytes = encodeCasNode(node([7, 8, 9]))
    const endpoint = yield* serveCredentialPeer({
      nodes: new Map([[digest(residentBytes), residentBytes]]),
    })

    yield* Effect.gen(function* () {
      const store = yield* CasStore
      yield* store.load(digest(residentBytes))
      yield* store.put(node([10, 11], 5))
    }).pipe(Effect.provide(remoteLayer(config(endpoint.authority))))

    const observed = endpoint.observe()
    expect(observed.requests).toBe(3)
    expect(observed.authorizations).toEqual(
      Array.from({ length: observed.requests }, () => undefined),
    )
  })))

it.effect("a 401 is terminal for its operation: no retry and no challenge answer", () =>
  Effect.scoped(Effect.gen(function* () {
    const deniedId = digest(encodeCasNode(node([2, 4, 8])))
    const endpoint = yield* serveCredentialPeer({ unauthenticated: true })

    const error = yield* CasStore.use((store) => store.load(deniedId)).pipe(
      Effect.flip,
      Effect.provide(remoteLayer(config(endpoint.authority, {
        credentials: credential,
        maxAttempts: 3,
      }))),
    )

    expect(error).toMatchObject({
      _tag: "CasError/RemoteFailure",
      cause: { _tag: "CasRemoteError/Unavailable", code: "unauthenticated" },
    })
    // One capability probe and exactly one denied load: the challenge is never
    // answered and the attempt budget is never spent on a 401.
    expect(endpoint.observe().gets).toBe(1)
    expect(endpoint.observe().requests).toBe(2)
  })))

it.effect("no credential byte reaches an error, a push report, or a decision transcript", () =>
  Effect.scoped(Effect.gen(function* () {
    const child = node([3, 3, 3], 6)
    const childBytes = encodeCasNode(child)
    const endpoint = yield* serveCredentialPeer({})
    const remoteConfig = config(endpoint.authority, { credentials: credential })

    yield* Effect.gen(function* () {
      const transport = yield* makeRemoteHttp(remoteConfig)
      const address = yield* makeSha256Address
      const adapter = yield* makeRemoteAdapter(remoteConfig, transport, address)

      const root = yield* adapter.store.put(child)
      const report = yield* adapter.transfer.push(root)
      expect([...report.transferred, ...report.alreadyPresent]).toEqual([digest(childBytes)])

      const failure = yield* adapter.store.load(digest(encodeCasNode(node([0], 9)))).pipe(
        Effect.flip,
      )
      const snapshot = yield* adapter.snapshot
      expect(snapshot.decisions.length).toBeGreaterThan(0)

      const rendered = renderings([
        failure,
        report,
        snapshot.decisions,
        remoteConfig,
        remoteConfig.credentials,
      ])
      // Positive controls: these renderings really did carry their content,
      // so the credential's absence from them is a fact and not a vacuity.
      expect(rendered).toContain(remoteConfig.authority)
      expect(rendered).toContain(digest(childBytes))

      expect(rendered).not.toContain(secret)
      expect(rendered).not.toContain("Bearer")
    }).pipe(Effect.provide(HttpRuntime))
  })))
