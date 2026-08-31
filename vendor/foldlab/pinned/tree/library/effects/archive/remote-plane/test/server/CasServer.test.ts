/**
 * The real server against the wire authority: full PUT admission
 * (canonical decode, known kind, reference closure, size budget, digest
 * equality), server-side closure verification on publish, the closed
 * capability and presence documents, profile-header refusal, closed
 * empty acknowledgments, and the §9 bearer rules — then the shipped
 * adapter run against it end to end, client versus server as handler
 * substitution over a real socket.
 */
import { expect, it } from "@effect/vitest"
import { Effect } from "effect"
import { createHash } from "node:crypto"
import { CasNodeInput, ContentId } from "../../src/cas/Node.ts"
import {
  encodeCasNode,
  layerCryptoWebCrypto,
  makeMemoryCasStore,
  makeSha256Address,
} from "../../src/cas/Store.ts"
import { remoteConfig } from "../../src/cas/Remote.ts"
import { makeRemoteAdapter } from "../../src/internal/remote.ts"
import { makeRemoteHttp } from "../../src/internal/remoteHttp.ts"
import { decodeCapabilityDocument } from "../../src/internal/remoteControl.ts"
import { makeEffectPeer } from "../remote/harness/EffectPeer.ts"

const digest = (bytes: Uint8Array): string =>
  createHash("sha256").update(bytes).digest("hex")

const node = (payload: ReadonlyArray<number>, tag: number, refs: CasNodeInput["refs"] = []) =>
  CasNodeInput.make({
    kind: { version: 0, tag },
    payload: Uint8Array.from(payload),
    refs,
  })

const octet = "application/octet-stream"
const profileHeaders = { accept: octet, "cas-profile": "cas-http/0" }

const toBody = (bytes: Uint8Array): ArrayBuffer =>
  bytes.slice().buffer as ArrayBuffer

const rawPut = (
  authority: string,
  path: string,
  body: Uint8Array,
  headers: Record<string, string> = {},
): Promise<Response> => fetch(`${authority}${path}`, {
  body: toBody(body),
  headers: { ...profileHeaders, "content-type": octet, ...headers },
  method: "PUT",
})

const keyList = (keys: ReadonlyArray<string>): Uint8Array => {
  const bytes = new Uint8Array(4 + keys.length * 32)
  new DataView(bytes.buffer).setUint32(0, keys.length)
  keys.forEach((key, index) => {
    for (let byte = 0; byte < 32; byte += 1) {
      bytes[4 + index * 32 + byte] = Number.parseInt(key.slice(byte * 2, byte * 2 + 2), 16)
    }
  })
  return bytes
}

it.effect("the capability document is exact and the profile header is required", () =>
  Effect.scoped(Effect.gen(function* () {
    const endpoint = yield* makeEffectPeer().serve({
      capabilities: { maxBatchKeys: 7, maxBlobBytes: 2048 },
    })
    const refused = yield* Effect.promise(() =>
      fetch(`${endpoint.authority}/control/capabilities`))
    expect(refused.status).toBe(400)

    const answered = yield* Effect.promise(() =>
      fetch(`${endpoint.authority}/control/capabilities`, { headers: profileHeaders }))
    const bytes = new Uint8Array(yield* Effect.promise(() => answered.arrayBuffer()))
    expect({ status: answered.status, length: bytes.length }).toEqual({
      status: 200,
      length: 8,
    })
    expect(decodeCapabilityDocument(bytes)).toMatchObject({
      value: { maxBatchKeys: 7, maxBlobBytes: 2048 },
    })
  })))

it.effect("upload admission enforces the full store law, not a digest check", () =>
  Effect.scoped(Effect.gen(function* () {
    const endpoint = yield* makeEffectPeer().serve({})
    const child = node([1, 2, 3], 91)
    const childBytes = encodeCasNode(child)
    const childId = digest(childBytes)

    const admitted = yield* Effect.promise(() =>
      rawPut(endpoint.authority, `/cas/${childId}`, childBytes))
    expect(admitted.status).toBe(201)
    // Closed empty acknowledgment: no body byte at all.
    expect((yield* Effect.promise(() => admitted.arrayBuffer())).byteLength).toBe(0)

    const rejoined = yield* Effect.promise(() =>
      rawPut(endpoint.authority, `/cas/${childId}`, childBytes))
    expect(rejoined.status).toBe(200)

    // Non-canonical bytes at their own correct digest: the reference
    // peer admitted these; the real server refuses them.
    const nonCanonical = Uint8Array.from([...childBytes, 0])
    const refusedShape = yield* Effect.promise(() =>
      rawPut(endpoint.authority, `/cas/${digest(nonCanonical)}`, nonCanonical))
    expect(refusedShape.status).toBe(409)

    // A canonical parent whose reference is not admitted content.
    const dangling = node([9], 92, [{
      id: ContentId.make("ab".repeat(32)),
      expectedTag: 91,
    }])
    const danglingBytes = encodeCasNode(dangling)
    const refusedClosure = yield* Effect.promise(() =>
      rawPut(endpoint.authority, `/cas/${digest(danglingBytes)}`, danglingBytes))
    expect(refusedClosure.status).toBe(409)

    // A digest that does not match the body.
    const refusedDigest = yield* Effect.promise(() =>
      rawPut(endpoint.authority, `/cas/${"00".repeat(32)}`, childBytes))
    expect(refusedDigest.status).toBe(409)

    // A body past the published node budget.
    const oversized = encodeCasNode(node(
      Array.from({ length: 5000 }, (_, index) => index % 256),
      93,
    ))
    const refusedBudget = yield* Effect.promise(() =>
      rawPut(endpoint.authority, `/cas/${digest(oversized)}`, oversized))
    expect(refusedBudget.status).toBe(413)
  })))

it.effect("publish verifies the declared closure server-side and is idempotent", () =>
  Effect.scoped(Effect.gen(function* () {
    const endpoint = yield* makeEffectPeer().serve({})
    const child = node([4, 5], 91)
    const childBytes = encodeCasNode(child)
    const childId = digest(childBytes)
    const parent = node([6], 92, [{ id: ContentId.make(childId), expectedTag: 91 }])
    const parentBytes = encodeCasNode(parent)
    const parentId = digest(parentBytes)

    const early = yield* Effect.promise(() =>
      rawPut(endpoint.authority, `/roots/${parentId}`, keyList([childId])))
    expect(early.status).toBe(409)

    // Root presence is a plain GET: absent until published.
    const unpublished = yield* Effect.promise(() =>
      fetch(`${endpoint.authority}/roots/${parentId}`, { headers: profileHeaders }))
    expect(unpublished.status).toBe(404)

    yield* Effect.promise(() => rawPut(endpoint.authority, `/cas/${childId}`, childBytes))
    yield* Effect.promise(() => rawPut(endpoint.authority, `/cas/${parentId}`, parentBytes))

    const published = yield* Effect.promise(() =>
      rawPut(endpoint.authority, `/roots/${parentId}`, keyList([childId])))
    expect(published.status).toBe(204)
    const republished = yield* Effect.promise(() =>
      rawPut(endpoint.authority, `/roots/${parentId}`, keyList([childId])))
    expect(republished.status).toBe(204)
    expect(endpoint.observe().publishedRoots).toEqual([parentId, parentId])

    const present = yield* Effect.promise(() =>
      fetch(`${endpoint.authority}/roots/${parentId}`, { headers: profileHeaders }))
    expect({ status: present.status }).toEqual({ status: 204 })
    expect((yield* Effect.promise(() => present.arrayBuffer())).byteLength).toBe(0)
  })))

it.effect("presence answers positionally over the admitted set", () =>
  Effect.scoped(Effect.gen(function* () {
    const child = node([7, 8], 91)
    const childBytes = encodeCasNode(child)
    const childId = digest(childBytes)
    const endpoint = yield* makeEffectPeer().serve({
      nodes: new Map([[childId, childBytes]]),
    })
    const answered = yield* Effect.promise(() => fetch(
      `${endpoint.authority}/control/missing`,
      {
        body: toBody(keyList([childId, "cd".repeat(32)])),
        headers: { ...profileHeaders, "content-type": octet },
        method: "POST",
      },
    ))
    const statuses = new Uint8Array(yield* Effect.promise(() => answered.arrayBuffer()))
    expect({ status: answered.status, statuses: Array.from(statuses) }).toEqual({
      status: 200,
      statuses: [1, 0],
    })
  })))

it.effect("bearer policy: writes require the credential, reads may stay anonymous", () =>
  Effect.scoped(Effect.gen(function* () {
    const { Redacted } = yield* Effect.promise(() => import("effect"))
    const endpoint = yield* makeEffectPeer({
      policy: {
        anonymousReads: true,
        credential: Redacted.make("open-sesame"),
      },
    }).serve({})
    const child = node([1], 91)
    const childBytes = encodeCasNode(child)
    const childId = digest(childBytes)

    const anonymousRead = yield* Effect.promise(() =>
      fetch(`${endpoint.authority}/cas/${"ef".repeat(32)}`, { headers: profileHeaders }))
    expect(anonymousRead.status).toBe(404)

    const anonymousWrite = yield* Effect.promise(() =>
      rawPut(endpoint.authority, `/cas/${childId}`, childBytes))
    expect(anonymousWrite.status).toBe(401)

    const wrongBearer = yield* Effect.promise(() =>
      rawPut(endpoint.authority, `/cas/${childId}`, childBytes, {
        authorization: "Bearer wrong",
      }))
    expect(wrongBearer.status).toBe(401)

    const bearerWrite = yield* Effect.promise(() =>
      rawPut(endpoint.authority, `/cas/${childId}`, childBytes, {
        authorization: "Bearer open-sesame",
      }))
    expect(bearerWrite.status).toBe(201)
  })))

it.effect("the shipped adapter pushes and re-pushes a graph through the real server", () =>
  Effect.scoped(Effect.gen(function* () {
    const endpoint = yield* makeEffectPeer().serve({
      capabilities: { maxBatchKeys: 4, maxBlobBytes: 4096 },
    })
    const config = remoteConfig(endpoint.authority)
    const address = yield* makeSha256Address
    const localStore = yield* makeMemoryCasStore(address)
    const child = node([11, 12, 13], 91)
    const childId = yield* localStore.put(child)
    const parent = node([14], 92, [{ id: childId, expectedTag: 91 }])
    const parentId = yield* localStore.put(parent)
    const adapter = yield* makeRemoteAdapter(
      config,
      yield* makeRemoteHttp(config),
      address,
      { localStore },
    )

    const first = yield* adapter.transfer.push(parentId)
    expect({
      transferred: [...first.transferred].sort(),
      alreadyPresent: first.alreadyPresent,
    }).toEqual({
      transferred: [childId, parentId].sort(),
      alreadyPresent: [],
    })
    expect(endpoint.observe().publishedRoots).toEqual([parentId])

    // The second push attests what the server reports present: no
    // downloads, nothing re-uploaded, the root republished.
    const second = yield* adapter.transfer.push(parentId)
    expect({
      transferred: second.transferred,
      alreadyPresent: [...second.alreadyPresent].sort(),
    }).toEqual({
      transferred: [],
      alreadyPresent: [childId, parentId].sort(),
    })
    expect(endpoint.observe().gets).toBe(0)
  }).pipe(Effect.provide(layerCryptoWebCrypto))))
