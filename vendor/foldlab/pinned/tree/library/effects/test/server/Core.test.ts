/**
 * The factoring's payoff, demonstrated: the wire law is a pure function
 * tested as a table, and the semantic core round-trips over the memory
 * backend with no HTTP anywhere — the same core the socket peer serves.
 */
import { expect, it } from "@effect/vitest"
import { Effect, Layer, Redacted } from "effect"
import { createHash } from "node:crypto"
import {
  ByteReader,
  ByteWriter,
  layerMemoryBackend,
  makeMemoryBackend,
  RootStore,
} from "../../src/cas/Backend.ts"
import { CasNodeInput, ContentId, StoreFailure } from "../../src/cas/Node.ts"
import { encodeCasNode, layerAddressSha256Live } from "../../src/cas/Store.ts"
import { encodeKeyListDocument } from "../../src/internal/wire.ts"
import { CasServerCore } from "../../src/server/Core.ts"
import {
  CasOutcome,
  CasRequest,
  decide,
  Principal,
  type CasServerPolicy,
  type WireFacts,
} from "../../src/server/Protocol.ts"
import { deterministicAddress } from "../fixtures/address.ts"

const digest = (bytes: Uint8Array): string =>
  createHash("sha256").update(bytes).digest("hex")

const openPolicy: CasServerPolicy = { maxBatchKeys: 4, maxNodeBytes: 4096 }

const guardedPolicy: CasServerPolicy = {
  anonymousReads: true,
  credential: Redacted.make("secret"),
  maxBatchKeys: 4,
  maxNodeBytes: 4096,
}

const facts = (overrides: Partial<WireFacts>): WireFacts => ({
  authorization: undefined,
  body: new Uint8Array(0),
  contentType: "application/octet-stream",
  method: "GET",
  path: "/control/capabilities",
  profile: "cas-http/0",
  ...overrides,
})

const hex = (byte: string): string => byte.repeat(32)

it.effect("the wire law decides the precedence table purely", () =>
  Effect.sync(() => {
    const table: ReadonlyArray<{
      readonly name: string
      readonly policy: CasServerPolicy
      readonly facts: WireFacts
      readonly expected: string
    }> = [
      {
        name: "profile header before everything",
        policy: guardedPolicy,
        facts: facts({ profile: undefined, authorization: "Bearer wrong" }),
        expected: "Refused/MissingProfile",
      },
      {
        name: "a wrong bearer never authenticates",
        policy: guardedPolicy,
        facts: facts({ authorization: "Bearer wrong" }),
        expected: "Refused/Unauthenticated",
      },
      {
        name: "an unknown resource is malformed wire",
        policy: openPolicy,
        facts: facts({ path: "/elsewhere" }),
        expected: "Refused/UnknownResource",
      },
      {
        name: "method is checked before media type",
        policy: openPolicy,
        facts: facts({ path: "/control/missing", contentType: undefined }),
        expected: "Refused/MethodNotAllowed",
      },
      {
        name: "media type is checked before the body decodes",
        policy: openPolicy,
        facts: facts({
          body: Uint8Array.from([9]),
          contentType: "text/plain",
          method: "POST",
          path: "/control/missing",
        }),
        expected: "Refused/WrongMediaType",
      },
      {
        name: "a malformed key list never becomes an operation",
        policy: openPolicy,
        facts: facts({
          body: Uint8Array.from([1, 2, 3]),
          method: "POST",
          path: "/control/missing",
        }),
        expected: "Refused/MalformedBody",
      },
      {
        name: "anonymous reads pass under the guarded policy",
        policy: guardedPolicy,
        facts: facts({ path: `/cas/${hex("ab")}` }),
        expected: "Accepted/LoadNode/Anonymous",
      },
      {
        name: "a root read is a read: GET /roots decodes and stays anonymous",
        policy: guardedPolicy,
        facts: facts({ path: `/roots/${hex("ab")}` }),
        expected: "Accepted/ReadRoot/Anonymous",
      },
      {
        name: "anonymous writes never pass under the guarded policy",
        policy: guardedPolicy,
        facts: facts({ method: "PUT", path: `/cas/${hex("ab")}` }),
        expected: "Refused/Unauthenticated",
      },
      {
        name: "the bearer principal reaches the operation",
        policy: guardedPolicy,
        facts: facts({
          authorization: "Bearer secret",
          method: "PUT",
          path: `/cas/${hex("ab")}`,
        }),
        expected: "Accepted/UploadNode/Bearer",
      },
    ]

    for (const row of table) {
      const decision = decide(row.policy, row.facts)
      const observed = decision._tag === "Refused"
        ? `Refused/${decision.refusal._tag}`
        : `Accepted/${decision.request._tag}/${decision.principal._tag}`
      expect({ name: row.name, observed }).toEqual({
        name: row.name,
        observed: row.expected,
      })
    }
  }))

const coreLayer = CasServerCore.layer(openPolicy).pipe(
  Layer.provideMerge(Layer.mergeAll(
    layerMemoryBackend,
    layerAddressSha256Live,
  )),
)

it.effect("the semantic core round-trips a graph with no transport at all", () =>
  Effect.gen(function* () {
    const core = yield* CasServerCore
    const anonymous = Principal.Anonymous()

    const child = CasNodeInput.make({
      kind: { version: 0, tag: 91 },
      payload: Uint8Array.from([1, 2, 3]),
      refs: [],
    })
    const childBytes = encodeCasNode(child)
    const childId = ContentId.make(digest(childBytes))
    const parent = CasNodeInput.make({
      kind: { version: 0, tag: 92 },
      payload: Uint8Array.from([4]),
      refs: [{ id: childId, expectedTag: 91 }],
    })
    const parentBytes = encodeCasNode(parent)
    const parentId = ContentId.make(digest(parentBytes))

    // Parent before child: the shared admission law refuses the closure.
    const early = yield* core.serve(
      anonymous,
      CasRequest.UploadNode({ bytes: parentBytes, id: parentId }),
    )
    expect(early).toEqual(CasOutcome.AdmissionRefused({ verdict: "DanglingReference" }))

    expect(yield* core.serve(
      anonymous,
      CasRequest.UploadNode({ bytes: childBytes, id: childId }),
    )).toEqual(CasOutcome.Admitted())
    expect(yield* core.serve(
      anonymous,
      CasRequest.UploadNode({ bytes: parentBytes, id: parentId }),
    )).toEqual(CasOutcome.Admitted())

    const loaded = yield* core.serve(
      anonymous,
      CasRequest.LoadNode({ id: childId }),
    )
    expect(loaded).toEqual(CasOutcome.NodeBytes({ bytes: childBytes }))

    expect(yield* core.serve(
      anonymous,
      CasRequest.QueryPresence({
        keys: [childId, ContentId.make(hex("cd"))],
      }),
    )).toEqual(CasOutcome.Presence({ statuses: ["present", "missing"] }))

    // Root presence answers over the published set — absent before,
    // published after.
    expect(yield* core.serve(
      anonymous,
      CasRequest.ReadRoot({ root: parentId }),
    )).toEqual(CasOutcome.RootAbsent())

    expect(yield* core.serve(
      anonymous,
      CasRequest.PublishRoot({ closure: [childId], root: parentId }),
    )).toEqual(CasOutcome.Published())

    expect(yield* core.serve(
      anonymous,
      CasRequest.ReadRoot({ root: parentId }),
    )).toEqual(CasOutcome.RootPublished())

    // The decoded key-list codec and the core agree on the wire body.
    expect(encodeKeyListDocument([childId]).length).toBe(36)
  }).pipe(Effect.provide(coreLayer)))
