/**
 * Executable pins for the verified host-boundary review of 0fa1bde7.
 *
 * Discipline: each pin exercises one confirmed finding's exact fault
 * scenario. Remediated pins assert the fixed behavior; a pin intentionally
 * left standing documents a ruled deferral beside its current expectation.
 * Findings resolved before this review exist as locks.
 *
 * Not pinned here, with reasons:
 * - CQ-2 (manufactured budget evidence in `resultError`) and CQ-3 (the
 *   three-primitive session synchronization topology) are internal shape
 *   findings with no distinct observable behavior; their behavioral
 *   consequences are pinned by findings 2 and 3.
 * - DX-2 (restartable source) is RESOLVED — the factory contract is
 *   witnessed by "a restartable upload reacquires and rechecks its source
 *   before a bounded retry" in remote/RemoteAdapter.test.ts.
 * - DX-6 (budget units in prose) is a naming finding; pin 8 covers the
 *   one place where the unlabeled number is also wrong.
 * - Finding 2 is RESOLVED by SES-003: the reducer tracks the outstanding
 *   delegation, refuses interleaved invocations (DelegationOutstanding)
 *   and unsolicited outcomes (UnsolicitedOutcome), and the runtime
 *   converts the refusal into a typed session rejection — lock 2 below.
 *   Sound concurrent recording (event identity and causality) remains a
 *   designed future milestone, per IMPLEMENTATION-PLAN.md.
 */
import { expect, it } from "@effect/vitest"
import { expectTypeOf } from "vitest"
import {
  Channel,
  Context,
  Crypto,
  Deferred,
  Effect,
  Encoding,
  Fiber,
  Layer,
  Schema,
  Stream,
} from "effect"
import { TestClock } from "effect/testing"
import * as HttpClient from "effect/unstable/http/HttpClient"
import * as HttpClientError from "effect/unstable/http/HttpClientError"
import * as HttpClientRequest from "effect/unstable/http/HttpClientRequest"
import { createHash, randomBytes } from "node:crypto"
import * as barrel from "../src/index.ts"
import { CasNodeInput, ContentId } from "../src/cas/Node.ts"
import {
  encodeCasNode,
  layerMemory,
  makeMemoryCasStore,
  makeSha256Address,
  CasStore,
  type CasAddress,
} from "../src/cas/Store.ts"
import { CasRemoteConfig, RemoteAuthority, restartable } from "../src/cas/Remote.ts"
import type { CasTransferShape } from "../src/cas/Transfer.ts"
import { CasBlob } from "../src/cas/Blob.ts"
import { makeRemoteAdapter } from "../src/internal/remote.ts"
import { classifyTransportFailure, makeRemoteHttp } from "../src/internal/remoteHttp.ts"
import { encodeCapabilityDocument } from "../src/internal/remoteControl.ts"
import type { RemoteCasTransport } from "../src/internal/remoteTransport.ts"
import type { ServiceDescriptions } from "../src/replay/Operation.ts"
import { describeService } from "../src/replay/Operation.ts"
import { layerReplay, session } from "../src/replay/Replay.ts"
import { WitnessSink, type WitnessReceipt } from "../src/replay/WitnessSink.ts"
import { replayable } from "../src/replay/ServiceAdapter.ts"
import { decodeWitness, StoredWitness } from "../src/internal/storage.ts"
import { awaitPeerSocketsReleased } from "./remote/harness/ConformancePeer.ts"
import { HostilePeer } from "./remote/harness/HostilePeer.ts"
import {
  deterministicAddress,
  HistoryKindTag as HistoryTag,
  WitnessKindTag as WitnessTag,
} from "./fixtures/address.ts"

class PinFail extends Schema.TaggedError<PinFail>()(
  "ReviewPins/Fail",
  { note: Schema.String },
) {}

interface SpyPut {
  readonly id: ContentId
  readonly node: CasNodeInput
}

/** A memory store whose puts are captured after commit, with optional
 * hooks before and after the underlying admission. */
const makeSpyStore = (hooks?: {
  readonly before?: (node: CasNodeInput) => Effect.Effect<void>
  readonly after?: (node: CasNodeInput, id: ContentId) => Effect.Effect<void>
}) => Effect.gen(function* () {
  const underlying = yield* makeMemoryCasStore(deterministicAddress())
  const captured: Array<SpyPut> = []
  const shape = CasStore.of({
    put: (input) => Effect.gen(function* () {
      if (hooks?.before) yield* hooks.before(input)
      const id = yield* underlying.put(input)
      captured.push({ id, node: input })
      if (hooks?.after) yield* hooks.after(input, id)
      return id
    }),
    load: underlying.load,
  })
  return { shape, captured, underlying }
})

const decodeStoredWitness = (payload: Uint8Array) =>
  Schema.decodeUnknownSync(StoredWitness)(decodeWitness(payload))

const TestCrypto = Layer.succeed(Crypto.Crypto, Crypto.make({
  randomBytes: (size) => new Uint8Array(randomBytes(size)),
  digest: (algorithm, bytes) => Effect.sync(() => {
    const name = algorithm.toLowerCase().replace("-", "")
    return new Uint8Array(createHash(name).update(bytes).digest())
  }),
}))

const pinConfig = (overrides: Partial<{
  readonly authority: string
  readonly maxEncodedBytes: number
  readonly maxQueuedBytes: number
}> = {}) => new CasRemoteConfig({
  authority: RemoteAuthority.make(overrides.authority ?? "http://127.0.0.1:1"),
  authorityMode: "remote-authoritative",
  maxEncodedBytes: overrides.maxEncodedBytes ?? 4096,
  maxDecodedBytes: 4096,
  maxDecompressedBytes: 4096,
  maxQueuedBytes: overrides.maxQueuedBytes ?? 4096,
  maxAttempts: 1,
  operationDeadlineMs: 5_000,
  redirectPolicy: { maxRedirects: 0, crossOrigin: "deny" },
})

const capabilityBytes = () =>
  encodeCapabilityDocument({ maxBatchKeys: 4, maxBlobBytes: 4_096 })

/** A transport that serves the capability probe and refuses any other
 * wire exchange — for adapter paths that must fail before traffic. */
const probeOnlyTransport = (): RemoteCasTransport => ({
  issue: (_operationId, _attempt, request) => {
    if (request.command._tag === "ProbeCapabilities") {
      const bytes = capabilityBytes()
      return Channel.fromArray([
        { _tag: "ResponseStarted", declared: bytes.length } as const,
        { _tag: "BodyChunk", bytes } as const,
      ]).pipe(
        Channel.concatWith(() => Channel.fromEffectDone(Effect.succeed({
          receivedBytes: bytes.length,
          sentBytes: 0,
          terminalFraming: "complete" as const,
        }))),
      )
    }
    return Channel.fromEffectDone(
      Effect.die(new Error("review pin drove an unexpected wire exchange")),
    )
  },
})

/* ------------------------------------------------------------------ */
/* Replay fixtures                                                     */
/* ------------------------------------------------------------------ */

interface PairShape {
  readonly alpha: (x: string) => Effect.Effect<string, PinFail>
  readonly beta: (x: string) => Effect.Effect<string, PinFail>
}

class Pair extends Context.Service<Pair, PairShape>()(
  "test/effect-replay/ReviewPins/Pair",
) {}

const PairDescriptions = {
  alpha: {
    id: "pins/Pair/alpha",
    revision: 0,
    request: Schema.String,
    success: Schema.String,
    failure: PinFail,
    leafReplay: "substitutable",
  },
  beta: {
    id: "pins/Pair/beta",
    revision: 0,
    request: Schema.String,
    success: Schema.String,
    failure: PinFail,
    leafReplay: "substitutable",
  },
} satisfies ServiceDescriptions<PairShape>

const pairKit = replayable(Pair, PairDescriptions)

const runtimeOver = (store: Layer.Layer<CasStore>) =>
  layerReplay.pipe(Layer.provide(store))

/* ------------------------------------------------------------------ */
/* Finding 1 — the redirect guarantee is not transport-independent      */
/* ------------------------------------------------------------------ */

it.effect("pin 1: the owned Fetch transport observes a real redirect without following it", () =>
  Effect.scoped(Effect.gen(function* () {
    const endpoint = yield* HostilePeer.serve({
      fault: "redirect",
      body: new Uint8Array(),
    })
    const remoteConfig = new CasRemoteConfig({
      ...pinConfig(),
      authority: RemoteAuthority.make(endpoint.authority),
    })
    const transport = yield* makeRemoteHttp(remoteConfig)
    const address = yield* makeSha256Address
    const adapter = yield* makeRemoteAdapter(remoteConfig, transport, address)
    const id = ContentId.make("00".repeat(32))
    const error = yield* adapter.store.load(id).pipe(Effect.flip)
    expect(error).toMatchObject({
      _tag: "CasError/RemoteFailure",
      cause: { _tag: "CasRemoteError/Policy", code: "redirectDenied" },
    })
    expect(endpoint.observe().gets).toBe(1)
    yield* awaitPeerSocketsReleased(endpoint)
    expect(endpoint.observe().openSockets).toBe(0)
  }).pipe(Effect.provide(TestCrypto))))

/* ------------------------------------------------------------------ */
/* Finding 2 — concurrent record has completion-order semantics         */
/* ------------------------------------------------------------------ */

it.effect("lock 2: overlapping record invocation is refused as DelegationOutstanding", () =>
  Effect.gen(function* () {
    // RESOLVED by SES-003: record-mode delegation is exclusive, so the
    // completion-order history the original finding demonstrated is now
    // unrepresentable — the second in-flight invocation is a typed
    // rejection before any occurrence exists. Sound concurrent recording
    // (event identity and causality) is reserved as its own milestone.
    const spy = yield* makeSpyStore()
    const runtime = runtimeOver(Layer.succeed(CasStore, spy.shape))
    const parked = yield* Deferred.make<void>()
    const live = Pair.of({
      alpha: (x) => Deferred.await(parked).pipe(Effect.as(`A:${x}`)),
      beta: (x) => Effect.succeed(`B:${x}`),
    })
    const concurrent = Pair.use((pair) =>
      Effect.all([pair.alpha("x"), pair.beta("y")], { concurrency: 2 }))
    const recorded = yield* session(
      concurrent.pipe(
        Effect.provide(pairKit.record),
        Effect.provideService(pairKit.live, live),
      ),
      { mode: "record" },
    ).pipe(Effect.provide(runtime))
    expect(recorded.outcome).toMatchObject({
      _tag: "Rejected",
      category: "DelegationOutstanding",
      at: 0,
    })
    expect(recorded.history).toBeUndefined()
    expect(spy.captured.filter((p) => p.node.kind.tag === HistoryTag))
      .toHaveLength(0)
  }))

/* ------------------------------------------------------------------ */
/* Finding 3 — interruption between CAS commit and state publication    */
/* ------------------------------------------------------------------ */

it.effect("pin 3: history commit and session-state publication form one masked cell update", () =>
  Effect.gen(function* () {
    const reachedWindow = yield* Deferred.make<void>()
    const holdWindow = yield* Deferred.make<void>()
    let historyPuts = 0
    const spy = yield* makeSpyStore({
      after: (node) => Effect.gen(function* () {
        if (node.kind.tag !== HistoryTag) return
        historyPuts += 1
        if (historyPuts === 2) {
          // The second history node is committed; hold the fiber inside
          // the masked cell update before it publishes the new state.
          yield* Deferred.succeed(reachedWindow, undefined)
          yield* Deferred.await(holdWindow)
        }
      }),
    })
    const live = Pair.of({
      alpha: (x) => Effect.succeed(`A:${x}`),
      beta: (x) => Effect.succeed(`B:${x}`),
    })
    const program = Pair.use((pair) =>
      Effect.gen(function* () {
        yield* pair.alpha("one")
        yield* pair.beta("two")
      }))
    const fiber = yield* session(
      program.pipe(
        Effect.provide(pairKit.record),
        Effect.provideService(pairKit.live, live),
      ),
      { mode: "record" },
    ).pipe(
      Effect.provide(runtimeOver(Layer.succeed(CasStore, spy.shape))),
      Effect.forkChild,
    )
    yield* Deferred.await(reachedWindow)
    const interruptor = yield* Fiber.interrupt(fiber).pipe(Effect.forkChild)
    // Give the interrupt request a scheduling turn while the target remains
    // parked in the masked update, then let that update publish atomically.
    yield* Effect.yieldNow
    yield* Deferred.succeed(holdWindow, undefined)
    yield* Fiber.join(interruptor)

    const historyIds = spy.captured
      .filter((p) => p.node.kind.tag === HistoryTag)
      .map((p) => p.id)
    expect(historyIds).toHaveLength(2)
    const first = historyIds[0]
    const second = historyIds[1]
    if (first === undefined || second === undefined) {
      return yield* Effect.die("expected two committed history nodes")
    }
    // The second node IS committed in the store...
    const committed = yield* spy.underlying.load(second)
    expect(committed.kind.tag).toBe(HistoryTag)
    // The masked cell update publishes the committed root before the pending
    // interruption can reach the aborted-witness finalizer.
    const witness = spy.captured.find((p) => p.node.kind.tag === WitnessTag)
    if (witness === undefined) {
      return yield* Effect.die("expected a persisted aborted witness")
    }
    const stored = decodeStoredWitness(witness.node.payload)
    expect(stored.outcome).toEqual({ _tag: "Aborted", reason: "Interrupted" })
    expect(stored.historyRoot).toBe(second)
    expect(stored.historyRoot).not.toBe(first)
  }))

/* ------------------------------------------------------------------ */
/* Finding 4 — generic terminals die in the plain-object codec          */
/* ------------------------------------------------------------------ */

it.effect("pin 4: an unsupported terminal persists the declared unrepresentable marker", () =>
  Effect.gen(function* () {
    const spy = yield* makeSpyStore()
    const result = yield* session(
      Effect.succeed(new Date(0)),
      { mode: "record" },
    ).pipe(Effect.provide(runtimeOver(Layer.succeed(CasStore, spy.shape))))
    expect(result.outcome).toMatchObject({
      _tag: "Completed",
      terminal: { _tag: "Succeeded", value: new Date(0) },
    })
    const witness = spy.captured.find((put) => put.node.kind.tag === WitnessTag)
    if (witness === undefined) return yield* Effect.die("expected terminal witness")
    expect(decodeStoredWitness(witness.node.payload).outcome).toEqual({
      _tag: "Completed",
      terminal: {
        _tag: "Succeeded",
        value: { _tag: "Unrepresentable" },
      },
    })
  }))

it.effect("explicit terminal schemas project non-plain values before witness storage", () =>
  Effect.gen(function* () {
    const spy = yield* makeSpyStore()
    yield* session(
      Effect.succeed(new Date(0)),
      {
        mode: "record",
        terminal: {
          success: Schema.DateFromMillis,
          failure: Schema.Never,
        },
      },
    ).pipe(Effect.provide(runtimeOver(Layer.succeed(CasStore, spy.shape))))
    const witness = spy.captured.find((put) => put.node.kind.tag === WitnessTag)
    if (witness === undefined) return yield* Effect.die("expected projected witness")
    const outcome = decodeStoredWitness(witness.node.payload).outcome
    expect(outcome._tag).toBe("Completed")
    if (outcome._tag === "Completed" && outcome.terminal._tag === "Succeeded") {
      expect(outcome.terminal.value).not.toEqual({ _tag: "Unrepresentable" })
    }
  }))

/* ------------------------------------------------------------------ */
/* Finding 5 — abort persistence is owned, bounded, and receipted        */
/* ------------------------------------------------------------------ */

it.effect("pin 5a: the aborted witness receipt reaches the sink", () =>
  Effect.gen(function* () {
    const spy = yield* makeSpyStore()
    const receipts: Array<WitnessReceipt> = []
    const defect = new Error("pin-defect")
    const caught = yield* session(Effect.die(defect), { mode: "record" }).pipe(
      Effect.catchDefect((d) => Effect.succeed(d)),
      Effect.provide(runtimeOver(Layer.succeed(CasStore, spy.shape))),
      Effect.provideService(WitnessSink, {
        record: (receipt) => Effect.sync(() => {
          receipts.push(receipt)
        }),
      }),
    )
    const witness = spy.captured.find((p) => p.node.kind.tag === WitnessTag)
    if (witness === undefined) {
      return yield* Effect.die("expected a persisted aborted witness")
    }
    const stored = decodeStoredWitness(witness.node.payload)
    expect(stored.outcome).toEqual({ _tag: "Aborted", reason: "Defect" })
    // The emitted channel still re-raises the original defect unchanged;
    // the receipt travels through the sink, carrying the witness id.
    expect(caught).toBe(defect)
    expect(receipts).toEqual([{
      executionId: stored.executionId,
      reason: "Defect",
      result: { _tag: "Persisted", witness: witness.id },
    }])
  }))

it.effect("pin 5b: a hung abort write is interrupted at the deadline and receipted as timed out", () =>
  Effect.gen(function* () {
    const witnessStarted = yield* Deferred.make<void>()
    const releaseStore = yield* Deferred.make<void>()
    const receipts: Array<WitnessReceipt> = []
    const spy = yield* makeSpyStore({
      before: (node) => node.kind.tag === WitnessTag
        ? Deferred.succeed(witnessStarted, undefined).pipe(
            Effect.andThen(Deferred.await(releaseStore)),
          )
        : Effect.void,
    })
    const fiber = yield* session(
      Effect.die(new Error("pin-hang")),
      { mode: "record" },
    ).pipe(
      Effect.provide(runtimeOver(Layer.succeed(CasStore, spy.shape))),
      Effect.provideService(WitnessSink, {
        record: (receipt) => Effect.sync(() => {
          receipts.push(receipt)
        }),
      }),
      Effect.forkChild,
    )
    yield* Deferred.await(witnessStarted)
    let interruptSettled = false
    const interruptor = yield* Fiber.interrupt(fiber).pipe(
      Effect.tap(() => Effect.sync(() => {
        interruptSettled = true
      })),
      Effect.forkChild,
    )
    yield* TestClock.adjust(1_001)
    yield* Fiber.join(interruptor)
    expect(interruptSettled).toBe(true)
    // No detached fiber survives: the write was interrupted at the
    // deadline, and the sacrifice is observable rather than silent.
    // The reason is the abort's own cause — the defect that ended the
    // session — not the later interrupt racing its teardown.
    expect(receipts).toEqual([{
      executionId: expect.any(String),
      reason: "Defect",
      result: { _tag: "TimedOut" },
    }])
  }))

/* ------------------------------------------------------------------ */
/* Finding 6 — nested cancellation is misclassified                     */
/* ------------------------------------------------------------------ */

it("pin 6: an AbortError nested under a TypeError classifies as cancelled", () => {
  const request = HttpClientRequest.get("http://127.0.0.1/cas/pin")
  const error = new HttpClientError.HttpClientError({
    reason: new HttpClientError.TransportError({
      request,
      cause: Object.assign(new TypeError("fetch failed"), {
        cause: Object.assign(new Error("the operation was aborted"), {
          name: "AbortError",
        }),
      }),
    }),
  })
  expect(classifyTransportFailure(error, 0).code).toBe("cancelled")
})

/* ------------------------------------------------------------------ */
/* Finding 7 — 204 bypasses the content-encoding guard                  */
/* ------------------------------------------------------------------ */

it.effect("pin 7: a 204 acknowledgement rejects a hostile content-encoding", () =>
  Effect.scoped(Effect.gen(function* () {
    const endpoint = yield* HostilePeer.serve({ fault: "contentEncodingAck204" })
    const remoteConfig = pinConfig({ authority: endpoint.authority })
    const transport = yield* makeRemoteHttp(remoteConfig)
    const adapter = yield* makeRemoteAdapter(remoteConfig, transport, yield* makeSha256Address)
    const uploaded = CasNodeInput.make({
      kind: { version: 0, tag: 3 },
      payload: Uint8Array.from([9, 9, 9]),
      refs: [],
    })
    const error = yield* adapter.store.put(uploaded).pipe(Effect.flip)
    expect(error).toMatchObject({
      _tag: "CasError/RemoteFailure",
      cause: { _tag: "CasRemoteError/Protocol", code: "invalidHeaders" },
    })
    yield* awaitPeerSocketsReleased(endpoint)
    expect(endpoint.observe().openSockets).toBe(0)
  }).pipe(Effect.provide(TestCrypto))))

/* ------------------------------------------------------------------ */
/* Finding 8 — raw payload length labeled as encoded-node evidence      */
/* ------------------------------------------------------------------ */

it.effect("pin 8: putStream reports canonical node length as encoded-stage evidence", () =>
  Effect.gen(function* () {
    const remoteConfig = pinConfig({ maxEncodedBytes: 8, maxQueuedBytes: 4096 })
    const address = yield* makeSha256Address
    const adapter = yield* makeRemoteAdapter(
      remoteConfig,
      probeOnlyTransport(),
      address,
    )
    const payload = Uint8Array.from([1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11])
    const kind = { version: 0, tag: 5 }
    const error = yield* adapter.transfer.putStream(
      restartable(() => Stream.succeed(payload)),
      { kind, refs: [] },
    ).pipe(Effect.flip)
    const trueEncoded = encodeCasNode(CasNodeInput.make({
      kind,
      payload,
      refs: [],
    })).length
    expect(trueEncoded).toBeGreaterThan(payload.length)
    expect(error).toMatchObject({
      _tag: "CasRemoteError/Budget",
      stage: "encoded",
      observed: trueEncoded,
      bound: 8,
    })
  }).pipe(Effect.provide(TestCrypto)))

/* ------------------------------------------------------------------ */
/* CQ-1 — witness envelope consistency across both persistence paths    */
/* ------------------------------------------------------------------ */

it.effect("lock CQ-1: completed and aborted witnesses share one envelope discipline", () =>
  Effect.gen(function* () {
    const spy = yield* makeSpyStore()
    const live = Pair.of({
      alpha: (x) => Effect.succeed(`A:${x}`),
      beta: () => Effect.die(new Error("pin-abort")),
    })
    const runtime = runtimeOver(Layer.succeed(CasStore, spy.shape))
    yield* session(
      Pair.use((pair) => pair.alpha("ok")).pipe(
        Effect.provide(pairKit.record),
        Effect.provideService(pairKit.live, live),
      ),
      { mode: "record" },
    ).pipe(Effect.provide(runtime))
    yield* session(
      Pair.use((pair) => pair.alpha("ok").pipe(
        Effect.andThen(pair.beta("boom")),
      )).pipe(
        Effect.provide(pairKit.record),
        Effect.provideService(pairKit.live, live),
      ),
      { mode: "record" },
    ).pipe(
      Effect.catchDefect(() => Effect.void),
      Effect.provide(runtime),
    )
    const witnesses = spy.captured.filter((p) => p.node.kind.tag === WitnessTag)
    expect(witnesses).toHaveLength(2)
    for (const w of witnesses) {
      expect(w.node.kind.version).toBe(0)
      expect(w.node.refs).toHaveLength(1)
      expect(w.node.refs[0]?.expectedTag).toBe(HistoryTag)
      const stored = decodeStoredWitness(w.node.payload)
      expect(stored.historyRoot).toBe(w.node.refs[0]?.id)
    }
  }))

/* ------------------------------------------------------------------ */
/* DX pins                                                              */
/* ------------------------------------------------------------------ */

interface DupShape {
  readonly ping: (x: string) => Effect.Effect<number, PinFail>
}

class Dup extends Context.Service<Dup, DupShape>()(
  "test/effect-replay/ReviewPins/Dup",
) {}

it("pin DX-1: kit memoization rejects a conflicting registration", () => {
  const descA = {
    ping: {
      id: "pins/Dup/ping",
      revision: 1,
      request: Schema.String,
      success: Schema.Number,
      failure: PinFail,
      leafReplay: "substitutable",
    },
  } satisfies ServiceDescriptions<DupShape>
  const descB = {
    ping: {
      id: "pins/Dup/ping",
      revision: 2,
      request: Schema.String,
      success: Schema.Number,
      failure: PinFail,
      leafReplay: "substitutable",
    },
  } satisfies ServiceDescriptions<DupShape>
  const first = replayable(Dup, descA)
  expect(replayable(Dup, descA)).toBe(first)
  expect(() => replayable(Dup, descB)).toThrowError(
    /registered with conflicting descriptions/,
  )
})

it("pin DX-3: loadStream hides its internally managed scope", () => {
  type LoadStreamEffect = ReturnType<CasTransferShape["loadStream"]>
  type ContextOf<T> = T extends Effect.Effect<infer _A, infer _E, infer R>
    ? R
    : never
  expectTypeOf<ContextOf<LoadStreamEffect>>().toEqualTypeOf<never>()
})

it.effect("pin DX-4: blob get shares one resolved read plan", () =>
  Effect.gen(function* () {
    const underlying = yield* makeMemoryCasStore(deterministicAddress())
    const loads = new Map<ContentId, number>()
    const counting = CasStore.of({
      put: underlying.put,
      load: (id) => Effect.suspend(() => {
        loads.set(id, (loads.get(id) ?? 0) + 1)
        return underlying.load(id)
      }),
    })
    const blobLayer = CasBlob.layer.pipe(
      Layer.provide(Layer.succeed(CasStore, counting)),
    )
    yield* Effect.gen(function* () {
      const ref = yield* CasBlob.put(Stream.succeed(Uint8Array.from([1, 2, 3])))
      loads.clear()
      const bytes = yield* CasBlob.get(ref)
      expect(Array.from(bytes)).toEqual([1, 2, 3])
      expect(loads.get(ContentId.make(ref))).toBe(1)
    }).pipe(Effect.provide(blobLayer))
  }))

it("pin DX-5: describeService validates prefixes and revisions", () => {
  const spec = (revision: number) => ({
    ping: {
      revision,
      request: Schema.String,
      success: Schema.Number,
      failure: PinFail,
    },
  })
  expect(() => describeService<DupShape>("")(spec(0))).toThrowError(/prefix/)
  expect(() => describeService<DupShape>("pins/frac")(spec(1.5))).toThrowError(/revision/)
  expect(() => describeService<DupShape>("pins/negative")(spec(-1))).toThrowError(/revision/)
})

it("lock DX-7: the barrel is exactly the three plane doors", () => {
  expect(Object.keys(barrel).sort()).toEqual(["Cas", "Replay", "Server"])
  expect("value" in barrel.Cas).toBe(true)
  expect("restartable" in barrel.Cas).toBe(true)
  expect("reduce" in barrel.Replay).toBe(true)
  expect("replayable" in barrel.Replay).toBe(true)
  expect("Core" in barrel.Server).toBe(true)
  expect("httpApp" in barrel.Server).toBe(true)
  // The reducer clause helpers stay module-internal.
  expect("absorb" in barrel.Replay).toBe(false)
  expect("invokeRecord" in barrel.Replay).toBe(false)
})
