/**
 * Production sync workloads driven end-to-end through the seeded fixtures
 * in `fixtures/`: seeded regeneration, dedup pressure, shared-subtree
 * pulls, an incremental push over the wire, a cancelled push, and a
 * cold-then-warm pull — against the in-memory store and the remote
 * adapter speaking cas-http/0 to the in-process reference peer.
 *
 * Evidence class: G4 sampled evidence only. These are workload fixtures
 * for exploratory and regression tests; they are NEVER a substitute for
 * the ratified conformance vectors under `conformance/manifest`.
 */
import { expect, it } from "@effect/vitest"
import { Crypto, Deferred, Effect, Fiber, Layer } from "effect"
import * as FetchHttpClient from "effect/unstable/http/FetchHttpClient"
import { createHash, randomBytes } from "node:crypto"
import * as Cas from "../../src/Cas.ts"
import { CasStore } from "../../src/cas/Store.ts"
import { CasRemoteConfig, RemoteAuthority } from "../../src/cas/Remote.ts"
import { makeMemoryCasStore, makeSha256Address } from "../../src/cas/Store.ts"
import { admitGraphBottomUp, distinctNodeCount, generateGraph } from "./fixtures/Graph.ts"
import { serveSeededReference } from "./fixtures/Peer.ts"
import {
  coldPull,
  dedupHeavy,
  incrementalPush,
  interruptedSync,
  warmPull,
} from "./fixtures/Profiles.ts"
import {
  auditRemoteClosure,
  buildScenario,
  drivePull,
  driveUploadSchedule,
} from "./fixtures/Sync.ts"

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

const config = (authority: string) => new CasRemoteConfig({
  authority: RemoteAuthority.make(authority),
  authorityMode: "remote-authoritative",
  maxEncodedBytes: 4096,
  maxDecodedBytes: 4096,
  maxDecompressedBytes: 4096,
  maxQueuedBytes: 4096,
  maxAttempts: 1,
  operationDeadlineMs: 5_000,
  redirectPolicy: { maxRedirects: 0, crossOrigin: "deny" },
})

const remoteLayer = (remoteConfig: CasRemoteConfig) =>
  Cas.layerRemote(remoteConfig).pipe(Layer.provideMerge(HttpRuntime))

const freshMemoryStore = Effect.gen(function* () {
  const address = yield* makeSha256Address
  return yield* makeMemoryCasStore(address)
})

it.effect("the same seed regenerates the same workload byte for byte; a different seed diverges", () =>
  Effect.gen(function* () {
    const generate = (seed: number) => generateGraph({
      seed,
      shape: incrementalPush.shape,
      payload: incrementalPush.payload,
    })

    const first = yield* admitGraphBottomUp(yield* freshMemoryStore, generate(incrementalPush.seed))
    const second = yield* admitGraphBottomUp(yield* freshMemoryStore, generate(incrementalPush.seed))
    expect(second).toEqual(first)

    const scenarioA = buildScenario(incrementalPush)
    const scenarioB = buildScenario(incrementalPush)
    expect(scenarioB.upload).toEqual(scenarioA.upload)
    expect(scenarioB.remoteHas).toEqual(scenarioA.remoteHas)

    const reseeded = yield* admitGraphBottomUp(
      yield* freshMemoryStore,
      generate(incrementalPush.seed + 1),
    )
    expect(reseeded[reseeded.length - 1]).not.toBe(first[first.length - 1])
  }).pipe(Effect.provide(TestCrypto)))

it.effect("a duplicate-heavy bulk import admits every slot yet stores one node per distinct byte sequence", () =>
  Effect.gen(function* () {
    const scenario = buildScenario(dedupHeavy)
    const store = yield* freshMemoryStore
    const ids = yield* admitGraphBottomUp(store, scenario.graph)

    expect(ids).toHaveLength(scenario.graph.nodes.length)
    const distinct = new Set(ids).size
    expect(distinct).toBe(distinctNodeCount(scenario.graph))
    expect(distinct).toBe(7)
    expect(distinct).toBeLessThan(scenario.graph.nodes.length)
  }).pipe(Effect.provide(TestCrypto)))

it.effect("a pull of a shared-subtree graph starts at the root and visits every shared node exactly once", () =>
  Effect.gen(function* () {
    const scenario = buildScenario(coldPull)
    const store = yield* freshMemoryStore
    const ids = yield* admitGraphBottomUp(store, scenario.graph)

    const order = scenario.pull.discovery
    expect(order[0]).toBe(scenario.graph.root)
    expect(order).toHaveLength(scenario.graph.nodes.length)
    expect(new Set(order).size).toBe(order.length)

    const loaded = yield* drivePull({ store, order, ids })
    order.forEach((index, position) => {
      const delivered = loaded[position]
      const generated = scenario.graph.nodes[index]
      expect(Array.from(delivered?.payload ?? [])).toEqual(Array.from(generated?.payload ?? []))
      expect(delivered?.refs).toHaveLength(generated?.children.length ?? -1)
    })
  }).pipe(Effect.provide(TestCrypto)))

it.effect("an incremental push of a 40-node tree with 80 percent remote residency uploads only the missing closure, children before parents", () =>
  Effect.scoped(Effect.gen(function* () {
    const scenario = buildScenario(incrementalPush)
    expect(scenario.graph.nodes.length).toBe(40)
    expect(scenario.upload.expectedPuts).toBeGreaterThan(0)
    expect(scenario.upload.expectedPuts).toBeLessThan(40)
    expect(scenario.remoteHas.length).toBeGreaterThan(0)
    const present = new Set(scenario.remoteHas)
    for (const step of scenario.upload.schedule) {
      if (step._tag === "upload") expect(present.has(step.index)).toBe(false)
      else expect(present.has(step.index)).toBe(true)
    }
    expect(scenario.upload.expectedGets).toBe(scenario.remoteHas.length)

    const uploadPositions = new Map<number, number>()
    scenario.upload.schedule.forEach((step, position) => uploadPositions.set(step.index, position))
    for (const step of scenario.upload.schedule) {
      if (step._tag !== "upload") continue
      for (const child of scenario.graph.nodes[step.index]?.children ?? []) {
        const childPosition = uploadPositions.get(child)
        expect(childPosition).toBeDefined()
        expect(childPosition ?? Infinity).toBeLessThan(uploadPositions.get(step.index) ?? -1)
      }
    }
    const lastStep = scenario.upload.schedule[scenario.upload.schedule.length - 1]
    expect(lastStep?.index).toBe(scenario.graph.root)

    const { endpoint, seed } = yield* serveSeededReference(scenario.graph, scenario.remoteHas)
    yield* Effect.gen(function* () {
      const store = yield* CasStore
      const report = yield* driveUploadSchedule({
        store,
        graph: scenario.graph,
        ids: seed.ids,
        plan: scenario.upload,
        concurrency: scenario.concurrency,
      })
      expect(report.completed).toHaveLength(scenario.upload.schedule.length)
      expect(report.admitted.get(scenario.graph.root)).toBe(seed.ids[scenario.graph.root])
    }).pipe(Effect.provide(remoteLayer(config(endpoint.authority))))

    expect(endpoint.observe().puts).toBe(scenario.upload.expectedPuts)
    expect(endpoint.observe().gets).toBe(scenario.upload.expectedGets)
  })).pipe(Effect.provide(TestCrypto)))

it.effect("a push cancelled mid-schedule leaves no parent on the remote without its children", () =>
  Effect.scoped(Effect.gen(function* () {
    const scenario = buildScenario(interruptedSync)
    const cut = scenario.interruptAfter
    expect(cut).toBeDefined()
    if (cut === undefined) return

    const { endpoint, seed } = yield* serveSeededReference(scenario.graph, scenario.remoteHas)
    expect(scenario.remoteHas).toHaveLength(0)

    const reached = yield* Deferred.make<void>()
    const sync = yield* Effect.gen(function* () {
      const store = yield* CasStore
      return yield* driveUploadSchedule({
        store,
        graph: scenario.graph,
        ids: seed.ids,
        plan: scenario.upload,
        concurrency: 1,
        beforeStep: (_step, position) => position >= cut
          ? Deferred.succeed(reached, undefined).pipe(Effect.andThen(Effect.never))
          : Effect.void,
      })
    }).pipe(
      Effect.provide(remoteLayer(config(endpoint.authority))),
      Effect.forkScoped,
    )
    yield* Deferred.await(reached)
    yield* Fiber.interrupt(sync)
    expect(endpoint.observe().puts).toBe(cut)

    const audit = yield* Effect.gen(function* () {
      const replica = yield* CasStore
      return yield* auditRemoteClosure({
        store: replica,
        graph: scenario.graph,
        ids: seed.ids,
      })
    }).pipe(Effect.provide(remoteLayer(config(endpoint.authority))))

    expect(audit.dangling).toEqual([])
    const transferred = scenario.upload.schedule.slice(0, cut).map((step) => step.index)
    expect(audit.held).toEqual(transferred.sort((left, right) => left - right))
    const held = new Set(audit.held)
    for (const index of audit.held) {
      for (const child of scenario.graph.nodes[index]?.children ?? []) {
        expect(held.has(child)).toBe(true)
      }
    }
  })).pipe(Effect.provide(TestCrypto)))

it.effect("a cold pull fills the replica children first over the wire; a warm pull replays from the local mirror", () =>
  Effect.scoped(Effect.gen(function* () {
    const scenario = buildScenario(warmPull)
    expect(scenario.remoteHas).toHaveLength(scenario.graph.nodes.length)

    const { endpoint, seed } = yield* serveSeededReference(scenario.graph, scenario.remoteHas)
    yield* Effect.gen(function* () {
      const store = yield* CasStore

      const cold = yield* drivePull({
        store,
        order: scenario.pull.admission,
        ids: seed.ids,
      })
      expect(cold).toHaveLength(scenario.graph.nodes.length)
      expect(endpoint.observe().gets).toBe(scenario.graph.nodes.length)

      const warm = yield* drivePull({
        store,
        order: scenario.pull.discovery,
        ids: seed.ids,
      })
      expect(endpoint.observe().gets).toBe(scenario.graph.nodes.length)
      expect(endpoint.observe().puts).toBe(0)
      scenario.pull.discovery.forEach((index, position) => {
        const generated = scenario.graph.nodes[index]
        expect(Array.from(warm[position]?.payload ?? [])).toEqual(
          Array.from(generated?.payload ?? []),
        )
      })
    }).pipe(Effect.provide(remoteLayer(config(endpoint.authority))))
  })).pipe(Effect.provide(TestCrypto)))
