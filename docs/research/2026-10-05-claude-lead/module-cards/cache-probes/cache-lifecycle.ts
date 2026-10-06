// Cache probes over one Effect 4 build (2026-10-06). Finite host runs, not proofs.
//
// Run: EFFECT_DIR=<an effect package directory> bun run cache-lifecycle.ts
// The package directory is the one that holds package.json and dist/index.js.
// Each probe is one schedule. The output names the build's version and the runtime's.
import { readFileSync } from "node:fs"

const dir = process.env.EFFECT_DIR!
const version: string = JSON.parse(readFileSync(`${dir}/package.json`, "utf8")).version
const E = await import(`${dir}/dist/index.js`)
const { Effect, Deferred, Cache, Fiber } = E

const fork = Effect.forkChild
const settle = Effect.gen(function*() {
  for (let i = 0; i < 24; i++) yield* Effect.yieldNow
})

// A cache whose lookup records each start. A key with a behaviour runs it; any other key
// answers at once with `v-<key>`.
const makeCache = (capacity: number, behaviours: Record<string, (n: number) => any> = {}) => {
  const log: Array<string> = []
  const count: Record<string, number> = {}
  const lookup = (key: string) =>
    Effect.suspend(() => {
      count[key] = (count[key] ?? 0) + 1
      log.push(`lookup ${key} starts (${count[key]})`)
      const behaviour = behaviours[key]
      return behaviour ? behaviour(count[key]) : Effect.succeed(`v-${key}`)
    })
  return Effect.map(Cache.make({ lookup, capacity }), (cache: any) => ({ cache, log, count }))
}
const keysOf = (cache: any) => Effect.map(Cache.keys(cache), (ks: Iterable<string>) => Array.from(ks))
const exitText = (exit: any): string =>
  exit._tag === "Success"
    ? `success ${String(exit.value)}`
    : `failure ${(exit.cause.reasons ?? []).map((r: any) => r._tag === "Fail" ? `Fail ${String(r.error)}` : r._tag).join(", ")}`

// CP1. A read moves its key to the fresh end. Capacity 2. Get a, get z, get a again, get b.
const cp1 = Effect.gen(function*() {
  const { cache, log } = yield* makeCache(2)
  yield* Cache.get(cache, "a")
  yield* Cache.get(cache, "z")
  yield* Cache.get(cache, "a")
  yield* Cache.get(cache, "b")
  return { keys: yield* keysOf(cache), log }
})

// CP2. `has` does not move its key. Capacity 2. Get a, get z, ask has(a), get b.
const cp2 = Effect.gen(function*() {
  const { cache, log } = yield* makeCache(2)
  yield* Cache.get(cache, "a")
  yield* Cache.get(cache, "z")
  const hasA = yield* Cache.has(cache, "a")
  yield* Cache.get(cache, "b")
  return { hasA, keys: yield* keysOf(cache), log }
})

// CP3. `set` on a present key keeps its place. Capacity 2. Get a, get z, set a, get b.
const cp3 = Effect.gen(function*() {
  const { cache, log } = yield* makeCache(2)
  yield* Cache.get(cache, "a")
  yield* Cache.get(cache, "z")
  yield* Cache.set(cache, "a", "written")
  yield* Cache.get(cache, "b")
  return { keys: yield* keysOf(cache), log }
})

// CP4. Two readers of one pending key share one lookup.
const cp4 = Effect.gen(function*() {
  const gate = yield* Deferred.make()
  const { cache, log, count } = yield* makeCache(4, {
    k: () => Effect.as(Deferred.await(gate), "v-k")
  })
  const got: Array<string> = []
  yield* fork(Effect.map(Cache.get(cache, "k"), (v: string) => { got.push(`R1 ${v}`) }))
  yield* settle
  yield* fork(Effect.map(Cache.get(cache, "k"), (v: string) => { got.push(`R2 ${v}`) }))
  yield* settle
  yield* Deferred.succeed(gate, undefined)
  yield* settle
  return { lookupsOfK: count.k, got, log }
})

// CP5. A pending lookup and its readers. With two readers one is interrupted, and the gate then
// opens. With one reader that reader is interrupted.
const cp5 = Effect.gen(function*() {
  const gate = yield* Deferred.make()
  const { cache, log, count } = yield* makeCache(4, {
    k: () =>
      Effect.onInterrupt(
        Effect.as(Deferred.await(gate), "v-k"),
        () => Effect.sync(() => { log.push("lookup k is interrupted") })
      ),
    lone: () =>
      Effect.onInterrupt(Effect.never, () => Effect.sync(() => { log.push("lookup lone is interrupted") }))
  })
  const got: Array<string> = []
  const r1 = yield* fork(Effect.map(Cache.get(cache, "k"), (v: string) => { got.push(`R1 ${v}`) }))
  yield* settle
  yield* fork(Effect.map(Cache.get(cache, "k"), (v: string) => { got.push(`R2 ${v}`) }))
  yield* settle
  yield* Fiber.interrupt(r1)
  yield* settle
  const afterOneOfTwoLeaves = log.slice()
  yield* Deferred.succeed(gate, undefined)
  yield* settle
  const r3 = yield* fork(Cache.get(cache, "lone"))
  yield* settle
  yield* Fiber.interrupt(r3)
  yield* settle
  return { afterOneOfTwoLeaves, got, lookupsOfK: count.k, keys: yield* keysOf(cache), log }
})

// CP6. A new reader arrives while an abandoned lookup is still cleaning up. The lookup's
// cleanup waits for a second gate. R1 reads k and is interrupted: it was the last reader. R2
// then reads k. The second gate opens, and then the first.
const cp6 = Effect.gen(function*() {
  const gate = yield* Deferred.make()
  const cleanupGate = yield* Deferred.make()
  const { cache, log, count } = yield* makeCache(4, {
    k: (n: number) =>
      Effect.onInterrupt(
        Effect.as(Deferred.await(gate), `v-k from lookup ${n}`),
        () =>
          Effect.gen(function*() {
            log.push(`lookup ${n} starts its cleanup`)
            yield* Deferred.await(cleanupGate)
            log.push(`lookup ${n} ends its cleanup`)
          })
      )
  })
  const r1 = yield* fork(Cache.get(cache, "k"))
  yield* settle
  // The interruption is awaited by a fiber of its own: the cleanup is pending.
  yield* fork(Fiber.interrupt(r1))
  yield* settle
  const keysWhileTheCleanupIsPending = yield* keysOf(cache)
  const r2: any = yield* fork(Effect.exit(Cache.get(cache, "k")))
  yield* settle
  const lookupsWhenR2Arrived = count.k
  yield* Deferred.succeed(cleanupGate, undefined)
  yield* settle
  const keysAfterTheCleanup = yield* keysOf(cache)
  yield* Deferred.succeed(gate, undefined)
  yield* settle
  const exitR2: any = r2.pollUnsafe()
  return {
    keysWhileTheCleanupIsPending,
    lookupsWhenR2Arrived,
    keysAfterTheCleanup,
    r2: exitR2 ? exitText(exitR2.value ?? exitR2) : "still waiting",
    lookupsOfK: count.k,
    keysAtTheEnd: yield* keysOf(cache),
    log
  }
})

// CP7. A pending entry is evicted while its reader waits. Capacity 1. R1 reads a, whose lookup
// waits. R2 reads b. The gate opens. A third read of a follows.
const cp7 = Effect.gen(function*() {
  const gate = yield* Deferred.make()
  const { cache, log, count } = yield* makeCache(1, {
    a: (n: number) => (n === 1 ? Effect.as(Deferred.await(gate), "v-a from lookup 1") : Effect.succeed(`v-a from lookup ${n}`))
  })
  const got: Array<string> = []
  yield* fork(Effect.map(Cache.get(cache, "a"), (v: string) => { got.push(`R1 ${v}`) }))
  yield* settle
  yield* Cache.get(cache, "b")
  const keysAfterB = yield* keysOf(cache)
  yield* Deferred.succeed(gate, undefined)
  yield* settle
  const third = yield* Cache.get(cache, "a")
  return { keysAfterB, got, third, lookupsOfA: count.a, keysAtTheEnd: yield* keysOf(cache), log }
})

// CP8. A failed lookup is kept. Two reads of a key whose lookup fails.
const cp8 = Effect.gen(function*() {
  const { cache, log, count } = yield* makeCache(4, { f: () => Effect.fail("boom") })
  const first = exitText(yield* Effect.exit(Cache.get(cache, "f")))
  const second = exitText(yield* Effect.exit(Cache.get(cache, "f")))
  return { first, second, lookupsOfF: count.f, keys: yield* keysOf(cache), log }
})

// CP9. Two readers of a pending entry whose key leaves the map, by an eviction or by
// `invalidate`. R1 and R2 read a, whose first lookup waits. The key leaves. R1 is interrupted:
// one reader is left. A third read of a follows: a replacement. R2 is interrupted: it was the
// old entry's last reader. A fourth read of a follows.
const cp9 = (removal: "evict" | "invalidate") =>
  Effect.gen(function*() {
    const gate = yield* Deferred.make()
    const { cache, log, count } = yield* makeCache(removal === "evict" ? 1 : 4, {
      a: (n: number) =>
        n === 1
          ? Effect.onInterrupt(
            Effect.as(Deferred.await(gate), "v-a from lookup 1"),
            () => Effect.sync(() => { log.push("lookup 1 of a is interrupted") })
          )
          : Effect.succeed(`v-a from lookup ${n}`)
    })
    const r1 = yield* fork(Cache.get(cache, "a"))
    yield* settle
    const r2 = yield* fork(Cache.get(cache, "a"))
    yield* settle
    if (removal === "evict") yield* Cache.get(cache, "b")
    else yield* Cache.invalidate(cache, "a")
    yield* settle
    const keysAfterTheRemoval = yield* keysOf(cache)
    yield* Fiber.interrupt(r1)
    yield* settle
    const logAfterTheFirstLeaves = log.slice()
    const third = yield* Cache.get(cache, "a")
    const keysAfterTheReplacement = yield* keysOf(cache)
    yield* Fiber.interrupt(r2)
    yield* settle
    const logAfterTheLastLeaves = log.slice()
    const keysAfterTheOldCleanup = yield* keysOf(cache)
    const fourth = yield* Cache.get(cache, "a")
    return {
      keysAfterTheRemoval,
      logAfterTheFirstLeaves,
      third,
      keysAfterTheReplacement,
      logAfterTheLastLeaves,
      keysAfterTheOldCleanup,
      fourth,
      lookupsOfA: count.a,
      keysAtTheEnd: yield* keysOf(cache)
    }
  })

const run = (e: any) => Effect.runPromise(e).catch((error: unknown) => ({ probeError: String(error) }))
const out = {
  effect: version,
  runtime: `bun ${Bun.version}`,
  cp1_a_read_moves_its_key: await run(cp1),
  cp2_has_does_not_move: await run(cp2),
  cp3_set_keeps_the_place: await run(cp3),
  cp4_one_shared_lookup: await run(cp4),
  cp5_readers_leave: await run(cp5),
  cp6_reader_during_a_cleanup: await run(cp6),
  cp7_pending_entry_evicted: await run(cp7),
  cp8_failed_lookup_kept: await run(cp8),
  cp9_two_readers_and_an_eviction: await run(cp9("evict")),
  cp9_two_readers_and_an_invalidation: await run(cp9("invalidate"))
}
console.log(JSON.stringify(out, null, 1))
