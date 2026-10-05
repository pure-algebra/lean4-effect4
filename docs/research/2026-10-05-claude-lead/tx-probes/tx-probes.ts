// Transaction probes over one Effect build (2026-10-05). Finite host runs, not proofs.
//
// Run: EFFECT_DIR=<an effect package directory> bun run tx-probes.ts
// Effect 4 has Effect.tx, Effect.txRetry and TxRef. Effect 3 has the STM type and TRef, whose
// bodies cannot hold a yield, so TX1 and TX4 have no Effect 3 form.
import { existsSync, readFileSync } from "node:fs"

const dir = process.env.EFFECT_DIR!
const version: string = JSON.parse(readFileSync(`${dir}/package.json`, "utf8")).version
const entry = existsSync(`${dir}/dist/index.js`) ? `${dir}/dist/index.js` : `${dir}/dist/esm/index.js`
const { Effect, Fiber, TxRef, STM, TRef } = await import(entry)

const v4 = typeof Effect.forkChild === "function"
const fork = v4 ? Effect.forkChild : Effect.fork
const yieldNow = v4 ? Effect.yieldNow : Effect.yieldNow()
const settle = Effect.gen(function*() {
  for (let i = 0; i < 8; i++) yield* yieldNow
})

// One vocabulary over both versions.
const make = (n: number) => v4 ? TxRef.make(n) : TRef.make(n)
const get = (r: any) => v4 ? TxRef.get(r) : STM.commit(TRef.get(r))
const set = (r: any, n: number) => v4 ? TxRef.set(r, n) : STM.commit(TRef.set(r, n))
// A transaction that answers the cell's value once it is not zero, and counts its runs.
const awaitNonZero = (r: any, onRun: () => void) =>
  v4
    ? Effect.tx(Effect.gen(function*() {
      onRun()
      const v = yield* TxRef.get(r)
      if (v === 0) return yield* Effect.txRetry
      return v
    }))
    : STM.commit(STM.gen(function*() {
      yield* STM.sync(onRun)
      const v = yield* TRef.get(r)
      if (v === 0) return yield* STM.retry
      return v
    }))

// TX1 (Effect 4 only). A body reads a cell, yields, and retries on the value it read. Another
// fiber commits a new value during the yield. Nothing touches the cell afterwards.
// A transaction that waits for a change must see that change.
const tx1 = Effect.gen(function*() {
  const ref = yield* TxRef.make(0)
  let runs = 0
  let result: unknown = "waiting"
  const f = yield* fork(Effect.gen(function*() {
    result = yield* Effect.tx(Effect.gen(function*() {
      runs++
      const v = yield* TxRef.get(ref)
      yield* yieldNow
      if (v === 0) return yield* Effect.txRetry
      return v
    }))
  }))
  yield* yieldNow
  yield* TxRef.set(ref, 1)
  yield* settle
  const out = { result, runs }
  yield* Fiber.interrupt(f)
  return out
})

// TX2. A transaction waits for a cell to change. Another fiber reads the cell three times.
// The documentation says a retry waits until an accessed value changes.
const tx2 = Effect.gen(function*() {
  const ref = yield* make(0)
  let runs = 0
  let result: unknown = "waiting"
  const f = yield* fork(Effect.gen(function*() {
    result = yield* awaitNonZero(ref, () => runs++)
  }))
  yield* settle
  const runsBefore = runs
  for (let i = 0; i < 3; i++) {
    yield* get(ref)
    yield* settle
  }
  const runsAfterReads = runs
  yield* set(ref, 0)
  yield* settle
  const runsAfterEqualWrite = runs
  yield* set(ref, 7)
  yield* settle
  const out = { runsBefore, runsAfterReads, runsAfterEqualWrite, runsAtEnd: runs, result }
  yield* Fiber.interrupt(f)
  return out
})

// TX4 (Effect 4 only). Two cells keep a + b = 0. A body reads a, yields, then reads b, and
// records the pair. Another fiber moves both cells in one transaction during the yield.
// The pairs each attempt saw are the observation.
const tx4 = Effect.gen(function*() {
  const a = yield* TxRef.make(0)
  const b = yield* TxRef.make(0)
  const seen: Array<[number, number]> = []
  let result: unknown = "waiting"
  const f = yield* fork(Effect.gen(function*() {
    result = yield* Effect.tx(Effect.gen(function*() {
      const x = yield* TxRef.get(a)
      yield* yieldNow
      const y = yield* TxRef.get(b)
      seen.push([x, y])
      return x + y
    }))
  }))
  yield* yieldNow
  yield* Effect.tx(Effect.gen(function*() {
    yield* TxRef.set(a, 1)
    yield* TxRef.set(b, -1)
  }))
  yield* settle
  const out = { seen, result }
  yield* Fiber.interrupt(f)
  return out
})

// TX5. A transaction waits for a cell to leave zero. One fiber commits 1, then 2. `gap` says
// whether that fiber yields between its two commits.
const tx5 = (gap: boolean) =>
  Effect.gen(function*() {
    const ref = yield* make(0)
    let runs = 0
    let result: unknown = "waiting"
    const f = yield* fork(Effect.gen(function*() {
      result = yield* awaitNonZero(ref, () => runs++)
    }))
    yield* settle
    yield* set(ref, 1)
    if (gap) yield* settle
    yield* set(ref, 2)
    yield* settle
    const out = { gap, result, runs }
    yield* Fiber.interrupt(f)
    return out
  })

const main = Effect.gen(function*() {
  const out: Record<string, unknown> = { effect: version }
  if (v4) out.tx1_staleReadThenRetry = yield* tx1
  out.tx2_wakeOnReadOrEqualWrite = yield* tx2
  if (v4) out.tx4_pairsSeen = yield* tx4
  out.tx5_twoCommits = [yield* tx5(false), yield* tx5(true)]
  return out
})

Effect.runPromise(main).then((r: unknown) => console.log(JSON.stringify(r)))
