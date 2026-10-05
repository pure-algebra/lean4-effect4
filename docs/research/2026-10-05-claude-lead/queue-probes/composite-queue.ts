// A composite queue over Ref and Deferred, with three deliveries of its signal (2026-10-05).
// Finite host runs on one Effect 4 build, not proofs.
//
// Run: EFFECT_DIR=<an effect package directory> bun run composite-queue.ts
//
// The queue is the contract of decisions rows 219 to 222, cut to what the probes need: one cell,
// one pure step for each operation, strict request order, consumption at the taker's own step,
// and a signal that is only a hint. The three deliveries of a signal:
//   inline: Deferred.succeed, which resumes the waiter inside the signalling step;
//   yield:  the same, and the waiter yields once after its await;
//   fork:   a detached fork with a deferred start whose body is Deferred.succeed.
// The question: which delivery gives the native Effect 4 answers on P5, P6 and P7, and does the
// strict order hold on P1?
import { readFileSync } from "node:fs"

const dir = process.env.EFFECT_DIR!
const version: string = JSON.parse(readFileSync(`${dir}/package.json`, "utf8")).version
const { Effect, Fiber, Deferred, Ref } = await import(`${dir}/dist/index.js`)

type Mode = "inline" | "yield" | "fork"
type Strategy = "unbounded" | "sliding" | "dropping"
interface Ticket { readonly id: object; readonly hint: any; readonly min: number; readonly max: number }
interface State { readonly messages: ReadonlyArray<unknown>; readonly takers: ReadonlyArray<Ticket> }
interface Q { readonly cell: any; readonly capacity: number; readonly strategy: Strategy; readonly mode: Mode }

const settle = Effect.gen(function*() {
  for (let i = 0; i < 8; i++) yield* Effect.yieldNow
})

// The pure steps. Each answers the new state, a reply, and the hints to signal.
const ready = (s: State, t: Ticket) => s.messages.length >= 1 && s.messages.length >= Math.min(t.min, Infinity)
const wake = (s: State): ReadonlyArray<any> => {
  const head = s.takers[0]
  return head !== undefined && ready(s, head) ? [head.hint] : []
}
const offerStep = (q: Q, m: unknown) => (s: State): [{ ok: boolean; signals: ReadonlyArray<any> }, State] => {
  const full = s.messages.length >= q.capacity
  if (full && q.strategy === "dropping") return [{ ok: false, signals: wake(s) }, s]
  const kept = full && q.strategy === "sliding" ? s.messages.slice(1) : s.messages
  const next: State = { ...s, messages: [...kept, m] }
  return [{ ok: true, signals: wake(next) }, next]
}
const takeStep = (t: Ticket) => (s: State): [{ got: ReadonlyArray<unknown> | undefined; signals: ReadonlyArray<any> }, State] => {
  const waiting = s.takers.findIndex((u) => u.id === t.id)
  const turn = waiting === 0 || (waiting === -1 && s.takers.length === 0)
  if (ready(s, t) && turn) {
    const next: State = { messages: s.messages.slice(t.max), takers: s.takers.filter((u) => u.id !== t.id) }
    return [{ got: s.messages.slice(0, t.max), signals: wake(next) }, next]
  }
  const takers = waiting === -1 ? [...s.takers, t] : s.takers.map((u) => (u.id === t.id ? t : u))
  return [{ got: undefined, signals: [] }, { ...s, takers }]
}
const cancelStep = (id: object) => (s: State): [ReadonlyArray<any>, State] => {
  const next: State = { ...s, takers: s.takers.filter((u) => u.id !== id) }
  return [wake(next), next]
}

// The delivery of the hints that a step answers.
const post = (q: Q, signals: ReadonlyArray<any>) =>
  Effect.forEach(signals, (d) =>
    q.mode === "fork"
      ? Effect.forkDetach(Deferred.succeed(d, undefined), { startImmediately: false, uninterruptible: true })
      : Deferred.succeed(d, undefined), { discard: true })

const make = (mode: Mode, strategy: Strategy, capacity: number) =>
  Effect.map(Ref.make<State>({ messages: [], takers: [] }), (cell): Q => ({ cell, capacity, strategy, mode }))

const offer = (q: Q, m: unknown) =>
  Effect.uninterruptible(Effect.gen(function*() {
    const r = yield* Ref.modify(q.cell, offerStep(q, m))
    yield* post(q, r.signals)
    return r.ok
  }))

const size = (q: Q) => Effect.map(Ref.get(q.cell), (s: State) => s.messages.length)

const takeBetween = (q: Q, min: number, max: number) =>
  Effect.uninterruptibleMask((restore: any) =>
    Effect.gen(function*() {
      const id = {}
      let hint = yield* Deferred.make()
      while (true) {
        const r = yield* Ref.modify(q.cell, takeStep({ id, hint, min, max }))
        yield* post(q, r.signals)
        if (r.got !== undefined) return r.got
        yield* restore(Deferred.await(hint)).pipe(
          Effect.onInterrupt(() => Effect.flatMap(Ref.modify(q.cell, cancelStep(id)), (s: any) => post(q, s)))
        )
        if (q.mode === "yield") yield* Effect.yieldNow
        hint = yield* Deferred.make()
      }
    })
  )
const take = (q: Q) => Effect.map(takeBetween(q, 1, 1), (ms: any) => ms[0])

// P5, P6 and P7 of queue-timing.ts, on the composite.
const burst = (mode: Mode, strategy: Strategy, capacity: number, min: number, max: number, gap: boolean) =>
  Effect.gen(function*() {
    const q = yield* make(mode, strategy, capacity)
    let result: unknown = "waiting"
    const f = yield* Effect.forkChild(Effect.gen(function*() {
      result = yield* takeBetween(q, min, max)
    }))
    yield* settle
    const first = yield* offer(q, 1)
    if (gap) yield* settle
    const second = yield* offer(q, 2)
    yield* settle
    const left = yield* size(q)
    yield* Fiber.interrupt(f)
    return { gap, taker: result, offers: [first, second], left }
  })

// P1 of queue-faults.ts, on the composite: A parks first; B takes in a loop.
const p1 = (mode: Mode) =>
  Effect.gen(function*() {
    const rounds = 6
    const q = yield* make(mode, "unbounded", Infinity)
    const log: Array<string> = []
    const a = yield* Effect.forkChild(Effect.gen(function*() {
      log.push(`A got ${yield* take(q)}`)
    }))
    yield* Effect.yieldNow
    const b = yield* Effect.forkChild(Effect.gen(function*() {
      for (let i = 0; i < rounds; i++) {
        log.push(`B got ${yield* take(q)}`)
        yield* Effect.yieldNow
      }
    }))
    for (let i = 1; i <= rounds; i++) {
      yield* offer(q, i)
      yield* Effect.yieldNow
    }
    yield* settle
    yield* Fiber.interrupt(a)
    yield* Fiber.interrupt(b)
    return log.join(", ")
  })

// Cancellation. (a) A taker waits and is interrupted; a later offer stays in the queue.
// (b) A taker is signalled and then interrupted before the signal is delivered; a second
// taker, which waits behind it, receives the message.
const cancelWaiting = (mode: Mode) =>
  Effect.gen(function*() {
    const q = yield* make(mode, "unbounded", Infinity)
    const f = yield* Effect.forkChild(take(q))
    yield* settle
    yield* Fiber.interrupt(f)
    yield* offer(q, 1)
    yield* settle
    return { left: yield* size(q) }
  })
const cancelAfterSignal = (mode: Mode) =>
  Effect.gen(function*() {
    const q = yield* make(mode, "unbounded", Infinity)
    let second: unknown = "waiting"
    const t1 = yield* Effect.forkChild(take(q))
    yield* settle
    const t2 = yield* Effect.forkChild(Effect.gen(function*() {
      second = yield* take(q)
    }))
    yield* settle
    yield* offer(q, 1)
    yield* Fiber.interrupt(t1)
    yield* settle
    const out = { secondTaker: second, left: yield* size(q) }
    yield* Fiber.interrupt(t2)
    return out
  })

const main = Effect.gen(function*() {
  const out: Record<string, unknown> = { effect: version }
  for (const mode of ["inline", "yield", "fork"] as const) {
    out[mode] = {
      p5_batchOneToTwo: [yield* burst(mode, "unbounded", Infinity, 1, 2, false), yield* burst(mode, "unbounded", Infinity, 1, 2, true)],
      p6_slidingOne: [yield* burst(mode, "sliding", 1, 1, 1, false), yield* burst(mode, "sliding", 1, 1, 1, true)],
      p7_droppingOne: [yield* burst(mode, "dropping", 1, 1, 1, false), yield* burst(mode, "dropping", 1, 1, 1, true)],
      p1: yield* p1(mode),
      cancelWaiting: yield* cancelWaiting(mode),
      cancelAfterSignal: yield* cancelAfterSignal(mode)
    }
  }
  return out
})

Effect.runPromise(main).then((r: unknown) => console.log(JSON.stringify(r, null, 1)))
