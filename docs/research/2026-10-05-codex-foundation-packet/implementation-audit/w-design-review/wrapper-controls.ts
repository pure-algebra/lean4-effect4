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


// Review harness below. The copied queue definitions above are unchanged.
function assert(ok: unknown, message: string): asserts ok { if (!ok) throw new Error(message) }
const summary = (f: any) => {
 const x = f.pollUnsafe()
 return x === undefined ? { tag: "Pending" } : x._tag === "Success" ? { tag: "Success", value: x.value ?? null } : { tag: "Failure", reasons: x.cause.reasons.map((r: any) => r._tag) }
}
class Manual {
 executionMode = "sync"; tasks: any[] = []; seq = 0; executions = 0; hook: undefined | ((fiber: any) => void)
 shouldYield(fiber: any) { this.hook?.(fiber); return false }
 makeDispatcher() { return { scheduleTask: (run: any, priority: number) => this.tasks.push({ run, priority, seq: this.seq++ }), flush: () => this.drain() } }
 run(e: any) { return Effect.runFork(e, { scheduler: this }) }
 get(e: any) { const f = this.run(e), x = f.pollUnsafe(); assert(x?._tag === "Success", "Expected immediate success"); return x.value }
 drain() { for (let n = 0; this.tasks.length; n++) { assert(n < 100, "Task limit"); this.tasks.sort((a,b) => a.priority - b.priority || a.seq - b.seq); this.executions++; this.tasks.shift().run() } }
}
function registrationGap(cancel: boolean) {
 const h = new Manual(), events: any[] = []
 const q = h.get(make("fork", "unbounded", Infinity)), go = h.get(Deferred.make())
 const f = h.run(Effect.gen(function*() { yield* Deferred.await(go); return yield* take(q) }))
 let observed = false, interrupter: any
 h.hook = (fiber) => {
  if (observed || fiber !== f || Ref.getUnsafe(q.cell).takers.length !== 1) return
  observed = true
  const t = Ref.getUnsafe(q.cell).takers[0]
  events.push({ event: "registered-before-await", interruptible: fiber.interruptible, awaitCallbacks: t.hint.resumes?.length ?? 0 })
  if (cancel) interrupter = h.run(Fiber.interrupt(f))
 }
 h.get(Deferred.succeed(go, undefined)); h.hook = undefined
 assert(observed, "Must visit registered gap")
 assert(events[0].interruptible === false && events[0].awaitCallbacks === 0, "Gap must be masked and before hint await registration")
 if (cancel) {
  assert(summary(f).tag === "Failure", "Gap cancellation must interrupt")
  assert(Ref.getUnsafe(q.cell).takers.length === 0, "Gap cancellation must withdraw registration")
  assert(summary(interrupter).tag === "Success", "Gap interrupter must finish")
 } else assert(summary(f).tag === "Pending", "Control must wait")
 h.get(offer(q, 1)); h.get(offer(q, 2))
 const tasksBeforeDrain = h.tasks.length
 h.drain()
 const s = Ref.getUnsafe(q.cell)
 assert(s.takers.length === 0, "No abandoned registration")
 assert(s.messages.length === (cancel ? 2 : 1), "Unexpected remaining messages")
 if (!cancel) { assert(summary(f).tag === "Success" && (summary(f) as any).value === 1, "Control consumes first message"); assert(tasksBeforeDrain === 2, "Two offers post two helpers for the same hint") }
 return { name: "registration-gap", cancel, events, tasksBeforeDrain, tasksExecuted: h.executions, target: summary(f), takers: s.takers.length, messages: s.messages }
}
function postedCancellation(incomingMasked: boolean) {
 const h = new Manual(), events: any[] = []
 const q = h.get(make("fork", "unbounded", Infinity))
 const caller = Effect.gen(function*() { const value = yield* take(q); events.push({ event: "inside-caller-continuation", value }); return value })
 const f = h.run(incomingMasked ? Effect.uninterruptible(caller) : caller)
 assert(summary(f).tag === "Pending" && Ref.getUnsafe(q.cell).takers.length === 1, "Target must wait")
 h.get(offer(q, 1))
 assert(h.tasks.length === 1, "Offer posts one helper")
 const interrupter = h.run(Fiber.interrupt(f))
 const afterInterrupt = { target: summary(f), interrupter: summary(interrupter), takers: Ref.getUnsafe(q.cell).takers.length, messages: [...Ref.getUnsafe(q.cell).messages] }
 if (incomingMasked) {
  assert(afterInterrupt.target.tag === "Pending" && afterInterrupt.takers === 1, "Masked waiter must not withdraw yet")
 } else {
  assert(afterInterrupt.target.tag === "Failure" && afterInterrupt.takers === 0, "Interruptible waiter must withdraw")
 }
 h.drain()
 const s = Ref.getUnsafe(q.cell)
 assert(summary(f).tag === "Failure" && (summary(f) as any).reasons.includes("Interrupt"), "Final target exit must interrupt")
 assert(summary(interrupter).tag === "Success", "Interrupter must finish")
 assert(s.messages.length === (incomingMasked ? 0 : 1), "Masked waiter consumes; unmasked waiter retains message")
 assert(events.length === (incomingMasked ? 1 : 0), "Incoming mask permits its inner continuation")
 return { name: "posted-window-cancellation", incomingMasked, afterInterrupt, events, target: summary(f), interrupter: summary(interrupter), takers: s.takers.length, messages: s.messages, tasksExecuted: h.executions }
}
console.log(JSON.stringify({ evidence: "Four finite wrapper cases; queue definitions copied unchanged", effect: version, bun: Bun.version, entry: `${dir}/dist/index.js`, cases: [registrationGap(true), registrationGap(false), postedCancellation(false), postedCancellation(true)] }, null, 2))
