// Finite host controls. No general simulation or scheduler claim.
import * as Effect from "/Users/pooks/Dev/lean4-effect4/ts/release/node_modules/effect/dist/Effect.js"
import * as Fiber from "/Users/pooks/Dev/lean4-effect4/ts/release/node_modules/effect/dist/Fiber.js"
import * as PS from "/Users/pooks/Dev/lean4-effect4/ts/release/node_modules/effect/dist/PartitionedSemaphore.js"
import * as Queue from "/Users/pooks/Dev/lean4-effect4/ts/release/node_modules/effect/dist/Queue.js"

const observations: Array<{ name: string; actual: unknown; expected?: unknown; rejected?: unknown }> = []
let positive = 0
let negative = 0
const same = (a: unknown, b: unknown): boolean => JSON.stringify(a) === JSON.stringify(b)
const expect = (name: string, actual: unknown, expected: unknown): void => {
  if (!same(actual, expected)) throw new Error(`${name}: ${JSON.stringify(actual)} != ${JSON.stringify(expected)}`)
  observations.push({ name, actual, expected })
  positive += 1
}
const reject = (name: string, actual: unknown, rejected: unknown): void => {
  if (same(actual, rejected)) throw new Error(`${name}: deliberately wrong prediction passed`)
  observations.push({ name, actual, rejected })
  negative += 1
}

// Refund is an allocation producer: B consumes A's reservation before A's outer finalizer.
const pool = PS.makeUnsafe<number>({ permits: 2 })
Effect.runSync(pool.take(0, 1))
const trace: string[] = []
const canceled = Effect.runFork(Effect.onExit(pool.take(1, 2), () =>
  Effect.sync(() => { trace.push("A exit") })))
expect("refund.before-successor", Effect.runSync(pool.available), 0)
const successor = Effect.runFork(Effect.andThen(pool.take(2, 1), Effect.sync(() => {
  trace.push("B acquired")
})))
expect("refund.successor-still-waits", successor.pollUnsafe()?._tag ?? "Waiting", "Waiting")
await Effect.runPromise(Fiber.interrupt(canceled))
expect("refund.canceled-exit", canceled.pollUnsafe()?._tag, "Failure")
expect("refund.successor-success", successor.pollUnsafe()?._tag, "Success")
expect("refund.client-before-canceled-exit", trace, ["B acquired", "A exit"])
reject("refund.reject-no-refund", successor.pollUnsafe()?._tag ?? "Waiting", "Waiting")
reject("refund.reject-posted-delivery", trace, ["A exit", "B acquired"])
expect("refund.available-after-successor", Effect.runSync(pool.available), 0)
reject("refund.reject-credit-only-cleanup", Effect.runSync(pool.available), 1)
expect("refund.successor-returns-reservation", Effect.runSync(pool.release(1)), 1)
expect("refund.original-holder-returns", Effect.runSync(pool.release(1)), 2)

// Queue cancellation drops only the unaccepted suffix, retaining the accepted prefix.
const queue = Effect.runSync(Queue.bounded<number>(2))
Effect.runSync(Queue.offer(queue, 10))
const offering = Effect.runFork(Queue.offerAll(queue, [20, 30]))
expect("queue.partial-offer-waits", offering.pollUnsafe()?._tag ?? "Waiting", "Waiting")
await Effect.runPromise(Fiber.interrupt(offering))
expect("queue.partial-offer-interrupted", offering.pollUnsafe()?._tag, "Failure")
const messages = Effect.runSync(Queue.takeAll(queue))
expect("queue.accepted-prefix-stays", messages, [10, 20])
reject("queue.reject-rollback-accepted-prefix", messages, [10])
reject("queue.reject-commit-unaccepted-suffix", messages, [10, 20, 30])

console.log(JSON.stringify({ positive, negative, observations }, null, 2))
