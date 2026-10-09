// Finite runtime controls only. This file states no Lean theorem or schedule law.
// Imports deliberately select the primary checkout's installed Effect 4.0.1.
import * as Effect from "/Users/pooks/Dev/lean4-effect4/ts/release/node_modules/effect/dist/Effect.js"
import * as Fiber from "/Users/pooks/Dev/lean4-effect4/ts/release/node_modules/effect/dist/Fiber.js"
import * as PS from "/Users/pooks/Dev/lean4-effect4/ts/release/node_modules/effect/dist/PartitionedSemaphore.js"

let positive = 0
let negative = 0
const observations: Array<{ name: string; actual: unknown; expected?: unknown; rejected?: unknown }> = []
const same = (a: unknown, b: unknown): boolean => JSON.stringify(a) === JSON.stringify(b)
const expect = (name: string, actual: unknown, expected: unknown): void => {
  if (!same(actual, expected)) throw new Error(`${name}: ${JSON.stringify(actual)} != ${JSON.stringify(expected)}`)
  positive += 1
  observations.push({ name, actual, expected })
}
const reject = (name: string, actual: unknown, wrongPrediction: unknown): void => {
  if (same(actual, wrongPrediction)) throw new Error(`${name}: wrong model passed`)
  negative += 1
  observations.push({ name, actual, rejected: wrongPrediction })
}

// Acquisition reserves the available prefix. Cancellation refunds all reservations,
// including permits allocated while the request waits.
const partial = PS.makeUnsafe<number>({ permits: 3 })
Effect.runSync(partial.take(0, 2))
expect("partial.before", Effect.runSync(partial.available), 1)
const waiting = Effect.runFork(partial.take(1, 3))
expect("partial.reservation", Effect.runSync(partial.available), 0)
reject("partial.reject-all-or-nothing", Effect.runSync(partial.available), 1)
expect("partial.additional-allocation", Effect.runSync(partial.release(1)), 0)
await Effect.runPromise(Fiber.interrupt(waiting))
expect("partial.cancel-refunds-two", Effect.runSync(partial.available), 2)
reject("partial.reject-no-refund", Effect.runSync(partial.available), 0)
reject("partial.reject-whole-request-refund", Effect.runSync(partial.available), 3)

// The temporary acquisition cleanup ends when take finishes.
const laterFailure = PS.makeUnsafe<number>({ permits: 2 })
const failed = Effect.runSyncExit(Effect.andThen(laterFailure.take(0, 1), Effect.fail("later")))
expect("completed-take.later-client-fails", failed._tag, "Failure")
expect("completed-take.holds-permit", Effect.runSync(laterFailure.available), 1)
reject("completed-take.reject-fiber-lifetime-refund", Effect.runSync(laterFailure.available), 2)

// A yielded callback resumes its fiber synchronously. Its client can return the
// permit before the releasing operation reads and returns its available count.
const reentrant = PS.makeUnsafe<number>({ permits: 1 })
Effect.runSync(reentrant.take(0, 1))
const reentrantTrace: string[] = []
const reentrantWaiter = Effect.runFork(Effect.andThen(
  reentrant.take(1, 1),
  Effect.andThen(
    Effect.sync(() => { reentrantTrace.push("client resumed") }),
    Effect.andThen(reentrant.release(1), Effect.sync(() => { reentrantTrace.push("client released") }))
  )
))
const reentrantReply = Effect.runSync(reentrant.release(1))
reentrantTrace.push("outer returned")
expect("reentrant.public-release-reply", reentrantReply, 1)
expect("reentrant.client-before-return", reentrantTrace, ["client resumed", "client released", "outer returned"])
reject("reentrant.reject-wakes-after-return", reentrantTrace, ["outer returned", "client resumed", "client released"])
reject("reentrant.reject-pre-delivery-reply", reentrantReply, 0)
expect("reentrant.waiter-success", Effect.runSyncExit(Fiber.join(reentrantWaiter))._tag, "Success")

// Allocation visits partitions, rather than finishing the oldest global request.
// Each visited partition allocates to its oldest waiter.
const grouped = PS.makeUnsafe<number>({ permits: 3 })
Effect.runSync(grouped.take(0, 3))
const groupedTrace: string[] = []
const queue = (pool: PS.PartitionedSemaphore<number>, key: number, count: number, name: string, trace: string[]) =>
  Effect.runFork(Effect.andThen(pool.take(key, count), Effect.sync(() => { trace.push(name) })))
const a1 = queue(grouped, 1, 2, "A1", groupedTrace)
const a2 = queue(grouped, 1, 1, "A2", groupedTrace)
const b1 = queue(grouped, 2, 1, "B1", groupedTrace)
expect("grouped.first-release-available", Effect.runSync(grouped.release(2)), 0)
expect("grouped.first-completion", [...groupedTrace], ["B1"])
reject("grouped.reject-global-fifo", [...groupedTrace], ["A1"])
Effect.runSync(grouped.release(1))
expect("grouped.second-completion", [...groupedTrace], ["B1", "A1"])
Effect.runSync(grouped.release(1))
expect("grouped.within-key-fifo", [...groupedTrace], ["B1", "A1", "A2"])
Effect.runSync(Fiber.join(a1))
Effect.runSync(Fiber.join(a2))
Effect.runSync(Fiber.join(b1))

// Removing the first partition and reinserting its key appends a new map entry.
// The persistent iterator continues beyond B and C to the reinserted A.
const reinserted = PS.makeUnsafe<number>({ permits: 3 })
Effect.runSync(reinserted.take(0, 3))
const insertionTrace: string[] = []
const oldA = queue(reinserted, 1, 1, "A-old", insertionTrace)
const nextB = queue(reinserted, 2, 2, "B", insertionTrace)
const nextC = queue(reinserted, 3, 2, "C", insertionTrace)
Effect.runSync(reinserted.release(1))
const newA = queue(reinserted, 1, 1, "A-new", insertionTrace)
Effect.runSync(reinserted.release(2))
expect("iterator-host.partial-B-C", [...insertionTrace], ["A-old"])
Effect.runSync(reinserted.release(1))
expect("iterator-host.reinserted-A-before-wrap", [...insertionTrace], ["A-old", "A-new"])
reject("iterator-host.reject-reset-each-release", [...insertionTrace], ["A-old", "B"])
Effect.runSync(reinserted.release(2))
expect("iterator-host.wrapped-completions", [...insertionTrace], ["A-old", "A-new", "B", "C"])
Effect.runSync(Fiber.join(oldA))
Effect.runSync(Fiber.join(newA))
Effect.runSync(Fiber.join(nextB))
Effect.runSync(Fiber.join(nextC))

// These native Map observations are finite controls, not a formal iterator simulation.
const map = new Map<number, string>([[1, "a"], [2, "b"]])
const iterator = map.entries()
expect("native-map.first", iterator.next().value, [1, "a"])
map.delete(2)
map.set(3, "c")
const afterDelete = iterator.next().value
expect("native-map.skip-deleted-observe-appended", afterDelete, [3, "c"])
reject("native-map.reject-frozen-snapshot", afterDelete, [2, "b"])
map.delete(1)
map.set(1, "a2")
expect("native-map.reinserted-entry", iterator.next().value, [1, "a2"])
expect("native-map.exhausted", iterator.next().done, true)
map.set(4, "d")
const exhaustedAgain = iterator.next()
expect("native-map.exhaustion-persists", exhaustedAgain.done, true)
reject("native-map.reject-exhausted-iterator-revival", exhaustedAgain.done, false)
expect("native-map.replacement-observes-live-order", Array.from(map.entries()), [[3, "c"], [1, "a2"], [4, "d"]])

console.log(JSON.stringify({ runtime: "Effect 4.0.1; Bun 1.4.2", positive, negative, observations }, null, 2))
