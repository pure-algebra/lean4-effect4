import * as Effect from "../../../vendor/effect-4.0.1/src/Effect.ts"
import * as Fiber from "../../../vendor/effect-4.0.1/src/Fiber.ts"
import * as PS from "../../../vendor/effect-4.0.1/src/PartitionedSemaphore.ts"
import * as Ref from "../../../vendor/effect-4.0.1/src/Ref.ts"
import * as SR from "../../../vendor/effect-4.0.1/src/SynchronizedRef.ts"
const assert = (label: string, actual: unknown, expected: unknown) => {
 if (JSON.stringify(actual) !== JSON.stringify(expected)) throw new Error(`${label}: ${JSON.stringify(actual)} != ${JSON.stringify(expected)}`)
 console.log(label, JSON.stringify(actual))
}
const p = PS.makeUnsafe<string>({permits: 2})
Effect.runSync(p.take("owner", 1))
const waiter = Effect.runFork(p.take("a", 2))
assert("partial reservation", Effect.runSync(p.available), 0)
await Effect.runPromise(Fiber.interrupt(waiter))
assert("cancellation refund", Effect.runSync(p.available), 1)
const failed = PS.makeUnsafe<string>({permits: 2})
Effect.runSyncExit(Effect.andThen(failed.take("a", 1), Effect.fail("fail")))
assert("later failure after completed take holds permit", Effect.runSync(failed.available), 1)
const q = PS.makeUnsafe<string>({permits: 3})
Effect.runSync(q.take("owner", 3))
const order: string[] = []
const take = (key: string, count: number, name: string) => Effect.runFork(Effect.andThen(q.take(key,count), Effect.sync(()=>order.push(name))))
const a1 = take("A", 2, "A1"); const a2 = take("A", 1, "A2"); const b1 = take("B",1,"B1")
assert("release returns available", Effect.runSync(q.release(2)), 0)
await new Promise(r => setTimeout(r,20))
assert("per-key first round", order, ["B1"])
Effect.runSync(q.release(1)); await new Promise(r => setTimeout(r,20))
assert("per-key second round", order, ["B1", "A1"])
Effect.runSync(q.release(1)); await new Promise(r => setTimeout(r,20))
assert("within-key FIFO", order, ["B1", "A1", "A2"])
const s = SR.makeUnsafe(4)
await Effect.runPromiseExit(SR.modifyEffect(s, old => Effect.andThen(Effect.sync(() => order.push(`old:${old}`)), Effect.fail("x"))))
assert("failed synchronized update keeps cell", SR.getUnsafe(s), 4)
assert("next synchronized update after failure", Effect.runSync(SR.modify(s, old => [old,old+1])), 4)
assert("new synchronized value", SR.getUnsafe(s), 5)
const ref = Ref.makeUnsafe(0)
const reply = Effect.runSync(Ref.set(ref, 8))
console.log("Ref.set actual reply shape", {sameRef: reply === ref, sameBacking: reply === ref.ref, stored: Ref.getUnsafe(ref)})
