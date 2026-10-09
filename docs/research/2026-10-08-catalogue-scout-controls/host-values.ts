import * as Effect from "../../../vendor/effect-4.0.1/src/Effect.ts"
import * as Ref from "../../../vendor/effect-4.0.1/src/Ref.ts"
import * as PS from "../../../vendor/effect-4.0.1/src/PartitionedSemaphore.ts"
import * as PubSub from "../../../vendor/effect-4.0.1/src/PubSub.ts"
const r = Ref.makeUnsafe(3)
console.log("ref", Effect.runSync(Ref.getAndUpdate(r, n => n + 2)), Ref.getUnsafe(r))
const hub = PubSub.makeAtomicBounded<number>(1)
console.log("pubsub no subscribers", hub.publish(1), hub.size())
const a = hub.subscribe(); const b = hub.subscribe()
console.log("pubsub two subscribers", hub.publish(7), hub.size(), a.poll(), hub.size(), b.poll(), hub.size())
const p = PS.makeUnsafe<string>({permits: 2})
Effect.runSync(p.take("owner", 1))
const waiter = Effect.runFork(p.take("a", 2))
console.log("partitioned reservation", Effect.runSync(p.available))
process.exit(0)
