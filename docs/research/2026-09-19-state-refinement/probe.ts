// Bounded research control over the vendored rc.112 source. No production changes.
// Run from any cwd: bun <path-to-this-file>
import * as Effect from '../../../vendor/effect-4.0.0-rc.112/src/Effect.ts'
import * as Latch from '../../../vendor/effect-4.0.0-rc.112/src/Latch.ts'
import * as Deferred from '../../../vendor/effect-4.0.0-rc.112/src/Deferred.ts'
import * as M from '../../../vendor/effect-4.0.0-rc.112/src/MutableHashMap.ts'
function harness() {
 const tasks: Array<() => void> = []
 const dispatcher = {scheduleTask(f: () => void, _: number) {tasks.push(f)}, flush() {while(tasks.length) tasks.shift()!()}}
 const scheduler = {executionMode: 'sync' as const, shouldYield: () => false, makeDispatcher: () => dispatcher}
 return {tasks, dispatcher, scheduler}
}
function assert(ok: unknown, message: string) {if(!ok) throw Error(message)}
function runGate(kind: 'latch' | 'deferred') {
 const h=harness(); let value=0; let seen: number|undefined
 const l=Latch.makeUnsafe(); const d=Deferred.makeUnsafe<void>()
 const wait=kind==='latch' ? l.await : Deferred.await(d)
 Effect.runFork(Effect.andThen(wait, Effect.sync(()=>{seen=value})), {scheduler:h.scheduler})
 const open=kind==='latch' ? l.open : Deferred.succeed(d, undefined)
 Effect.runFork(Effect.andThen(open, Effect.sync(()=>{value=1})), {scheduler:h.scheduler})
 const before=seen
 h.dispatcher.flush()
 return {before: before ?? null, after:seen}
}
const latch=runGate('latch'); const deferred=runGate('deferred')
assert(latch.after===1 && deferred.after===0, 'Expected scheduled and inline gates to expose different final read values')
const h=harness(); const l=Latch.makeUnsafe(); let resumed=0
const waiter=Effect.runFork(Effect.andThen(l.await, Effect.sync(()=>{resumed++})), {scheduler:h.scheduler})
Effect.runFork(l.open, {scheduler:h.scheduler})
const scheduledBefore=(l as any).scheduled.length
waiter.interruptUnsafe()
const scheduledAfter=(l as any).scheduled.length
h.dispatcher.flush()
assert(scheduledBefore===1 && scheduledAfter===0 && resumed===0, 'Expected cancellation to remove captured waiter before flush')
const map=M.empty<object,number>(); M.set(map,{id:1},1); M.set(map,{id:1},2)
assert(M.size(map)===1,'Expected rc112 structural equality for plain object keys')
console.log(JSON.stringify({kind:'finite pinned-rc112 probe, not a Lean theorem',gateObservations:{latch,deferred},cancelScheduled:{scheduledBefore,scheduledAfter,resumed},mutableHashMapObjectKeys:M.size(map), nativeMapObjectKeys:new Map([[{id:1},1],[{id:1},2]]).size},null,2))
