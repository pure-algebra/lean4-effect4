import * as Effect from "/Users/pooks/Dev/lean4-effect4/ts/eff/node_modules/effect/dist/Effect.js"
import type * as Fiber from "/Users/pooks/Dev/lean4-effect4/ts/eff/node_modules/effect/dist/Fiber.js"
import type * as Scheduler from "/Users/pooks/Dev/lean4-effect4/ts/eff/node_modules/effect/dist/Scheduler.js"

function probe(completion: Effect.Effect<string, string>, label: string, forceYield: boolean) {
const tasks: Array<() => void> = []
const events: Array<string> = []
let attempts = 0
let heldId = -1
let yieldReply = false
let answer: ((value: Effect.Effect<string, string>) => void) | undefined
let tick: ((value: Effect.Effect<never, string>) => void) | undefined
const scheduler: Scheduler.Scheduler = {
  executionMode: "sync",
  shouldYield(fiber: Fiber.Fiber<unknown, unknown>) {
    if (yieldReply && fiber.id === heldId) {
      yieldReply = false
      events.push("yield attempt after host reply")
      return true
    }
    return false
  },
  makeDispatcher() {
    return {
      scheduleTask(task: () => void) { tasks.push(task) },
      flush() { while (tasks.length > 0) tasks.shift()!() }
    }
  }
}
const attempt = Effect.onExit(
  Effect.flatMap(Effect.sync(() => { attempts++; events.push(`call ${attempts}`) }), () =>
    Effect.withFiber(fiber => Effect.callback<string, string>(resume => {
      heldId = fiber.id
      answer = resume
    }))),
  () => Effect.sync(() => events.push(`cleanup ${attempts}`)))
const timer = Effect.callback<never, string>(resume => { tick = resume })
const client = Effect.retry(Effect.raceFirst(attempt, timer), { times: 3, while: e => e === "Timeout" })
const root = Effect.runFork(client, { scheduler })
root.addObserver(exit => events.push(`root ${exit._tag}`))
while (tasks.length > 0) tasks.shift()!()
if (!answer || !tick || attempts !== 1) throw new Error("initial calls missing")
yieldReply = forceYield
events.push(`host applies ${label} reply`)
answer(completion)
if (forceYield && !events.includes("yield attempt after host reply")) {
  const next = tasks.shift()
  if (!next) throw new Error("reply scheduled no task")
  next()
}
events.push("clock fires timeout")
tick(Effect.fail("Timeout"))
// The script selects the timer's runnable task before the yielded attempt.
if (tasks.length > 1) tasks.pop()!()
while (tasks.length > 0) tasks.shift()!()
const expected = forceYield ? 2 : 1
if (Number(attempts) !== expected) throw new Error(`expected ${expected} attempts, saw ${attempts}`)
return { completion: label, forceYield, attempts, events }
}
console.log(JSON.stringify({ effect: "4.0.0-rc.112", cases: [
  probe(Effect.succeed("body-1"), "success", true),
  probe(Effect.fail("BadRequest"), "nonretryable BadRequest", true),
  probe(Effect.succeed("body-1"), "success", false),
  probe(Effect.fail("BadRequest"), "nonretryable BadRequest", false)
]}, null, 2))
