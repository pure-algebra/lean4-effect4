import { Context, Effect, Layer, Ref, Scheduler } from "effect"
import { Cell, incr } from "./fixture.ts"

// 1. Every service call is an observable event: wrap the implementation.
type Event = { kind: "op"; op: string; args: unknown[]; stack: string[] } |
             { kind: "answer"; op: string; value: unknown } |
             { kind: "schedule"; priority: number } |
             { kind: "finalizer"; exit: string }
const trace: Event[] = []

// 2. The frame stack is a plain array on the fiber; `withFiber` hands us the fiber.
const frames = (fiber: any): string[] => fiber._stack.map((p: any) => p["~effect/Effect/identifier"] ?? Object.getPrototypeOf(p)?._tag ?? "?")

const traced = <A, E, R>(op: string, args: unknown[], eff: Effect.Effect<A, E, R>) =>
  Effect.withFiber((fiber) => {
    trace.push({ kind: "op", op, args, stack: frames(fiber) })
    return eff.pipe(Effect.tap((value) => { trace.push({ kind: "answer", op, value }); return Effect.void }))
  })

// 3. Handler with a Ref, every method routed through the tracer.
const CellLive = (initial: number): Layer.Layer<Cell> =>
  Layer.effect(Cell, Effect.gen(function* () {
    const ref = yield* Ref.make(initial)
    return {
      get: traced("get", [], Ref.get(ref)),
      put: (n: number) => traced("put", [n], Ref.set(ref, n))
    }
  }))

// 4. The scheduler is pluggable: every scheduled task is a visible, controllable decision.
class TapeScheduler extends Scheduler.MixedScheduler {
  override scheduleTask(task: () => void, priority: number): void {
    trace.push({ kind: "schedule", priority })
    super.scheduleTask(task, priority)
  }
}

const program = incr(0).pipe(
  Effect.provide(CellLive(41)),
  Effect.onExit((exit) => Effect.sync(() => { trace.push({ kind: "finalizer", exit: exit._tag }) })))

const fiber = Effect.runFork(program, { scheduler: new TapeScheduler() })
const exit = await new Promise((resolve) => (fiber as any).addObserver(resolve))
console.log(JSON.stringify({ exit, trace }, null, 1))
