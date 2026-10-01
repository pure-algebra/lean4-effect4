/** Capture control (seat PROGRAMS): a service method built by a layer closes over a service it
 * read at build time. Re-providing that service at the call site does not reach the method
 * (captured: answers 1); a method that reads the service when called does (call site: answers 2).
 * The builder route (method bodies inlined at the call site) has only the second behaviour. */
import { Context, Effect, Layer } from "effect"

class N extends Context.Service<N, number>()("ctl/N") {}
class Svc extends Context.Service<Svc, {
  readonly captured: Effect.Effect<number>
  readonly atCall: Effect.Effect<number, never, N>
}>()("ctl/Svc") {}

const SvcLive = Layer.effect(Svc, Effect.gen(function*() {
  const n = yield* N
  return { captured: Effect.succeed(n), atCall: Effect.service(N) }
}))

export const control = Effect.gen(function*() {
  const svc = yield* Svc
  const a = yield* Effect.provideService(svc.captured, N, 2)
  const b = yield* Effect.provideService(svc.atCall, N, 2)
  return [a, b] as const
}).pipe(Effect.provide(SvcLive), Effect.provideService(N, 1))

export const pinControl: Effect.Effect<readonly [number, number]> = control
console.log("capture control", JSON.stringify(await Effect.runPromise(control)))
