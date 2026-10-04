/** Capture control 2 (seat PROGRAMS): `Cache.make`'s lookup runs under the creation context
 * merged under the caller's (`Cache.ts:205-211`, `Context.merge(context, input)`, and
 * `Context.ts:1816-1819`: the second argument's entries win). A key re-provided at the
 * `Cache.get` call site reaches the lookup (N: 2); a key only the creation site had is still
 * seen (M: 7). Compare `capture-control.ts`: a layer's closure keeps its build-time value. */
import { Cache, Context, Effect } from "effect"

class N extends Context.Service<N, number>()("ctl/N") {}
class M extends Context.Service<M, number>()("ctl/M") {}

export const control = Effect.gen(function*() {
  const cache = yield* Cache.make({
    capacity: 10,
    lookup: (_key: string) => Effect.all([Effect.service(N), Effect.service(M)])
  })
  return yield* Effect.provideService(Cache.get(cache, "k"), N, 2)
}).pipe(Effect.provideService(N, 1), Effect.provideService(M, 7))

export const pinControl: Effect.Effect<readonly [number, number]> = control
console.log("cache capture control", JSON.stringify(await Effect.runPromise(control)))
