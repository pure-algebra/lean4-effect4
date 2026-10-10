/**

 */

export const makeCounter = (a0: void): Effect.Effect<number, never, never> => Effect.suspend(() => Effect.succeed(7))

export const readCounter = (a0: number): Effect.Effect<number, never, never> => Effect.suspend(() => Effect.succeed(a0))

export const Counter = Context.Service<"Counter", { readonly read: () => Effect.Effect<number, never, never> }>("Counter")

export const CounterLayer = Layer.effect(Counter, Effect.map(makeCounter(), (a0) => {
  return { read: () => readCounter(a0) }
}))

export const main: Effect.Effect<number, never, never> = Effect.succeed(1)
