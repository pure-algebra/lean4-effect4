import { Cause, Context, Data, Deferred, Effect, Exit, Fiber, Layer, Option, Ref, Scope, pipe } from "/Users/pooks/Dev/lean4-effect4/harness/truth/node_modules/effect/dist/index.js";
const Widget = { run: (n: number) => Effect.succeed(n + 1) };
const Token = 7;
const readWidget = (_n: number, token: number) => Effect.succeed(token);
/**

 */

export const makeCounter = (a0: void): Effect.Effect<number, never, never> => Effect.suspend(() => Effect.succeed(7))

export const readCounter = (a0: number, use: (a0: number) => Effect.Effect<number, never, never>): Effect.Effect<number, never, never> => Effect.suspend(() => use(a0))

export const Counter = Context.Service<"Counter", { readonly read: () => Effect.Effect<number, never, never> }>("Counter")

export const CounterLayer = Layer.effect(Counter, Effect.map(makeCounter(), (a0) => {
  return { read: () => readCounter(a0) }
}))

export const main: Effect.Effect<number, never, never> = Effect.succeed(1)
