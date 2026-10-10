import { Cause, Context, Data, Deferred, Effect, Exit, Fiber, Layer, Option, Ref, Scope, pipe } from "/Users/pooks/Dev/lean4-effect4/harness/truth/node_modules/effect/dist/index.js";
const Widget = { run: (n: number) => Effect.succeed(n + 1) };
const Token = 7;
const readWidget = (_n: number, token: number) => Effect.succeed(token);
/**

 */

export const readExternal = (a0: number, Widget: (a0: number) => Effect.Effect<number, never, never>): Effect.Effect<number, never, never> => Effect.suspend(() => Widget.run(a0))

export const main: Effect.Effect<number, never, never> = Effect.succeed(1)
