import { Cause, Context, Data, Deferred, Effect, Exit, Fiber, Layer, Option, Ref, Scope, pipe } from "/Users/pooks/Dev/lean4-effect4/harness/truth/node_modules/effect/dist/index.js";
/**

 */

export const selectedProgram = (a0: number, firstTask: (a0: number) => Effect.Effect<number, never, never>, secondTask: (a0: number) => Effect.Effect<number, never, never>): Effect.Effect<number, never, never> => Effect.suspend(() => secondTask(a0))

export const main: Effect.Effect<number, never, never> = selectedProgram(5, (a0) => Effect.succeed(11), (a0) => Effect.succeed(17))
