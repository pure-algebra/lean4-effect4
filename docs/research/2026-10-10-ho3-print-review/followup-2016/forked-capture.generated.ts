/**

 */

export const forkedProgram = (a0: number, use: (a0: number) => Effect.Effect<number, never, never>): Effect.Effect<number, never, never> => Effect.suspend(() => Effect.flatMap(Effect.forkChild(use(a0), { startImmediately: true, uninterruptible: "inherit" }), (a1) => Fiber.join(a1)))

export const main: Effect.Effect<number, never, never> = Effect.flatMap(Effect.succeed(37), (a0) => forkedProgram(5, (a1) => Effect.succeed(a0)))
