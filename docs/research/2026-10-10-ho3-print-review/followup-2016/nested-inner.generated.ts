/**

 */

export const applyProgram = (a0: number, use: (a0: number) => Effect.Effect<number, never, never>): Effect.Effect<number, never, never> => Effect.suspend(() => use(a0))

export const main: Effect.Effect<number, never, never> = Effect.flatMap(Effect.succeed(11), (a0) => applyProgram(5, (a1) => applyProgram(3, (a2) => Effect.succeed(a2))))
