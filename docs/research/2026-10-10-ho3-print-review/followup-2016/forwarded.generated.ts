/**

 */

export const applyProgram = (a0: number, use: (a0: number) => Effect.Effect<number, never, never>): Effect.Effect<number, never, never> => Effect.suspend(() => use(a0))

export const relayProgram = (a0: number, forwarded: (a0: number) => Effect.Effect<number, never, never>): Effect.Effect<number, never, never> => Effect.suspend(() => applyProgram(a0, (a1) => forwarded(a1)))

export const main: Effect.Effect<number, never, never> = Effect.flatMap(Effect.succeed(29), (a0) => relayProgram(5, (a1) => Effect.succeed(a0)))
