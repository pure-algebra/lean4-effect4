/**

 */

export const readExternal = (a0: number, use: (a0: number) => Effect.Effect<number, never, never>): Effect.Effect<number, never, never> => Effect.suspend(() => Widget.run(a0))

export const main: Effect.Effect<number, never, never> = Effect.succeed(1)
