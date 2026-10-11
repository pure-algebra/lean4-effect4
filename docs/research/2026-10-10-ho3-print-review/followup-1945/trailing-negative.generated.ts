/**

 */

export const readExternal = (a0: number, Token: (a0: number) => Effect.Effect<number, never, never>): Effect.Effect<number, never, never> => Effect.suspend(() => readWidget(a0, Token))

export const main: Effect.Effect<number, never, never> = Effect.succeed(1)
