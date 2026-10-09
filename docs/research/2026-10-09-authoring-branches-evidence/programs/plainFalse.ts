export const main: Effect.Effect<number, never, never> = ifCase(() => false, () => Effect.succeed(7), () => Effect.succeed(9))
