export const main: Effect.Effect<number, never, never> = ifCase(() => true, () => Effect.succeed(7), () => Effect.succeed(9))
