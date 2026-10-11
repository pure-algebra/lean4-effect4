/**

 */

export class OnlyParam extends Data.TaggedError("OnlyParam")<{ readonly id: number }> {}

export const onlyHelper = (a0: OnlyParam, use: (a0: OnlyParam) => Effect.Effect<number, never, never>): Effect.Effect<number, never, never> => Effect.suspend(() => Effect.succeed(1))

export const main: Effect.Effect<number, never, never> = Effect.succeed(1)
