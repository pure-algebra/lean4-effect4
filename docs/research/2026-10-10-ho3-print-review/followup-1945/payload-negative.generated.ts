/**

 */

export class Payload extends Data.TaggedError("Payload")<{ readonly id: number }> {}

export const buildPayload = (a0: number, Payload: (a0: number) => Effect.Effect<number, never, never>): Effect.Effect<Payload, never, never> => Effect.suspend(() => Effect.succeed(new Payload({ id: 7 })))

export const main: Effect.Effect<number, never, never> = Effect.succeed(1)
