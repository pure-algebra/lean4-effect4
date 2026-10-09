export class LeftFailure extends Data.TaggedError("LeftFailure")<{ readonly code: number }> {}
export class RightFailure extends Data.TaggedError("RightFailure")<{ readonly code: number }> {}
export const main: Effect.Effect<number, never, never> = Effect.matchCauseEffect(ifCase(() => true, () => Effect.fail(new LeftFailure({ code: 11 })), () => Effect.fail(new RightFailure({ code: 22 }))), { onFailure: (a0) => optionCase(causeError(a0), () => Effect.succeed(998), (a1) => Effect.succeed(recordRequired<"code">("code")(a1))), onSuccess: (a0) => Effect.succeed(999) })
