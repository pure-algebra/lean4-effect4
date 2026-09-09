import { Effect } from "effect"
export const answer = Effect.succeed(42)
export const failure = Effect.fail("boom")
export const mapped = Effect.succeed(42).pipe(Effect.as(43))
Effect.runSyncExit(Effect.succeed(7))
