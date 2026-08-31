import { Effect } from "effect"

export const hiddenPromise = Effect.sync(() => Promise.resolve(1))
