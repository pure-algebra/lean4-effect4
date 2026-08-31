import type { Effect } from "effect"

declare const effectWithError: Effect.Effect<number, "boom">

// The ordinary type error is suppressed so the dedicated Effect diagnostic
// is the sole red signal exercised by this project.
// @ts-expect-error
export const missingError: Effect.Effect<number> = effectWithError
