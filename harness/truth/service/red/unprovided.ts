// Red control of the consumer: with no repository provided, the program still requires the
// repository's key, so it is no `Effect.Effect<…, …, never>`.
import type { Effect } from "effect"
import { programs } from "../consumer.ts"

export const unprovided: Effect.Effect<unknown, unknown, never> = programs.addMilk
