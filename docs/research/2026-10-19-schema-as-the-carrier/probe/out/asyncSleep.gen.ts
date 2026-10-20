/**
 * faces: asyncSleep, written by Faces.lean. Do not edit.
 */
import { Effect } from "effect"

export const main: Effect.Effect<void, never, never> = Effect.sleep(1000)
