/** Red control for the type check (seat PROGRAMS): each line must be refused by tsgo against
 * rc.112. If this file ever checks clean, the paths in tsconfig.json resolve to something other
 * than the pinned declarations, and the five green checks mean nothing. */
import { Effect, Schedule } from "effect"
export const r1 = Effect.forkDaemon(Effect.void)            // Effect 3 spelling; rc.112 has forkDetach
export const r2 = Schedule.intersect(Schedule.recurs(2), Schedule.spaced("100 millis")) // not in rc.112
export const r3: Effect.Effect<number, never> = Effect.fail("boom") // error channel mismatch
