/**
 * faces: successList, written by Faces.lean. Do not edit.
 */
import { Effect } from "effect"
import { cons, nil } from "../../../../../harness/truth/prelude.ts"

export const main: Effect.Effect<ReadonlyArray<number>, never, never> = Effect.succeed(cons(1, cons(2, nil())))
