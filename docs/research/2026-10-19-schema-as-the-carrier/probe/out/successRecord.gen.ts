/**
 * faces: successRecord, written by Faces.lean. Do not edit.
 */
import { Effect } from "effect"
import { recordValue } from "../../../../../harness/truth/prelude.ts"

export const main: Effect.Effect<{ readonly id: number; readonly nick?: string; readonly title: string }, never, never> = Effect.succeed(
  recordValue<{ readonly id: number; readonly nick?: string; readonly title: string }>(
    [
      10,
      [20],
      [[4, [[5, [3, "id"], [5, [1, false], [10, [2], []]]], [5, [3, "nick"], [5, [1, true], [10, [4], []]]], [5, [3, "title"], [5, [1, false], [10, [4], []]]]]]]
    ],
    { id: 1, title: "milk" }
  )
)
