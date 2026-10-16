// expect: none
// Recursion through a record field and ReadonlyArray (`list`).
import { Effect } from "effect"
export type Tree = { readonly value: number; readonly children: ReadonlyArray<Tree> }
export const tree: Effect.Effect<Tree> = Effect.succeed({ value: 1, children: [{ value: 2, children: [] }] })
