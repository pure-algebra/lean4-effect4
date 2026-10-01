// Seat R, question 3: red twins of forms-wave.ts. Each statement must be refused.
import { Data } from "effect"
type T3 = readonly [number, string, boolean]
const t: T3 = [1, "a", true]
export const nested: readonly [number, readonly [string, boolean]] = t        // nested pairs are not a 3-tuple
export const out: string = t[3]                                              // past the end
type M = Readonly<Record<string, number>>
const m: M = { a: 1 }
export const unchecked: number = m["a"]                                      // noUncheckedIndexedAccess
export class NotFound extends Data.TaggedError("NotFound")<{ readonly id: number }> {}
export const asRecord: NotFound = { _tag: "NotFound", id: 2 }                // a record is not the class
