// expect: TS2300 TS2300
// A declared name that a payload class of the module already declares (decisions row 120).
import { Data } from "effect"
export class NotFound extends Data.TaggedError("NotFound")<{ readonly id: number }> {}
export type NotFound = { readonly id: number }
