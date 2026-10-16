// expect: TS2322
// A refinement by a guard narrows the target type; a filter does not. The first has no document
// (census C5); the second has one when it carries an id (C1, C6).
import { Schema } from "effect"
export const Tank = Schema.String.pipe(Schema.refine((s): s is `TK-${string}` => s.startsWith("TK-")))
export const Checked = Schema.String.check(Schema.isStartsWith("TK-"))
export const fromFilter: `TK-${string}` = Schema.decodeSync(Checked)("TK-1")
export const fromRefine: `TK-${string}` = Schema.decodeSync(Tank)("TK-1")
