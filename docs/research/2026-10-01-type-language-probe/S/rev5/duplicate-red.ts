// Historical malformed output retained only as a rejecting compiler control.
import * as Schema from "effect/Schema";
export const DUP = Schema.Struct({a: Schema.Number, a: Schema.String});
