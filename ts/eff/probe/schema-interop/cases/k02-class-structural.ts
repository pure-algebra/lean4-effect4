// expect: none
// A Schema class's instance type is structural on the target: a plain record with its fields is
// assignable to it, so the class identity that decoding builds is no type-level distinction.
import { Schema } from "effect"
export class DesignRef extends Schema.Class<DesignRef>("DesignRef")({ vesselId: Schema.String, revision: Schema.Number }) {}
export const plain: DesignRef = { vesselId: "TK-101", revision: 3 }
