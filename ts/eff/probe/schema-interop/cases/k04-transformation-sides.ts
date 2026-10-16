// expect: TS2322
// A transformation is a pair of types: NumberFromString's type side is number, its encoded side
// string. The document (census T1) keeps the encoded side only.
import { Schema } from "effect"
export const decoded: number = Schema.decodeSync(Schema.NumberFromString)("1")
export const encoded: string = Schema.encodeSync(Schema.NumberFromString)(1)
export const wrong: number = Schema.encodeSync(Schema.NumberFromString)(1)
