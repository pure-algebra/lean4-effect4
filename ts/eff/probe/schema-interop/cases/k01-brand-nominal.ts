// expect: TS2322 TS2322
// A brand makes two quantities with one body two types on the target, as Lean's nominal order
// makes two declared names (decisions rows 158, 406). The structural aliases of the named-types
// probe (`a01`) cross silently; the branded ones do not.
import { Schema } from "effect"
const Positive = Schema.Number.check(Schema.isInt(), Schema.isGreaterThan(0))
export const FlowRate = Positive.pipe(Schema.brand("FlowRate"))
export const HoldUp = Positive.pipe(Schema.brand("HoldUp"))
export type FlowRate = typeof FlowRate.Type
export type HoldUp = typeof HoldUp.Type
export const flow: FlowRate = Schema.decodeSync(FlowRate)(250)
// refused: a flow is not a hold-up, and a bare number is no flow
export const hold: HoldUp = flow
export const bare: FlowRate = 250
// accepted: the brand is erased on the way out, a flow is a number
export const asNumber: number = flow
