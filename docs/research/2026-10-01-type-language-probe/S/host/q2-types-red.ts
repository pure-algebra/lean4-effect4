// Red twin of q2-types.ts: two false exact-type claims, each must fail with TS2344.
import { OP, OK, T1S, ARR } from "./q2-types.ts"
type Equal<A, B> = (<T>() => T extends A ? 1 : 2) extends (<T>() => T extends B ? 1 : 2) ? true : false
type Assert<T extends true> = T
export type OptionalIsOptionalKey = Assert<Equal<typeof OP.Type, typeof OK.Type>>
export type TupleIsArray = Assert<Equal<typeof T1S.Type, typeof ARR.Type>>
