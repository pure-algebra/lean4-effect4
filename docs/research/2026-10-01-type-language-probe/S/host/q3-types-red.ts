// Red twin of q3-types.ts: two false exact-type claims; each must fail with TS2344.
import * as G from "./generated-profile.ts"
type Equal<A, B> = (<T>() => T extends A ? 1 : 2) extends (<T>() => T extends B ? 1 : 2) ? true : false
type Assert<T extends true> = T
export type TupleIsArray = Assert<Equal<typeof G.TUPLE3.Type, ReadonlyArray<number | string | boolean>>>
export type OptionalIsRequired = Assert<Equal<typeof G.OPTIONAL.Type, { readonly a: number; readonly b: string }>>
