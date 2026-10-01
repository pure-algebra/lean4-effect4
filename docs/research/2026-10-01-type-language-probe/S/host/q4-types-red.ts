// Red twin of q4-types.ts: two false exact-type claims on route U's emitted runtime; each must fail
// with TS2344. The second says route U's `__proto__` loss is visible in its type (it is not).
import * as U from "./upstream-generated.ts"
type Equal<A, B> = (<T>() => T extends A ? 1 : 2) extends (<T>() => T extends B ? 1 : 2) ? true : false
type Assert<T extends true> = T
export type TupleIsArray = Assert<Equal<typeof U.TUPLE3.Type, ReadonlyArray<number | string | boolean>>>
export type ProtoLossVisible = Assert<Equal<typeof U.N_PROTO.Type, {}>>
