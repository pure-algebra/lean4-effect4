// expect: TS2456
// Recursion through Option.Option, a type alias of a union of interfaces (`Option.ts:55`): through
// a tuple inside it the cycle defers (Chain); directly as its argument it does not (Peano).
import { Option } from "effect"
export type Chain = Option.Option<readonly [number, Chain]>
export type Peano = Option.Option<Peano>
export const chain: Chain = Option.some([1, Option.some([2, Option.none()])] as const)
export const two: Peano = Option.some(Option.some(Option.none()))
