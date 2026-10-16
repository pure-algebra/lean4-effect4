// expect: none
// Recursion through a readonly tuple (`prod`, `tuple`) and through a union at the top.
export type Cons = readonly [number, Cons] | null
export type Nested = number | ReadonlyArray<Nested>
export const cons: Cons = [1, [2, null]]
export const nested: Nested = [1, [2, [3]]]
