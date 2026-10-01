// Seat T RED CONTROL for nullish.ts: asserting that `string | void` and `string | undefined` are
// mutually assignable must fail (TS2322 at the one line).
type Mutual<A, B> = [A] extends [B] ? ([B] extends [A] ? true : false) : false
export const u1: Mutual<string | undefined, string | void> = true
