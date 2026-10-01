// Seat T: does the printed `ReadonlyArray<T>` (Ty.list) agree with a mutable `T[]`? (green: exit 0)
type Mutual<A, B> = [A] extends [B] ? ([B] extends [A] ? true : false) : false
type Below<A, B> = [A] extends [B] ? true : false
export const v1: Mutual<ReadonlyArray<number>, readonly number[]> = true
export const v2: Mutual<ReadonlyArray<number>, number[]> = false // mutability matters for arrays
export const v3: Below<number[], ReadonlyArray<number>> = true // a mutable array fits the printed type
export const v4: Mutual<{ readonly xs: ReadonlyArray<number> }, { xs: number[] }> = false
