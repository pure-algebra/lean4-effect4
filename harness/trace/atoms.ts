/** Host body of the pure atom `succ`; its Lean model is `succ` in Generate.lean. */
export const succ = (n: number): number => n + 1
import { Result } from "effect"
/** Host body of the pure atom `orZero`; its Lean model is `orZero` in Generate.lean. */
export const orZero = (e: Result.Result<number, string>): number => Result.isSuccess(e) ? e.success : 0
/** Host body of the pure atom `dec`; its Lean model is `jobAtom "dec"` in
 * Generate.lean. Naturals are truncated at zero on the Lean side, and the job
 * runner never calls it at zero. */
export const dec = (n: number): number => n - 1
import { Option } from "effect"
/** Host body of the pure atom `flagToNat`; its Lean model is `flagToNat` in Generate.lean. */
export const flagToNat = (flag: boolean): number => flag ? 1 : 0
/** Host body of the pure atom `pollValue`; its Lean model is `pollValue` in Generate.lean. */
export const pollValue = (cell: Option.Option<Result.Result<number, number>>): number =>
  Option.isSome(cell) && Result.isSuccess(cell.value) ? cell.value.success : 0
/** Host body of the pure atom `addNat`; its Lean model is `addNat` in Generate.lean. */
export const addNat = (left: number, right: number): number => left + right
