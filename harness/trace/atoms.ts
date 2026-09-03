/** Host body of the pure atom `succ`; its Lean model is `succ` in Generate.lean. */
export const succ = (n: number): number => n + 1
import { Result } from "effect"
/** Host body of the pure atom `orZero`; its Lean model is `orZero` in Generate.lean. */
export const orZero = (e: Result.Result<number, string>): number => Result.isSuccess(e) ? e.success : 0
