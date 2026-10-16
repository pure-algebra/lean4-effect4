// expect: TS2456
// Recursion through Result.Result, a type alias of a union of interfaces (`Result.ts:66`), directly
// as its argument: refused.
import { Result } from "effect"
export type Steps = Result.Result<Steps, string>
export const steps: Steps = Result.succeed(Result.fail("stop"))
