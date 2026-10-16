// expect: none
// The deferring spellings of a1's refused cycles: an alias of a union of interfaces written as
// that union, and the map as an object type with an index signature. Each is the same type as
// the alias spelling, in both directions.
import { Exit, Option, Result } from "effect"
export type Peano = Option.None<Peano> | Option.Some<Peano>
export type Steps = Result.Success<Steps, string> | Result.Failure<Steps, string>
export type E1 = Exit.Success<E1, string> | Exit.Failure<E1, string>
export type Dict = { readonly [key: string]: Dict }
export const two: Peano = Option.some(Option.some(Option.none()))
const asAlias: Option.Option<Peano> = two
export const back: Peano = asAlias
export const steps: Steps = Result.succeed(Result.fail("stop"))
const stepsAlias: Result.Result<Steps, string> = steps
export const stepsBack: Steps = stepsAlias
const exitAlias: Exit.Exit<E1, string> = Exit.fail("x")
export const exitBack: E1 = exitAlias
export const dict: Dict = { a: { b: {} } }
const dictAlias: Readonly<Record<string, Dict>> = dict
export const dictBack: Dict = dictAlias
