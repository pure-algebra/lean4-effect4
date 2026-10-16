// expect: none
// The exact texts that lean4-typescript v0.8.0's tests render (`TypeScriptTest/TypeAlias.lean`),
// compiled under the printed modules' options.
import { Option, Result, Schema } from "effect"
export type UserId = number
type LocalUserId = number
/** A user's identity.
 * Never reused. */
export type DocumentedUserId = number
export type Tree = { readonly value: number; readonly children: ReadonlyArray<Tree> }
export const Tree = Schema.Struct({ value: Schema.Number, children: Schema.Array(Schema.suspend((): Schema.Codec<Tree> => Tree)) })
export type Expr = { readonly _tag: "Lit"; readonly value: number } | { readonly _tag: "Add"; readonly left: Expr; readonly right: Expr }
export type Peano = Option.None<Peano> | Option.Some<Peano>
export type Dict = { readonly [key: string]: Dict }
export type Nested = { readonly [key: string]: { readonly [key: string]: number } } | null
export type Box<out A> = { readonly value: A }
export type List<A, out E> = { readonly head: A; readonly tail: Result.Result<readonly [A, List<A, E>], E> }
export const local: LocalUserId = 1
