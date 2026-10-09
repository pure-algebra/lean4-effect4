import { Effect, Option, Ref } from "effect"
type Wide<T> = T extends number ? number : T extends boolean ? boolean : T
type Pointwise<A extends readonly unknown[]> = {readonly [I in keyof A]: Wide<A[I]>}
type Product<A,B> = A extends unknown ? B extends unknown ? readonly [Wide<A>,Wide<B>] : never : never
type ProductTuple<A extends readonly unknown[]> = A extends readonly [infer X,infer Y] ? Product<X,Y> : Pointwise<A>
declare const cell: Ref.Ref<number>
declare const fixedProduct: readonly [Option.None<number>,number] | readonly [Option.Some<number>,number]
// @ts-expect-error The correctly typed union callback result still defeats contextual B inference.
const fixed = Ref.modify(cell,state => fixedProduct)
const explicit = Ref.modify<number,Option.Option<number>>(cell,state => fixedProduct)
const annotated = Ref.modify(cell,(state): readonly [Option.Option<number>,number] => fixedProduct)
const explicitPin: Effect.Effect<Option.Option<number>> = explicit
const annotatedPin: Effect.Effect<Option.Option<number>> = annotated
declare function unsafeAlias<const A extends readonly unknown[], R extends readonly unknown[] = Pointwise<A>>(...items:A): ProductTuple<R>
// A disconnected generic return can accept a false result type. This is a rejected candidate.
const forged: readonly [string,boolean] = unsafeAlias(1,2)
declare const answer: Option.Option<number>
const lost = Ref.modify(cell,state => unsafeAlias(answer,state))
// @ts-expect-error The apparently accepted modify result loses its Option answer type.
const exactPin: Effect.Effect<Option.Option<number>> = lost
