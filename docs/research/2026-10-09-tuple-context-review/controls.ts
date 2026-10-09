import { Option, Ref, Effect } from "effect"
type Wide<T> = T extends number ? number : T extends boolean ? boolean : T
type Pointwise<A extends readonly unknown[]> = {readonly [I in keyof A]: Wide<A[I]>}
type Product<A,B> = A extends unknown ? B extends unknown ? readonly [Wide<A>,Wide<B>] : never : never
type ProductTuple<A extends readonly unknown[]> = A extends readonly [infer X,infer Y] ? Product<X,Y> : Pointwise<A>
type End = readonly ["End",void]
type Chunk = readonly ["Chunk",ReadonlyArray<number>]
type Pull = End | Chunk
type Target = readonly [End,End] | readonly [End,Chunk] | readonly [Chunk,End] | readonly [Chunk,Chunk]
declare const cell: Ref.Ref<number>
declare const answer: Option.Option<number>
declare const a: Pull
 declare const b: Pull
// The correct union value already exists; no generic tuple helper participates.
declare const fixedProduct: readonly [Option.None<number>, number] | readonly [Option.Some<number>, number]
const fixedModify = Ref.modify(cell, state => fixedProduct)
const explicitModify = Ref.modify<number,Option.Option<number>>(cell, state => fixedProduct)
const annotatedCallback = Ref.modify(cell, (state): readonly [Option.Option<number>,number] => fixedProduct)
declare function mapped<const A extends readonly unknown[]>(...items: A): Pointwise<A>
declare function distributed<const A extends readonly unknown[]>(...items: A): ProductTuple<A>
declare function aliasResult<const A extends readonly unknown[], R extends readonly unknown[] = Pointwise<A>>(...items: A): ProductTuple<R>
declare function aliasIntersection<const A extends readonly unknown[], R extends readonly unknown[] = Pointwise<A>>(...items: A): R & ProductTuple<R>
declare function contextual<const A extends readonly unknown[], R extends readonly unknown[] = Pointwise<A>>(...items: A & R): ProductTuple<R>
declare function contextualReturn<const A extends readonly unknown[], R extends readonly unknown[] = Pointwise<A>>(...items: A): R & ProductTuple<A>
declare function deferred<const A extends readonly unknown[]>(...items: A): ProductTuple<Pointwise<A>>
const mappedModify = Ref.modify(cell, state => mapped(answer,state))
const mappedTarget: Target = mapped(a,b)
const distributedModify = Ref.modify(cell, state => distributed(answer,state))
const distributedTarget: Target = distributed(a,b)
const aliasModify = Ref.modify(cell, state => aliasResult(answer,state))
const aliasTarget: Target = aliasResult(a,b)
const intersectionModify = Ref.modify(cell, state => aliasIntersection(answer,state))
const intersectionTarget: Target = aliasIntersection(a,b)
const contextualModify = Ref.modify(cell, state => contextual(answer,state))
const contextualTarget: Target = contextual(a,b)
const contextualReturnModify = Ref.modify(cell, state => contextualReturn(answer,state))
const contextualReturnTarget: Target = contextualReturn(a,b)
const deferredModify = Ref.modify(cell, state => deferred(answer,state))
const deferredTarget: Target = deferred(a,b)
const explicitHelperArguments = Ref.modify(cell,state => distributed<readonly [Option.Option<number>,number]>(answer,state))
const resultPin: Effect.Effect<Option.Option<number>> = explicitModify
const callbackPin: Effect.Effect<Option.Option<number>> = annotatedCallback

const aliasNarrowPin: Effect.Effect<Option.None<number>> = aliasModify
const intersectionNarrowPin: Effect.Effect<Option.None<number>> = intersectionModify
// These disconnected return parameters can claim an unrelated payload type.
const forgedAlias: readonly [string, boolean] = aliasResult(1,2)
const forgedIntersection: readonly [string, boolean] = aliasIntersection(1,2)
