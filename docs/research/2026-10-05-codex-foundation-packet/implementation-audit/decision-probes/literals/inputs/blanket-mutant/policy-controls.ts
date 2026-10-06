import { Deferred, Effect, Ref } from "effect"
import { pair, tuple, fst, snd } from "./prelude-atoms.gen.ts"
import { recordValue, recordSet, caseTagR } from "./records.ts"
import { tupleAt } from "./tuples.ts"
type Equal<A,B> = (<T>()=>T extends A ? 1 : 2) extends (<T>()=>T extends B ? 1 : 2) ? true : false
type Assert<T extends true> = T

const scalarPair = pair(1,true)
type PrimitivePair = Assert<Equal<typeof scalarPair, readonly [number, boolean]>>
const scalarTuple = tuple(7,"Tag",true)
type PrimitiveTuple = Assert<Equal<typeof scalarTuple, readonly [number,"Tag",boolean]>>
const empty = tuple()
type EmptyTuple = Assert<Equal<typeof empty, readonly []>>
const nested = tuple(tuple(1,"Inner"),pair(true,"Tag"))
type NestedConstructors = Assert<Equal<typeof nested, readonly [readonly [number,"Inner"],readonly [boolean,"Tag"]]>>
const importedNested = tuple([1,true] as const)
type NoRecursiveRewrite = Assert<Equal<typeof importedNested, readonly [readonly [1,true]]>>
const list = [1,2] as const
const preservedList = tuple(list)
type ListIdentity = Assert<Equal<typeof preservedList, readonly [readonly [1,2]]>>
const variableString: string = "text"
const broadString = pair(variableString,1)
type BroadString = Assert<Equal<typeof broadString, readonly [string,number]>>
// @ts-expect-error numeric singleton precision intentionally widens
const noNumericSingleton: 1 = scalarPair[0]
// @ts-expect-error boolean singleton precision intentionally widens
const noBooleanSingleton: true = scalarPair[1]
// @ts-expect-error tuple remains readonly
scalarTuple[0] = 9
// @ts-expect-error tuple still has exactly three positions
scalarTuple[3]
// @ts-expect-error tuple projection still refuses a missing position
tupleAt<"3">("3")(scalarTuple)

const success = pair("Success",7)
const failure = pair("Failure","message")
type Tagged = typeof success | typeof failure
const byTag = (x: Tagged): number => {
  if (x[0] === "Success") { const payload: number = x[1]; return payload }
  const message: "message" = x[1]; return message.length
}
const record = recordValue<{readonly _tag:"Success";readonly value:number}>(null,{_tag:"Success",value:1})
const recordTuple = tuple(record)
type RecordTagKept = Assert<Equal<typeof recordTuple,readonly [{readonly _tag:"Success";readonly value:number}]>>
const retagged = recordSet<"_tag">("_tag")(record)("Failure")
const literalTag: "Failure" = retagged._tag
const recordBranch = (x: typeof record | {readonly _tag:"Failure";readonly reason:string}) =>
  caseTagR(x,"Success",r=>Effect.succeed(r.value),r=>Effect.succeed(r.reason.length))

// These handles must retain their exact invariant parameters.
declare const refOne: Ref.Ref<1>
declare const deferredTrue: Deferred.Deferred<true,"E">
const handles = tuple(refOne,deferredTrue)
type HandleIdentity = Assert<Equal<typeof handles,readonly [Ref.Ref<1>,Deferred.Deferred<true,"E">]>>
const handlePair = pair(refOne,deferredTrue)
type PairHandleIdentity = Assert<Equal<typeof handlePair,readonly [Ref.Ref<1>,Deferred.Deferred<true,"E">]>>
const sameRef: Ref.Ref<1> = fst(handlePair)
const sameDeferred: Deferred.Deferred<true,"E"> = snd(handlePair)
// @ts-expect-error invariant Ref parameter cannot widen through tuple
const widerRef: Ref.Ref<number> = handles[0]
// @ts-expect-error invariant Deferred payload cannot widen through tuple
const widerDeferred: Deferred.Deferred<boolean,"E"> = handles[1]
// @ts-expect-error invariant Deferred error cannot widen through tuple
const widerError: Deferred.Deferred<true,string> = handles[1]
Ref.set(handles[0],1)
// @ts-expect-error exact Ref payload refuses a different number
Ref.set(handles[0],2)
Deferred.succeed(handles[1],true)
// @ts-expect-error exact Deferred payload refuses false
Deferred.succeed(handles[1],false)

// The desired widening lets normal generated numeric and boolean cells evolve.
const numericCell = Effect.flatMap(Ref.make(tuple(0,false)),cell=>Ref.update(cell,()=>tuple(1,true)))
// Boolean tuple discriminants deliberately lose correlation; string tags above do not.
const booleanLeft = tuple(true,1)
const booleanRight = tuple(false,"text")
const noBooleanRefinement = (x: typeof booleanLeft | typeof booleanRight) => {
  if (x[0]) {
    // @ts-expect-error boolean is not a singleton discriminant after widening
    const n: number = x[1]
    return n
  }
  return 0
}
