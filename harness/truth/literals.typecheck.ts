/**
 * literals.typecheck.ts: the literal rule of `pair` and `tuple` on the target, under the one
 * compiler (decisions row 256, inside DI-55's ruling). A finite compiler control, not a run:
 * `check-truth` type-checks it beside the printed modules. Each `@ts-expect-error` line is a red
 * control that the compiler must keep refusing.
 *
 * The rule. The two helpers widen a number or a Boolean type in an immediate slot to `number`
 * or `boolean` (`Wide`, `prelude-atoms.gen.ts`). A string literal keeps its literal type. Every
 * other argument keeps its type: no record, list, supplied tuple or handle is rewritten, and
 * nothing is recursive. The target then types those slots as Lean's literal rule does
 * (`litArgTy`, `src/Effect4/Program/Typing/Rules.lean`).
 *
 * The consequence, which the last section pins. A number or Boolean singleton type, or a brand,
 * in a direct slot is lost on the target. A Boolean tuple tag no longer discriminates. These
 * helpers preserve no arbitrary TypeScript refinement.
 *
 * The starting text is Codex's probe of 2026-10-06
 * (`docs/research/2026-10-05-codex-foundation-packet/implementation-audit/decision-probes/literals/inputs/revised/policy-controls.ts`):
 * its positive assertions and its thirteen refusals are all here.
 */
import { Deferred, Effect, Ref } from "effect"
import { fst, ite, pair, snd, tuple } from "./prelude-atoms.gen.ts"
import { caseTagR, recordSet, recordValue } from "./records.ts"
import { tupleAt } from "./tuples.ts"

/** Exact equality of two types: neither direction of assignability is enough for a pin. */
type Equal<A, B> = (<T>() => T extends A ? 1 : 2) extends (<T>() => T extends B ? 1 : 2) ? true : false
type Assert<T extends true> = T

// ---- the rule: a number or a Boolean in an immediate slot widens, a string literal stays ----

const scalarPair = pair(1, true)
type PrimitivePair = Assert<Equal<typeof scalarPair, readonly [number, boolean]>>
const scalarTuple = tuple(7, "Tag", true)
type PrimitiveTuple = Assert<Equal<typeof scalarTuple, readonly [number, "Tag", boolean]>>
const empty = tuple()
type EmptyTuple = Assert<Equal<typeof empty, readonly []>>
// A string variable stays `string`, as before.
const variableString: string = "text"
const broadString = pair(variableString, 1)
type BroadString = Assert<Equal<typeof broadString, readonly [string, number]>>

// The singleton is gone from a direct slot, through both helpers.
// @ts-expect-error The number literal's type is gone from `pair`'s slot.
const noNumericSingleton: 1 = scalarPair[0]
// @ts-expect-error The Boolean literal's type is gone from `pair`'s slot.
const noBooleanSingleton: true = scalarPair[1]
// @ts-expect-error The number literal's type is gone from `tuple`'s slot.
const noNumericSingletonInTuple: 7 = scalarTuple[0]
// @ts-expect-error The Boolean literal's type is gone from `tuple`'s slot.
const noBooleanSingletonInTuple: true = scalarTuple[2]

// What the repair is for: two arms that Lean types alike are one target type.
declare const flag: boolean
const choice = ite(flag, pair(true, 0), pair(false, 0))
type Choice = Assert<Equal<typeof choice, readonly [boolean, number]>>
// A cell made from literals holds numbers and Booleans, so a later value is a value of it.
const numericCell = Effect.flatMap(Ref.make(tuple(0, false)), (cell) => Ref.update(cell, () => tuple(1, true)))

// ---- what the rule keeps: the tuple's shape ----

// @ts-expect-error A tuple stays readonly.
scalarTuple[0] = 9
// @ts-expect-error A pair stays readonly.
scalarPair[0] = 2
// @ts-expect-error A tuple of three has exactly three positions.
scalarTuple[3]
// @ts-expect-error A pair has exactly two positions.
scalarPair[2]
// @ts-expect-error The tuple projection still refuses a missing position.
tupleAt<"3">("3")(scalarTuple)

// ---- what the rule keeps: a string tag ----

const success = pair("Success", 7)
const failure = pair("Failure", "message")
type SuccessPair = Assert<Equal<typeof success, readonly ["Success", number]>>
type FailurePair = Assert<Equal<typeof failure, readonly ["Failure", "message"]>>
type Tagged = typeof success | typeof failure
// The string tag still discriminates: each arm reads its own payload. Under a helper that
// widened a string too, the compiler refuses both reads (the mutant's control).
const byTag = (x: Tagged): number => {
  if (x[0] === "Success") {
    const payload: number = x[1]
    return payload
  }
  const message: "message" = x[1]
  return message.length
}
// @ts-expect-error A string tag keeps its literal type: `"Success"` is no `"Failure"`.
const otherTag: "Failure" = success[0]
const stringTuple = tuple("Tag", "x")
type StringTuple = Assert<Equal<typeof stringTuple, readonly ["Tag", "x"]>>
// A record's tag is not a slot of the helper: the record keeps its type.
const record = recordValue<{ readonly _tag: "Success"; readonly value: number }>(null, { _tag: "Success", value: 1 })
const recordTuple = tuple(record)
type RecordTagKept = Assert<Equal<typeof recordTuple, readonly [{ readonly _tag: "Success"; readonly value: number }]>>
const retagged = recordSet<"_tag">("_tag")(record)("Failure")
const literalTag: "Failure" = retagged._tag
const recordBranch = (x: typeof record | { readonly _tag: "Failure"; readonly reason: string }) =>
  caseTagR(x, "Success", (r) => Effect.succeed(r.value), (r) => Effect.succeed(r.reason.length))

// ---- what the rule keeps: every argument that is no number and no Boolean ----

// Each constructor widens its own slots, and a constructor's result is no number.
const nested = tuple(tuple(1, "Inner"), pair(true, "Tag"))
type NestedConstructors = Assert<Equal<typeof nested, readonly [readonly [number, "Inner"], readonly [boolean, "Tag"]]>>
// No recursive rewrite: a supplied tuple and a supplied list keep their types.
const supplied = tuple([1, true] as const)
type NoRecursiveRewrite = Assert<Equal<typeof supplied, readonly [readonly [1, true]]>>
const list = [1, 2] as const
const suppliedList = tuple(list)
type ListIdentity = Assert<Equal<typeof suppliedList, readonly [readonly [1, 2]]>>
const suppliedInPair = pair([1, true] as const, { n: 1 } as const)
type NoRewriteInPair = Assert<Equal<typeof suppliedInPair, readonly [readonly [1, true], { readonly n: 1 }]>>

// A handle keeps its exact, invariant parameters through both helpers.
declare const refOne: Ref.Ref<1>
declare const deferredTrue: Deferred.Deferred<true, "E">
const handles = tuple(refOne, deferredTrue)
type HandleIdentity = Assert<Equal<typeof handles, readonly [Ref.Ref<1>, Deferred.Deferred<true, "E">]>>
const handlePair = pair(refOne, deferredTrue)
type PairHandleIdentity = Assert<Equal<typeof handlePair, readonly [Ref.Ref<1>, Deferred.Deferred<true, "E">]>>
const sameRef: Ref.Ref<1> = fst(handlePair)
const sameDeferred: Deferred.Deferred<true, "E"> = snd(handlePair)
// @ts-expect-error An invariant `Ref` parameter does not widen through `tuple`.
const widerRef: Ref.Ref<number> = handles[0]
// @ts-expect-error An invariant `Deferred` value parameter does not widen through `tuple`.
const widerDeferred: Deferred.Deferred<boolean, "E"> = handles[1]
// @ts-expect-error An invariant `Deferred` error parameter does not widen through `tuple`.
const widerError: Deferred.Deferred<true, string> = handles[1]
// @ts-expect-error An invariant `Ref` parameter does not widen through `pair`.
const widerRefOfPair: Ref.Ref<number> = fst(handlePair)
// @ts-expect-error An invariant `Deferred` value parameter does not widen through `pair`.
const widerDeferredOfPair: Deferred.Deferred<boolean, "E"> = snd(handlePair)
Ref.set(handles[0], 1)
// @ts-expect-error The exact `Ref` refuses another number.
Ref.set(handles[0], 2)
// @ts-expect-error The same through `pair`.
Ref.set(fst(handlePair), 2)
Deferred.succeed(handles[1], true)
// @ts-expect-error The exact `Deferred` refuses `false`.
Deferred.succeed(handles[1], false)
// @ts-expect-error The same through `pair`.
Deferred.succeed(snd(handlePair), false)

// ---- the consequence: what a direct slot loses ----

// A Boolean tuple tag no longer discriminates. A string tag does (`byTag`, above).
const booleanLeft = tuple(true, 1)
const booleanRight = tuple(false, "text")
const noBooleanRefinement = (x: typeof booleanLeft | typeof booleanRight) => {
  if (x[0]) {
    // @ts-expect-error A Boolean in a direct slot is no singleton discriminant.
    const n: number = x[1]
    return n
  }
  return 0
}
// The rule is on the slot's type, not on a literal expression: a number or Boolean brand in a
// direct slot is lost. A brand inside a supplied record stays.
declare const brandedNumber: number & { readonly __brand: "Meters" }
declare const brandedBoolean: boolean & { readonly __brand: "Flag" }
const branded = tuple(brandedNumber, brandedBoolean)
type NumericBrandErased = Assert<Equal<(typeof branded)[0], number>>
type BooleanBrandErased = Assert<Equal<(typeof branded)[1], boolean>>
// @ts-expect-error A number brand in a direct slot is lost.
const noNumericBrand: typeof brandedNumber = branded[0]
// @ts-expect-error A Boolean brand in a direct slot is lost.
const noBooleanBrand: typeof brandedBoolean = branded[1]
const recordWithBrand = tuple({ value: brandedNumber } as const)
type NestedBrandKept = Assert<Equal<(typeof recordWithBrand)[0]["value"], typeof brandedNumber>>

void [
  noNumericSingleton, noBooleanSingleton, noNumericSingletonInTuple, noBooleanSingletonInTuple, choice, numericCell,
  byTag, otherTag, stringTuple, literalTag, recordBranch, nested, supplied, suppliedList, suppliedInPair,
  sameRef, sameDeferred, widerRef, widerDeferred, widerError, widerRefOfPair, widerDeferredOfPair,
  noBooleanRefinement, noNumericBrand, noBooleanBrand, recordWithBrand, broadString, empty,
]
export type {
  PrimitivePair, PrimitiveTuple, EmptyTuple, BroadString, Choice, SuccessPair, FailurePair, StringTuple, RecordTagKept,
  NestedConstructors, NoRecursiveRewrite, ListIdentity, NoRewriteInPair, HandleIdentity, PairHandleIdentity,
  NumericBrandErased, BooleanBrandErased, NestedBrandKept,
}

// ---- finite blocker: normalized binary products and downstream result inference ----
// These proposed types do not change the generated helper. Boolean stays one widened arm.
type ProbeTail<A, B> = (boolean extends B ? readonly [A, boolean] : never)
  | (B extends boolean ? never : B extends unknown ? readonly [A, B] : never)
type ProbeMembers<A, B> = (boolean extends A ? ProbeTail<boolean, B> : never)
  | (A extends boolean ? never : A extends unknown ? ProbeTail<A, B> : never)
type ProbeProduct<A, B> = ProbeMembers<PreviousWide<A>, PreviousWide<B>>
type PreviousWide<T> = T extends number ? number : T extends boolean ? boolean : T
type ProbePointwise<A extends readonly unknown[]> = { readonly [I in keyof A]: PreviousWide<A[I]> }
type ProbeTuple<A extends readonly unknown[]> = A extends readonly [infer X, infer Y] ? ProbeProduct<X, Y> : ProbePointwise<A>
declare const proposedTuple: <const A extends readonly unknown[]>(...items: A) => ProbeTuple<A>
declare const proposedPair: <const A, const B>(a: A, b: B) => ProbeProduct<A, B>
type PullEnd = readonly ["End", void]
type PullChunk = readonly ["Chunk", ReadonlyArray<number>]
type Pull = PullEnd | PullChunk
type PullProduct = readonly [PullEnd, PullEnd] | readonly [PullEnd, PullChunk]
  | readonly [PullChunk, PullEnd] | readonly [PullChunk, PullChunk]
declare const firstPull: Pull
declare const secondPull: Pull
// @ts-expect-error The current tuple helper cannot serve the normalized result annotation.
const currentTupleRefused: PullProduct = tuple(firstPull, secondPull)
// @ts-expect-error The current pair helper has the same annotation limitation.
const currentPairRefused: PullProduct = pair(firstPull, secondPull)
const proposedPullTuple = proposedTuple(firstPull, secondPull)
const proposedPullPair = proposedPair(firstPull, secondPull)
type ProposedTupleProduct = Assert<Equal<typeof proposedPullTuple, PullProduct>>
type ProposedPairProduct = Assert<Equal<typeof proposedPullPair, PullProduct>>
const allPullCombinations: readonly PullProduct[] = [
  proposedTuple(proposedTuple("End", undefined), proposedTuple("End", undefined)),
  proposedTuple(proposedTuple("End", undefined), proposedTuple("Chunk", [1, 2])),
  proposedTuple(proposedTuple("Chunk", [1, 2]), proposedTuple("End", undefined)),
  proposedTuple(proposedTuple("Chunk", [1, 2]), proposedTuple("Chunk", [3])),
]
// @ts-expect-error Distribution cannot invent an End payload.
const wrongEnd: PullProduct = proposedTuple(proposedTuple("End", [1]), proposedTuple("End", undefined))
// @ts-expect-error Distribution cannot erase a Chunk payload.
const wrongChunk: PullProduct = proposedPair(proposedTuple("Chunk", undefined), proposedTuple("End", undefined))
// @ts-expect-error Distribution cannot invent a tag.
const wrongTag: PullProduct = proposedTuple(proposedTuple("Missing", undefined), firstPull)
// @ts-expect-error The normalized result remains readonly.
proposedPullTuple[0] = proposedTuple("End", undefined)
const proposedEmpty = proposedTuple()
const proposedSingle = proposedTuple(firstPull)
const proposedThree = proposedTuple(firstPull, secondPull, firstPull)
type ProposedEmpty = Assert<Equal<typeof proposedEmpty, readonly []>>
type ProposedSingle = Assert<Equal<typeof proposedSingle, readonly [Pull]>>
type ProposedThree = Assert<Equal<typeof proposedThree, readonly [Pull, Pull, Pull]>>
const proposedBooleans = proposedTuple(flag, flag)
type ProposedBooleans = Assert<Equal<typeof proposedBooleans, readonly [boolean, boolean]>>
declare const booleanOrTag: boolean | "Flag"
const proposedMixed = proposedTuple(booleanOrTag, 1)
type ProposedMixed = Assert<Equal<typeof proposedMixed, readonly [boolean, number] | readonly ["Flag", number]>>
// @ts-expect-error Direct numeric literals still widen.
const proposedLiteralRefused: readonly [boolean, 1] | readonly ["Flag", 1] = proposedMixed
const proposedNested = <T>(a: ReadonlyArray<T> | readonly ["Box", T], b: Pull):
  readonly [ReadonlyArray<T>, PullEnd] | readonly [ReadonlyArray<T>, PullChunk]
  | readonly [readonly ["Box", T], PullEnd] | readonly [readonly ["Box", T], PullChunk] => proposedTuple(a, b)
const proposedGenericBoolean = <T>(a: boolean, b: ReadonlyArray<T> | readonly ["Box", T]):
  readonly [boolean, ReadonlyArray<T>] | readonly [boolean, readonly ["Box", T]] => proposedTuple(a, b)
declare const nestedNumbers: ReadonlyArray<number> | readonly ["Box", number]
// @ts-expect-error Supplied nested payloads retain their element type.
const proposedNestedRefused: readonly [ReadonlyArray<string> | readonly ["Box", string], Pull] = proposedNested(nestedNumbers, firstPull)

// The existing callback compiles. Every distributed proposal below regresses its result inference.
import { Option } from "effect"
declare const numericRef: Ref.Ref<number>
declare const optionAnswer: Option.Option<number>
const currentPairInference = Ref.modify(numericRef, state => pair(optionAnswer, state))
const currentTupleInference = Ref.modify(numericRef, state => tuple(optionAnswer, state))
// @ts-expect-error A distributed pair makes Ref.modify infer None and reject Some.
const proposedPairInferenceRefused = Ref.modify(numericRef, state => proposedPair(optionAnswer, state))
// @ts-expect-error A distributed tuple makes Ref.modify infer None and reject Some.
const proposedTupleInferenceRefused = Ref.modify(numericRef, state => proposedTuple(optionAnswer, state))
declare const forwardIntersection: <const A extends readonly unknown[]>(...items: A) => ProbeTuple<A> & ProbePointwise<A>
declare const reverseIntersection: <const A extends readonly unknown[]>(...items: A) => ProbePointwise<A> & ProbeTuple<A>
declare const noInferenceResult: <const A extends readonly unknown[]>(...items: A) => NoInfer<ProbeTuple<A>>
const forwardAnnotation: PullProduct = forwardIntersection(firstPull, secondPull)
const reverseAnnotation: PullProduct = reverseIntersection(firstPull, secondPull)
// @ts-expect-error Adding the pointwise tuple after the product does not repair inference.
const forwardInferenceRefused = Ref.modify(numericRef, state => forwardIntersection(optionAnswer, state))
// @ts-expect-error Adding the pointwise tuple before the product does not repair inference.
const reverseInferenceRefused = Ref.modify(numericRef, state => reverseIntersection(optionAnswer, state))
// @ts-expect-error NoInfer on the result does not repair this downstream inference.
const noInferenceRefused = Ref.modify(numericRef, state => noInferenceResult(optionAnswer, state))
declare function pointwiseFirst<const A extends readonly unknown[]>(...items: A): ProbePointwise<A>
declare function pointwiseFirst<const A, const B>(a: A, b: B): ProbeProduct<A, B>
declare function distributedFirst<const A, const B>(a: A, b: B): ProbeProduct<A, B>
declare function distributedFirst<const A extends readonly unknown[]>(...items: A): ProbePointwise<A>
const pointwiseOverloadInference = Ref.modify(numericRef, state => pointwiseFirst(optionAnswer, state))
const distributedOverloadAnnotation: PullProduct = distributedFirst(firstPull, secondPull)
// @ts-expect-error Pointwise-first overloads retain the normalized annotation failure.
const pointwiseOverloadAnnotationRefused: PullProduct = pointwiseFirst(firstPull, secondPull)
// @ts-expect-error Distributed-first overloads retain the downstream inference failure.
const distributedOverloadInferenceRefused = Ref.modify(numericRef, state => distributedFirst(optionAnswer, state))
void [currentTupleRefused, currentPairRefused, allPullCombinations, wrongEnd, wrongChunk, wrongTag,
  proposedLiteralRefused, proposedNestedRefused, proposedGenericBoolean, currentPairInference,
  currentTupleInference, proposedPairInferenceRefused, proposedTupleInferenceRefused, forwardAnnotation,
  reverseAnnotation, forwardInferenceRefused, reverseInferenceRefused, noInferenceRefused,
  pointwiseOverloadInference, distributedOverloadAnnotation, pointwiseOverloadAnnotationRefused,
  distributedOverloadInferenceRefused]
export type { ProposedTupleProduct, ProposedPairProduct, ProposedEmpty, ProposedSingle, ProposedThree,
  ProposedBooleans, ProposedMixed }
