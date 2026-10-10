/**
 * folds.typecheck.ts: the list fold and the three atoms of decisions rows 228 and 229 under the
 * one compiler. A finite compiler control, not a run: `check-truth` type-checks it beside the
 * printed modules. Each `@ts-expect-error` line is a red control that the compiler must refuse.
 *
 * The three printed images are Lean's own text, pinned by `Test/Program/FoldContract.lean`:
 * `total` is `pFold`'s term, `nested` is the truth program `pFold`'s (`harness/truth/Truth.lean`),
 * and `paired` is `pFoldNested`'s, whose outer fold states its accumulator's type.
 */
import type { Deferred, Option, Ref } from "effect"
import {
  add, append, cons, drop, fold, get, length, mapEntries, mapGet, mapKeys, mapSet, nil, sameHandle, sub, succ, take, tuple
} from "./prelude.ts"

// The image without a type argument: both parameters are inferred, and a numeric literal
// widens to `number`, as Lean's literal rule types it.
const total: number = fold(cons(1, cons(2, cons(3, nil()))), 10, (a0, a1) => sub(a0, a1))

// An outer capture and a fold inside a fold: the inner fold walks the captured list `a1` again,
// from the outer element `a3`, and its body reads the outer element.
const nested = (a0: number): number => {
  const a1 = cons(succ(a0), cons(a0, nil()))
  return fold(a1, a0, (a2, a3) => add(a2, fold(a1, a3, (a4, a5) => add(a4, sub(a5, a3)))))
}

// A stated accumulator type is the call's type argument. The accumulator starts as the empty
// list, whose type is `ReadonlyArray<never>`, and the body answers a wider list.
const paired = (a0: ReadonlyArray<ReadonlyArray<number>>): ReadonlyArray<readonly [number, number]> =>
  fold<ReadonlyArray<readonly [number, number]>>(a0, nil(), (a1, a2) => fold(a2, a1, (a3, a4) => append(a3, cons(tuple(a4, length(a2)), nil()))))

// @ts-expect-error A fold over a value that is no list.
fold(1, 0, (a0, a1) => a0)
// @ts-expect-error A body whose answer is no member of the accumulator's type.
fold(cons(1, nil()), 0, (a0, a1) => cons(a1, nil()))
// @ts-expect-error An initial value that is no member of the stated type.
fold<string>(cons(1, nil()), 0, (a0, a1) => a0)
// @ts-expect-error An accumulator that starts as the empty list needs its stated type.
fold(cons(1, nil()), nil(), (a0, a1) => append(a0, cons(a1, nil())))

// `take` and `drop` take the list first, as `get` does.
const firstTwo: ReadonlyArray<number> = take(cons(1, cons(2, cons(3, nil()))), 2)
const rest: ReadonlyArray<number> = drop(cons(1, cons(2, cons(3, nil()))), 2)
// @ts-expect-error The list is the first argument.
take(2, cons(1, nil()))

// `sameHandle` admits two `Ref` handles or two `Deferred` handles, at any payload types.
declare const cellA: Ref.Ref<number>
declare const cellB: Ref.Ref<string>
declare const promiseA: Deferred.Deferred<number, never>
declare const promiseB: Deferred.Deferred<string, number>
const sameCell: boolean = sameHandle(cellA, cellB)
const samePromise: boolean = sameHandle(promiseA, promiseB)
// @ts-expect-error Handles of two kinds are not compared.
sameHandle(cellA, promiseA)
// @ts-expect-error A number is no handle.
sameHandle(1, 1)

// ---- the join of two element types (decisions row 303) ----

// `cons` and `append` take a list at its whole type, so the compiler computes the join that
// Lean's match by bounds answers: the union of the two element types.
declare const numbers: ReadonlyArray<number>
declare const strings: ReadonlyArray<string>
const consJoined: ReadonlyArray<number | string> = cons(1, strings)
const appendJoined: ReadonlyArray<number | string> = append(numbers, strings)
// @ts-expect-error The answer of `cons` is no smaller than the join.
const consNoSmaller: ReadonlyArray<number> = cons(1, strings)
// @ts-expect-error The same at `append`.
const appendNoSmaller: ReadonlyArray<string> = append(numbers, strings)

// ---- an argument that is a proper union (decisions row 303) ----

// Lean's match by bounds reads a union argument member by member, and it answers the join of
// the members' element types. The compiler forms no union of two inference candidates, so each
// atom below takes its argument at its whole type and reads the element type by index.
declare const twoLists: ReadonlyArray<number> | ReadonlyArray<string>
declare const twoMaps: Readonly<Record<string, number>> | Readonly<Record<string, string>>
const takeJoined: ReadonlyArray<number | string> = take(twoLists, 1)
const dropJoined: ReadonlyArray<number | string> = drop(twoLists, 1)
const getJoined: Option.Option<number | string> = get(twoLists, 0)
const mapGetJoined: Option.Option<number | string> = mapGet(twoMaps, "k")
const mapKeysJoined: ReadonlyArray<string> = mapKeys(twoMaps)
const mapEntriesJoined: ReadonlyArray<readonly [string, number | string]> = mapEntries(twoMaps)
const mapSetJoined: Readonly<Record<string, number | string | boolean>> = mapSet(twoMaps, "k", true)
// @ts-expect-error The answer of `take` is no smaller than the join.
const takeNoSmaller: ReadonlyArray<number> = take(twoLists, 1)
// @ts-expect-error The same at `drop`.
const dropNoSmaller: ReadonlyArray<string> = drop(twoLists, 1)
// @ts-expect-error The same at `mapGet`.
const mapGetNoSmaller: Option.Option<number> = mapGet(twoMaps, "k")
// @ts-expect-error The same at `mapEntries`.
const mapEntriesNoSmaller: ReadonlyArray<readonly [string, number]> = mapEntries(twoMaps)
// @ts-expect-error The same at `mapSet`.
const mapSetNoSmaller: Readonly<Record<string, number | string>> = mapSet(twoMaps, "k", true)

void [
  total, nested, paired, firstTwo, rest, sameCell, samePromise, consJoined, appendJoined, consNoSmaller, appendNoSmaller,
  takeJoined, dropJoined, getJoined, mapGetJoined, mapKeysJoined, mapEntriesJoined, mapSetJoined,
  takeNoSmaller, dropNoSmaller, mapGetNoSmaller, mapEntriesNoSmaller, mapSetNoSmaller
]
