/**
 * folds.typecheck.ts: the list fold and the three atoms of decisions rows 228 and 229 under the
 * one compiler. A finite compiler control, not a run: `check-truth` type-checks it beside the
 * printed modules. Each `@ts-expect-error` line is a red control that the compiler must refuse.
 *
 * The three printed images are Lean's own text, pinned by `Test/Program/FoldContract.lean`:
 * `total` is `pFold`'s term, `nested` is the truth program `pFold`'s (`harness/truth/Truth.lean`),
 * and `paired` is `pFoldNested`'s, whose outer fold states its accumulator's type.
 */
import type { Deferred, Ref } from "effect"
import { add, append, cons, drop, fold, length, nil, sameHandle, sub, succ, take, tuple } from "./prelude.ts"

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

void [total, nested, paired, firstTwo, rest, sameCell, samePromise]
