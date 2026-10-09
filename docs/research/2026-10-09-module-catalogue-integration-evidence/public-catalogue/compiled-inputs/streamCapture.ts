import { Cause, Context, Data, Deferred, Effect, Exit, Fiber, Layer, Option, Ref, Scope, pipe } from "effect"
import { ProfileRefusal, add, and, append, caseTag, caseTagR, causeError, causeIsDie, causeIsFail, causeIsInterrupt, concat, cons, div, drop, eq, fold, fst, get, getOrElse, isSome, isZero, ite, length, lt, mapEmpty, mapEntries, mapFromEntries, mapGet, mapKeys, mapSet, minus, mod, mul, nil, none, not, optionCase, or, pair, plus, pred, recordOptional, recordRequired, recordSet, recordValue, sameHandle, snd, some, strings, sub, succ, tagIs, take, tuple, tupleAt } from "./prelude.ts"
export const main: Effect.Effect<readonly [ReadonlyArray<number>, ReadonlyArray<number>], never, never> = Effect.flatMap(Effect.succeed(append(cons(1, nil()), append(cons(2, nil()), cons(3, nil())))), (a0) => Effect.flatMap(Effect.flatMap(Effect.scoped(Effect.flatMap(Effect.acquireRelease(Ref.make(recordRequired<"v">("v")(recordValue<{ readonly v: ReadonlyArray<number> }>([10, [20], [[4, [[5, [3, "v"], [5, [1, false], [10, [8], [[10, [2], []]]]]]]]]], { v: a0 }))), (a1, a2) => Effect.succeed(undefined)), (a1) => Effect.suspend(() => {
  let a2: readonly [ReadonlyArray<number>, Option.Option<void>] = pair(nil(), none())
  return Effect.map(Effect.whileLoop({
    while: () => not(isSome(snd(a2))),
    body: () => Effect.flatMap(Effect.flatMap(Ref.modify(a1, (a3) => pair(a3, take(a3, 0))), (a3) => Effect.succeed(ite(isZero(length(a3)), pair("End", undefined), pair("Chunk", a3)))), (a3) => caseTag(a3, "End", (a4) => Effect.succeed(pair(fst(a2), some(a4))), (a4) => Effect.flatMap(Effect.succeed(append(fst(a2), snd(a4))), (a5) => Effect.succeed(pair(a5, none()))))),
    step: (a3) => {
      a2 = a3
    },
  }), () => a2)
}))), (a1) => Effect.succeed(fst(a1))), (a1) => Effect.succeed(tuple(a1, a0))))
