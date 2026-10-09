export const e4$arrays$openArray = (a0: ReadonlyArray<number>): Effect.Effect<Ref.Ref<ReadonlyArray<number>>, never, never> => Effect.suspend(() => Ref.make(recordRequired<"v">("v")(recordValue<{ readonly v: ReadonlyArray<number> }>([10, [20], [[4, [[5, [3, "v"], [5, [1, false], [10, [8], [[10, [2], []]]]]]]]]], { v: a0 }))))
export const e4$arrays$pull = (a0: Ref.Ref<ReadonlyArray<number>>): Effect.Effect<readonly ["End", void] | readonly ["Chunk", ReadonlyArray<number>], never, never> => Effect.suspend(() => Effect.flatMap(Ref.modify(a0, (a1) => pair(a1, take(a1, 0))), (a1) => Effect.succeed(ite(isZero(length(a1)), pair("End", undefined), pair("Chunk", a1)))))
export const e4$arrays$close = (a0: Ref.Ref<ReadonlyArray<number>>): Effect.Effect<void, never, never> => Effect.suspend(() => Effect.succeed(undefined))
export const main: Effect.Effect<ReadonlyArray<number>, never, never> = Effect.flatMap(Effect.scoped(Effect.flatMap(Effect.acquireRelease(e4$arrays$openArray(append(cons(1, nil()), append(cons(2, nil()), cons(3, nil())))), (a0, a1) => e4$arrays$close(a0)), (a0) => Effect.suspend(() => {
  let a1: readonly [ReadonlyArray<number>, Option.Option<void>] = pair(nil(), none())
  return Effect.map(Effect.whileLoop({
    while: () => not(isSome(snd(a1))),
    body: () => Effect.flatMap(e4$arrays$pull(a0), (a2) => caseTag(a2, "End", (a3) => Effect.succeed(pair(fst(a1), some(a3))), (a3) => Effect.flatMap(Effect.succeed(append(fst(a1), snd(a3))), (a4) => Effect.succeed(pair(a4, none()))))),
    step: (a2) => {
      a1 = a2
    },
  }), () => a1)
}))), (a0) => Effect.succeed(fst(a0)))
