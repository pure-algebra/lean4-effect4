export const main: Effect.Effect<ReadonlyArray<number>, never, never> = Effect.flatMap(Effect.scoped(Effect.flatMap(Effect.acquireRelease(Ref.make(recordRequired<"v">("v")(recordValue<{ readonly v: ReadonlyArray<number> }>([10, [20], [[4, [[5, [3, "v"], [5, [1, false], [10, [8], [[10, [2], []]]]]]]]]], { v: nil() }))), (a0, a1) => Effect.succeed(undefined)), (a0) => Effect.suspend(() => {
  let a1: readonly [ReadonlyArray<number>, Option.Option<void>] = pair(nil(), none())
  return Effect.map(Effect.whileLoop({
    while: () => not(isSome(snd(a1))),
    body: () => Effect.flatMap(Effect.flatMap(Ref.modify(a0, (a2) => pair(a2, take(a2, 0))), (a2) => Effect.succeed(ite(isZero(length(a2)), pair("End", undefined), pair("Chunk", a2)))), (a2) => caseTag(a2, "End", (a3) => Effect.succeed(pair(fst(a1), some(a3))), (a3) => Effect.flatMap(Effect.succeed(append(fst(a1), snd(a3))), (a4) => Effect.succeed(pair(a4, none()))))),
    step: (a2) => {
      a1 = a2
    },
  }), () => a1)
}))), (a0) => Effect.succeed(fst(a0)))
