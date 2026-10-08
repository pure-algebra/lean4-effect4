import { Cause, Context, Data, Deferred, Effect, Exit, Fiber, Layer, Option, Ref, Scope, pipe } from "effect"
import { succ, pred, isZero, not, add, lt, eq, pair, fst, snd, strings, causeIsFail, causeError, causeIsDie, causeIsInterrupt, or, and, tagIs, isSome, getOrElse, ite, some, none, mul, nil, cons, get, length, append, sub, div, mod, concat, mapEmpty, mapGet, mapSet, mapKeys, mapEntries, mapFromEntries, tuple, take, drop, sameHandle, plus, minus, Host, L, Sql, Kv, recordValue, recordRequired, recordOptional, recordSet, tupleAt, fold, optionCase, caseTag, caseTagR, type MaskRestore } from "../prelude.ts"

export const optionJoined = (a0: Option.Option<number> | Option.Option<string>) => optionCase<number | string, number, never, never, number | string, never, never>(a0, () => Effect.succeed(0), (a1) => Effect.succeed(a1))


export const optionSingle = (a0: Option.Option<number>) => optionCase(a0, () => Effect.succeed(0), (a1) => Effect.succeed(a1))


export const foldInferredJoined = (a0: ReadonlyArray<number> | ReadonlyArray<string>, a1: number | string) => Effect.succeed(fold(a0, a1, (a2: number | string, a3: number | string) => a3))


export const foldInferredSingle = (a0: ReadonlyArray<number>, a1: number) => Effect.succeed(fold(a0, a1, (a2, a3) => a3))


export const foldStoredJoined = (a0: ReadonlyArray<number> | ReadonlyArray<string>, a1: number | string) => Effect.succeed(fold<number | string, number | string>(a0, a1, (a2: number | string, a3) => a3))


export const foldStoredSingle = (a0: ReadonlyArray<number>, a1: number) => Effect.succeed(fold<number>(a0, a1, (a2, a3) => a3))


export const fiberJoinJoined = (a0: Fiber.Fiber<number, never> | Fiber.Fiber<string, boolean>) => Fiber.join<number | string, boolean>(a0)


export const fiberJoinSingle = (a0: Fiber.Fiber<number, never>) => Fiber.join(a0)


export const fiberAwaitJoined = (a0: Fiber.Fiber<number, never> | Fiber.Fiber<string, boolean>) => Fiber.await<number | string, boolean>(a0)


export const fiberAwaitSingle = (a0: Fiber.Fiber<number, never>) => Fiber.await(a0)


export const fiberInterruptJoined = (a0: Fiber.Fiber<number, never> | Fiber.Fiber<string, boolean>) => Fiber.interrupt<number | string, boolean>(a0)


export const fiberInterruptSingle = (a0: Fiber.Fiber<number, never>) => Fiber.interrupt(a0)


export const fiberRunInJoined = (a0: Fiber.Fiber<number, never> | Fiber.Fiber<string, boolean>, a1: Scope.Scope) => Effect.withFiber(() => {
  Fiber.runIn<number | string, boolean>(a0, a1)
  return Effect.void
})


export const fiberRunInSingle = (a0: Fiber.Fiber<number, never>, a1: Scope.Scope) => Effect.withFiber(() => {
  Fiber.runIn(a0, a1)
  return Effect.void
})


export const fiberInterruptAllJoined = (a0: ReadonlyArray<Fiber.Fiber<number, never>> | ReadonlyArray<Fiber.Fiber<string, boolean>>) => Fiber.interruptAll<ReadonlyArray<Fiber.Fiber<number, never>> | ReadonlyArray<Fiber.Fiber<string, boolean>>>(a0)


export const fiberInterruptAllSingle = (a0: ReadonlyArray<Fiber.Fiber<number, never>>) => Fiber.interruptAll(a0)


export const fiberInterruptAllAsJoined = (a0: ReadonlyArray<Fiber.Fiber<number, never>> | ReadonlyArray<Fiber.Fiber<string, boolean>>) => Fiber.interruptAllAs<ReadonlyArray<Fiber.Fiber<number, never>> | ReadonlyArray<Fiber.Fiber<string, boolean>>>(a0, 7)


export const fiberInterruptAllAsSingle = (a0: ReadonlyArray<Fiber.Fiber<number, never>>) => Fiber.interruptAllAs(a0, 7)


export const fiberAwaitAllFirstJoined = (a0: ReadonlyArray<Fiber.Fiber<number, never>> | ReadonlyArray<Fiber.Fiber<string, boolean>>) => Effect.flatMap(Fiber.awaitAll<Fiber.Fiber<number | string, boolean>>(a0), (a1) => Effect.succeed(get(a1, 0)))


export const fiberAwaitAllFirstSingle = (a0: ReadonlyArray<Fiber.Fiber<number, never>>) => Effect.flatMap(Fiber.awaitAll(a0), (a1) => Effect.succeed(get(a1, 0)))


export const forkChildJoined = (a0: number | string) => Effect.forkChild<Effect.Effect<number | string, never, never>>(Effect.succeed(a0), { startImmediately: true, uninterruptible: "inherit" })


export const forkChildSingle = (a0: number) => Effect.forkChild(Effect.succeed(a0), { startImmediately: true, uninterruptible: "inherit" })


export const forkDetachJoined = (a0: number | string) => Effect.forkDetach<Effect.Effect<number | string, never, never>>(Effect.succeed(a0), { startImmediately: true, uninterruptible: "inherit" })


export const forkDetachSingle = (a0: number) => Effect.forkDetach(Effect.succeed(a0), { startImmediately: true, uninterruptible: "inherit" })


export const forkScopedJoined = (a0: number | string) => Effect.forkScoped<Effect.Effect<number | string, never, never>>(Effect.succeed(a0), { startImmediately: true, uninterruptible: "inherit" })


export const forkScopedSingle = (a0: number) => Effect.forkScoped(Effect.succeed(a0), { startImmediately: true, uninterruptible: "inherit" })


export const forkInJoined = (a0: number | string, a1: Scope.Scope) => Effect.forkIn<number | string, never, never>(Effect.succeed(a0), a1, { startImmediately: true, uninterruptible: "inherit" })


export const forkInSingle = (a0: number, a1: Scope.Scope) => Effect.forkIn(Effect.succeed(a0), a1, { startImmediately: true, uninterruptible: "inherit" })


export const scopeCloseJoined = (a0: Scope.Scope, a1: Exit.Exit<number, never> | Exit.Exit<string, boolean>) => Scope.close<number | string, boolean>(a0, a1)


export const scopeCloseSingle = (a0: Scope.Scope, a1: Exit.Exit<number, never>) => Scope.close(a0, a1)


export const scopedJoined = (a0: number | string) => Effect.scoped<number | string, never, Scope.Scope>(Effect.flatMap(Effect.service(Scope.Scope), (a1) => Effect.succeed(a0)))


export const scopedSingle = (a0: number) => Effect.scoped(Effect.flatMap(Effect.service(Scope.Scope), (a1) => Effect.succeed(a0)))


export const acquireReleaseJoined = (a0: number | string) => Effect.acquireRelease<number | string, never, never, never>(Effect.succeed(a0), (a1, a2) => Effect.succeed(undefined))


export const acquireReleaseSingle = (a0: number) => Effect.acquireRelease(Effect.succeed(a0), (a1, a2) => Effect.succeed(undefined))


export const causeIsFailJoined = (a0: Exit.Exit<void, string> | Cause.Cause<number>) => Effect.succeed(causeIsFail<unknown, number | string>(a0))


export const causeIsFailSingle = (a0: Cause.Cause<number>) => Effect.succeed(causeIsFail(a0))


export const causeIsDieJoined = (a0: Exit.Exit<void, string> | Cause.Cause<number>) => Effect.succeed(causeIsDie<unknown, number | string>(a0))


export const causeIsDieSingle = (a0: Cause.Cause<number>) => Effect.succeed(causeIsDie(a0))


export const causeIsInterruptJoined = (a0: Exit.Exit<void, string> | Cause.Cause<number>) => Effect.succeed(causeIsInterrupt<unknown, number | string>(a0))


export const causeIsInterruptSingle = (a0: Cause.Cause<number>) => Effect.succeed(causeIsInterrupt(a0))


export const causeErrorJoined = (a0: Exit.Exit<void, string> | Cause.Cause<number>) => Effect.succeed(causeError<unknown, number | string>(a0))


export const causeErrorSingle = (a0: Cause.Cause<number>) => Effect.succeed(causeError(a0))


export const tagJoined = (a0: readonly ["hit", number] | readonly ["miss", string]) => caseTag<readonly ["hit", number] | readonly ["miss", string], "hit", number, never, never, string, never, never>(a0, "hit", (a1) => Effect.succeed(a1), (a1) => Effect.succeed("miss"))


export const tagSingle = (a0: readonly ["hit", number]) => caseTag(a0, "hit", (a1) => Effect.succeed(a1), (a1) => Effect.succeed("miss"))


export const recordTagJoined = (a0: { readonly _tag: "hit-tag"; readonly x: number } | { readonly _tag: "miss-tag"; readonly x: string }) => caseTagR<{ readonly _tag: "hit-tag"; readonly x: number } | { readonly _tag: "miss-tag"; readonly x: string }, "hit-tag", number, never, never, string, never, never>(a0, "hit-tag", (a1) => Effect.succeed(recordRequired<"x">("x")(a1)), (a1) => Effect.succeed(recordRequired<"x">("x")(a1)))


export const recordTagSingle = (a0: { readonly _tag: "hit-tag"; readonly x: number }) => caseTagR(a0, "hit-tag", (a1) => Effect.succeed(recordRequired<"x">("x")(a1)), (a1) => Effect.succeed(recordRequired<"x">("x")(a1)))


export const recordRequiredJoined = (a0: { readonly left: boolean; readonly x: number } | { readonly right: boolean; readonly x: string }) => Effect.succeed(recordRequired<"x">("x")<{ readonly left: boolean; readonly x: number } | { readonly right: boolean; readonly x: string }>(a0))


export const recordRequiredSingle = (a0: { readonly left: boolean; readonly x: number }) => Effect.succeed(recordRequired<"x">("x")(a0))


export const recordOptionalJoined = (a0: { readonly left: boolean; readonly x: number } | { readonly right: boolean; readonly x: string }) => Effect.succeed(recordOptional<"x">("x")<{ readonly left: boolean; readonly x: number } | { readonly right: boolean; readonly x: string }>(a0))


export const recordOptionalSingle = (a0: { readonly left: boolean; readonly x: number }) => Effect.succeed(recordOptional<"x">("x")(a0))


export const recordSetJoined = (a0: { readonly left: boolean; readonly x: number } | { readonly right: boolean; readonly x: string }, a1: boolean) => Effect.succeed(recordSet<"x">("x")<{ readonly left: boolean; readonly x: number } | { readonly right: boolean; readonly x: string }>(a0)<boolean>(a1))


export const recordSetSingle = (a0: { readonly left: boolean; readonly x: number }, a1: boolean) => Effect.succeed(recordSet<"x">("x")(a0)(a1))


export const rawFiberAwaitAllJoined = (a0: ReadonlyArray<Fiber.Fiber<number, never>> | ReadonlyArray<Fiber.Fiber<string, boolean>>) => Fiber.awaitAll<Fiber.Fiber<number | string, boolean>>(a0)


export const rawFiberAwaitAllSingle = (a0: ReadonlyArray<Fiber.Fiber<number, never>>) => Fiber.awaitAll(a0)


export const recordSetLiteralSingle = (a0: { readonly left: boolean; readonly x: number }) => Effect.succeed(recordSet<"x">("x")(a0)(true))

