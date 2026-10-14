/**
 * todo: the to-do application with the banked Ref cache as one Effect service,
 * written by the Effect4 code generator (decisions row 378 (8) and (20)). Do not edit.
 */
import { Context, Data, Effect, Layer, type Option, Ref } from "effect"
import { eq, fst, ifCase, none, optionCase, pair, recordRequired, recordValue, snd, some } from "/Users/pooks/Dev/lean4-effect4/harness/truth/prelude.ts"

export class NotFound extends Data.TaggedError("NotFound")<{ readonly id: number }> {}

export const TodoRepoKey = Context.Service<"TodoRepo", { readonly insert: (a0: string) => Effect.Effect<{ readonly done: boolean; readonly id: number; readonly title: string }, readonly ["SqlError", string], never>; readonly all: () => Effect.Effect<ReadonlyArray<{ readonly done: boolean; readonly id: number; readonly title: string }>, readonly ["SqlError", string], never>; readonly setDone: (a0: readonly [number, boolean]) => Effect.Effect<Option.Option<{ readonly done: boolean; readonly id: number; readonly title: string }>, readonly ["SqlError", string], never>; readonly "delete": (a0: number) => Effect.Effect<boolean, readonly ["SqlError", string], never> }>(
  "TodoRepo"
)

export const TodoRepo = Object.assign(
  TodoRepoKey,
  {
    insert: (a0: string) => TodoRepoKey.use((a1) => a1.insert(a0)),
    all: () => TodoRepoKey.use((a0) => a0.all()),
    setDone: (a0: readonly [number, boolean]) => TodoRepoKey.use((a1) => a1.setDone(a0)),
    delete: (a0: number) => TodoRepoKey.use((a1) => a1.delete(a0))
  }
)

export const listCacheMake = (a0: void): Effect.Effect<Ref.Ref<Option.Option<ReadonlyArray<{ readonly done: boolean; readonly id: number; readonly title: string }>>>, never, never> => Effect.suspend(
  () => Ref.make(
    recordRequired<"v">(
      "v"
    )(
      recordValue<{ readonly v: Option.Option<ReadonlyArray<{ readonly done: boolean; readonly id: number; readonly title: string }>> }>(
        [
          10,
          [20],
          [[4, [[5, [3, "v"], [5, [1, false], [10, [7], [[10, [8], [[10, [20], [[4, [[5, [3, "done"], [5, [1, false], [10, [5], []]]], [5, [3, "id"], [5, [1, false], [10, [2], []]]], [5, [3, "title"], [5, [1, false], [10, [4], []]]]]]]]]]]]]]]]]
        ],
        { v: none() }
      )
    )
  )
)

export const listCacheGet = (a0: Ref.Ref<Option.Option<ReadonlyArray<{ readonly done: boolean; readonly id: number; readonly title: string }>>>, load: (a0: void) => Effect.Effect<ReadonlyArray<{ readonly done: boolean; readonly id: number; readonly title: string }>, readonly ["SqlError", string], never>): Effect.Effect<ReadonlyArray<{ readonly done: boolean; readonly id: number; readonly title: string }>, readonly ["SqlError", string], never> => Effect.suspend(
  () => Effect.flatMap(
    Ref.get(a0),
    (a1) => optionCase(
      a1,
      () => Effect.flatMap(load(), (a2) => Effect.flatMap(Ref.set(a0, some(a2)), (a3) => Effect.succeed(a2))),
      (a2) => Effect.succeed(a2)
    )
  )
)

export const listCacheInvalidate = (a0: Ref.Ref<Option.Option<ReadonlyArray<{ readonly done: boolean; readonly id: number; readonly title: string }>>>): Effect.Effect<void, never, never> => Effect.suspend(
  () => Effect.flatMap(Ref.set(a0, none()), (a1) => Effect.succeed(undefined))
)

export const TodoAppContext = (a0: void): Effect.Effect<readonly [Context.Context<"TodoRepo">, Ref.Ref<Option.Option<ReadonlyArray<{ readonly done: boolean; readonly id: number; readonly title: string }>>>], never, "TodoRepo"> => Effect.suspend(
  () => Effect.flatMap(
    Effect.context<"TodoRepo">(),
    (a1) => Effect.flatMap(listCacheMake(), (a2) => Effect.succeed(pair(a1, a2)))
  )
)

export const TodoApp_add = (a0: readonly [readonly [Context.Context<"TodoRepo">, Ref.Ref<Option.Option<ReadonlyArray<{ readonly done: boolean; readonly id: number; readonly title: string }>>>], string]): Effect.Effect<{ readonly done: boolean; readonly id: number; readonly title: string }, readonly ["SqlError", string] | readonly ["EmptyTitle", "a title is required"], never> => Effect.suspend(
  () => Effect.flatMap(
    Effect.succeed(snd(fst(a0))),
    (a1) => Effect.flatMap(
      Effect.provideContext(
        Effect.flatMap(
          Effect.succeed(snd(a0)),
          (a2) => ifCase(
            () => eq(a2, ""),
            () => Effect.fail(pair("EmptyTitle", "a title is required")),
            () => TodoRepo.insert(a2)
          )
        ),
        fst(fst(a0))
      ),
      (a2) => Effect.flatMap(listCacheInvalidate(a1), (a3) => Effect.succeed(a2))
    )
  )
)

export const TodoApp_list = (a0: readonly [Context.Context<"TodoRepo">, Ref.Ref<Option.Option<ReadonlyArray<{ readonly done: boolean; readonly id: number; readonly title: string }>>>]): Effect.Effect<ReadonlyArray<{ readonly done: boolean; readonly id: number; readonly title: string }>, readonly ["SqlError", string], never> => Effect.suspend(
  () => Effect.flatMap(
    Effect.succeed(snd(a0)),
    (a1) => listCacheGet(a1, (a2) => Effect.provideContext(TodoRepo.all(), fst(a0)))
  )
)

export const TodoApp_complete = (a0: readonly [readonly [Context.Context<"TodoRepo">, Ref.Ref<Option.Option<ReadonlyArray<{ readonly done: boolean; readonly id: number; readonly title: string }>>>], number]): Effect.Effect<{ readonly done: boolean; readonly id: number; readonly title: string }, readonly ["SqlError", string] | NotFound, never> => Effect.suspend(
  () => Effect.flatMap(
    Effect.succeed(snd(fst(a0))),
    (a1) => Effect.flatMap(
      Effect.provideContext(
        Effect.flatMap(
          Effect.succeed(snd(a0)),
          (a2) => Effect.flatMap(
            TodoRepo.setDone(pair(a2, true)),
            (a3) => optionCase(a3, () => Effect.fail(new NotFound({ id: a2 })), (a4) => Effect.succeed(a4))
          )
        ),
        fst(fst(a0))
      ),
      (a2) => Effect.flatMap(listCacheInvalidate(a1), (a3) => Effect.succeed(a2))
    )
  )
)

export const TodoApp_remove = (a0: readonly [readonly [Context.Context<"TodoRepo">, Ref.Ref<Option.Option<ReadonlyArray<{ readonly done: boolean; readonly id: number; readonly title: string }>>>], number]): Effect.Effect<void, readonly ["SqlError", string] | NotFound, never> => Effect.suspend(
  () => Effect.flatMap(
    Effect.succeed(snd(fst(a0))),
    (a1) => Effect.flatMap(
      Effect.provideContext(
        Effect.flatMap(
          Effect.succeed(snd(a0)),
          (a2) => Effect.flatMap(
            TodoRepo.delete(a2),
            (a3) => ifCase(() => a3, () => Effect.succeed(undefined), () => Effect.fail(new NotFound({ id: a2 })))
          )
        ),
        fst(fst(a0))
      ),
      (a2) => Effect.flatMap(listCacheInvalidate(a1), (a3) => Effect.succeed(a2))
    )
  )
)

export const ListCache = Context.Service<"ListCache", { readonly get: (load: (a0: void) => Effect.Effect<ReadonlyArray<{ readonly done: boolean; readonly id: number; readonly title: string }>, readonly ["SqlError", string], never>) => Effect.Effect<ReadonlyArray<{ readonly done: boolean; readonly id: number; readonly title: string }>, readonly ["SqlError", string], never>; readonly invalidate: () => Effect.Effect<void, never, never> }>(
  "ListCache"
)

export const ListCacheLayer = Layer.effect(ListCache, Effect.map(listCacheMake(), (a0) => {
  return {
    get: (load: (a0: void) => Effect.Effect<ReadonlyArray<{ readonly done: boolean; readonly id: number; readonly title: string }>, readonly ["SqlError", string], never>) => listCacheGet(a0, load),
    invalidate: () => listCacheInvalidate(a0)
  }
}))

export const TodoApp = Context.Service<"TodoApp", { readonly add: (a1: string) => Effect.Effect<{ readonly done: boolean; readonly id: number; readonly title: string }, readonly ["SqlError", string] | readonly ["EmptyTitle", "a title is required"], never>; readonly list: () => Effect.Effect<ReadonlyArray<{ readonly done: boolean; readonly id: number; readonly title: string }>, readonly ["SqlError", string], never>; readonly complete: (a1: number) => Effect.Effect<{ readonly done: boolean; readonly id: number; readonly title: string }, readonly ["SqlError", string] | NotFound, never>; readonly remove: (a1: number) => Effect.Effect<void, readonly ["SqlError", string] | NotFound, never> }>(
  "TodoApp"
)

export const TodoAppLayer = Layer.effect(TodoApp, Effect.map(TodoAppContext(), (a0) => {
  return {
    add: (a1: string) => TodoApp_add(pair(a0, a1)),
    list: () => TodoApp_list(a0),
    complete: (a1: number) => TodoApp_complete(pair(a0, a1)),
    remove: (a1: number) => TodoApp_remove(pair(a0, a1))
  }
}))

export const main: Effect.Effect<void, never, never> = Effect.succeed(undefined)
