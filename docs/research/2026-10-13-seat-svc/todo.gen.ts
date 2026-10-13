/**
 * todo: the to-do application as one Effect service, written by the Effect4 code
 * generator (decisions row 378 (20)). Do not edit.
 */
import { Context, Data, Effect, Layer } from "effect"
import { eq, fst, ifCase, optionCase, pair, snd } from "../prelude/prelude.ts"

export class NotFound extends Data.TaggedError("NotFound")<{ readonly id: number }> {}

export const TodoAppContext = (a0: void): Effect.Effect<Context.Context<never>, never, never> => Effect.suspend(
  () => Effect.context<never>()
)

export const TodoApp_add = (a0: readonly [Context.Context<never>, string]): Effect.Effect<{ readonly done: boolean; readonly id: number; readonly title: string }, readonly ["SqlError", string] | readonly ["EmptyTitle", "a title is required"], never> => Effect.suspend(
  () => Effect.provideContext(
    Effect.flatMap(
      Effect.succeed(snd(a0)),
      (a1) => ifCase(
        () => eq(a1, ""),
        () => Effect.fail(pair("EmptyTitle", "a title is required")),
        () => TodoRepo.insert(a1)
      )
    ),
    fst(a0)
  )
)

export const TodoApp_list = (a0: Context.Context<never>): Effect.Effect<ReadonlyArray<{ readonly done: boolean; readonly id: number; readonly title: string }>, readonly ["SqlError", string], never> => Effect.suspend(
  () => Effect.provideContext(TodoRepo.all(), a0)
)

export const TodoApp_complete = (a0: readonly [Context.Context<never>, number]): Effect.Effect<{ readonly done: boolean; readonly id: number; readonly title: string }, readonly ["SqlError", string] | NotFound, never> => Effect.suspend(
  () => Effect.provideContext(
    Effect.flatMap(
      Effect.succeed(snd(a0)),
      (a1) => Effect.flatMap(
        TodoRepo.setDone(pair(a1, true)),
        (a2) => optionCase(a2, () => Effect.fail(new NotFound({ id: a1 })), (a3) => Effect.succeed(a3))
      )
    ),
    fst(a0)
  )
)

export const TodoApp_remove = (a0: readonly [Context.Context<never>, number]): Effect.Effect<void, readonly ["SqlError", string] | NotFound, never> => Effect.suspend(
  () => Effect.provideContext(
    Effect.flatMap(
      Effect.succeed(snd(a0)),
      (a1) => Effect.flatMap(
        TodoRepo.delete(a1),
        (a2) => ifCase(() => a2, () => Effect.succeed(undefined), () => Effect.fail(new NotFound({ id: a1 })))
      )
    ),
    fst(a0)
  )
)

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
