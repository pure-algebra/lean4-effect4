// Seat SVC's consumer of the emitted to-do service: an Effect program that takes the service by its
// key, calls its methods and provides its layer. tsgo 7 type-checks it against `todo.gen.ts`.
import { Effect, type Layer } from "effect"
import { NotFound, TodoApp, TodoAppLayer } from "./todo.gen.ts"

type Todo = { readonly done: boolean; readonly id: number; readonly title: string }
type TodoError = readonly ["SqlError", string] | readonly ["EmptyTitle", "a title is required"] | NotFound

export const program = Effect.gen(function* () {
  const todo = yield* TodoApp
  const added = yield* todo.add("milk")
  const done = yield* todo.complete(added.id)
  yield* todo.remove(done.id)
  return yield* todo.list()
})

// The program requires the service until its layer is provided; then it requires nothing.
export const needsService: Effect.Effect<ReadonlyArray<Todo>, TodoError, typeof TodoApp.Identifier> = program
export const provided: Effect.Effect<ReadonlyArray<Todo>, TodoError, never> =
  program.pipe(Effect.provide(TodoAppLayer))

// The layer provides the service, fails with nothing and requires the rows' keys: none yet.
export const layer: Layer.Layer<typeof TodoApp.Identifier, never, never> = TodoAppLayer
