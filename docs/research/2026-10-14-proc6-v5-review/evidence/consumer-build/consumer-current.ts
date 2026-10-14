/** The consumer of the to-do application's emitted service (decisions row 378 (20), slices E4
 * and V4). An Effect program takes the service by its key, calls one method, and provides the
 * service's layer. The layer reads the repository's service from its context, so a program here
 * requires the repository's key until a repository is provided. tsgo 7 type-checks this file
 * against the emitted module, which `EmitTodo.lean` writes into the application's work folder.
 * The front (`server.ts`) serves its programs over SQLite, and the keyed lane's runner performs
 * the to-do's scripts on them (`harness/truth/service/run-todo.ts`). */
import { Effect, Layer } from "/Users/pooks/Dev/lean4-effect4/apps/todo/node_modules/effect/src/index.ts"
import { NotFound, TodoApp, TodoAppLayer, TodoRepo } from "./emitted/todo.gen.ts"

/** A to-do, as the service's methods answer it. */
export type Todo = { readonly done: boolean; readonly id: number; readonly title: string }
/** The repository's failure, and the empty title's. */
export type SqlError = readonly ["SqlError", string]
export type EmptyTitle = readonly ["EmptyTitle", "a title is required"]
/** The repository's key, which the service's layer requires. */
export type Repo = typeof TodoRepo.Identifier

/** A program over the to-do service, its layer provided: it requires the repository alone. */
export const withTodo = <A, E>(use: (todo: typeof TodoApp.Service) => Effect.Effect<A, E>): Effect.Effect<A, E, Repo> =>
  Effect.gen(function* () {
    const todo = yield* TodoApp
    return yield* use(todo)
  }).pipe(Effect.provide(TodoAppLayer))

/** The to-do's scripts (`runsOf`, `Test/Dogfood/Scenario/Todo/Claims.lean`), each as the program
 * of the method its script runs. */
export const programs = {
  addEmpty: withTodo(todo => todo.add("")),
  addMilk: withTodo(todo => todo.add("milk")),
  list: withTodo(todo => todo.list()),
  completeOne: withTodo(todo => todo.complete(1))
}

// The types an Effect user expects: each method's answer and error, and the repository's key as
// the one requirement.
export const added: Effect.Effect<Todo, SqlError | EmptyTitle, Repo> = programs.addMilk
export const listed: Effect.Effect<ReadonlyArray<Todo>, SqlError, Repo> = programs.list
export const completed: Effect.Effect<Todo, SqlError | NotFound, Repo> = programs.completeOne

/** A repository given as a layer of the key (`Layer.succeed`), as a person provides one. */
export const repository = (impl: typeof TodoRepo.Service): Layer.Layer<Repo> => Layer.succeed(TodoRepo, impl)
/** With a repository provided, the program requires nothing. */
export const closed = (impl: typeof TodoRepo.Service): Effect.Effect<Todo, SqlError | EmptyTitle> =>
  programs.addMilk.pipe(Effect.provide(repository(impl)))

/** Two `list`s, an `add`, and a third `list` in one `TodoAppLayer` scope (decisions row 378 (8)):
 * the second `list` answers from the `Ref` cache without calling `TodoRepo.all`, and `add`
 * invalidates the cache (`cached_list_after_add`) so the third `list` reads the repository again. */
export const cachedListAfterAdd = (
  title: string
): Effect.Effect<readonly [ReadonlyArray<Todo>, ReadonlyArray<Todo>, Todo, ReadonlyArray<Todo>], SqlError | EmptyTitle, Repo> =>
  withTodo(todo =>
    Effect.gen(function* () {
      const first = yield* todo.list()
      const hit = yield* todo.list()
      const item = yield* todo.add(title)
      const after = yield* todo.list()
      return [first, hit, item, after] as const
    })
  )

