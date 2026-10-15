// The to-do application's HTTP interface, as an Effect HttpApi, and a client that Effect derives
// from it. The server is OCaml on Eio (todo_http.ml).
//
// Exploration probe (2026-10-15), effect 4.0.0-rc.112 under bun. The API below is written by
// hand in the shape a generator would print from the application's four entries
// (Test/Dogfood/Scenario/Todo.lean: `openTy "add" = (Todo.ty, EmptyTitle ∪ SqlError)`, …).

import { Effect, Layer, Schema } from "effect"
import { FetchHttpClient } from "effect/unstable/http"
import { HttpApi, HttpApiClient, HttpApiEndpoint, HttpApiGroup, HttpApiSchema } from "effect/unstable/httpapi"

// `eff_record Todo where id : .nat, title : .string, done : .bool`
const Todo = Schema.Struct({ id: Schema.Int, title: Schema.String, done: Schema.Boolean })

// `eff_failure EmptyTitle message`, `eff_failure NotFound where id : .nat`,
// `eff_failure SqlError message`: tagged records, each with the status the edge answers.
class EmptyTitle extends Schema.TaggedError<EmptyTitle>()("EmptyTitle", { message: Schema.String }, {
  httpApiStatus: 400
}) {}
class NotFound extends Schema.TaggedError<NotFound>()("NotFound", { id: Schema.Int }, { httpApiStatus: 404 }) {}
class SqlError extends Schema.TaggedError<SqlError>()("SqlError", { message: Schema.String }, {
  httpApiStatus: 500
}) {}

// One group, one endpoint per entry: add, list, complete, remove.
class Todos extends HttpApiGroup.make("todos").add(
  HttpApiEndpoint.post("add", "/todos", {
    payload: { title: Schema.String },
    success: Todo,
    error: [EmptyTitle, SqlError]
  }),
  HttpApiEndpoint.get("list", "/todos", { success: Schema.Array(Todo), error: SqlError }),
  HttpApiEndpoint.post("complete", "/todos/:id/complete", {
    params: { id: Schema.Int },
    success: Todo,
    error: [NotFound, SqlError]
  }),
  HttpApiEndpoint.delete("remove", "/todos/:id", {
    params: { id: Schema.Int },
    success: HttpApiSchema.NoContent,
    error: [NotFound, SqlError]
  })
) {}

class TodoApi extends HttpApi.make("todo").add(Todos) {}

const baseUrl = process.argv[2] ?? "http://127.0.0.1:8471"

const show = (label: string, value: unknown) => console.log(`${label.padEnd(34)} ${JSON.stringify(value)}`)

const program = Effect.gen(function*() {
  const client = yield* HttpApiClient.make(TodoApi, { baseUrl })
  show("add milk", yield* client.todos.add({ payload: { title: "milk" } }))
  show("add tea", yield* client.todos.add({ payload: { title: "tea" } }))
  show("add '' (EmptyTitle, 400)", yield* Effect.flip(client.todos.add({ payload: { title: "" } })))
  show("complete 1", yield* client.todos.complete({ params: { id: 1 } }))
  show("complete 9 (NotFound, 404)", yield* Effect.flip(client.todos.complete({ params: { id: 9 } })))
  show("remove 2 (NoContent, 204)", yield* client.todos.remove({ params: { id: 2 } }))
  show("remove 2 again (NotFound, 404)", yield* Effect.flip(client.todos.remove({ params: { id: 2 } })))
  show("list", yield* client.todos.list())
  const failed = yield* Effect.flip(client.todos.complete({ params: { id: 9 } }))
  show("the failure is a typed NotFound", failed instanceof NotFound && failed.id === 9)
})

Effect.runPromise(program.pipe(Effect.provide(Layer.mergeAll(FetchHttpClient.layer)))).then(
  () => console.log("ALL HTTPAPI CLIENT CALLS ANSWERED"),
  (e) => {
    console.error("FAILED", e)
    process.exit(1)
  }
)
