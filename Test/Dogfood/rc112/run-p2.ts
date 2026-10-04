/** Program 2 on rc.112: the module's own layers, handler and middleware over one in-memory
 * SQLite database that a setup step fills first. `provideMerge` exposes the client to the setup;
 * `main` itself provides the client privately (`Layer.provide`). */
import { Effect, Exit, Layer } from "effect"
import { SqlClient } from "effect/unstable/sql"
import { SqliteClient } from "@effect/sql-sqlite-bun"
import { handle, AppConfigLive, UserRepoLive } from "./p2-handler-layers.ts"

process.env.ADMIN_TOKEN = "secret"
const setup = Effect.gen(function*() {
  const sql = yield* SqlClient.SqlClient
  yield* sql`CREATE TABLE users (id INTEGER PRIMARY KEY, name TEXT NOT NULL, role TEXT NOT NULL)`
  yield* sql`INSERT INTO users (id, name, role) VALUES (1, 'ada', 'admin'), (2, 'bob', 'member')`
})
const graph = Layer.mergeAll(AppConfigLive, UserRepoLive).pipe(
  Layer.provideMerge(SqliteClient.layer({ filename: ":memory:" }))
)
const cases: Array<[string, number]> = [["secret", 2], ["secret", 9], ["wrong", 2]]
for (const [token, id] of cases) {
  const exit = await Effect.runPromiseExit(Effect.provide(Effect.andThen(setup, handle(token, id)), graph))
  console.log("p2", token, id, Exit.isSuccess(exit) ? JSON.stringify(exit.value) : JSON.stringify(exit.cause))
}
delete process.env.ADMIN_TOKEN
const missing = await Effect.runPromiseExit(Effect.provide(Effect.andThen(setup, handle("secret", 2)), graph))
console.log("p2 no ADMIN_TOKEN", Exit.isSuccess(missing) ? "success" : JSON.stringify(missing.cause).slice(0, 160))
