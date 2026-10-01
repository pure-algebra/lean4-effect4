/** Red control for the config finding: the same graph in a fresh process that never had
 * ADMIN_TOKEN must fail with a ConfigError; run-p2.ts deleting it mid-process does not. */
import { Effect, Exit, Layer } from "effect"
import { SqliteClient } from "@effect/sql-sqlite-bun"
import { handle, AppConfigLive, UserRepoLive } from "./p2-handler-layers.ts"
const graph = Layer.mergeAll(AppConfigLive, UserRepoLive).pipe(
  Layer.provideMerge(SqliteClient.layer({ filename: ":memory:" }))
)
const exit = await Effect.runPromiseExit(Effect.provide(handle("secret", 2), graph))
console.log("p2 fresh process, no ADMIN_TOKEN:", Exit.isSuccess(exit) ? "success" : JSON.stringify(exit.cause).slice(0, 200))
