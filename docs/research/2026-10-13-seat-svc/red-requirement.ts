// Red control of the consumer's check: without the service's layer the program still requires
// the service, so it is no `Effect.Effect<…, …, never>` (tsgo 7: TS2375, "TodoApp" is not never).
import { Effect } from "effect"
import { TodoApp } from "./todo.gen.ts"

export const unprovided: Effect.Effect<unknown, unknown, never> = Effect.gen(function* () {
  const todo = yield* TodoApp
  return yield* todo.list()
})
