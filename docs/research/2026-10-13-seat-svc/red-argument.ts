// Red control of the consumer's check: `add` takes a title, so a number is refused (TS2345).
import { Effect } from "effect"
import { TodoApp } from "./todo.gen.ts"

export const wrongArgument = Effect.gen(function* () {
  const todo = yield* TodoApp
  return yield* todo.add(1)
})
