// Red control: a client that passes a number where the generated service takes a path string.
import { Effect } from "effect"
import { Fpath } from "./Fpath.service.ts"
export const wrong = Effect.gen(function*() {
  const fpath = yield* Fpath
  return yield* fpath.normalize(42)
})
