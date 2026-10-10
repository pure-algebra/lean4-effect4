import { Effect } from "effect"
import * as canonical from "./canonical.ts"
import * as changed from "./changed.ts"

const before = await Effect.runPromise(Effect.provide(
  Effect.flatMap(canonical.S, service => service.get()), canonical.SLayer))
const after = await Effect.runPromise(Effect.provide(
  Effect.flatMap(changed.S, service => service.get()), changed.SLayer))
const rootBefore = await Effect.runPromise(canonical.main)
const rootAfter = await Effect.runPromise(changed.main)
if (before !== 1 || after !== 99 || rootBefore !== 1 || rootAfter !== 1) {
  throw new Error(`unexpected observations: ${before}, ${after}, ${rootBefore}, ${rootAfter}`)
}
console.log(JSON.stringify({ before, after, rootBefore, rootAfter }))
