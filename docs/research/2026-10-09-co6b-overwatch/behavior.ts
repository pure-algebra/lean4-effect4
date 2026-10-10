import { Effect } from "effect"
import * as original from "./positive.ts"
import * as changed from "./changed-request.ts"
import * as quoted from "./method-name-repaired.ts"
import * as prototype from "./prototype-name-repaired.ts"

const before = await Effect.runPromise(Effect.provide(
  Effect.flatMap(original.S, service => service.get()), original.SLayer))
const after = await Effect.runPromise(Effect.provide(
  Effect.flatMap(changed.S, service => service.get()), changed.SLayer))
if (before !== 1 || after !== 99) {
  throw new Error(`unexpected results: ${before}, ${after}`)
}
console.log(JSON.stringify({ original: before, changedArgument: after }))

const quotedService = await Effect.runPromise(Effect.provide(quoted.S, quoted.SLayer))
const prototypeService = await Effect.runPromise(Effect.provide(prototype.S, prototype.SLayer))
const quotedResult = await Effect.runPromise(quotedService["bad-name"]())
const prototypeResult = await Effect.runPromise(prototypeService["__proto__"]())
const ownPrototypeMethod = Object.hasOwn(prototypeService, "__proto__")
if (quotedResult !== 1 || prototypeResult !== 1 || !ownPrototypeMethod ||
    Object.getPrototypeOf(prototypeService) !== Object.prototype) {
  throw new Error("record key policy did not preserve an own callable method")
}
console.log(JSON.stringify({ quotedResult, prototypeResult, ownPrototypeMethod }))
