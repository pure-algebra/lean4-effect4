import { Effect } from "effect"
import { program } from "./p4-rate-limiter.ts"
console.log("p4", JSON.stringify(await Effect.runPromise(program)))
