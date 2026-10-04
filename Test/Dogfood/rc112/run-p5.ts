import { Effect } from "effect"
import { program } from "./p5-ledger-service.ts"
console.log("p5", JSON.stringify(await Effect.runPromise(program)))
