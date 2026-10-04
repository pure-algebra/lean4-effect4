import { Effect } from "effect"
import { program } from "./p3-worker-queue.ts"
const log = await Effect.runPromise(program)
console.log("p3 log", JSON.stringify(log))
