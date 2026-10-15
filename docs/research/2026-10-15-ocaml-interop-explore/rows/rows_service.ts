// The to-do's rows, called through the run-time client (rows_client.ts) against an OCaml host
// (`rows_http serve 8473`). Exploration probe (2026-10-15), effect 4.0.0-rc.112 under bun.

import { Effect } from "effect"
import { FetchHttpClient } from "effect/unstable/http"
import { buildRows, Rows } from "./rows_client.ts"

const baseUrl = process.argv[2] ?? "http://127.0.0.1:8473"

const show = (label: string, value: unknown) => console.log(`${label.padEnd(36)} ${JSON.stringify(value)}`)

const program = Effect.gen(function*() {
  const { TodoRepo } = yield* Rows
  show("TodoRepo.insert('milk')", yield* TodoRepo.insert("milk"))
  show("TodoRepo.insert('tea')", yield* TodoRepo.insert("tea"))
  show("TodoRepo.setDone([1, true])", yield* TodoRepo.setDone([1, true]))
  show("TodoRepo.delete(2)", yield* TodoRepo.delete(2))
  show("TodoRepo.all(null)", yield* TodoRepo.all(null))
  // The request schema refuses before anything is sent: a negative natural.
  const refused = yield* Effect.flip(TodoRepo.setDone([-1, true]))
  show("setDone([-1, true]) refused locally", String(refused).split("\n")[0])
})

Effect.runPromise(
  program.pipe(
    Effect.provideServiceEffect(Rows, buildRows(baseUrl)),
    Effect.provide(FetchHttpClient.layer)
  )
).then(
  () => console.log("ALL ROW SERVICE CALLS ANSWERED"),
  (e) => {
    console.error("FAILED", e)
    process.exit(1)
  }
)
