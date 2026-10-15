// One Effect program, two layers under the same `Rows` service: the Fpath host as native OCaml
// behind HTTP (fpath_main 8474), and the same generated host compiled to JavaScript by
// js_of_ocaml, called in-process (fpath_host.cjs). The program does not know which it runs on.
//
// Exploration probe (2026-10-15), effect 4.0.0-rc.112 under bun.

import { Effect, Layer } from "effect"
import { FetchHttpClient } from "effect/unstable/http"
import { createRequire } from "node:module"
import { buildRowsOver, httpTransport, inProcessTransport, Rows } from "../rows/rows_client.ts"

const require = createRequire(import.meta.url)
const { fpathHost } = require("./fpath_host.cjs")

const baseUrl = process.argv[2] ?? "http://127.0.0.1:8474"

// The program: a few calls, and their answers as one list.
const program = Effect.gen(function*() {
  const { Fpath } = yield* Rows
  const answers: Array<unknown> = []
  answers.push(yield* Fpath.normalize("a/./b/../c"))
  answers.push(yield* Fpath.segs("/usr/local/lib"))
  answers.push(yield* Fpath.split_ext("archive.tar.gz"))
  answers.push(yield* Fpath.rem_prefix(["/srv", "/srv/www/x"]))
  answers.push(Fpath.relativize === undefined ? "relativize: refused by the generator" : "present")
  answers.push(yield* Effect.flip(Fpath.of_string("")))
  answers.push(yield* Effect.flip(Fpath.v("")))
  return answers
})

// Two layers of the same service.
const nativeOverHttp = Layer.effect(Rows, Effect.flatMap(httpTransport(baseUrl), buildRowsOver)).pipe(
  Layer.provide(FetchHttpClient.layer)
)
const jsInProcess = Layer.effect(Rows, buildRowsOver(inProcessTransport("js_of_ocaml in-process", fpathHost)))

const main = Effect.gen(function*() {
  const a = yield* Effect.provide(program, nativeOverHttp)
  const b = yield* Effect.provide(program, jsInProcess)
  a.forEach((x, i) => console.log(`${String(i).padStart(2)}  native/http ${JSON.stringify(x)}\n    js/inproc   ${JSON.stringify(b[i])}`))
  const same = JSON.stringify(a) === JSON.stringify(b)
  console.log(same ? "THE TWO LAYERS ANSWER ALIKE" : "THE LAYERS DIFFER")
  if (!same) return yield* Effect.fail("layers differ")
})

Effect.runPromise(main).catch((e) => {
  console.error("FAILED", e)
  process.exit(1)
})
