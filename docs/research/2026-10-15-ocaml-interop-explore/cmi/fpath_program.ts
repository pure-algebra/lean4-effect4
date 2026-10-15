// An Effect program calling the OCaml library Fpath, through a service built at run time from the
// rows that cmi_rows generated out of fpath.cmi (fpath_main 8474 serves them).
//
// Exploration probe (2026-10-15), effect 4.0.0-rc.112 under bun.

import { Effect } from "effect"
import { FetchHttpClient } from "effect/unstable/http"
import { buildRows, Rows } from "../rows/rows_client.ts"

const baseUrl = process.argv[2] ?? "http://127.0.0.1:8474"

const show = (label: string, value: unknown) => console.log(`${label.padEnd(44)} ${JSON.stringify(value)}`)

const program = Effect.gen(function*() {
  const { Fpath } = yield* Rows
  show("Fpath.normalize('a/./b/../c')", yield* Fpath.normalize("a/./b/../c"))
  show("Fpath.segs('/usr/local/lib')", yield* Fpath.segs("/usr/local/lib"))
  show("Fpath.split_ext('archive.tar.gz')  ?multi default", yield* Fpath.split_ext("archive.tar.gz"))
  show("Fpath.add_seg(['/srv', 'www'])", yield* Fpath.add_seg(["/srv", "www"]))
  show("Fpath.rem_prefix(['/srv', '/srv/www/x'])", yield* Fpath.rem_prefix(["/srv", "/srv/www/x"]))
  show("Fpath.is_prefix(['/a', '/b/c'])", yield* Fpath.is_prefix(["/a", "/b/c"]))
  show("Fpath.compare(['a', 'b'])", yield* Fpath.compare(["a", "b"]))
  // A `result`'s error arrives as its tagged case; an exception arrives as `Raised`.
  show("Fpath.of_string('')  (Error `Msg)", yield* Effect.flip(Fpath.of_string("")))
  show("Fpath.v('')  (raises Invalid_argument)", yield* Effect.flip(Fpath.v("")))
})

Effect.runPromise(
  program.pipe(Effect.provideServiceEffect(Rows, buildRows(baseUrl)), Effect.provide(FetchHttpClient.layer))
).then(
  () => console.log("ALL FPATH CALLS ANSWERED"),
  (e) => {
    console.error("FAILED", e)
    process.exit(1)
  }
)
