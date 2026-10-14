/** The to-do application's run for the host-protocol gate (decisions row 378 (16), slice V4).
 *
 *     bun --no-install apps/todo/run.ts OUT
 *
 * From an empty database, the front (`server.ts`) serves one script of requests over HTTP, once
 * for each repository below. Each run writes its session's file `OUT/<name>.jsonl`, which Lean
 * checks (`Check.lean`):
 *
 * - `sqlite`: `SqliteTodoRepo` as it ships. Every check of every request passes.
 * - `forgetful`: red control. Its `insert` answers the new to-do from a transaction that it rolls
 *   back, so it forgets the write. Its runs conform, and they do not agree with the model.
 * - `titleless`: red control. Its `insert` ignores the title: it stores and answers an empty one.
 *   Its runs do not conform to `insert`'s protocol.
 * - `readonly`: the shipped repository over a connection that SQLite keeps read-only
 *   (`pragma query_only`). Each write fails with SQLite's own error, which the row declares as
 *   `["SqlError", message]`, and each failure escapes its entry as the exit. Its runs conform, and
 *   they do not agree with the model, which never fails.
 *
 * The script covers each entry, both typed failures, an empty title that calls nothing, a second
 * `complete`, and an add after a remove. Three inputs that the wire does not carry are refused
 * before any program runs, so they leave no record: a title of 4097 characters, an id with a
 * leading zero, and an id beyond the wire's naturals. The run checks each answer's status, the
 * shipped repository's last list, and each session's count of records, over HTTP: the front's
 * glue, which no Lean check reads. */
import { mkdir, rm } from "node:fs/promises"
import { resolve } from "node:path"
import { deepStrictEqual } from "node:assert"
import type { Database } from "bun:sqlite"
import { Effect } from "effect"
import { cachedListAfterAdd, repository } from "./consumer.ts"
import { serve, versions } from "./server.ts"
import { open, sqliteRepository, type Repository } from "./repo.ts"

const [outPath] = process.argv.slice(2)
if (!outPath) throw Error("usage: run.ts OUT")
const out = resolve(outPath)
const runtime = versions()
console.log(`to-do on SQLite: effect ${runtime.effect} under bun ${runtime.bun}, SQLite ${runtime.sqlite}`)

/** Red control: an adapter that forgets a write. */
const forgetful = (db: Database): Repository => {
  const shipped = sqliteRepository(db)
  return { ...shipped, insert: title => Effect.suspend(() => {
    db.run("begin")
    return Effect.ensuring(shipped.insert(title), Effect.sync(() => db.run("rollback")))
  }) }
}

/** Red control: an adapter whose insert ignores the title. */
const titleless = (db: Database): Repository => {
  const shipped = sqliteRepository(db)
  return { ...shipped, insert: _title => shipped.insert("") }
}

/** The shipped repository over a connection that SQLite keeps read-only. */
const readonly = (db: Database): Repository => {
  db.run("pragma query_only = true")
  return sqliteRepository(db)
}

/** The script: each request with the status that the shipped repository answers. A request that
 * the front refuses runs no program. */
const script: ReadonlyArray<{ method: string; path: string; body?: unknown; status: number; refused?: true }> = [
  { method: "POST", path: "/todos", body: { title: "milk" }, status: 200 },
  { method: "POST", path: "/todos", body: { title: "x".repeat(4097) }, status: 400, refused: true },
  { method: "POST", path: "/todos", body: { title: "tea" }, status: 200 },
  { method: "POST", path: "/todos", body: { title: "" }, status: 400 },
  { method: "GET", path: "/todos", status: 200 },
  { method: "POST", path: "/todos/1/complete", status: 200 },
  { method: "POST", path: "/todos/1/complete", status: 200 },
  { method: "POST", path: "/todos/7/complete", status: 404 },
  { method: "POST", path: "/todos/01/complete", status: 400, refused: true },
  { method: "DELETE", path: "/todos/2", status: 200 },
  { method: "DELETE", path: "/todos/2", status: 404 },
  { method: "DELETE", path: "/todos/9007199254740992", status: 400, refused: true },
  { method: "POST", path: "/todos", body: { title: "bread" }, status: 200 },
  { method: "GET", path: "/todos", status: 200 }
]

/** One session: a fresh database, the front over the repository, the script over HTTP. Answers each
 * response's status and the last response's body. */
const session = async (name: string, over: (db: Database) => Repository): Promise<{ statuses: number[]; last: unknown }> => {
  const db = resolve(out, `${name}.db`), file = resolve(out, `${name}.jsonl`)
  await rm(db, { force: true }); await rm(file, { force: true })
  const served = await serve({ db, session: file, port: 0, over })
  try {
    const statuses: number[] = []
    let last: unknown
    for (const request of script) {
      const response = await fetch(`http://localhost:${served.port}${request.path}`, {
        method: request.method,
        ...(request.body === undefined ? {} : { headers: { "content-type": "application/json" }, body: JSON.stringify(request.body) })
      })
      statuses.push(response.status)
      last = await response.json()
    }
    const records = (await Bun.file(file).text()).split("\n").filter(line => line !== "").length - 1
    deepStrictEqual(records, script.filter(request => !request.refused).length, `${name}: one record for each request that ran`)
    return { statuses, last }
  } finally {
    await served.stop()
  }
}

await mkdir(out, { recursive: true })
const shipped = await session("sqlite", sqliteRepository)
deepStrictEqual(shipped.statuses, script.map(request => request.status), "the shipped repository's statuses")
deepStrictEqual(shipped.last, [{ done: true, id: 1, title: "milk" }, { done: false, id: 3, title: "bread" }],
  "the shipped repository's last list")
await session("forgetful", forgetful)
await session("titleless", titleless)
// A write that SQLite refuses answers 500 with the row's declared error; a read still answers.
const refused = await session("readonly", readonly)
deepStrictEqual(refused.statuses, script.map(request => request.method === "GET" || request.status === 400 ? request.status : 500),
  "the read-only repository's statuses")
// In one `TodoAppLayer` scope, the second `list` answers from the `Ref` cache (no second `all`
// query), and `add` invalidates the cache so the third `list` queries SQLite again (row 378 (8)).
const cacheDbPath = resolve(out, "cached.db")
await rm(cacheDbPath, { force: true })
const cacheDb = open(cacheDbPath)
let allQueries = 0
try {
  const base = sqliteRepository(cacheDb)
  const counted: Repository = {
    ...base,
    all: () => Effect.suspend(() => {
      allQueries += 1
      return base.all()
    })
  }
  const [first, hit, item, after] = await Effect.runPromise(
    cachedListAfterAdd("milk").pipe(Effect.provide(repository(counted)))
  )
  deepStrictEqual(first, [], "cached: first list is empty")
  deepStrictEqual(hit, [], "cached: second list answers the cached empty list")
  deepStrictEqual(item, { done: false, id: 1, title: "milk" }, "cached: add answers the new to-do")
  deepStrictEqual(after, [{ done: false, id: 1, title: "milk" }], "cached: list after add answers the new to-do")
  deepStrictEqual(allQueries, 2, "cached: two SQL `all` queries across three `list` calls (one cache hit, one invalidation)")
} finally {
  cacheDb.close()
}
console.log(`PASS the to-do on SQLite: ${script.length} requests served over HTTP for each of 4 repositories, ` +
  `${script.filter(request => request.refused).length} of them refused with no record; the statuses of the shipped and ` +
  `the read-only repositories, the shipped last list, and the Ref cache hit + invalidation as expected; sessions in ${out}`)

