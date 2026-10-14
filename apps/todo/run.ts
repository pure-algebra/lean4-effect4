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
 *
 * The script covers each entry, both typed failures, an empty title that calls nothing, a second
 * `complete`, and an add after a remove. The run checks each answer's status, and the last list of
 * the shipped repository, over HTTP: the front's glue, which no Lean check reads. */
import { mkdir, rm } from "node:fs/promises"
import { resolve } from "node:path"
import { deepStrictEqual } from "node:assert"
import type { Database } from "bun:sqlite"
import { Effect } from "effect"
import { serve, versions } from "./server.ts"
import { sqliteRepository, type Repository } from "./repo.ts"

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

/** The script: each request with the status that the shipped repository answers. */
const script: ReadonlyArray<{ method: string; path: string; body?: unknown; status: number }> = [
  { method: "POST", path: "/todos", body: { title: "milk" }, status: 200 },
  { method: "POST", path: "/todos", body: { title: "tea" }, status: 200 },
  { method: "POST", path: "/todos", body: { title: "" }, status: 400 },
  { method: "GET", path: "/todos", status: 200 },
  { method: "POST", path: "/todos/1/complete", status: 200 },
  { method: "POST", path: "/todos/1/complete", status: 200 },
  { method: "POST", path: "/todos/7/complete", status: 404 },
  { method: "DELETE", path: "/todos/2", status: 200 },
  { method: "DELETE", path: "/todos/2", status: 404 },
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
console.log(`PASS the to-do on SQLite: ${script.length} requests served over HTTP for each of 3 repositories; ` +
  `the shipped repository's statuses and last list as expected; sessions in ${out}`)
