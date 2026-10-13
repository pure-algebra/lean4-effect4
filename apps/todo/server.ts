/** The to-do application's front (decisions row 378 (16), slice V4): a Bun HTTP server.
 *
 *     bun --no-install apps/todo/server.ts DATABASE SESSION [PORT]
 *
 * Each request runs one entry of the to-do's emitted service through its consumer
 * (`consumer.ts`, `withTodo`), over SQLite (`repo.ts`, `SqliteTodoRepo`). The keyed lane's
 * recorder, live (`harness/truth/session/keyed-recorder.ts`), writes the request's record: the
 * entry, its arguments, each host call's row, request and completion, and the root's exit. The
 * session's file holds a header line, then one record a line. Lean rebuilds each request's run
 * from its record and decides its checks (`Check.lean`, the lowering note's §6.1).
 *
 * | Route | Entry | Answer |
 * | --- | --- | --- |
 * | `POST /todos` with `{"title": string}` | `add` | the stored to-do; 400 for an empty title |
 * | `GET /todos` | `list` | the to-dos |
 * | `POST /todos/:id/complete` | `complete` | the to-do, marked done; 404 for a missing one |
 * | `DELETE /todos/:id` | `remove` | `null`; 404 for a missing one |
 *
 * A failure of SQLite answers 500. A request whose input is no entry's argument answers 400 and
 * runs nothing, so it leaves no record. The server serves one request at a time, so the session's
 * order is the order of its runs. The header gives the repository's state at the session's start,
 * which Lean takes as the reference model's start state. */
import { appendFileSync, existsSync, readFileSync } from "node:fs"
import { basename, dirname, resolve } from "node:path"
import { Database } from "bun:sqlite"
import { Cause, Context, Effect, Exit, Layer, Scope } from "effect"
import { KeyedRecorder, valueJson, type RequestRecord } from "../../harness/truth/session/keyed-recorder.ts"
import { provideRows, tableRows } from "../../harness/truth/session/keyed-bindings.ts"
import type { Json } from "../../harness/truth/session/protocol.ts"
import * as Service from "./.work/todo.gen.ts"
import { withTodo, type Repo } from "./consumer.ts"
import { SqliteTodoRepo, open, sqliteRepository, stateOf, type Repository } from "./repo.ts"

/** The application's row table and its service namespaces, as `EmitTodo.lean` wrote them beside
 * the service. */
const emitted = JSON.parse(readFileSync(resolve(import.meta.dir, ".work/todo.table.json"), "utf8")) as
  { application: string; table: Json[]; services: string[] }

/** The versions of the runtime: the pinned effect, bun and SQLite. The effect that the emitted
 * module and the recorder load must be one package, the pinned one. */
export const versions = (): { effect: string; bun: string; sqlite: string } => {
  const pinned = Bun.resolveSync("effect", import.meta.dir)
  const recorder = Bun.resolveSync("effect", resolve(import.meta.dir, "../../harness/truth/session"))
  if (pinned !== recorder) throw Error(`the application loads effect from ${pinned}, and the recorder from ${recorder}`)
  const effect = (JSON.parse(readFileSync(resolve(dirname(pinned), "../package.json"), "utf8")) as { version: string }).version
  if (effect !== "4.0.0-rc.112") throw Error(`the pinned effect 4.0.0-rc.112 is required, and ${effect} loaded`)
  const sqlite = new Database(":memory:").query<{ version: string }, []>("select sqlite_version() as version").get()!.version
  return { effect, bun: Bun.version, sqlite }
}

/** The four entries, each as the consumer's program at its arguments. */
type Entry = "add" | "list" | "complete" | "remove"
const programOf = (entry: Entry, args: ReadonlyArray<Json>): Effect.Effect<unknown, unknown, Repo> => {
  switch (entry) {
    case "add": return withTodo(todo => todo.add(args[0] as string))
    case "list": return withTodo(todo => todo.list())
    case "complete": return withTodo(todo => todo.complete(args[0] as number))
    case "remove": return withTodo(todo => todo.remove(args[0] as number))
  }
}

/** The answer of a run over HTTP. */
const respond = (exit: Exit.Exit<unknown, unknown>): Response => {
  if (Exit.isSuccess(exit)) return Response.json(exit.value ?? null)
  const failure = exit.cause.reasons.find(Cause.isFailReason)
  const error: unknown = failure?.error
  if (error instanceof Service.NotFound) return Response.json({ error: "NotFound", id: error.id }, { status: 404 })
  if (Array.isArray(error) && error[0] === "EmptyTitle") return Response.json({ error: "EmptyTitle", message: error[1] }, { status: 400 })
  if (Array.isArray(error) && error[0] === "SqlError") return Response.json({ error: "SqlError", message: error[1] }, { status: 500 })
  return Response.json({ error: "Defect" }, { status: 500 })
}

/** A request whose input is no entry's argument. */
const refuse = (why: string): Response => Response.json({ error: "BadRequest", message: why }, { status: 400 })

/** An id from a route: a decimal natural that the wire carries (`Number.MAX_SAFE_INTEGER` at most). */
const idOf = (text: string): number | undefined => {
  const id = /^(0|[1-9][0-9]*)$/.test(text) ? Number(text) : NaN
  return Number.isSafeInteger(id) ? id : undefined
}

export interface Served { readonly port: number; stop(): Promise<void> }

/** Serve the to-do over the database at `db`, writing the session's file at `session` (a new
 * file). `over` gives the repository from the open database (`repo.ts`). */
export const serve = async (options: { db: string; session: string; port?: number; over?: (db: Database) => Repository }): Promise<Served> => {
  if (existsSync(options.session)) throw Error(`${options.session}: a session's file is new; this one exists`)
  const name = basename(options.session).replace(/\.[^.]*$/, "")
  const startDb = open(options.db)
  const start = stateOf(startDb)
  startDb.close()
  appendFileSync(options.session, JSON.stringify({ format: "effect4-app-session-v1", application: emitted.application,
    session: name, table: emitted.table, start, versions: versions() }) + "\n")
  const scope = Scope.makeUnsafe()
  const context = await Effect.runPromise(Layer.buildWithScope(SqliteTodoRepo(options.db, options.over ?? sqliteRepository), scope))
  const repository = Context.get(context, Service.TodoRepo)
  /** One request: its program run with the repository's calls recorded, and its record written. */
  const run = async (entry: Entry, args: Json[]): Promise<Response> => {
    const recorder = new KeyedRecorder({ name: entry, expression: "", table: emitted.table, source: null, plan: [],
      expected: null, live: true }, name)
    const rows = tableRows<Record<string, unknown>>(emitted.application, emitted.table, (row, request, image) => {
      const method = (repository as unknown as Record<string, (request: unknown) => Effect.Effect<unknown, unknown>>)[row.method]
      if (typeof method !== "function") throw Error(`${emitted.application}: the repository has no method ${row.method}`)
      return recorder.external(row.index, image, method(request))
    })
    const program = provideRows(emitted.application, rows, emitted.services, Service, programOf(entry, args))
    const exit = await Effect.runPromiseExit(Effect.withFiber(fiber => {
      recorder.attachRoot(fiber)
      return program
    }))
    const record: RequestRecord = recorder.request(args, exit)
    appendFileSync(options.session, JSON.stringify(record) + "\n")
    return respond(exit)
  }
  /** The server serves one request at a time. */
  let queue: Promise<unknown> = Promise.resolve()
  const serial = (entry: Entry, args: Json[]): Promise<Response> => {
    const next = queue.then(() => run(entry, args))
    queue = next.catch(() => undefined)
    return next
  }
  const server = Bun.serve({
    port: options.port ?? 0,
    routes: {
      "/todos": {
        GET: () => serial("list", []),
        POST: async request => {
          const body: unknown = await request.json().catch(() => undefined)
          const title = typeof body === "object" && body !== null ? (body as { title?: unknown }).title : undefined
          if (typeof title !== "string" || title.length > 4096) return refuse("a title is a string of 4096 characters at most")
          return serial("add", [valueJson(title)])
        }
      },
      "/todos/:id/complete": {
        POST: request => {
          const id = idOf(request.params.id)
          return id === undefined ? refuse("an id is a decimal natural") : serial("complete", [valueJson(id)])
        }
      },
      "/todos/:id": {
        DELETE: request => {
          const id = idOf(request.params.id)
          return id === undefined ? refuse("an id is a decimal natural") : serial("remove", [valueJson(id)])
        }
      }
    },
    fetch: () => Response.json({ error: "NotFound", message: "no such route" }, { status: 404 }),
    error: error => Response.json({ error: "Refused", message: error.message }, { status: 500 })
  })
  return {
    port: server.port!,
    stop: async () => {
      await server.stop()
      await queue
      await Effect.runPromise(Scope.close(scope, Exit.void))
    }
  }
}

if (import.meta.main) {
  const [db, session, port] = process.argv.slice(2)
  if (!db || !session) throw Error("usage: server.ts DATABASE SESSION [PORT]")
  const served = await serve({ db, session, port: port === undefined ? 3000 : Number(port) })
  console.log(`to-do: serving on port ${served.port}; the session's records go to ${session}`)
}
