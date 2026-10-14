/** The to-do's repository over SQLite (decisions row 378 (16), slice V4).
 *
 * `SqliteTodoRepo` is the layer that provides the emitted module's `TodoRepo` service
 * (`.work/todo.gen.ts`, written by `EmitTodo.lean`) over `bun:sqlite`, Bun's built-in driver, so
 * nothing is installed. Each of the four rows is one SQL statement. A failure of SQLite is the
 * row's declared error, `["SqlError", message]`. Ids come from `AUTOINCREMENT`: the table never
 * gives an id twice, as the reference model `repository` (`Test/Dogfood/Scenario/Todo.lean`) never
 * does. Without it, SQLite would give a deleted greatest id again.
 *
 * The adapter is host code: Lean reads only the completions that a request's record holds. */
import { Database } from "bun:sqlite"
import { Effect, Layer, Option } from "effect"
import { TodoRepo } from "./.work/todo.gen.ts"
import type { Repo, SqlError, Todo } from "./consumer.ts"

/** The repository's service: one method for each of the four rows. */
export type Repository = typeof TodoRepo.Service

/** A stored to-do, as SQLite gives its row. */
interface Row { readonly id: number; readonly title: string; readonly done: number }

const todoOf = (row: Row): Todo => ({ done: row.done !== 0, id: row.id, title: row.title })

/** One SQLite operation, its failure the row's declared error. */
export const sql = <A>(operation: () => A): Effect.Effect<A, SqlError> =>
  Effect.try({ try: operation, catch: error => ["SqlError", error instanceof Error ? error.message : String(error)] as const })

/** Open the database at `path`, with its one table. */
export const open = (path: string): Database => {
  const db = new Database(path, { create: true, strict: true })
  db.run("create table if not exists todos (id integer primary key autoincrement, title text not null, done integer not null default 0)")
  return db
}

/** The repository over an open database. */
export const sqliteRepository = (db: Database): Repository => ({
  insert: title => sql(() => {
    const row = db.query<Row, [string]>("insert into todos (title) values (?) returning id, title, done").get(title)
    if (row === null) throw Error("the insert returned no row")
    return todoOf(row)
  }),
  all: () => sql(() => db.query<Row, []>("select id, title, done from todos order by id").all().map(todoOf)),
  setDone: ([id, done]) => sql(() => Option.map(
    Option.fromNullishOr(db.query<Row, [number, number]>("update todos set done = ? where id = ? returning id, title, done").get(done ? 1 : 0, id)),
    todoOf)),
  delete: id => sql(() => db.query<Row, [number]>("delete from todos where id = ?").run(id).changes > 0)
})

/** The repository's state as the reference model holds it: the next id and the stored to-dos, in
 * id order. A session's header carries it as the model's start state. */
export const stateOf = (db: Database): { next: number; todos: Array<[number, string, boolean]> } => {
  const seq = db.query<{ seq: number }, []>("select seq from sqlite_sequence where name = 'todos'").get()
  const todos = db.query<Row, []>("select id, title, done from todos order by id").all()
  return { next: (seq?.seq ?? 0) + 1, todos: todos.map(row => [row.id, row.title, row.done !== 0]) }
}

/** `SqliteTodoRepo`: the layer that opens the database at `path`, provides the repository over it,
 * and closes the database with the layer's scope. `over` gives the repository from the open
 * database; the red controls of `run.ts` pass a faulty one. */
export const SqliteTodoRepo = (path: string, over: (db: Database) => Repository = sqliteRepository): Layer.Layer<Repo, SqlError> =>
  Layer.effect(TodoRepo, Effect.map(Effect.acquireRelease(sql(() => open(path)), db => Effect.sync(() => db.close())), over))
