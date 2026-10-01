/**
 * Program 2 (seat PROGRAMS, 2026-09-30): a request handler over layered services. A UserRepo
 * implemented over the SQL client, an AppConfig read from configuration, an authentication
 * middleware that discharges CurrentUser, and the whole graph provided once in main.
 * Idiomatic Effect rc.112.
 *
 * rc.112 lines relied on (vendor/effect-4.0.0-rc.112/src/ unless noted):
 *   Context.Service (class form)   Context.ts:160-201 (the key string is the runtime identity)
 *   Layer.effect                   Layer.ts:1347, :1427-1438 (Exclude<R, Scope>), effectImpl :1435-1440
 *   Layer.succeed                  Layer.ts:1012, :1074-1078
 *   Layer.provide                  Layer.ts:2008, :2258 (RIn | Exclude<RIn2, ROut>)
 *   Layer.mergeAll                 Layer.ts:1652
 *   Effect.provide                 Effect.ts:11383; internal/layer.ts:8-22
 *   Effect.provideService          Effect.ts:12324; internal/effect.ts:2202-2232
 *   Effect.catchTag                Effect.ts:4370
 *   Config.string / Config.int     Config.ts:1465, :1550; Config.withDefault :744
 *   Schema.Struct / Literals       Schema.ts:3581, :4969; Schema.decodeUnknownEffect :1516
 *   SqlClient (the `sql` template) unstable/sql/SqlClient.ts:30-100; Statement.ts:431-445
 *   SqliteClient.layer             @effect/sql-sqlite-bun@4.0.0-rc.112 dist/SqliteClient.d.ts:91
 */
import { Config, Context, Data, Effect, Layer, Schema } from "effect"
import { SqlClient } from "effect/unstable/sql"
import { SqliteClient } from "@effect/sql-sqlite-bun"

/** A record with a variant field, decoded from a row. */
const User = Schema.Struct({
  id: Schema.Number,
  name: Schema.String,
  role: Schema.Literals(["admin", "member"])
})
type User = typeof User.Type

export class NotFound extends Data.TaggedError("NotFound")<{ readonly id: number }> {}
export class Unauthorized extends Data.TaggedError("Unauthorized")<{ readonly reason: string }> {}

/** A configuration service: a record of a string and a number. */
export class AppConfig extends Context.Service<AppConfig, {
  readonly adminToken: string
  readonly pageSize: number
}>()("app/AppConfig") {}

/** A repository service: a record of one operation, implemented in the program over SQL. */
export class UserRepo extends Context.Service<UserRepo, {
  readonly findById: (id: number) => Effect.Effect<User, NotFound | Schema.SchemaError | SqlErrorT>
}>()("app/UserRepo") {}
type SqlErrorT = import("effect/unstable/sql").SqlError.SqlError

/** The authenticated caller: a service whose value is a record. */
export class CurrentUser extends Context.Service<CurrentUser, User>()("app/CurrentUser") {}

export const AppConfigLive = Layer.effect(AppConfig, Effect.gen(function*() {
  const adminToken = yield* Config.string("ADMIN_TOKEN")
  const pageSize = yield* Config.int("PAGE_SIZE").pipe(Config.withDefault(20))
  return { adminToken, pageSize }
}))

/** The repository captures the client it was built with: `findById` closes over `sql`. */
export const UserRepoLive = Layer.effect(UserRepo, Effect.gen(function*() {
  const sql = yield* SqlClient.SqlClient
  const decode = Schema.decodeUnknownEffect(User)
  return {
    findById: (id: number) =>
      sql`SELECT id, name, role FROM users WHERE id = ${id}`.pipe(
        Effect.flatMap((rows): Effect.Effect<User, NotFound | Schema.SchemaError> => {
          const row = rows[0]
          return row === undefined ? Effect.fail(new NotFound({ id })) : decode(row)
        })
      )
  }
}))

/** Authentication as a requirement transformer: the handler's CurrentUser is discharged, and
 * AppConfig and UserRepo are required instead (provision algebra §5). */
const withAuth = <A, E, R>(token: string, handler: Effect.Effect<A, E, R>) =>
  Effect.gen(function*() {
    const config = yield* AppConfig
    if (token !== config.adminToken) {
      return yield* Effect.fail(new Unauthorized({ reason: "bad token" }))
    }
    const repo = yield* UserRepo
    const me = yield* repo.findById(1)
    return yield* Effect.provideService(handler, CurrentUser, me)
  })

const getProfile = (id: number) =>
  Effect.gen(function*() {
    const me = yield* CurrentUser
    if (me.role !== "admin" && me.id !== id) {
      return yield* Effect.fail(new Unauthorized({ reason: "not yours" }))
    }
    const repo = yield* UserRepo
    return yield* repo.findById(id)
  })

/** A response: a record with a status and a body. */
interface Response {
  readonly status: number
  readonly body: string
}

export const handle = (token: string, id: number) =>
  withAuth(token, getProfile(id)).pipe(
    Effect.map((user): Response => ({ status: 200, body: user.name })),
    Effect.catchTag("NotFound", (e) => Effect.succeed<Response>({ status: 404, body: `no user ${e.id}` })),
    Effect.catchTag("Unauthorized", (e) => Effect.succeed<Response>({ status: 401, body: e.reason }))
  )

/** The graph, provided once. The repository needs the SQL client; the platform supplies it. */
const AppLive = Layer.mergeAll(
  AppConfigLive,
  UserRepoLive.pipe(Layer.provide(SqliteClient.layer({ filename: ":memory:" })))
)

export const main = Effect.provide(handle("secret", 2), AppLive)

/** The checked types, pinned. */
export const pinMain: Effect.Effect<
  Response,
  Schema.SchemaError | SqlErrorT | Config.ConfigError
> = main
