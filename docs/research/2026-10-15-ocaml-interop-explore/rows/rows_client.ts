// One Effect client for every row table: the service is built at run time from the table a
// host serves as data (GET /rows), and each method calls POST /rows/<spelling>.
//
// Exploration probe (2026-10-15), effect 4.0.0-rc.112 under bun. The OCaml half is
// transport.ml. Nothing here names a row.

import { Context, Effect, Schema } from "effect"
import { HttpClient, HttpClientRequest } from "effect/unstable/http"

type TyJson =
  | "unit" | "nat" | "int" | "string" | "bool"
  | { list: TyJson } | { option: TyJson } | { prod: [TyJson, TyJson] } | { record: Array<[string, TyJson]> }
  | { tagged: Array<[string] | [string, TyJson]> }

interface RowJson { spelling: string; request: TyJson; answer: TyJson; error: TyJson }

// The row type language, read into Effect Schema: one fold over the description.
const schemaOf = (t: TyJson): Schema.Top => {
  if (t === "unit") return Schema.Null
  if (t === "nat") return Schema.Int.pipe(Schema.check(Schema.isGreaterThanOrEqualTo(0)))
  if (t === "int") return Schema.Int
  if (t === "string") return Schema.String
  if (t === "bool") return Schema.Boolean
  if ("list" in t) return Schema.Array(schemaOf(t.list))
  if ("option" in t) return Schema.NullOr(schemaOf(t.option))
  if ("prod" in t) return Schema.Tuple([schemaOf(t.prod[0]), schemaOf(t.prod[1])])
  if ("tagged" in t) {
    return Schema.Union(t.tagged.map(([tag, payload]) =>
      payload === undefined
        ? Schema.Struct({ _tag: Schema.Literal(tag) })
        : Schema.Struct({ _tag: Schema.Literal(tag), value: schemaOf(payload) })
    ))
  }
  return Schema.Struct(Object.fromEntries(t.record.map(([n, f]) => [n, schemaOf(f)])))
}

// A completion as the transport sends it.
const completionOf = (row: RowJson) =>
  Schema.Union([
    Schema.Struct({ _tag: Schema.Literal("Success"), value: schemaOf(row.answer) }),
    Schema.Struct({ _tag: Schema.Literal("Failure"), error: schemaOf(row.error) })
  ])

export class RowFailure extends Schema.TaggedError<RowFailure>()("RowFailure", {
  row: Schema.String,
  error: Schema.Unknown
}) {}

// The service: one method per row, keyed by the method's name in its namespace.
type Methods = Record<string, (request: unknown) => Effect.Effect<unknown, unknown>>
export class Rows extends Context.Service<Rows, Record<string, Methods>>()("explore/Rows") {}

// A transport: how the table is read and how one call travels. The service does not depend on
// which one it is; each is a layer under the same `Rows`.
export interface Transport {
  readonly name: string
  readonly table: Effect.Effect<Array<RowJson>, unknown>
  readonly call: (spelling: string, body: unknown) => Effect.Effect<unknown, unknown>
}

// Over HTTP: GET /rows and POST /rows/<spelling> (transport.ml's edge).
export const httpTransport = (baseUrl: string) =>
  Effect.gen(function*() {
    const http = yield* HttpClient.HttpClient
    return {
      name: `http ${baseUrl}`,
      table: Effect.flatMap(http.get(`${baseUrl}/rows`), (r) => r.json) as Effect.Effect<Array<RowJson>, unknown>,
      call: (spelling, body) =>
        Effect.flatMap(
          http.execute(HttpClientRequest.post(`${baseUrl}/rows/${spelling}`).pipe(HttpClientRequest.bodyJsonUnsafe(body))),
          (r) => r.json
        )
    } satisfies Transport
  })

// In process: a host compiled to JavaScript that answers `table()` and `call(spelling, json)`.
export const inProcessTransport = (
  name: string,
  host: { table(): string; call(spelling: string, request: string): string | null }
): Transport => ({
  name,
  table: Effect.sync(() => JSON.parse(host.table()) as Array<RowJson>),
  call: (spelling, body) =>
    Effect.sync(() => {
      const out = host.call(spelling, JSON.stringify(body))
      return out === null ? { _tag: "NoAnswer" } : JSON.parse(out)
    })
})

// Build the service from a transport's table: one method per row.
export const buildRowsOver = (transport: Transport) => Effect.gen(function*() {
  const table = yield* transport.table
  const services: Record<string, Methods> = {}
  for (const row of table) {
    const [ns, method] = row.spelling.split(".")
    const encodeRequest = Schema.encodeUnknownEffect(schemaOf(row.request))
    const decodeCompletion = Schema.decodeUnknownEffect(completionOf(row))
    ;(services[ns] ??= {})[method] = (request: unknown) =>
      Effect.gen(function*() {
        const body = yield* encodeRequest(request)
        const completion = (yield* decodeCompletion(yield* transport.call(row.spelling, body))) as
          | { _tag: "Success"; value: unknown }
          | { _tag: "Failure"; error: unknown }
        if (completion._tag === "Failure") return yield* new RowFailure({ row: row.spelling, error: completion.error })
        return completion.value
      })
  }
  console.log(`[${transport.name}] built ${table.length} methods: ${table.slice(0, 6).map((r) => r.spelling).join(", ")}${table.length > 6 ? ", ..." : ""}`)
  return Rows.of(services)
})

// The HTTP case, as before.
export const buildRows = (baseUrl: string) => Effect.flatMap(httpTransport(baseUrl), buildRowsOver)
