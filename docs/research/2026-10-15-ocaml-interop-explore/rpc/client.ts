// Effect's own RpcClient against an OCaml server (effect_rpc.ml), over two channels: a raw TCP
// socket with NDJSON framing, and HTTP with JSON. The program and the RPC group are the same;
// only the layer under them changes.
//
// Exploration probe (2026-10-15), effect 4.0.0-rc.112 under bun.

import { Effect, Layer, Queue, Schema } from "effect"
import { FetchHttpClient } from "effect/unstable/http"
import { Rpc, RpcClient, RpcGroup, RpcSerialization } from "effect/unstable/rpc"
import { Socket } from "effect/unstable/socket"
import * as Net from "node:net"

// The rows, as an RPC group: each row is one Rpc with its payload, success and error schemas.
const Todo = Schema.Struct({ id: Schema.Int, title: Schema.String, done: Schema.Boolean })
class SqlError extends Schema.TaggedError<SqlError>()("SqlError", { message: Schema.String }) {}

class TodoRpcs extends RpcGroup.make(
  Rpc.make("insert", { payload: Schema.String, success: Todo, error: SqlError }),
  Rpc.make("all", { payload: Schema.Null, success: Schema.Array(Todo), error: SqlError }),
  Rpc.make("setDone", { payload: Schema.Tuple([Schema.Int, Schema.Boolean]), success: Schema.NullOr(Todo), error: SqlError }),
  Rpc.make("delete", { payload: Schema.Int, success: Schema.Boolean, error: SqlError }),
  Rpc.make("echoAfter", { payload: Schema.Tuple([Schema.Int, Schema.String]), success: Schema.String })
) {}

// The lowest primitive Effect needs: a Socket is "run a handler on each chunk" and "a writer".
// Here it is a node:net TCP connection.
const netSocket = (port: number) =>
  Effect.gen(function*() {
    const conn = Net.createConnection({ host: "127.0.0.1", port })
    const chunks = yield* Queue.unbounded<Uint8Array | null>()
    conn.on("data", (b: Buffer) => Queue.offerUnsafe(chunks, new Uint8Array(b)))
    conn.on("close", () => Queue.offerUnsafe(chunks, null))
    yield* Effect.callback<void>((resume) => {
      conn.once("connect", () => resume(Effect.void))
    })
    return Socket.make({
      runRaw: (handler, options) =>
        Effect.gen(function*() {
          if (options?.onOpen) yield* options.onOpen
          while (true) {
            const chunk = yield* Queue.take(chunks)
            if (chunk === null) return
            const result = handler(chunk)
            if (Effect.isEffect(result)) yield* result
          }
        }),
      writer: Effect.succeed((chunk) =>
        Effect.sync(() => {
          if (typeof chunk === "string" || chunk instanceof Uint8Array) conn.write(chunk)
          else conn.end()
        })
      )
    })
  })

const socketPort = Number(process.argv[2] ?? 8475)
const httpPort = Number(process.argv[3] ?? 8476)

// Two layers of one protocol: the transport and its framing are the only difference.
const overSocket = RpcClient.layerProtocolSocket().pipe(
  Layer.provide(Layer.effect(Socket.Socket, netSocket(socketPort))),
  Layer.provide(RpcSerialization.layerNdjson)
)
const overHttp = RpcClient.layerProtocolHttp({ url: `http://127.0.0.1:${httpPort}/` }).pipe(
  Layer.provide(FetchHttpClient.layer),
  Layer.provide(RpcSerialization.layerJson)
)

const program = (channel: string) =>
  Effect.gen(function*() {
    const client = yield* RpcClient.make(TodoRpcs)
    const out: Array<[string, unknown]> = []
    const note = (label: string, value: unknown) => {
      out.push([label, value])
      console.log(`[${channel}] ${label.padEnd(40)} ${JSON.stringify(value)}`)
    }
    note("insert('milk')", yield* client.insert("milk"))
    note("insert('tea')", yield* client.insert("tea"))
    note("setDone([1, true])", yield* client.setDone([1, true]))
    // Two calls in flight at once. Over the socket they share one connection, and the answers
    // come back in the order they finish, matched by request id.
    const finished: Array<string> = []
    const both = yield* Effect.all(
      [
        client.echoAfter([300, "slow"]).pipe(Effect.tap((s) => Effect.sync(() => finished.push(s)))),
        client.echoAfter([20, "fast"]).pipe(Effect.tap((s) => Effect.sync(() => finished.push(s))))
      ],
      { concurrency: "unbounded" }
    )
    note("echoAfter slow and fast, in parallel", both)
    note("the order they finished", finished)
    // A failure from the host travels as Exit(Failure(Fail(error))) and comes back typed.
    const failed = yield* Effect.flip(client.insert("boom"))
    note("insert('boom') fails with SqlError", failed instanceof SqlError ? failed.message : String(failed))
    // An interrupted call: the client sends Interrupt for its id, when the channel can carry it.
    const timedOut = yield* client.echoAfter([2000, "never"]).pipe(Effect.timeout("150 millis"), Effect.flip)
    note("echoAfter 2000 ms, timed out at 150 ms", String(timedOut).split("\n")[0])
    note("delete(2)", yield* client.delete(2))
    note("all(null)", yield* client.all(null))
    return out
  }).pipe(Effect.scoped)

const main = Effect.gen(function*() {
  const a = yield* program("socket").pipe(Effect.provide(overSocket))
  const b = yield* program("http").pipe(Effect.provide(overHttp))
  const same = JSON.stringify(a) === JSON.stringify(b)
  console.log(same ? "THE TWO CHANNELS ANSWER ALIKE" : "THE CHANNELS DIFFER (see above)")
})

Effect.runPromise(main).then(
  () => process.exit(0),
  (e) => {
    console.error("FAILED", e)
    process.exit(1)
  }
)
