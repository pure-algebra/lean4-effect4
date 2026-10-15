// Vendor Effect's RPC wire alphabet as data: every schema the protocol uses, written as rc.112's
// own SchemaRepresentation JSON, plus the serialization descriptors. Nothing is transcribed by
// hand; Lean reads this file (Alphabet.lean).
//
// Exploration probe (2026-10-15), effect 4.0.0-rc.112 under bun.
// Usage: bun --no-install run export.ts > vendored/effect-rpc-rc112.json

import { Schema, SchemaRepresentation } from "effect"
import { Rpc, RpcGroup, RpcMessage, RpcSerialization } from "effect/unstable/rpc"

const rep = (schema: Schema.Top) => SchemaRepresentation.toJson(SchemaRepresentation.toRepresentation(schema.ast))

// The to-do rows, as the hand-written client (../rpc/client.ts) declares them.
const Todo = Schema.Struct({ id: Schema.Int, title: Schema.String, done: Schema.Boolean })
class SqlError extends Schema.TaggedError<SqlError>()("SqlError", { message: Schema.String }) {}
const TodoRpcs = RpcGroup.make(
  Rpc.make("insert", { payload: Schema.String, success: Todo, error: SqlError }),
  Rpc.make("all", { payload: Schema.Null, success: Schema.Array(Todo), error: SqlError }),
  Rpc.make("setDone", { payload: Schema.Tuple([Schema.Int, Schema.Boolean]), success: Schema.NullOr(Todo), error: SqlError }),
  Rpc.make("delete", { payload: Schema.Int, success: Schema.Boolean, error: SqlError })
)

const rpcs = [...TodoRpcs.requests.values()].map((rpc) => ({
  tag: rpc._tag,
  payload: rep(rpc.payloadSchema),
  success: rep(rpc.successSchema),
  error: rep(rpc.errorSchema),
  exit: rep(Rpc.exitSchema(rpc))
}))

const serialization = (name: string, s: RpcSerialization.RpcSerialization["Service"]) => ({
  name,
  contentType: s.contentType,
  includesFraming: s.includesFraming
})

console.log(JSON.stringify(
  {
    source: "effect 4.0.0-rc.112: src/unstable/rpc/RpcMessage.ts (EncodedSchema), src/unstable/rpc/Rpc.ts (exitSchema), src/unstable/rpc/RpcSerialization.ts",
    envelope: rep(RpcMessage.EncodedSchema),
    rpcs,
    serializations: [
      serialization("json", RpcSerialization.json),
      serialization("ndjson", RpcSerialization.ndjson),
      serialization("jsonRpc", RpcSerialization.jsonRpc()),
      serialization("ndJsonRpc", RpcSerialization.ndJsonRpc()),
      serialization("msgPack", RpcSerialization.msgPack)
    ]
  },
  null,
  1
))
