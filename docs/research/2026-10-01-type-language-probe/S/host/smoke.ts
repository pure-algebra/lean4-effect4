import * as Schema from "effect/Schema"
import * as SR from "effect/SchemaRepresentation"
const S = Schema.Struct({ a: Schema.Number })
console.log(JSON.stringify(Schema.decodeUnknownSync(S)({ a: 1, b: 2 })))
console.log(JSON.stringify(SR.toJson(SR.toRepresentation(S.ast))))
console.log(import.meta.resolve("effect/Schema"))
