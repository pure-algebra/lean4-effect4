// Seat S, question 5: the meta-schema module without and with (C), revived by rc.112 (bun, vendored).
import * as Raw from "./meta-raw.ts"
import * as Deduped from "./meta-deduped.ts"
import * as SR from "effect/SchemaRepresentation"
const keys = (j: any) => Object.keys(j.references)
console.log(`raw JSON object keys: ${keys(Raw.MetaSchemaJson).length}; deduped: ${keys(Deduped.MetaSchemaJson).length}`)
const same = JSON.stringify(SR.toJson(Raw.MetaSchema)) === JSON.stringify(SR.toJson(Deduped.MetaSchema))
console.log(`the two revived documents are equal: ${same}`)
if (!same) (globalThis as any).process.exit(1)
