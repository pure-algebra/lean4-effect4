// The red twin of int-twin.ts: Lean's `Schema.Int` transcription with its `arbitrary` annotation
// removed is claimed equal to what the vendored source persists. It must exit 1: the comparison
// sees the ninth key.
import assert from "node:assert/strict"
import { pathToFileURL } from "node:url"
import * as Schema from "effect/Schema"
import * as SR from "effect/SchemaRepresentation"
const { intDoc } = await import(pathToFileURL(process.argv[2]!).href)
const withoutArbitrary = structuredClone(intDoc)
delete withoutArbitrary.representation.checks[0].annotations.arbitrary
assert.deepEqual(withoutArbitrary, SR.toJson(SR.toRepresentation(Schema.Int.ast)))
console.log("UNEXPECTED: the document without arbitrary is rc.112's own Schema.Int")
