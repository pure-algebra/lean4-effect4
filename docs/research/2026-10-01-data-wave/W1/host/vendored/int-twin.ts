// Seat W1, the host case of row 179's ninth key (bun, the vendored rc.112 source through
// tsconfig.json's paths). Green: the battery's transcriptions of rc.112's own `Schema.Int` and
// `Schema.Int.check(Schema.isGreaterThanOrEqualTo(0))` documents equal what the vendored source
// persists for them (and `Schema.Natural` persists the second), and Lean's production reader reads
// them as `int` and `nat`.
import assert from "node:assert/strict"
import { pathToFileURL } from "node:url"
import * as Schema from "effect/Schema"
import * as SR from "effect/SchemaRepresentation"

const resolved = import.meta.resolve("effect/Schema")
console.log(`effect/Schema resolves to ${resolved}`)
assert.ok(resolved.endsWith("/vendor/effect-4.0.0-rc.112/src/Schema.ts"), "not the vendored source")
const input = process.argv[2]
if (!input) throw new Error("expected the module EmitIntDocs.lean wrote")
const { intDoc, natDoc, leanReadsInt, leanReadsNat } = await import(pathToFileURL(input).href)

const persisted = (s: any): any => SR.toJson(SR.toRepresentation(s.ast)) as any
let checks = 0
assert.deepEqual(intDoc, persisted(Schema.Int), "Schema.Int's document differs from Lean's transcription")
checks++
assert.deepEqual(natDoc, persisted(Schema.Int.check(Schema.isGreaterThanOrEqualTo(0))),
  "Schema.Int.check(isGreaterThanOrEqualTo(0))'s document differs from Lean's transcription")
checks++
assert.deepEqual(natDoc, persisted(Schema.Natural), "Schema.Natural's document differs")
checks++
assert.equal(leanReadsInt, true, "Lean's reader does not read Schema.Int as int")
assert.equal(leanReadsNat, true, "Lean's reader does not read the nonnegative Int as nat")
checks += 2
console.log(`PASS int-twin: ${checks} checks (3 persisted documents equal Lean's transcriptions, Lean reads int and nat)`)
