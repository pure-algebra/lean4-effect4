// Seat W1, the host twin of E4-SCHEMA-CE-061 (rc.112 under bun). Green: Lean's Exit and Cause
// documents, as the production Bridge.schema writes them after row 128's commit, revive in rc.112
// with its own revivers, persist as rc.112's own Exit/Cause modulo annotations (N_S), and encode a
// value as rc.112's own schema does. Red: the Exit document with the defect id before the commit
// (effect/schema/Defect) does not revive.
import assert from "node:assert/strict"
import { pathToFileURL } from "node:url"
import { Cause, Exit, Schema, SchemaRepresentation as SR } from "effect"
import effectPackage from "effect/package.json"

assert.equal(effectPackage.version, "4.0.0-rc.112")
const input = process.argv[2]
if (!input) throw new Error("expected the module EmitDefectDocs.lean wrote")
const { exitDoc, causeDoc, exitDocBefore } = await import(pathToFileURL(input).href)

const revivers = [Schema.ExitReviver, Schema.CauseReviver, Schema.JsonReviver]
const revive = (doc: any): any => SR.fromRepresentation(SR.fromJson(doc), { revivers })
// every annotation rc.112 writes on these documents is `expected`, a documentation key (row 179)
const stripAnnotations = (j: any): any =>
  j === null || typeof j !== "object" ? j :
  Array.isArray(j) ? j.map(stripAnnotations) :
  Object.fromEntries(Object.entries(j).filter(([k]) => k !== "annotations")
    .map(([k, v]) => [k, stripAnnotations(v)]))
const persisted = (s: any): any => (SR.toJson(SR.toRepresentation(s.ast)) as any).representation

let checks = 0
const ownExit = Schema.Exit(Schema.Boolean, Schema.String, Schema.Defect())
const ownCause = Schema.Cause(Schema.String, Schema.Defect())

// green 1: Lean's documents revive with rc.112's revivers
const leanExit = revive(exitDoc)
const leanCause = revive(causeDoc)
checks += 2
// green 2: Lean's documents are rc.112's own persisted forms modulo annotations
assert.deepEqual(exitDoc.representation, stripAnnotations(persisted(ownExit)), "Exit document differs")
assert.deepEqual(causeDoc.representation, stripAnnotations(persisted(ownCause)), "Cause document differs")
checks += 2
// green 3: the revived schemas encode a value as rc.112's own do (success and a failing cause)
const cause = Cause.fromReasons([Cause.makeFailReason("bad"), Cause.makeDieReason({ user: 7 })])
for (const value of [Exit.succeed(true), Exit.failCause(cause)]) {
  assert.deepEqual(Schema.encodeSync(Schema.toCodecJson(leanExit))(value),
    Schema.encodeSync(Schema.toCodecJson(ownExit))(value), "Exit encoding differs")
  checks++
}
assert.deepEqual(Schema.encodeSync(Schema.toCodecJson(leanCause))(cause),
  Schema.encodeSync(Schema.toCodecJson(ownCause))(cause), "Cause encoding differs")
checks++
// red: the defect id before the commit does not revive
assert.throws(() => revive(exitDocBefore), /Missing reviver for effect\/schema\/Defect/)
checks++
console.log(`PASS defect-twin: ${checks} checks (2 revivals, 2 persisted forms modulo annotations, 3 encodings, 1 red)`)
