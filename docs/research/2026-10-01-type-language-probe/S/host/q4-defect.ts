// Seat S, question 4 (a finding of route U): what rc.112 persists for Exit and Cause, against the
// `Declaration("effect/schema/Defect")` that Lean's `Bridge.defectRep` writes in their defect slot.
import * as Schema from "effect/Schema"
import * as SR from "effect/SchemaRepresentation"
const show = (s: any) => JSON.stringify((SR.toJson(SR.toRepresentation(s.ast)) as any).representation)
const exit = Schema.Exit(Schema.Number, Schema.String, Schema.Defect())
const cause = Schema.Cause(Schema.String, Schema.Defect())
console.log("DEFECT " + show(Schema.Defect()))
console.log("EXIT " + show(exit))
console.log("CAUSE " + show(cause))
const ids = (j: any): string[] => j === null || typeof j !== "object" ? [] :
  Array.isArray(j) ? j.flatMap(ids) :
  [...(j._tag === "Declaration" ? [j.representation.id] : []), ...Object.values(j).flatMap(ids)]
const exitIds = ids(JSON.parse(show(exit)))
console.log("EXIT declaration ids " + JSON.stringify(exitIds))
if (exitIds.includes("effect/schema/Defect")) { console.log("UNEXPECTED: rc.112 writes a Defect declaration"); (globalThis as any).process.exit(1) }
console.log("ok: rc.112 has no effect/schema/Defect declaration; its defect slot persists as " + show(Schema.Defect()).slice(0, 80))
