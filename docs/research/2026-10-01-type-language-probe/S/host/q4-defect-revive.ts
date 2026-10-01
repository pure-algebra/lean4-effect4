// Seat S, question 4: can rc.112 revive its own persisted Exit, and Lean's with the Json id?
import * as Schema from "effect/Schema"
import * as SR from "effect/SchemaRepresentation"
const exit = Schema.Exit(Schema.Number, Schema.String, Schema.Defect())
const doc = SR.fromJson(SR.toJson(SR.toRepresentation(exit.ast)))
const try_ = (f: () => unknown) => { try { f(); return "ok" } catch (e: any) { return String(e?.message ?? e).split("\n")[0] } }
const revivers: any[] = [Schema.ExitReviver, Schema.CauseReviver]
console.log("rc.112's own Exit with [ExitReviver, CauseReviver]: " + try_(() => SR.fromRepresentation(doc, { revivers })))
const withJson = (Schema as any).JsonReviver
console.log("JsonReviver exported: " + (withJson !== undefined))
if (withJson) console.log("with JsonReviver: " + try_(() => SR.fromRepresentation(doc, { revivers: [...revivers, withJson] })))
