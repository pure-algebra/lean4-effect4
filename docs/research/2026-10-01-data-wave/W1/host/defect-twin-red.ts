// The red twin of defect-twin.ts: the claim that Lean's document with the defect id before row
// 128's commit revives in rc.112. It must exit 1.
import { pathToFileURL } from "node:url"
import { Schema, SchemaRepresentation as SR } from "effect"
const { exitDocBefore } = await import(pathToFileURL(process.argv[2]!).href)
const revivers = [Schema.ExitReviver, Schema.CauseReviver, Schema.JsonReviver]
SR.fromRepresentation(SR.fromJson(exitDocBefore), { revivers })
console.log("UNEXPECTED: the document with effect/schema/Defect revived")
