import { ada, PersonSchema, PersonSchemaJson, prototypeData } from "./Person.generated.ts"
import type { JsonObject } from "effect/Schema"

if (PersonSchema.representation._tag !== "Objects") {
  throw new Error("generated document did not revive as an Objects representation")
}

if (PersonSchema.representation.propertySignatures.length !== 2) {
  throw new Error("generated document lost a property signature")
}

if (typeof PersonSchemaJson !== "object" || PersonSchemaJson === null ||
    Array.isArray(PersonSchemaJson)) {
  throw new Error("generated raw document is not a JSON object")
}

if (typeof ada !== "object" || ada === null || Array.isArray(ada)) {
  throw new Error("generated associated data is not an object")
}

const adaObject = ada as JsonObject
if (adaObject["name"] !== "Ada" || adaObject["active"] !== true) {
  throw new Error("generated associated data changed")
}

if (typeof prototypeData !== "object" || prototypeData === null ||
    Array.isArray(prototypeData) ||
    !Object.hasOwn(prototypeData, "__proto__") ||
    (prototypeData as JsonObject)["__proto__"] !== "data") {
  throw new Error("generated __proto__ data did not remain an own property")
}

console.log("schema-generation-runtime: ok")
