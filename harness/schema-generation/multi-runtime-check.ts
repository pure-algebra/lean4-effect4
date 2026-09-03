import * as SchemaRepresentation from "effect/SchemaRepresentation"
import { TwoRootsSchemaJson } from "./TwoRoots.generated.ts"

const multi = SchemaRepresentation.fromJsonMultiDocument(TwoRootsSchemaJson)

if (multi.representations.length !== 2) {
  throw new Error("generated multi-document lost a root")
}

if (multi.representations[0]?._tag !== "String" ||
    multi.representations[1]?._tag !== "Boolean") {
  throw new Error(`multi-document root order drift: ${JSON.stringify(
    multi.representations.map((representation) => representation._tag))}`)
}

const shared = multi.references["shared"]
if (shared?._tag !== "Number") {
  throw new Error("generated multi-document lost its shared reference")
}

if (Object.keys(multi.references).length !== 1) {
  throw new Error("generated multi-document references table changed size")
}

console.log("schema-generation-multi: 2 roots, 1 shared reference")
