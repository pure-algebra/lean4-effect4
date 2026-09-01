import { AllRepresentationsSchema } from "./AllRepresentations.generated.ts"

const expectedTags = [
  "Declaration", "Reference", "Suspend", "Null", "Undefined", "Void",
  "Never", "Unknown", "Any", "String", "Number", "Boolean", "BigInt",
  "Symbol", "Literal", "UniqueSymbol", "ObjectKeyword", "Enum",
  "TemplateLiteral", "Arrays", "Objects", "Union"
] as const

const actualTags = Object.entries(AllRepresentationsSchema.references)
  .filter(([key]) => key.startsWith("case/"))
  .map(([, representation]) => representation._tag)

if (actualTags.length !== expectedTags.length ||
    actualTags.some((tag, index) => tag !== expectedTags[index])) {
  throw new Error(`representation coverage drift: ${JSON.stringify(actualTags)}`)
}

const declaration = AllRepresentationsSchema.references["case/Declaration"]
if (declaration?._tag !== "Declaration" || declaration.checks.length !== 2 ||
    declaration.checks[0]?._tag !== "Filter" ||
    declaration.checks[1]?._tag !== "FilterGroup") {
  throw new Error("check constructor coverage drift")
}

console.log("schema-generation-coverage: 22 representations, 2 checks")
