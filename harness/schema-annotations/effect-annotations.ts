import { Schema, SchemaRepresentation } from "effect"

interface CodegenDimension {
  readonly version: 1
  readonly typeName: string
  readonly brand?: string
}

interface AnalysisDimension {
  readonly version: 1
  readonly sensitivity: "public" | "internal" | "secret"
  readonly determinism: "deterministic" | "nondeterministic"
}

declare module "effect/Schema" {
  namespace Annotations {
    interface Annotations {
      readonly "effect4/codegen"?: CodegenDimension | undefined
      readonly "effect4/analysis"?: AnalysisDimension | undefined
      readonly "effect4/property-role"?: string | undefined
    }
  }
}

const withCodegen = (dimension: CodegenDimension) =>
  <S extends Schema.Top>(schema: S): S["Rebuild"] =>
    schema.annotate({ "effect4/codegen": dimension })

const withAnalysis = (dimension: AnalysisDimension) =>
  <S extends Schema.Top>(schema: S): S["Rebuild"] =>
    schema.annotate({ "effect4/analysis": dimension })

const withDimensions = (
  codegen: CodegenDimension,
  analysis: AnalysisDimension
) => <S extends Schema.Top>(schema: S) =>
  schema.pipe(withCodegen(codegen), withAnalysis(analysis))

const UserId = Schema.String.pipe(
  withDimensions(
    { version: 1, typeName: "UserId", brand: "UserId" },
    {
      version: 1,
      sensitivity: "internal",
      determinism: "deterministic"
    }
  ),
  Schema.annotate({
    identifier: "domain/UserId",
    title: "User identifier",
    description: "Stable identity assigned by the identity service",
    examples: ["user_123"]
  })
)

const User = Schema.Struct({
  id: UserId.annotateKey({
    description: "Primary identity lookup key",
    messageMissingKey: "A user identifier is required",
    "effect4/property-role": "identity"
  })
})

const WireUserId = UserId.pipe(
  Schema.annotateEncoded({
    title: "UserId on the wire",
    contentMediaType: "text/plain"
  })
)

const NonEmptyUserId = UserId
  .check(Schema.isMinLength(1))
  .annotate({
    expected: "a non-empty user identifier",
    "effect4/analysis": {
      version: 1,
      sensitivity: "internal",
      determinism: "deterministic"
    }
  })

const resolved = Schema.resolveAnnotations(NonEmptyUserId)
if (resolved?.expected !== "a non-empty user identifier") {
  throw new Error("last-check annotation resolution changed")
}

const keyAnnotations = Schema.resolveAnnotationsKey(User.fields.id)
if (keyAnnotations?.["effect4/property-role"] !== "identity") {
  throw new Error("key-level annotation resolution changed")
}

const document = SchemaRepresentation.toRepresentation(User.ast)
const raw = SchemaRepresentation.toJson(document)
const rendered = JSON.stringify(raw, undefined, 2)
if (!rendered.includes("effect4/codegen") || !rendered.includes("effect4/analysis")) {
  throw new Error("JSON-valued custom annotation dimensions were not persisted")
}

const encodedAnnotations = Schema.resolveAnnotations(Schema.toEncoded(WireUserId))
if (encodedAnnotations?.title !== "UserId on the wire") {
  throw new Error("encoded-side annotations changed")
}

console.log("schema-annotations: typed dimensions, persistence, and resolution passed")
