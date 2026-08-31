// Synthetic fixture for `scripts/test-schema-fields-gate.sh`.
//
// This is NOT Effect source and is NOT evidence about rc.112 field spellings.
// It reproduces the six declaration shapes the field extractor recognises —
// a bare object literal, a `Schema.Struct` literal, a struct carrying a
// spread, a struct nested inside `Schema.toCodecJson`, and the two helper-made
// struct forms — so the drift detector can be tested hermetically without
// depending on a node_modules tree that may or may not exist on a given
// machine.
//
// Mutating it exercises only the named detector reactions. It proves nothing
// about Effect's real source, its persisted fields, or its semantics.

const KeywordFields = {
  annotations: AnnotationsSchema,
  checks: ChecksSchema
}

function makeKeywordSchema<Tag extends string>(tag: Tag) {
  return Schema.Struct({
    _tag: Schema.tag(tag),
    ...KeywordFields
  })
}

function makeValueSchema<Type extends string, Value>(type: Type, value: Schema.Codec<Value>) {
  return value.pipe(
    Schema.encodeTo(Schema.Struct({ type: Schema.tag(type), value }), {
      decode: passthrough,
      encode: passthrough
    })
  )
}

const RepresentationAnnotationSchema = Schema.Struct({
  id: Schema.NonEmptyString,
  payload: Schema.Json
})

const SuspendSchema = Schema.Struct({
  _tag: Schema.tag("Suspend"),
  annotations: AnnotationsSchema,
  checks: Schema.Tuple([]),
  thunk: RepresentationSchema
})

const UnionSchema = Schema.Struct({
  _tag: Schema.tag("Union"),
  ...KeywordFields,
  types: RepresentationsSchema,
  mode: Schema.Literals(["anyOf", "oneOf"])
})

const DocumentFromJson: Schema.Codec<Document, Schema.Json> = Schema.toCodecJson(
  Schema.Struct({
    representation: RepresentationSchema,
    references: ReferencesSchema
  })
)
