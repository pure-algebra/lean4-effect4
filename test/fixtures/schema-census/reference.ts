// Synthetic fixture for `scripts/test-schema-census-gate.sh`.
//
// This is NOT Effect source and is NOT evidence about the rc.112 census. It
// reproduces the two call shapes and the two closed union declarations the
// extractor recognises, so the drift detector can be tested hermetically
// without depending on a node_modules tree that may or may not exist on a
// given machine.
//
// It carries the 22 representation tags and 2 check tags the frozen census
// claims. Mutating it exercises only the named detector reactions; it proves
// nothing about Effect's real source or semantics.

const FilterSchema = Schema.Struct({ _tag: Schema.tag("Filter") })
const FilterGroupSchema = Schema.Struct({ _tag: Schema.tag("FilterGroup") })
const CheckUnion = Schema.Union([FilterSchema, FilterGroupSchema])

const DeclarationSchema = Schema.Struct({ _tag: Schema.tag("Declaration") })
const SuspendSchema = Schema.Struct({ _tag: Schema.tag("Suspend") })
const ReferenceSchema = Schema.Struct({ _tag: Schema.tag("Reference") })
const LiteralSchema = Schema.Struct({ _tag: Schema.tag("Literal") })
const UniqueSymbolSchema = Schema.Struct({ _tag: Schema.tag("UniqueSymbol") })
const EnumSchema = Schema.Struct({ _tag: Schema.tag("Enum") })
const TemplateLiteralSchema = Schema.Struct({ _tag: Schema.tag("TemplateLiteral") })
const ArraysSchema = Schema.Struct({ _tag: Schema.tag("Arrays") })
const ObjectsSchema = Schema.Struct({ _tag: Schema.tag("Objects") })
const UnionSchema = Schema.Struct({ _tag: Schema.tag("Union") })
const SymbolSchema = Schema.Struct({ _tag: Schema.tag("Symbol") })

const RepresentationSchema = Schema.Union([
  makeKeywordSchema("Null"),
  makeKeywordSchema("Undefined"),
  makeKeywordSchema("Void"),
  makeKeywordSchema("Never"),
  makeKeywordSchema("Unknown"),
  makeKeywordSchema("Any"),
  makeKeywordSchema("String"),
  makeKeywordSchema("Number"),
  makeKeywordSchema("Boolean"),
  makeKeywordSchema("BigInt"),
  makeKeywordSchema("ObjectKeyword")
])

// The closed type unions. These are the authoritative, exhaustive route: a
// 23rd persisted member cannot exist without appearing here.

export type Representation =
  | Declaration
  | Reference
  | Suspend
  | Null
  | Undefined
  | Void
  | Never
  | Unknown
  | Any
  | String
  | Number
  | Boolean
  | BigInt
  | Symbol
  | Literal
  | UniqueSymbol
  | ObjectKeyword
  | Enum
  | TemplateLiteral
  | Arrays
  | Objects
  | Union

export type Check = Filter | FilterGroup
