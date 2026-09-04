/-
Executable witnesses for `E4-SURFACE-CE-006`, `E4-SURFACE-CE-007` and
`E4-SURFACE-CE-008`.

Contract: `test/contracts/surface-jsonschema.contract.md`. Frozen by the
wave-1b breaker before `Effect4/Surface/JsonSchema.lean` exists; red until the
builder lands it.
-/

import Effect4Test.Surface.Fixtures
import Effect4.Data.Json

set_option autoImplicit false

namespace Effect4Test.Counterexamples.Surface.JsonSchema

open Effect4 (Json Representation)
open Effect4.Surface
open Effect4Test.Surface.Fixtures
open Effect4.Schema (struct property string number)

/--
`E4-SURFACE-CE-006`. Attacked statement: "`toJsonSchema` and `ofJsonSchema`
round-trip a representation", stated without a quotient. They do not: the JSON
Schema fragment rc.112 emits carries `description` and `title` and drops every
other annotation, so the composite is the identity only up to
`annotationErasure`. An unnamed quotient is the failure mode that makes a
"round trip" receipt vacuous, because whatever the pair happens to do becomes
the definition.

There is a second, sharper half. A persisted check the fragment *can* express
(`Check.pattern`, which is the JSON Schema `pattern` keyword) has to survive
the trip; one it cannot express (`Check.trimmed` has no draft 2020-12
spelling) must make the forward direction answer `none`, because dropping it
would emit a schema that accepts values the representation refuses.

Forced repair: `annotationErasure` is a declared function, the quotient is
stated in `ofJsonSchema_toJsonSchema` against it and not against `Eq`, and an
inexpressible check is a `none`, never a silent drop.
-/
def annotatedUserId : Representation :=
  (Effect4.Schema.withChecks? [Effect4.Schema.Check.pattern "^[a-z]+$"] string).getD string

/-- The same representation carrying a check the fragment cannot spell. -/
def unspellableCheck : Representation :=
  (Effect4.Schema.withChecks? [Effect4.Schema.Check.trimmed] string).getD string

-- The expressible check survives; the erasure is not "drop every check".
#guard (toJsonSchema shopRefs annotatedUserId).bind (fun j => (ofJsonSchema j).toOption)
  = some (annotationErasure annotatedUserId)
#guard annotationErasure annotatedUserId = annotatedUserId
-- The inexpressible one refuses rather than emitting a weaker schema.
#guard (toJsonSchema shopRefs unspellableCheck).isNone
-- And the quotient is not the identity, so naming it is not decoration.
#guard (toJsonSchema shopRefs userRep).bind (fun j => (ofJsonSchema j).toOption)
  = some (annotationErasure userRep)

/--
`E4-SURFACE-CE-007`. Attacked statement: "a `$ref` names an entry of the
document's `$defs`". Draft 2020-12 `$ref` is a URI reference: it may point at
`#/definitions/...`, at a sibling pointer, at another document or at a remote
URL. A decoder that strips a `#/$defs/` prefix and takes the remainder as an
entity name turns `#/definitions/User` into the entity `definitions/User`, or
worse takes a remote URL as a local key.

Forced repair: `ofJsonSchema` refuses every pointer that is not exactly
`#/$defs/<segment>` with `Refusal.unsupportedRefTarget` carrying the pointer
verbatim. No base URI is resolved and no remote document is fetched.
-/
def foreignPointers : List String :=
  [ "#/definitions/User", "#/components/schemas/User", "https://example.com/User.json"
  , "User.json#/$defs/User", "#/$defs/User/properties/id", "#" ]

#guard foreignPointers.all
  (fun p => ofJsonSchema (.obj [("$ref", .str p)]) == .error (.unsupportedRefTarget p))
#guard ofJsonSchema (.obj [("$ref", .str "#/$defs/User")]) = .ok (Effect4.Schema.reference "User")

/--
`E4-SURFACE-CE-008`. Attacked statement: "the decoder reads the keywords it
models and ignores the rest". Ignoring is the defect: a schema with
`contentEncoding: base64`, `patternProperties`, `if`/`then`, `not`,
`unevaluatedProperties` or `additionalProperties: {…}` describes a *smaller*
or *different* set of values than the keywords the fragment reads, so the
decoded representation is not the source schema. The row then carries
`stance := .ingested` and looks like a faithful model of a resource it does not
model.

Forced repair: an object carrying any keyword outside the fragment is refused
with `Refusal.unknownKeyword` naming that keyword, and the refusal is not
suppressed because the sibling keywords parsed.
-/
def unmodeledKeywords : List (String × Json) :=
  [ ("contentEncoding", .str "base64")
  , ("patternProperties", .obj [])
  , ("not", .obj [])
  , ("unevaluatedProperties", .bool false)
  , ("dependentRequired", .obj [])
  , ("$dynamicRef", .str "#meta") ]

#guard unmodeledKeywords.all
  (fun kv => ofJsonSchema (.obj [("type", .str "string"), kv]) == .error (.unknownKeyword kv.1))
-- The same object without the unmodeled keyword decodes, so the refusal is
-- caused by the keyword and not by the shape.
#guard ofJsonSchema (.obj [("type", .str "string")]) = .ok string
-- `if` without `then` is refused on the first unmodeled keyword it meets.
#guard ofJsonSchema (.obj [("if", .obj []), ("then", .obj [])]) = .error (.unknownKeyword "if")

end Effect4Test.Counterexamples.Surface.JsonSchema
