/-
Contract: `Test/contracts/surface-jsonschema.contract.md`.

Frozen by the wave-1b breaker before `src/Effect4/Codegen/JsonSchema.lean` exists,
from `docs/research/2026-09-04-surface-library-plan.md` §4.3 alone. Red until
the builder lands the module.

The pair is not an isomorphism. The forward direction is pinned against
literal `Json` terms so a key spelling, a key order or a missing `$defs` entry
fails here; the backward direction is pinned against `.ok` and against exact
`.error` constructors. The quotient the round trip is taken modulo is
`annotationErasure`, and the battery states it rather than hiding it behind an
`isSome`.
-/

import Test.Surface.Fixtures
import Effect4.Data.Json

set_option autoImplicit false

namespace Test.Surface.JsonSchemaContract

open Effect4 (Representation Json)
open Effect4.Surface
open Test.Surface.Fixtures
open Effect4.Schema (struct property string number boolean array anyOf literalString reference)

/-! ## The forward direction, pinned to literal JSON -/

#guard toJsonSchema shopRefs string = some (.obj [("type", .str "string")])
#guard toJsonSchema shopRefs number = some (.obj [("type", .str "number")])
#guard toJsonSchema shopRefs boolean = some (.obj [("type", .str "boolean")])
#guard toJsonSchema shopRefs (array string) =
  some (.obj [("type", .str "array"), ("items", .obj [("type", .str "string")])])
#guard toJsonSchema shopRefs (literalString "admin") =
  some (.obj [("type", .str "string"), ("enum", .arr [.str "admin"])])
#guard toJsonSchema shopRefs (reference "User") =
  some (.obj [("$ref", .str "#/$defs/User")])
#guard toJsonSchema shopRefs userIdRep =
  some (.obj
    [ ("type", .str "object")
    , ("properties", .obj [("id", .obj [("type", .str "string")])])
    , ("required", .arr [.str "id"]) ])
-- The optional property is absent from `required` and present in `properties`.
#guard toJsonSchema shopRefs newUserRep =
  some (.obj
    [ ("type", .str "object")
    , ("properties", .obj
        [ ("name", .obj [("type", .str "string")])
        , ("email", .obj [("type", .str "string")]) ])
    , ("required", .arr [.str "name"]) ])

#guard (toJsonSchema shopRefs userRep).isSome
#guard (documentJsonSchema (Entity.document shop userEntity)).isSome
#guard (documentJsonSchema (Domain.doc shop)).isSome

-- No JSON inhabitant, no JSON Schema.
#guard (toJsonSchema shopRefs Effect4.Schema.bigint).isNone
#guard (toJsonSchema shopRefs Effect4.Schema.undefined).isNone
#guard (toJsonSchema shopRefs Effect4.Schema.symbol).isNone
-- A reference with no entry has no `$defs` target.
#guard (toJsonSchema shopRefs (reference "Warehouse")).isNone

/-! ## The backward direction -/

#guard ofJsonSchema (.obj [("type", .str "string")]) = .ok string
#guard ofJsonSchema (.obj [("type", .str "number")]) = .ok number
#guard ofJsonSchema (.obj [("type", .str "boolean")]) = .ok boolean
#guard ofJsonSchema (.obj [("type", .str "array"), ("items", .obj [("type", .str "string")])])
  = .ok (array string)
#guard ofJsonSchema (.obj [("$ref", .str "#/$defs/User")]) = .ok (reference "User")
#guard ofJsonSchema
  (.obj
    [ ("type", .str "object")
    , ("properties", .obj [("id", .obj [("type", .str "string")])])
    , ("required", .arr [.str "id"]) ]) = .ok userIdRep

-- `E4-SURFACE-CE-007`: a pointer outside `#/$defs/` is refused by name, never
-- resolved against a base URI, a sibling pointer or a remote document.
#guard ofJsonSchema (.obj [("$ref", .str "#/definitions/User")])
  = .error (.unsupportedRefTarget "#/definitions/User")
#guard ofJsonSchema (.obj [("$ref", .str "https://example.com/User.json")])
  = .error (.unsupportedRefTarget "https://example.com/User.json")

-- `E4-SURFACE-CE-008`: an unmodeled keyword is refused with the keyword inside
-- the constructor. It is not ignored because the sibling keywords parsed.
#guard ofJsonSchema (.obj [("type", .str "string"), ("contentEncoding", .str "base64")])
  = .error (.unknownKeyword "contentEncoding")
#guard ofJsonSchema (.obj [("type", .str "object"), ("patternProperties", .obj [])])
  = .error (.unknownKeyword "patternProperties")
#guard ofJsonSchema (.obj [("if", .obj []), ("then", .obj [])]) = .error (.unknownKeyword "if")

/-! ## The round trip, and the quotient it is taken modulo

`annotationErasure` is the exact information the fragment drops: every
annotation payload except the `description` and `title` the fragment carries as
keys. A persisted check the fragment cannot express makes the forward direction
answer `none`; it is never dropped silently. -/

#guard annotationErasure string = string
#guard annotationErasure userIdRep = userIdRep
#guard annotationErasure newUserRep = newUserRep

#guard (toJsonSchema shopRefs userIdRep).bind (fun j => (ofJsonSchema j).toOption)
  = some (annotationErasure userIdRep)
#guard (toJsonSchema shopRefs newUserRep).bind (fun j => (ofJsonSchema j).toOption)
  = some (annotationErasure newUserRep)
#guard (toJsonSchema shopRefs addressRep).bind (fun j => (ofJsonSchema j).toOption)
  = some (annotationErasure addressRep)
#guard (toJsonSchema shopRefs userRep).bind (fun j => (ofJsonSchema j).toOption)
  = some (annotationErasure userRep)
#guard (toJsonSchema shopRefs notFoundRep).bind (fun j => (ofJsonSchema j).toOption)
  = some (annotationErasure notFoundRep)

theorem user_round_trip :
    ∀ j, toJsonSchema shopRefs userRep = some j → ofJsonSchema j = .ok (annotationErasure userRep) :=
  fun j h => ofJsonSchema_toJsonSchema shopRefs userRep j (by decide) h

end Test.Surface.JsonSchemaContract
