/-
Contract: `test/contracts/surface-kind.contract.md`.

Frozen by the wave-1b breaker before `Effect4/Surface/Kind.lean` exists, from
`docs/research/2026-09-04-surface-library-plan.md` §3 alone. Red until the
builder lands the module.

`Kind` is the slot classification and `Sch refs k` the subtype carrying a
kernel-checked equation. The battery is the census: for each of the seven
kinds of plan §13.1 one admitted and one refused representative, the
containment theorems used rather than restated, the fuel frontier separated
from a refusal, and the property-name helper the API contract's law mentions.

Wave 1a lands four kinds and wave 2a extends to seven in place; the three
extension guards are in their own section so the staging is visible.

Everything is inlined in the `#guard`s except the fixture rows, which are
alphabet-only definitions in `Effect4Test/Surface/Fixtures.lean`. Doc comments
cannot precede a `#guard`, so the receipts carry line comments.
-/

import Effect4Test.Surface.Fixtures

set_option autoImplicit false

namespace Effect4Test.Surface.KindContract

open Effect4 (Representation)
open Effect4.Surface
open Effect4Test.Surface.Fixtures
open Effect4.Schema (struct property string number boolean array anyOf literalString
  reference index literalBigInt globalSymbol suspend)

/-! ## `Kind.text`: a flat struct of URL-decodable properties -/

#guard kindCheck shopRefs 64 .text userIdRep = true
#guard kindCheck shopRefs 64 .text addressRep = true
#guard kindCheck shopRefs 64 .text (struct []) = true
#guard kindCheck shopRefs 64 .text (struct [property "n" number, property "b" boolean]) = true
#guard kindCheck shopRefs 64 .text (struct [property "q" string (isOptional := true)]) = true
#guard kindCheck shopRefs 64 .text
  (struct [property "role" (anyOf (literalString "admin") [literalString "member"])]) = true

-- A nested object property is not decodable from URL text: `E4-SURFACE-CE-001`.
#guard kindCheck shopRefs 64 .text (struct [property "nested" addressRep]) = false
-- Neither is an array property.
#guard kindCheck shopRefs 64 .text (struct [property "tags" (array string)]) = false
-- Neither is a reference, even one that resolves.
#guard kindCheck shopRefs 64 .text (struct [property "address" (reference "Address")]) = false
-- The fixture entity carries both, so it is a struct and not a text schema.
#guard kindCheck shopRefs 64 .text userRep = false
-- `text` is a classification of one object node, not of a bare keyword.
#guard kindCheck shopRefs 64 .text string = false

/-! ## `Kind.struct`: string keys, no index signatures -/

#guard kindCheck shopRefs 64 .struct userRep = true
#guard kindCheck shopRefs 64 .struct addressRep = true
#guard kindCheck shopRefs 64 .struct notFoundRep = true
#guard kindCheck shopRefs 64 .struct newUserRep = true
#guard kindCheck shopRefs 64 .struct (struct []) = true

-- An index signature makes the key set unenumerable: `E4-SURFACE-CE-002`.
#guard kindCheck shopRefs 64 .struct (struct [property "id" string] [index string string]) = false
-- A bare keyword is not a struct.
#guard kindCheck shopRefs 64 .struct string = false
#guard kindCheck shopRefs 64 .struct (array string) = false

/-! ## `Kind.json`: JSON-representable, and nothing else -/

#guard kindCheck shopRefs 64 .json userRep = true
#guard kindCheck shopRefs 64 .json (reference "User") = true
#guard kindCheck shopRefs 64 .json (array string) = true
#guard kindCheck shopRefs 64 .json string = true
#guard kindCheck shopRefs 64 .json number = true
#guard kindCheck shopRefs 64 .json boolean = true
#guard kindCheck shopRefs 64 .json (anyOf string [number]) = true
-- The one representation `json` admits and `struct` refuses: an index signature
-- is a JSON object shape, it is only unenumerable as an entity or a parameter set.
#guard kindCheck shopRefs 64 .json (struct [property "id" string] [index string string]) = true

-- No JSON inhabitant: `E4-SURFACE-CE-004`.
#guard kindCheck shopRefs 64 .json Effect4.Schema.undefined = false
#guard kindCheck shopRefs 64 .json Effect4.Schema.bigint = false
#guard kindCheck shopRefs 64 .json Effect4.Schema.symbol = false
#guard kindCheck shopRefs 64 .json (globalSymbol "k") = false
#guard kindCheck shopRefs 64 .json (literalBigInt 1) = false
#guard kindCheck shopRefs 64 .json (Effect4.Representation.templateLiteral none [] [string]) = false
-- Duplicate property keys collapse on the wire and are refused before an emitter sees them.
#guard kindCheck shopRefs 64 .json (struct [property "id" string, property "id" number]) = false

/-! ## `Kind.void`: exactly `Representation.void` -/

#guard kindCheck shopRefs 64 .void Effect4.Schema.void = true
-- `E4-SURFACE-CE-003`: nothing else, not even the other empty-ish keywords.
#guard kindCheck shopRefs 64 .void string = false
#guard kindCheck shopRefs 64 .void Effect4.Schema.null = false
#guard kindCheck shopRefs 64 .void Effect4.Schema.never = false
#guard kindCheck shopRefs 64 .void Effect4.Schema.unknown = false
#guard kindCheck shopRefs 64 .void (struct []) = false
-- `void` is disjoint from the chain: the no-content marker is not a JSON body.
#guard kindCheck shopRefs 64 .json Effect4.Schema.void = false
#guard kindCheck shopRefs 64 .struct Effect4.Schema.void = false
#guard kindCheck shopRefs 64 .text Effect4.Schema.void = false

/-! ## The three expressibility kinds of plan §13.1

`stream`, `multipart` and `urlEncoded` exist so a clause can refuse them by
name. `Effect4.Representation` has no node for any of the three, so each is
an existing set under a new name and the distinction is carried by the
constructor that consumes it. These three equations are the freeze. -/

#guard Kind.all = [.json, .struct, .text, .void, .multipart, .urlEncoded, .stream]
#guard Kind.all.length = 7
#guard (Kind.all.map Kind.name) =
  ["json", "struct", "text", "void", "multipart", "urlEncoded", "stream"]

#guard kindCheck shopRefs 64 .stream (reference "User")
  = kindCheck shopRefs 64 .json (reference "User")
#guard kindCheck shopRefs 64 .stream Effect4.Schema.bigint = false
#guard kindCheck shopRefs 64 .multipart userRep = kindCheck shopRefs 64 .struct userRep
#guard kindCheck shopRefs 64 .multipart (struct [property "id" string] [index string string])
  = false
#guard kindCheck shopRefs 64 .urlEncoded userIdRep = kindCheck shopRefs 64 .text userIdRep
#guard kindCheck shopRefs 64 .urlEncoded userRep = false

/-! ## Fuel is a frontier of the check, not a refusal of the representation

`E4-SURFACE-CE-005`: the same representation and the same reference table
answer differently at two fuels. The `false` at fuel `0` is exhaustion; no
refusal constructor and no theorem may read it as "not JSON-representable". -/

#guard kindCheck shopRefs 64 .json (reference "User") = true
#guard kindCheck shopRefs 0 .json (reference "User") = false
#guard kindCheck shopRefs 1 .json (reference "User") = false
-- A `suspend` node is walked through its thunk and costs fuel the same way.
#guard kindCheck shopRefs 0 .json (suspend string) = false
#guard kindCheck shopRefs 64 .json (suspend string) = true
-- An unresolvable reference is a genuine `false` at every fuel.
#guard kindCheck shopRefs 64 .json (reference "Missing") = false

/-! ## `Sch`: the two admitted ways in -/

#guard (Sch.of? shopRefs .text userIdRep).isSome
#guard (Sch.of? shopRefs .struct userRep).isSome
#guard (Sch.of? shopRefs .json (reference "User")).isSome
#guard (Sch.of? shopRefs .void Effect4.Schema.void).isSome
#guard (Sch.of? shopRefs .text userRep).isNone
#guard (Sch.of? shopRefs .void string).isNone
#guard (Sch.of? shopRefs .json Effect4.Schema.bigint).isNone

#guard (Sch.of? shopRefs .text userIdRep).map Sch.rep = some userIdRep
#guard Sch.rep userIdParams = userIdRep
#guard Sch.propertyNames userIdParams = ["id"]
#guard Sch.propertyNames lookupParams = ["id"]
#guard Sch.propertyNames (Sch.widenToStruct userIdParams) = ["id"]

/-! ## Named receipts

The two containment theorems are *used*, not restated: a battery that proved
each fixture separately by `decide` would still pass if the theorems were
vacuous. -/

theorem userRep_struct : kindCheck shopRefs 64 .struct userRep = true := by decide

theorem userIdRep_text : kindCheck shopRefs 64 .text userIdRep = true := by decide

theorem userRep_json : kindCheck shopRefs 64 .json userRep = true :=
  kindCheck_struct_json shopRefs 64 userRep userRep_struct

theorem userIdRep_struct : kindCheck shopRefs 64 .struct userIdRep = true :=
  kindCheck_text_struct shopRefs 64 userIdRep userIdRep_text

theorem userIdRep_json : kindCheck shopRefs 64 .json userIdRep = true :=
  kindCheck_struct_json shopRefs 64 userIdRep userIdRep_struct

theorem userRep_json_at_128 : kindCheck shopRefs 128 .json userRep = true :=
  kindCheck_fuel_mono shopRefs .json userRep 64 128 (by decide) userRep_json

theorem stream_is_json : kindCheck shopRefs 64 .stream userRep = kindCheck shopRefs 64 .json userRep :=
  kindCheck_stream_json shopRefs 64 userRep

theorem multipart_is_struct :
    kindCheck shopRefs 64 .multipart userRep = kindCheck shopRefs 64 .struct userRep :=
  kindCheck_multipart_struct shopRefs 64 userRep

theorem urlEncoded_is_text :
    kindCheck shopRefs 64 .urlEncoded userIdRep = kindCheck shopRefs 64 .text userIdRep :=
  kindCheck_urlEncoded_text shopRefs 64 userIdRep

theorem shop_void_not_string :
    ¬ (Effect4.Schema.string : Representation).tag = Effect4.RepresentationTag.void := by decide

end Effect4Test.Surface.KindContract
