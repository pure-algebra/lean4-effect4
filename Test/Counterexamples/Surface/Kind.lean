/-
Executable witnesses for `E4-SURFACE-CE-001` through `E4-SURFACE-CE-005`.

Contract: `test/contracts/surface-kind.contract.md`. Frozen by the wave-1b
breaker before `Effect4/Surface/Kind.lean` exists; red until the builder lands
it. Each attack is a named `def` whose docstring carries its id, the statement
it attacks and the repair it forces; the executable check is the `#guard` that
follows it.
-/

import Test.Surface.Fixtures

set_option autoImplicit false

namespace Test.Counterexamples.Surface.Kind

open Effect4 (Representation)
open Effect4.Surface
open Test.Surface.Fixtures
open Effect4.Schema (struct property string number array anyOf literalString reference index)

/--
`E4-SURFACE-CE-001`. Attacked statement: "`Kind.text` is a struct whose
properties are primitives", read loosely enough that a nested object counts as
a property like any other. A path or header codec has one string per property;
a nested object has no text spelling rc.112 would decode.

Forced repair: `kindCheck .text` inspects the property *types*, admitting only
`string`, `number`, `boolean`, a string or number literal, an `anyOf` of
those, and an optional of those. A nested `objects` node is refused, and so is
an array and a reference.
-/
def textWithNestedObject : Representation :=
  struct [property "id" string, property "address" addressRep]

#guard kindCheck shopRefs 64 .text textWithNestedObject = false
#guard (Sch.of? shopRefs .text textWithNestedObject).isNone
-- The nested object is a perfectly good `struct` and a perfectly good `json`,
-- so the refusal is about the kind and not about the representation.
#guard kindCheck shopRefs 64 .struct textWithNestedObject = true
#guard kindCheck shopRefs 64 .json textWithNestedObject = true

/--
`E4-SURFACE-CE-002`. Attacked statement: "`Kind.struct` is any `objects`
node". An index signature makes the key set unenumerable, so an entity's key
list cannot be checked against it, a tool's parameter list cannot be spelled,
and `Entity.key_subset_props` would be false.

Forced repair: `kindCheck .struct` requires every property key to be a string
key and the index-signature list to be empty.
-/
def structWithIndexSignature : Representation :=
  struct [property "id" string] [index string string]

#guard kindCheck shopRefs 64 .struct structWithIndexSignature = false
#guard (Sch.of? shopRefs .struct structWithIndexSignature).isNone
-- It remains JSON-representable: the refusal is enumerability, not the wire.
#guard kindCheck shopRefs 64 .json structWithIndexSignature = true

/--
`E4-SURFACE-CE-003`. Attacked statement: "`Kind.void` marks a no-content
response", read as "any representation with no fields". An empty struct, a
`null` and a `never` are all "nothing" in some reading; only
`Representation.void` is the marker rc.112's `HttpApiSchema.Empty` emits, and
conflating them makes a `204` carry a body of `{}`.

Forced repair: `kindCheck .void` admits exactly the representations whose tag
is `.void`, and `kindCheck_void_iff` states it.
-/
def voidLookalikes : List Representation :=
  [ struct [], Effect4.Schema.null, Effect4.Schema.never, Effect4.Schema.unknown
  , Effect4.Schema.undefined ]

#guard voidLookalikes.all (fun r => kindCheck shopRefs 64 .void r == false)
#guard kindCheck shopRefs 64 .void Effect4.Schema.void = true
-- And `void` is disjoint from the chain: the marker is not a body.
#guard kindCheck shopRefs 64 .json Effect4.Schema.void = false

/--
`E4-SURFACE-CE-004`. Attacked statement: "every `Representation` an emitter
receives is JSON-representable, because the estate only builds JSON schemas".
The Schema carrier admits `bigint`, `symbol`, `uniqueSymbol`, `undefined`, a
bigint literal and a `templateLiteral`, none of which has a JSON inhabitant.
Without a static check each reaches a wire emitter and is discovered at run
time, which is the "missing static check for every wire consumer" the schema
consumer survey recorded.

Forced repair: `JsonRepresentable` is `kindCheck refs 64 .json`, every emitter
requires it of every schema it touches, and the refusal set is exactly the one
`Effect4.Arch.Accepts` already names.
-/
def noJsonInhabitant : List Representation :=
  [ Effect4.Schema.undefined, Effect4.Schema.bigint, Effect4.Schema.symbol
  , Effect4.Schema.globalSymbol "k", Effect4.Schema.literalBigInt 7
  , Effect4.Representation.templateLiteral none [] [string] ]

#guard noJsonInhabitant.all (fun r => kindCheck shopRefs 64 .json r == false)
#guard noJsonInhabitant.all (fun r => JsonRepresentable shopRefs r == false)
#guard JsonRepresentable shopRefs userRep = true

/-- A duplicate property key collapses on the wire, so two distinct
representations would encode to one JSON object. It joins the refusal set of
`E4-SURFACE-CE-004` rather than being repaired downstream. -/
def duplicateKeys : Representation :=
  struct [property "id" string, property "id" number]

#guard kindCheck shopRefs 64 .json duplicateKeys = false
#guard kindCheck shopRefs 64 .struct duplicateKeys = false

/--
`E4-SURFACE-CE-005`. Attacked statement: "`kindCheck refs fuel k rep = false`
means `rep` does not have kind `k`". It does not: the walk is fuel bounded
through `reference` and `suspend`, so exhaustion also answers `false`. Reading
exhaustion as a refusal would let a deep but legal schema be reported as
un-representable, and would put a live frontier into a refusal alphabet, which
the root `AGENTS.md` forbids outright.

Forced repair: no `Refusal` constructor, error value or theorem may name fuel
exhaustion. `kindCheck_fuel_mono` is the law that lets a caller raise the
budget, and every emitter fixes the budget at 64 so the answer is stable
across call sites.
-/
def fuelFrontier : Representation := reference "User"

#guard kindCheck shopRefs 0 .json fuelFrontier = false
#guard kindCheck shopRefs 1 .json fuelFrontier = false
#guard kindCheck shopRefs 64 .json fuelFrontier = true
-- The genuine refusal at every fuel, for contrast: the key is not in the table.
#guard kindCheck shopRefs 0 .json (reference "Warehouse") = false
#guard kindCheck shopRefs 64 .json (reference "Warehouse") = false

end Test.Counterexamples.Surface.Kind
