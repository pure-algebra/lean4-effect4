/-
Contract packet: `Test/contracts/schema-representation.contract.md`

Breaker-owned red battery. The implementation phase must not edit this file.
It is red until the Schema representation tag census declarations exist.
-/

import Effect4.Schema.Representation

namespace Test.Schema.RepresentationContract

open Effect4

universe u

section SurfaceSnapshot

/-! D0: the tag alphabet. Twenty-two nominal constructors, exact names. -/

#check (@RepresentationTag : Type)
#synth DecidableEq RepresentationTag
#synth Repr RepresentationTag
#synth Inhabited RepresentationTag

#check (@RepresentationTag.declaration : RepresentationTag)
#check (@RepresentationTag.reference : RepresentationTag)
#check (@RepresentationTag.suspend : RepresentationTag)
#check (@RepresentationTag.null : RepresentationTag)
#check (@RepresentationTag.undefined : RepresentationTag)
#check (@RepresentationTag.void : RepresentationTag)
#check (@RepresentationTag.never : RepresentationTag)
#check (@RepresentationTag.unknown : RepresentationTag)
#check (@RepresentationTag.any : RepresentationTag)
#check (@RepresentationTag.string : RepresentationTag)
#check (@RepresentationTag.number : RepresentationTag)
#check (@RepresentationTag.boolean : RepresentationTag)
#check (@RepresentationTag.bigint : RepresentationTag)
#check (@RepresentationTag.symbol : RepresentationTag)
#check (@RepresentationTag.literal : RepresentationTag)
#check (@RepresentationTag.uniqueSymbol : RepresentationTag)
#check (@RepresentationTag.objectKeyword : RepresentationTag)
#check (@RepresentationTag.enum : RepresentationTag)
#check (@RepresentationTag.templateLiteral : RepresentationTag)
#check (@RepresentationTag.arrays : RepresentationTag)
#check (@RepresentationTag.objects : RepresentationTag)
#check (@RepresentationTag.union : RepresentationTag)

/-!
The dependent recursor freezes constructor order as part of the native public
API. A source edit that swaps two constructors can preserve the census and
every spelling theorem; it cannot preserve this signature.
-/

#check (@RepresentationTag.rec.{u} :
  {motive : RepresentationTag → Sort u} →
  motive .declaration →
  motive .reference →
  motive .suspend →
  motive .null →
  motive .undefined →
  motive .void →
  motive .never →
  motive .unknown →
  motive .any →
  motive .string →
  motive .number →
  motive .boolean →
  motive .bigint →
  motive .symbol →
  motive .literal →
  motive .uniqueSymbol →
  motive .objectKeyword →
  motive .enum →
  motive .templateLiteral →
  motive .arrays →
  motive .objects →
  motive .union →
  (tag : RepresentationTag) → motive tag)

/-! D1: the canonical census. D2: wire spelling. -/

#check (@RepresentationTag.census : List RepresentationTag)

#check (@RepresentationTag.tagName : RepresentationTag -> String)

#check (@RepresentationTag.ofTagName : String -> Option RepresentationTag)

/-! ENSURES 1-6, ascribed at their exact propositions. -/

#check (@RepresentationTag.census_length :
  RepresentationTag.census.length = 22)

#check (@RepresentationTag.census_nodup :
  RepresentationTag.census.Nodup)

#check (@RepresentationTag.mem_census :
  forall tag : RepresentationTag, tag ∈ RepresentationTag.census)

#check (@RepresentationTag.tagName_injective :
  forall {a b : RepresentationTag},
    RepresentationTag.tagName a = RepresentationTag.tagName b -> a = b)

#check (@RepresentationTag.ofTagName_tagName :
  forall tag : RepresentationTag,
    RepresentationTag.ofTagName (RepresentationTag.tagName tag) = some tag)

#check (@RepresentationTag.tagName_ofTagName :
  forall {s : String} {tag : RepresentationTag},
    RepresentationTag.ofTagName s = some tag ->
      RepresentationTag.tagName tag = s)

end SurfaceSnapshot

section SourceCensus

/-- The exact case-sensitive rc.112 `_tag` spellings, in the frozen order of
the census table in `docs/research/SCHEMA-CUTOVER.md`. -/
def expectedTagNames : List String :=
  ["Declaration", "Reference", "Suspend",
   "Null", "Undefined", "Void", "Never", "Unknown", "Any",
   "String", "Number", "Boolean", "BigInt", "Symbol",
   "Literal", "UniqueSymbol", "ObjectKeyword", "Enum",
   "TemplateLiteral", "Arrays", "Objects", "Union"]

/-- The census spells the frozen source table exactly, in order. This pins the
listing itself, not merely its length. -/
example :
    RepresentationTag.census.map RepresentationTag.tagName = expectedTagNames := by
  decide

/-- Every frozen source spelling is recognised. -/
example : expectedTagNames.all (fun s => (RepresentationTag.ofTagName s).isSome) := by
  decide

end SourceCensus

section PointwiseSpellings

/-!
The ordered example above pins the spelling *list*, not the spelling *map*.
`census.map tagName = expectedTagNames` is invariant under applying one
permutation to `census` and the same permutation to `tagName`, so on its own it
leaves every tag free to carry another tag's persisted `_tag` string. The
obligations below pin the map pointwise, per tag, in both directions. Together
with `census.map tagName = expectedTagNames` and `tagName_injective` they also
pin the census listing itself.
-/

example : RepresentationTag.tagName .declaration = "Declaration" := by decide
example : RepresentationTag.tagName .reference = "Reference" := by decide
example : RepresentationTag.tagName .suspend = "Suspend" := by decide
example : RepresentationTag.tagName .null = "Null" := by decide
example : RepresentationTag.tagName .undefined = "Undefined" := by decide
example : RepresentationTag.tagName .void = "Void" := by decide
example : RepresentationTag.tagName .never = "Never" := by decide
example : RepresentationTag.tagName .unknown = "Unknown" := by decide
example : RepresentationTag.tagName .any = "Any" := by decide
example : RepresentationTag.tagName .string = "String" := by decide
example : RepresentationTag.tagName .number = "Number" := by decide
example : RepresentationTag.tagName .boolean = "Boolean" := by decide
example : RepresentationTag.tagName .bigint = "BigInt" := by decide
example : RepresentationTag.tagName .symbol = "Symbol" := by decide
example : RepresentationTag.tagName .literal = "Literal" := by decide
example : RepresentationTag.tagName .uniqueSymbol = "UniqueSymbol" := by decide
example : RepresentationTag.tagName .objectKeyword = "ObjectKeyword" := by decide
example : RepresentationTag.tagName .enum = "Enum" := by decide
example : RepresentationTag.tagName .templateLiteral = "TemplateLiteral" := by decide
example : RepresentationTag.tagName .arrays = "Arrays" := by decide
example : RepresentationTag.tagName .objects = "Objects" := by decide
example : RepresentationTag.tagName .union = "Union" := by decide

example : RepresentationTag.ofTagName "Declaration" = some .declaration := by decide
example : RepresentationTag.ofTagName "Reference" = some .reference := by decide
example : RepresentationTag.ofTagName "Suspend" = some .suspend := by decide
example : RepresentationTag.ofTagName "Null" = some .null := by decide
example : RepresentationTag.ofTagName "Undefined" = some .undefined := by decide
example : RepresentationTag.ofTagName "Void" = some .void := by decide
example : RepresentationTag.ofTagName "Never" = some .never := by decide
example : RepresentationTag.ofTagName "Unknown" = some .unknown := by decide
example : RepresentationTag.ofTagName "Any" = some .any := by decide
example : RepresentationTag.ofTagName "String" = some .string := by decide
example : RepresentationTag.ofTagName "Number" = some .number := by decide
example : RepresentationTag.ofTagName "Boolean" = some .boolean := by decide
example : RepresentationTag.ofTagName "BigInt" = some .bigint := by decide
example : RepresentationTag.ofTagName "Symbol" = some .symbol := by decide
example : RepresentationTag.ofTagName "Literal" = some .literal := by decide
example : RepresentationTag.ofTagName "UniqueSymbol" = some .uniqueSymbol := by decide
example : RepresentationTag.ofTagName "ObjectKeyword" = some .objectKeyword := by decide
example : RepresentationTag.ofTagName "Enum" = some .enum := by decide
example : RepresentationTag.ofTagName "TemplateLiteral" = some .templateLiteral := by decide
example : RepresentationTag.ofTagName "Arrays" = some .arrays := by decide
example : RepresentationTag.ofTagName "Objects" = some .objects := by decide
example : RepresentationTag.ofTagName "Union" = some .union := by decide

end PointwiseSpellings

/-!
The durable executable attacks are separate modules under
`Test/Counterexamples/Schema/` and are imported by `Test.lean`.
The contract battery freezes the declaration surface; the witness modules
retain each attack without copying it into this file.
-/

end Test.Schema.RepresentationContract
