import Effect4.Target.TypeScript.Schema

/-!
Mechanically complete raw-generation corpus for all 22 representation tags
and both persisted check constructors.
-/

namespace Effect4Test.Target.TypeScript.SchemaGenerationCoverage

open Effect4

private def representedTrimmed : Check :=
  Schema.Check.named "effect/schema/isTrimmed" .null (some [Schema.string])

private def representedGroup : Check :=
  Schema.Check.group Schema.Check.trimmed
    (annotations := some [{ key := "__proto__", payload := .str "annotation" }])
    (representation := some
      { id := "effect/schema/isTrimmed"
        payload := .null
        schemas := some [Schema.string] })

/-- One field-admissible representative for each tag, in the exact canonical
tag-census order. Nested values also exercise both union modes, all literal
payload legs, global-symbol property keys, annotations, and both check nodes. -/
def allRepresentations : List Representation :=
  [ .declaration
      { id := "effect4/schema/declaration", payload := .null }
      none [Schema.string] [representedTrimmed, representedGroup]
  , Schema.reference "StringRef"
  , Schema.suspend (Schema.reference "StringRef")
  , Schema.null
  , Schema.undefined
  , Schema.void
  , Schema.never
  , Schema.unknown
  , Schema.any
  , Schema.string
  , Schema.number
  , Schema.boolean
  , Schema.bigint
  , Schema.symbol
  , .literal none [] (.number Float64.negZero)
  , Schema.globalSymbol "effect4/global-symbol"
  , Schema.objectKeyword
  , .enum none []
      [ { name := "word", value := .string "word" }
      , { name := "not-a-number", value := .number Float64.nan } ]
  , .templateLiteral none []
      [ Schema.literalString "prefix"
      , Schema.literalNumber Float64.zero
      , Schema.literalBigInt 42
      , Schema.literalBoolean true ]
  , Schema.tuple [Schema.element Schema.string] [Schema.number]
  , Schema.struct
      [ { name := .globalSymbol ⟨"effect4/property-key"⟩
          type := Schema.boolean
          isOptional := false
          isMutable := false
          annotations := some
            [{ key := "__proto__", payload := .str "property-annotation" }] } ]
      [Schema.index Schema.string Schema.unknown]
  , .union none []
      [ Schema.string
      , .union none [] [Schema.number, Schema.boolean] .oneOf ]
      .anyOf ]

theorem allRepresentations_tags :
    allRepresentations.map Representation.tag = RepresentationTag.census := by
  decide

private def referenceEntries : List ReferenceEntry :=
  (RepresentationTag.census.zip allRepresentations).map fun entry =>
    { key := "case/" ++ entry.1.tagName
      representation := entry.2 }

/-- A single raw document whose dead reference table intentionally carries the
complete generation corpus. `fromJson` preserves those entries without
requiring live revivers. -/
def document : Document :=
  Schema.document Schema.string
    (referenceEntries ++ [{ key := "StringRef", representation := Schema.string }])

#guard allRepresentations.length = 22
#guard allRepresentations.map Representation.tag = RepresentationTag.census
#guard document.fieldAdmissible
#guard Effect4.Target.TypeScript.Schema.documentReady document
#guard Effect4.Target.TypeScript.Schema.generationReady
  "AllRepresentationsSchema" document []

end Effect4Test.Target.TypeScript.SchemaGenerationCoverage
