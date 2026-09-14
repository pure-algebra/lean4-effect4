/-
Contract packet: `Test/contracts/schema-annotations.contract.md`

Breaker-owned red battery for `SCHEMA-PG-ANNOTATION-DATA`. The builder must
make this file green without editing it. All views target the existing raw
Schema carriers.
-/

import Effect4.Schema.Document

namespace Test.Schema.AnnotationDataPlaneContract

open Effect4

universe u

/-! ## A0 — typed keys are views over the existing Json payload -/

example {A : Type u} {key : AnnotationKey A}
    (law : key.Lawful) (value : A) :
    key.decode (key.encode value) = some value :=
  law.decode_encode value

example {A : Type u} {key : AnnotationKey A}
    (law : key.Lawful) (raw : Json) (value : A)
    (decoded : key.decode raw = some value) : key.encode value = raw :=
  law.encode_decode raw value decoded

/-! Three heterogeneous dimensions exercise the one generic carrier. -/

private def titleKey : AnnotationKey String where
  name := "effect/schema/title"
  encode := Json.str
  decode
    | .str value => some value
    | _ => none

private def deprecatedKey : AnnotationKey Bool where
  name := "effect/schema/deprecated"
  encode := Json.bool
  decode
    | .bool value => some value
    | _ => none

private def examplesKey : AnnotationKey (List Json) where
  name := "effect/schema/examples"
  encode := Json.arr
  decode
    | .arr values => some values
    | _ => none

#guard titleKey.entry "User" =
  { key := "effect/schema/title", payload := .str "User" }
#guard deprecatedKey.singleton true =
  some [{ key := "effect/schema/deprecated", payload := .bool true }]
#guard examplesKey.entry [.null, .str "x"] =
  { key := "effect/schema/examples", payload := .arr [.null, .str "x"] }

/-! ## A1 — raw and typed duplicate-preserving traversals -/

private def duplicateBag : Annotations :=
  some
    [ titleKey.entry "first"
    , { key := "other", payload := .null }
    , { key := titleKey.name, payload := .bool false }
    , titleKey.entry "second"
    ]

#guard (Annotations.payloadsAt titleKey.name).collect duplicateBag =
  [.str "first", .bool false, .str "second"]

#guard titleKey.getAll duplicateBag = ["first", "second"]

#guard titleKey.modifyAll (fun value => value ++ "!") duplicateBag =
  some
    [ titleKey.entry "first!"
    , { key := "other", payload := .null }
    , { key := titleKey.name, payload := .bool false }
    , titleKey.entry "second!"
    ]

#guard titleKey.replaceAll "same" duplicateBag =
  some
    [ titleKey.entry "same"
    , { key := "other", payload := .null }
    , { key := titleKey.name, payload := .bool false }
    , titleKey.entry "same"
    ]

#guard titleKey.append "third" none = some [titleKey.entry "third"]
#guard titleKey.append "third" duplicateBag =
  duplicateBag.map (fun entries => entries ++ [titleKey.entry "third"])

/-! ## A2 — local optics distinguish absence from a stored none -/

private def replacement : Annotations :=
  some [{ key := "replacement", payload := .null }]

#guard Representation.nodeAnnotations.replace replacement
    (.reference ⟨"Node"⟩) = .reference ⟨"Node"⟩
#guard Representation.nodeAnnotations.replace replacement (.string none []) =
  .string replacement []

#guard Check.annotationsLens.replace replacement
    (.filter
      { id := "filter", payload := .null, schemas := none }
      none false) =
  .filter { id := "filter", payload := .null, schemas := none }
    replacement false

#guard (ElementOf.annotationsLens (A := Nat)).replace replacement
    { isOptional := true, type := 7, annotations := none } =
  { isOptional := true, type := 7, annotations := replacement }

#guard (PropertySignatureOf.annotationsLens (A := Nat)).replace replacement
    { name := .string "field", type := 7, isOptional := false,
      isMutable := true, annotations := none } =
  { name := .string "field", type := 7, isOptional := false,
    isMutable := true, annotations := replacement }

/-! ## A3 — recursive structural bag traversals -/

private def site (label : String) : Annotations :=
  some [{ key := "site", payload := .str label }]

private def recursiveWitness : Representation :=
  .declaration
    { id := "root", payload := .null }
    (site "declaration")
    [ .arrays (site "arrays")
        [.filter
          { id := "array-check", payload := .null,
            schemas := some [.number (site "filter-schema") []] }
          (site "filter") false]
        [{ isOptional := false,
           type := .string (site "element-type") [],
           annotations := site "element" }]
        [.boolean (site "rest") []]
    ]
    [ .filterGroup
        (some
          { id := "group-schema", payload := .null,
            schemas := some [.bigint (site "group-schema") []] })
        (site "group")
        [.filter
          { id := "nested-filter", payload := .null,
            schemas := some [.symbol (site "nested-schema") []] }
          (site "nested-filter") false]
    ]

private def labels (bags : List Annotations) : List String :=
  bags.filterMap fun bag =>
    match bag with
    | some [{ key := "site", payload := .str label }] => some label
    | _ => none

#guard labels (Representation.annotationBags.collect recursiveWitness) =
  [ "declaration"
  , "arrays", "filter", "filter-schema", "element", "element-type", "rest"
  , "group", "group-schema", "nested-filter", "nested-schema"
  ]

private def documentWitness : Document :=
  { representation := .string (site "root") []
    references :=
      [ { key := "dead", representation := .number (site "dead-first") [] }
      , { key := "dead", representation := .boolean (site "dead-duplicate") [] }
      , { key := "unreachable", representation := .reference ⟨"nowhere"⟩ }
      ] }

#guard labels (Document.annotationBags.collect documentWitness) =
  ["root", "dead-first", "dead-duplicate"]

private def multiWitness : MultiDocument :=
  { representations :=
      [.string (site "root-one") [], .number (site "root-two") []]
    references := documentWitness.references }

#guard labels (MultiDocument.annotationBags.collect multiWitness) =
  ["root-one", "root-two", "dead-first", "dead-duplicate"]

/-! Typed whole-document traversal is derived, not handwritten. -/

private def siteKey : AnnotationKey String :=
  { name := "site"
    encode := Json.str
    decode
      | .str value => some value
      | _ => none }

#guard (siteKey.inTraversal Document.annotationBags).collect documentWitness =
  ["root", "dead-first", "dead-duplicate"]

end Test.Schema.AnnotationDataPlaneContract
