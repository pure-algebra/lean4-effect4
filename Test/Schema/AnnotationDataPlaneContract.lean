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

#check (@AnnotationKey.{u} : Type u -> Type u)
#check (@AnnotationKey.name.{u} : {A : Type u} -> AnnotationKey A -> String)
#check (@AnnotationKey.encode.{u} : {A : Type u} -> AnnotationKey A -> A -> Json)
#check (@AnnotationKey.decode.{u} :
  {A : Type u} -> AnnotationKey A -> Json -> Option A)

#check (@AnnotationKey.Lawful.{u} :
  {A : Type u} -> AnnotationKey A -> Prop)

example {A : Type u} {key : AnnotationKey A}
    (law : key.Lawful) (value : A) :
    key.decode (key.encode value) = some value :=
  law.decode_encode value

example {A : Type u} {key : AnnotationKey A}
    (law : key.Lawful) (raw : Json) (value : A)
    (decoded : key.decode raw = some value) : key.encode value = raw :=
  law.encode_decode raw value decoded

#check (@AnnotationKey.entry.{u} :
  {A : Type u} -> AnnotationKey A -> A -> AnnotationEntry)
#check (@AnnotationKey.singleton.{u} :
  {A : Type u} -> AnnotationKey A -> A -> Annotations)
#check (@AnnotationKey.append.{u} :
  {A : Type u} -> AnnotationKey A -> A -> Annotations -> Annotations)
#check (@AnnotationKey.decodeEntry.{u} :
  {A : Type u} -> AnnotationKey A -> AnnotationEntry -> Option A)
#check (@AnnotationKey.values.{u} :
  {A : Type u} -> AnnotationKey A -> Traversal Annotations A)
#check (@AnnotationKey.inTraversal.{u, 0} :
  {A : Type u} -> {S : Type} -> AnnotationKey A ->
    Traversal S Annotations -> Traversal S A)
#check (@AnnotationKey.getAll.{u} :
  {A : Type u} -> AnnotationKey A -> Annotations -> List A)
#check (@AnnotationKey.modifyAll.{u} :
  {A : Type u} -> AnnotationKey A -> (A -> A) ->
    Annotations -> Annotations)
#check (@AnnotationKey.replaceAll.{u} :
  {A : Type u} -> AnnotationKey A -> A -> Annotations -> Annotations)

#check (@AnnotationKey.decodeEntry_entry.{u} :
  forall {A : Type u} (key : AnnotationKey A), key.Lawful ->
    forall value, key.decodeEntry (key.entry value) = some value)

#check (@AnnotationKey.entry_of_decodeEntry.{u} :
  forall {A : Type u} (key : AnnotationKey A), key.Lawful ->
    forall {entry : AnnotationEntry} {value : A},
      key.decodeEntry entry = some value -> key.entry value = entry)

#check (@AnnotationKey.values_lawful.{u} :
  forall {A : Type u} (key : AnnotationKey A), key.Lawful ->
    Traversal.Lawful key.values)

#check (@AnnotationKey.inTraversal_lawful.{u, 0} :
  forall {A : Type u} {S : Type} (key : AnnotationKey A)
    {outer : Traversal S Annotations},
    key.Lawful -> Traversal.Lawful outer ->
      Traversal.Lawful (key.inTraversal outer))

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

#check (Annotations.payloadsAt : String -> Traversal Annotations Json)
#check (Annotations.payloadsAt_lawful :
  forall name, Traversal.Lawful (Annotations.payloadsAt name))

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

#check (Representation.nodeAnnotations : Optional Representation Annotations)
#check (Representation.nodeAnnotations_reference :
  forall ref, Representation.nodeAnnotations.preview (.reference ref) = none)
#check (Representation.nodeAnnotations_string_none :
  Representation.nodeAnnotations.preview (.string none []) = some none)
#check (Representation.nodeAnnotations_lawful :
  Optional.Lawful Representation.nodeAnnotations)

#check (Check.annotationsLens : Lens Check Annotations)
#check (Check.annotationsLens_lawful : Lens.Lawful Check.annotationsLens)
#check (@ElementOf.annotationsLens.{u} :
  {A : Type u} -> Lens (ElementOf A) Annotations)
#check (@ElementOf.annotationsLens_lawful.{u} :
  forall {A : Type u}, Lens.Lawful (ElementOf.annotationsLens (A := A)))
#check (@PropertySignatureOf.annotationsLens.{u} :
  {A : Type u} -> Lens (PropertySignatureOf A) Annotations)
#check (@PropertySignatureOf.annotationsLens_lawful.{u} :
  forall {A : Type u},
    Lens.Lawful (PropertySignatureOf.annotationsLens (A := A)))

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

#check (Representation.annotationBags : Traversal Representation Annotations)
#check (Check.annotationBags : Traversal Check Annotations)
#check (Document.annotationBags : Traversal Document Annotations)
#check (MultiDocument.annotationBags : Traversal MultiDocument Annotations)

#check (Representation.annotationBags_lawful :
  Traversal.Lawful Representation.annotationBags)
#check (Check.annotationBags_lawful :
  Traversal.Lawful Check.annotationBags)
#check (Document.annotationBags_lawful :
  Traversal.Lawful Document.annotationBags)
#check (MultiDocument.annotationBags_lawful :
  Traversal.Lawful MultiDocument.annotationBags)

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
