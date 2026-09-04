/-
Executable witnesses for `E4-SCHEMA-CE-044` through
`E4-SCHEMA-CE-048`. These attacks concern structural annotation data only;
they assign no annotation denotation and resolve no document reference.
-/

import Effect4.Schema.Document

namespace Test.Counterexamples.Schema.AnnotationDataPlane

open Effect4

private def bag (label : String) : Annotations :=
  some [{ key := "site", payload := .str label }]

private def labels (bags : List Annotations) : List String :=
  bags.filterMap fun annotations =>
    match annotations with
    | some [{ key := "site", payload := .str label }] => some label
    | _ => none

/-! `E4-SCHEMA-CE-044`: absence of a focus is not stored absence. -/

/-- This tempting projection collapses two observably different shapes. -/
private def collapsedNodeAnnotations : Representation -> Annotations
  | .reference _ => none
  | .declaration _ annotations _ _
  | .suspend annotations _ _
  | .null annotations _
  | .undefined annotations _
  | .void annotations _
  | .never annotations _
  | .unknown annotations _
  | .any annotations _
  | .string annotations _
  | .number annotations _
  | .boolean annotations _
  | .bigint annotations _
  | .symbol annotations _
  | .literal annotations _ _
  | .uniqueSymbol annotations _ _
  | .objectKeyword annotations _
  | .enum annotations _ _
  | .templateLiteral annotations _ _
  | .arrays annotations _ _ _
  | .objects annotations _ _ _
  | .union annotations _ _ _ => annotations

#guard collapsedNodeAnnotations (.reference ⟨"Node"⟩) =
  collapsedNodeAnnotations (.string none [])

/-- The Optional retains the distinction: no focus versus a focus containing none. -/
theorem no_focus_ne_present_none :
    Representation.nodeAnnotations.preview (.reference ⟨"Node"⟩) ≠
      Representation.nodeAnnotations.preview (.string none []) := by
  decide

/-! `E4-SCHEMA-CE-045`: first match is not all ordered matches. -/

private def duplicates : Annotations :=
  some
    [ { key := "k", payload := .str "first" }
    , { key := "other", payload := .null }
    , { key := "k", payload := .str "second" }
    , { key := "k", payload := .str "third" }
    ]

private def firstPayloadAt (name : String) : Annotations -> Option Json
  | none => none
  | some entries =>
      entries.findSome? fun entry =>
        if entry.key = name then some entry.payload else none

#guard firstPayloadAt "k" duplicates = some (.str "first")
#guard (Annotations.payloadsAt "k").collect duplicates =
  [.str "first", .str "second", .str "third"]

#guard (Annotations.payloadsAt "k").modifyAll
    (fun payload => .arr [payload]) duplicates =
  some
    [ { key := "k", payload := .arr [.str "first"] }
    , { key := "other", payload := .null }
    , { key := "k", payload := .arr [.str "second"] }
    , { key := "k", payload := .arr [.str "third"] }
    ]

/-! `E4-SCHEMA-CE-046`: one codec direction does not preserve raw data. -/

private def canonicalUnit : AnnotationKey Unit where
  name := "unit"
  encode := fun _ => .str "canonical"
  decode
    | .str _ => some ()
    | _ => none

theorem canonicalUnit_decode_encode (value : Unit) :
    canonicalUnit.decode (canonicalUnit.encode value) = some value := by
  cases value
  rfl

private def noncanonicalEntry : AnnotationEntry :=
  { key := "unit", payload := .str "authored-spelling" }

#guard canonicalUnit.decodeEntry noncanonicalEntry = some ()
#guard canonicalUnit.entry () ≠ noncanonicalEntry

/-- Hence `decode_encode` alone cannot inhabit the frozen exactness law. -/
theorem canonicalUnit_not_lawful : ¬ canonicalUnit.Lawful := by
  intro law
  have exactRaw := law.encode_decode (.str "authored-spelling") () (by rfl)
  exact (by decide : ("canonical" : String) ≠ "authored-spelling")
    (Json.str.inj exactRaw)

/-! `E4-SCHEMA-CE-047`: shallow node fields omit recursive annotation routes. -/

private def nestedRoutes : Representation :=
  .arrays (bag "arrays")
    [.filterGroup
      (some
        { id := "group", payload := .null,
          schemas := some [.number (bag "group-schema") []] })
      (bag "group")
      [.filter
        { id := "filter", payload := .null,
          schemas := some [.boolean (bag "filter-schema") []] }
        (bag "filter") false]]
    [{ isOptional := false,
       type := .objects (bag "objects") []
         [{ name := .string "p", type := .string (bag "property-type") [],
            isOptional := false, isMutable := false,
            annotations := bag "property" }]
         [],
       annotations := bag "element" }]
    []

private def rootOnly : Representation -> List Annotations
  | .reference _ => []
  | source => (Representation.nodeAnnotations.preview source).toList

#guard labels (rootOnly nestedRoutes) = ["arrays"]
#guard labels (Representation.annotationBags.collect nestedRoutes) =
  [ "arrays", "group", "group-schema", "filter", "filter-schema"
  , "element", "objects", "property", "property-type"
  ]

/-! `E4-SCHEMA-CE-048`: structural documents include every table entry. -/

private def document : Document :=
  { representation := .string (bag "root") []
    references :=
      [ { key := "unused", representation := .number (bag "dead") [] }
      , { key := "unused", representation := .boolean (bag "duplicate") [] }
      , { key := "also-unused", representation := .bigint (bag "second-dead") [] }
      ] }

/-- A reachability-shaped walk with no root references sees the root only. -/
private def reachableOnly (document : Document) : List Annotations :=
  Representation.annotationBags.collect document.representation

#guard labels (reachableOnly document) = ["root"]
#guard labels (Document.annotationBags.collect document) =
  ["root", "dead", "duplicate", "second-dead"]

end Test.Counterexamples.Schema.AnnotationDataPlane
