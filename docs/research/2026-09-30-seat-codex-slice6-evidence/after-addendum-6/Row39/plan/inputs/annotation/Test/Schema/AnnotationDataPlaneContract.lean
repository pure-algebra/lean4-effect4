/-
Retained annotation-carrier controls after decision row 39.

These controls retain the typed-key laws, entry construction and append, and
local node-annotation replacement from `SCHEMA-PG-ANNOTATION-DATA`. They do not
claim the retired annotation traversal contract is still implemented.
-/

import Effect4.Schema.Annotations

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

/-! ## A1 — append preserves existing entries and multiplicity -/

private def duplicateBag : Annotations :=
  some
    [ titleKey.entry "first"
    , { key := "other", payload := .null }
    , { key := titleKey.name, payload := .bool false }
    , titleKey.entry "second"
    ]

#guard titleKey.append "third" none = some [titleKey.entry "third"]
#guard titleKey.append "third" duplicateBag =
  duplicateBag.map (fun entries => entries ++ [titleKey.entry "third"])

/-! ## A2 — local node annotations distinguish absence from a stored none -/

private def replacement : Annotations :=
  some [{ key := "replacement", payload := .null }]

#guard Representation.nodeAnnotations.replace replacement
    (.reference ⟨"Node"⟩) = .reference ⟨"Node"⟩
#guard Representation.nodeAnnotations.replace replacement (.string none []) =
  .string replacement []

end Test.Schema.AnnotationDataPlaneContract
