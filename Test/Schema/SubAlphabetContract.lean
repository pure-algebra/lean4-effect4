/-
Contract packet: `Test/contracts/schema-subalphabets.contract.md`

Breaker-owned battery for the five closed sub-alphabets of the persisted
representation. The implementation phase must not edit this file.
-/

import Effect4.Schema.Representation

namespace Test.Schema.SubAlphabetContract

open Effect4

universe u

section SurfaceSnapshot

#check (@UnionMode : Type)
#synth DecidableEq UnionMode
#synth Repr UnionMode
#synth Inhabited UnionMode
#check (@UnionMode.anyOf : UnionMode)
#check (@UnionMode.oneOf : UnionMode)
#check (@UnionMode.rec.{u} :
  {motive : UnionMode → Sort u} →
  motive .anyOf → motive .oneOf →
  (mode : UnionMode) → motive mode)
#check (@UnionMode.census : List UnionMode)
#check (@UnionMode.modeName : UnionMode -> String)
#check (@UnionMode.ofModeName : String -> Option UnionMode)
#check (@UnionMode.census_length : UnionMode.census.length = 2)
#check (@UnionMode.census_nodup : UnionMode.census.Nodup)
#check (@UnionMode.mem_census :
  forall mode : UnionMode, mode ∈ UnionMode.census)
#check (@UnionMode.modeName_injective :
  forall {a b : UnionMode}, UnionMode.modeName a = UnionMode.modeName b -> a = b)
#check (@UnionMode.ofModeName_modeName :
  forall mode : UnionMode,
    UnionMode.ofModeName (UnionMode.modeName mode) = some mode)
#check (@UnionMode.modeName_ofModeName :
  forall {s : String} {mode : UnionMode},
    UnionMode.ofModeName s = some mode -> UnionMode.modeName mode = s)

#check (@CheckTag : Type)
#synth DecidableEq CheckTag
#synth Repr CheckTag
#synth Inhabited CheckTag
#check (@CheckTag.filter : CheckTag)
#check (@CheckTag.filterGroup : CheckTag)
#check (@CheckTag.rec.{u} :
  {motive : CheckTag → Sort u} →
  motive .filter → motive .filterGroup →
  (tag : CheckTag) → motive tag)
#check (@CheckTag.census : List CheckTag)
#check (@CheckTag.tagName : CheckTag -> String)
#check (@CheckTag.ofTagName : String -> Option CheckTag)
#check (@CheckTag.census_length : CheckTag.census.length = 2)
#check (@CheckTag.census_nodup : CheckTag.census.Nodup)
#check (@CheckTag.mem_census : forall tag : CheckTag, tag ∈ CheckTag.census)
#check (@CheckTag.tagName_injective :
  forall {a b : CheckTag}, CheckTag.tagName a = CheckTag.tagName b -> a = b)
#check (@CheckTag.ofTagName_tagName :
  forall tag : CheckTag, CheckTag.ofTagName (CheckTag.tagName tag) = some tag)
#check (@CheckTag.tagName_ofTagName :
  forall {s : String} {tag : CheckTag},
    CheckTag.ofTagName s = some tag -> CheckTag.tagName tag = s)

#check (@LiteralKind : Type)
#synth DecidableEq LiteralKind
#synth Repr LiteralKind
#synth Inhabited LiteralKind
#check (@LiteralKind.string : LiteralKind)
#check (@LiteralKind.number : LiteralKind)
#check (@LiteralKind.bigint : LiteralKind)
#check (@LiteralKind.boolean : LiteralKind)
#check (@LiteralKind.rec.{u} :
  {motive : LiteralKind → Sort u} →
  motive .string → motive .number → motive .bigint → motive .boolean →
  (kind : LiteralKind) → motive kind)
#check (@LiteralKind.census : List LiteralKind)
#check (@LiteralKind.census_length : LiteralKind.census.length = 4)
#check (@LiteralKind.census_nodup : LiteralKind.census.Nodup)
#check (@LiteralKind.mem_census :
  forall kind : LiteralKind, kind ∈ LiteralKind.census)

#check (@EnumValueKind : Type)
#synth DecidableEq EnumValueKind
#synth Repr EnumValueKind
#synth Inhabited EnumValueKind
#check (@EnumValueKind.string : EnumValueKind)
#check (@EnumValueKind.number : EnumValueKind)
#check (@EnumValueKind.rec.{u} :
  {motive : EnumValueKind → Sort u} →
  motive .string → motive .number →
  (kind : EnumValueKind) → motive kind)
#check (@EnumValueKind.census : List EnumValueKind)
#check (@EnumValueKind.census_length : EnumValueKind.census.length = 2)
#check (@EnumValueKind.census_nodup : EnumValueKind.census.Nodup)
#check (@EnumValueKind.mem_census :
  forall kind : EnumValueKind, kind ∈ EnumValueKind.census)
#check (@EnumValueKind.toLiteralKind : EnumValueKind -> LiteralKind)
#check (@EnumValueKind.toLiteralKind_injective :
  forall {a b : EnumValueKind},
    EnumValueKind.toLiteralKind a = EnumValueKind.toLiteralKind b -> a = b)
#check (@EnumValueKind.toLiteralKind_ne_bigint :
  forall kind : EnumValueKind,
    EnumValueKind.toLiteralKind kind ≠ LiteralKind.bigint)
#check (@EnumValueKind.toLiteralKind_ne_boolean :
  forall kind : EnumValueKind,
    EnumValueKind.toLiteralKind kind ≠ LiteralKind.boolean)

#check (@PropertyKeyKind : Type)
#synth DecidableEq PropertyKeyKind
#synth Repr PropertyKeyKind
#synth Inhabited PropertyKeyKind
#check (@PropertyKeyKind.string : PropertyKeyKind)
#check (@PropertyKeyKind.number : PropertyKeyKind)
#check (@PropertyKeyKind.globalSymbol : PropertyKeyKind)
#check (@PropertyKeyKind.rec.{u} :
  {motive : PropertyKeyKind → Sort u} →
  motive .string → motive .number → motive .globalSymbol →
  (kind : PropertyKeyKind) → motive kind)
#check (@PropertyKeyKind.census : List PropertyKeyKind)
#check (@PropertyKeyKind.census_length : PropertyKeyKind.census.length = 3)
#check (@PropertyKeyKind.census_nodup : PropertyKeyKind.census.Nodup)
#check (@PropertyKeyKind.mem_census :
  forall kind : PropertyKeyKind, kind ∈ PropertyKeyKind.census)

end SurfaceSnapshot

section PinnedSpellings

/-- The two pinned union modes, exactly. -/
example : UnionMode.census.map UnionMode.modeName = ["anyOf", "oneOf"] := by decide

/-- The two pinned check tags, exactly. -/
example : CheckTag.census.map CheckTag.tagName = ["Filter", "FilterGroup"] := by decide

/-- Case variants and the legacy `allOf` spelling are not modes. -/
example : UnionMode.ofModeName "AnyOf" = none := by decide
example : UnionMode.ofModeName "anyof" = none := by decide
example : UnionMode.ofModeName "allOf" = none := by decide

/-- A check tag is not a representation tag and vice versa. -/
example : CheckTag.ofTagName "Union" = none := by decide
example : RepresentationTag.ofTagName "Filter" = none := by decide
example : RepresentationTag.ofTagName "FilterGroup" = none := by decide

end PinnedSpellings

section PointwiseSpellings

/-!
The two ordered examples above pin each spelling *list*, not each spelling
*map*: `census.map modeName = ["anyOf", "oneOf"]` stays true when one
permutation is applied to `census` and the same permutation to `modeName`, so
on its own it lets a mode carry the other mode's persisted string. The
obligations below pin both spelled alphabets pointwise, in both directions.
With the ordered examples and the injectivity theorems they also pin the two
census listings.
-/

example : UnionMode.modeName .anyOf = "anyOf" := by decide
example : UnionMode.modeName .oneOf = "oneOf" := by decide
example : UnionMode.ofModeName "anyOf" = some .anyOf := by decide
example : UnionMode.ofModeName "oneOf" = some .oneOf := by decide

example : CheckTag.tagName .filter = "Filter" := by decide
example : CheckTag.tagName .filterGroup = "FilterGroup" := by decide
example : CheckTag.ofTagName "Filter" = some .filter := by decide
example : CheckTag.ofTagName "FilterGroup" = some .filterGroup := by decide

/-!
The three unspelled alphabets have no wire string to pin per member, so the
analogous obligation is the exact census listing. Their `census_length`,
`census_nodup`, and `mem_census` obligations are all permutation-invariant, and
the recursor snapshots freeze constructor order rather than listing order, so
without these the listings were free to permute.
-/

example : LiteralKind.census = [.string, .number, .bigint, .boolean] := by decide
example : EnumValueKind.census = [.string, .number] := by decide
example : PropertyKeyKind.census = [.string, .number, .globalSymbol] := by decide

end PointwiseSpellings

/-!
Constructor order is contractual for each leaf alphabet and is frozen by the
dependent recursor signatures above. The durable executable attacks are
separate modules under `Test/Counterexamples/Schema/` and are imported
by `Test.lean`.
-/

end Test.Schema.SubAlphabetContract
