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

#synth DecidableEq UnionMode
#synth Repr UnionMode
#synth Inhabited UnionMode

#synth DecidableEq CheckTag
#synth Repr CheckTag
#synth Inhabited CheckTag

#synth DecidableEq LiteralKind
#synth Repr LiteralKind
#synth Inhabited LiteralKind

#synth DecidableEq EnumValueKind
#synth Repr EnumValueKind
#synth Inhabited EnumValueKind

#synth DecidableEq PropertyKeyKind
#synth Repr PropertyKeyKind
#synth Inhabited PropertyKeyKind

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
Constructor order is contractual for each leaf alphabet; the compatibility snapshot
(`Test/fixtures/baseline`) and the derived projection guard hold it. The durable executable attacks are
separate modules under `Test/Counterexamples/Schema/` and are imported
by `Test.lean`.
-/

end Test.Schema.SubAlphabetContract
