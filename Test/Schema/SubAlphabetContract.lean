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

example : DecidableEq UnionMode := inferInstance
example : Repr UnionMode := inferInstance
example : Inhabited UnionMode := inferInstance

example : DecidableEq CheckTag := inferInstance
example : Repr CheckTag := inferInstance
example : Inhabited CheckTag := inferInstance

example : DecidableEq LiteralKind := inferInstance
example : Repr LiteralKind := inferInstance
example : Inhabited LiteralKind := inferInstance

example : DecidableEq EnumValueKind := inferInstance
example : Repr EnumValueKind := inferInstance
example : Inhabited EnumValueKind := inferInstance

example : DecidableEq PropertyKeyKind := inferInstance
example : Repr PropertyKeyKind := inferInstance
example : Inhabited PropertyKeyKind := inferInstance

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
Constructor order is contractual for each leaf alphabet, and the census listings above pin it by
`decide` (`LiteralKind.census = [...]` and its siblings). No check compares a snapshot of it: the
baseline directory (`Test/fixtures/baseline/`, the row of that name in `AGENTS.md`) is read by the
mirror census only (`tools/Conform/Effect4/mirrors.json`), which no make target runs.
The executable attacks once kept under `Test/Counterexamples/Schema/` were deleted with row 39
(`d75f5c25`, 2026-10-01); their rows are in `Test/Counterexamples/Archive/REGISTER.md`.
-/

end Test.Schema.SubAlphabetContract
