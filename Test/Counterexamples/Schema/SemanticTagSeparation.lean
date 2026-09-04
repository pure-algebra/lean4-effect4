/-
Executable witness for `E4-SCHEMA-CE-017`.

This file distinguishes the semantic requirement from the native API ruling:
the twelve keyword-shaped tags must remain distinguishable, while the flat
22-constructor carrier is a deliberately frozen public representation rather
than a consequence of their shared payload shape.
-/

import Effect4.Schema.Representation

namespace Test.Counterexamples.Schema.SemanticTagSeparation

open Effect4

/-- The tags that share the keyword-shaped persisted payload in rc.112. -/
def keywordShaped : List RepresentationTag :=
  [.null, .undefined, .void, .never, .unknown, .any,
   .string, .number, .boolean, .bigint, .symbol, .objectKeyword]

/-- Equal payload shape does not collapse the twelve nominal values. -/
example : keywordShaped.length = 12 := by decide

example : keywordShaped.Nodup := by decide

example : keywordShaped.all (fun tag => tag ∈ RepresentationTag.census) := by
  decide

example : (keywordShaped.map RepresentationTag.tagName).Nodup := by decide

/-
The flat native API has no parameterised replacement constructor. A separate
`KeywordKind` could in principle preserve all twelve values, so its exclusion
is an API/minimality ruling: it avoids duplicating an alphabet that carries no
additional semantic distinction.
-/

/--
error: Unknown constant
-/
#guard_msgs(error, substring := true) in
#check (@RepresentationTag.keyword)

/--
error: Unknown identifier `Effect4.KeywordKind`
-/
#guard_msgs(error, substring := true) in
#check (@Effect4.KeywordKind)

end Test.Counterexamples.Schema.SemanticTagSeparation
