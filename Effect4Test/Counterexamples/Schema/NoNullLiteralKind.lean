/- Executable witness for `E4-SCHEMA-CE-021`. -/

import Effect4.Schema.Representation

namespace Effect4Test.Counterexamples.Schema.NoNullLiteralKind

open Effect4

/--
error: Unknown constant
-/
#guard_msgs(error, substring := true) in
#check (@LiteralKind.null)

/-- The exclusion concerns literal payloads, not the nominal `Null` tag. -/
example : RepresentationTag.ofTagName "Null" = some RepresentationTag.null := by
  decide

end Effect4Test.Counterexamples.Schema.NoNullLiteralKind
