/- Executable witness for `E4-SCHEMA-CE-022`. -/

import Effect4.Schema.Representation

namespace Test.Counterexamples.Schema.NoLocalSymbolPropertyKey

open Effect4

/--
error: Unknown constant
-/
#guard_msgs(error, substring := true) in
#check (@PropertyKeyKind.localSymbol)

example : PropertyKeyKind.census.length = 3 := by decide

end Test.Counterexamples.Schema.NoLocalSymbolPropertyKey
