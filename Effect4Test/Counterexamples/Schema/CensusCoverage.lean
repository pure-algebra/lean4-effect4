/- Executable witness for `E4-SCHEMA-CE-019`. -/

import Effect4.Schema.Representation

namespace Effect4Test.Counterexamples.Schema.CensusCoverage

open Effect4

/-- A 22-row decoy with one duplicate and one omission. -/
def decoyCensus : List RepresentationTag :=
  [.declaration, .declaration, .reference, .suspend,
   .null, .undefined, .void, .never, .unknown, .any,
   .string, .number, .boolean, .bigint, .symbol,
   .literal, .uniqueSymbol, .objectKeyword, .enum,
   .templateLiteral, .arrays, .objects]

example : decoyCensus.length = 22 := by decide
example : ¬ decoyCensus.Nodup := by decide
example : RepresentationTag.union ∉ decoyCensus := by decide
example : RepresentationTag.census ≠ decoyCensus := by decide

end Effect4Test.Counterexamples.Schema.CensusCoverage
