/- Executable witness for `E4-SCHEMA-CE-020`. -/

import Effect4.Schema.Representation

namespace Effect4Test.Counterexamples.Schema.KindAlphabetSeparation

open Effect4

example : EnumValueKind.census.length < LiteralKind.census.length := by decide

example :
    EnumValueKind.census.map EnumValueKind.toLiteralKind =
      [LiteralKind.string, LiteralKind.number] := by
  decide

example :
    LiteralKind.bigint ∉ EnumValueKind.census.map EnumValueKind.toLiteralKind := by
  decide

example :
    LiteralKind.boolean ∉ EnumValueKind.census.map EnumValueKind.toLiteralKind := by
  decide

end Effect4Test.Counterexamples.Schema.KindAlphabetSeparation
