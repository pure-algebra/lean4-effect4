/- Executable witness for `E4-SCHEMA-CE-018`. -/

import Effect4.Schema.Representation

namespace Test.Counterexamples.Schema.WireSpellingDrift

open Effect4

example : RepresentationTag.tagName .objectKeyword = "ObjectKeyword" := by decide
example : RepresentationTag.tagName .uniqueSymbol = "UniqueSymbol" := by decide
example : RepresentationTag.tagName .templateLiteral = "TemplateLiteral" := by decide
example : RepresentationTag.tagName .bigint = "BigInt" := by decide

example : RepresentationTag.ofTagName "objectKeyword" = none := by decide
example : RepresentationTag.ofTagName "OBJECTKEYWORD" = none := by decide
example : RepresentationTag.ofTagName "uniqueSymbol" = none := by decide
example : RepresentationTag.ofTagName "templateliteral" = none := by decide
example : RepresentationTag.ofTagName "bigInt" = none := by decide
example : RepresentationTag.ofTagName "Bigint" = none := by decide

example : RepresentationTag.ofTagName "Refinement" = none := by decide
example : RepresentationTag.ofTagName "Transformation" = none := by decide

end Test.Counterexamples.Schema.WireSpellingDrift
