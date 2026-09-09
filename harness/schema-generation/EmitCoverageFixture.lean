import Tools.GeneratedStamp
import Test.Codegen.SchemaGenerationCoverage

namespace Effect4Harness.SchemaGenerationCoverage

private def fixture : String :=
  (Effect4.Codegen.Schema.generate? "AllRepresentationsSchema"
    Test.Codegen.SchemaGenerationCoverage.document).getD ""

#eval do
  IO.println ("// " ++ (← Tools.GeneratedStamp.line "harness/schema-generation/EmitCoverageFixture.lean"))
  IO.print fixture

end Effect4Harness.SchemaGenerationCoverage
