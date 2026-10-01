import Tools.GeneratedStamp
import Test.Codegen.SchemaGenerationCoverage

namespace Effect4Harness.SchemaGenerationCoverage

private def fixture : String :=
  TypeScript.Render.module TypeScript.house0
    (Effect4.Codegen.Schema.moduleSyntax "AllRepresentationsSchema"
      Test.Codegen.SchemaGenerationCoverage.document)

#eval do
  IO.println ("// " ++ Tools.GeneratedStamp.note "harness/schema-generation/EmitCoverageFixture.lean")
  IO.print fixture

end Effect4Harness.SchemaGenerationCoverage
