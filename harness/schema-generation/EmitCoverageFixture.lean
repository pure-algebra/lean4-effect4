import Tools.GeneratedStamp
import Test.Codegen.SchemaGenerationCoverage

namespace Effect4Harness.SchemaGenerationCoverage

private def fixture : Except Effect4.Codegen.Schema.ReferenceRefusal String :=
  (Effect4.Codegen.Schema.moduleSyntax "AllRepresentationsSchema"
    Test.Codegen.SchemaGenerationCoverage.document).map
    (TypeScript.Render.module TypeScript.house0)

#eval do
  IO.println ("// " ++ Tools.GeneratedStamp.note "harness/schema-generation/EmitCoverageFixture.lean")
  match fixture with
  | .ok text => IO.print text
  | .error e => throw (IO.userError s!"the emitter refused at {e.path}: {e.reason}")

end Effect4Harness.SchemaGenerationCoverage
