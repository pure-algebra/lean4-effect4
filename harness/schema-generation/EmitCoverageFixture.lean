import Test.Codegen.SchemaGenerationCoverage

namespace Effect4Harness.SchemaGenerationCoverage

private def fixture : String :=
  (Effect4.Codegen.Schema.generate? "AllRepresentationsSchema"
    Test.Codegen.SchemaGenerationCoverage.document).getD ""

#eval IO.print fixture

end Effect4Harness.SchemaGenerationCoverage
