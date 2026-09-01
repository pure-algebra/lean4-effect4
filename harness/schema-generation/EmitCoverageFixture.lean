import Effect4Test.Target.TypeScript.SchemaGenerationCoverage

namespace Effect4Harness.SchemaGenerationCoverage

private def fixture : String :=
  (Effect4.Target.TypeScript.Schema.generate? "AllRepresentationsSchema"
    Effect4Test.Target.TypeScript.SchemaGenerationCoverage.document).getD ""

#eval IO.print fixture

end Effect4Harness.SchemaGenerationCoverage
