import Tools.GeneratedStamp
import Effect4.Codegen.Schema

namespace Effect4Harness.SchemaGeneration

open Effect4

private def person : Representation :=
  Schema.struct
    [ Schema.property "name"
        ((Schema.withCheck Schema.string Schema.Check.trimmed).getD Schema.string)
    , Schema.property "active" Schema.boolean ]

private def personDocument : Document := Schema.document person

private def fixture : String :=
  TypeScript.Render.module TypeScript.house0
    (Codegen.Schema.moduleSyntax "PersonSchema" personDocument
    [ ("ada", .obj [("name", .str "Ada"), ("active", .bool true)])
    , ("prototypeData", .obj [("__proto__", .str "data")]) ])

#eval do
  IO.println ("// " ++ Tools.GeneratedStamp.note "harness/schema-generation/EmitFixture.lean")
  IO.print fixture

end Effect4Harness.SchemaGeneration
