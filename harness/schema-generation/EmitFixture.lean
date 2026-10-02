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

private def fixture : Except Codegen.Schema.ReferenceRefusal String :=
  (Codegen.Schema.moduleSyntax "PersonSchema" personDocument
    [ ("ada", .obj [("name", .str "Ada"), ("active", .bool true)])
    , ("prototypeData", .obj [("__proto__", .str "data")]) ]).map
    (TypeScript.Render.module TypeScript.house0)

#eval do
  IO.println ("// " ++ Tools.GeneratedStamp.note "harness/schema-generation/EmitFixture.lean")
  match fixture with
  | .ok text => IO.print text
  | .error e => throw (IO.userError s!"the emitter refused at {e.path}: {e.reason}")

end Effect4Harness.SchemaGeneration
