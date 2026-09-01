import Effect4.Target.TypeScript.Schema

namespace Effect4Harness.SchemaGeneration

open Effect4

private def person : Representation :=
  Schema.struct
    [ Schema.property "name"
        ((Schema.withCheck Schema.string Schema.Check.trimmed).getD Schema.string)
    , Schema.property "active" Schema.boolean ]

private def personDocument : Document := Schema.document person

private def fixture : String :=
  (Target.TypeScript.Schema.generate? "PersonSchema" personDocument
    [ ("ada", .obj [("name", .str "Ada"), ("active", .bool true)])
    , ("prototypeData", .obj [("__proto__", .str "data")]) ]).getD ""

#eval IO.print fixture

end Effect4Harness.SchemaGeneration
