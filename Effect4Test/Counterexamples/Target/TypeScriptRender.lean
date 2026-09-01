import Effect4.Target.TypeScript.Schema

/-!
Executable witnesses for `E4-TARGET-CE-001` through `E4-TARGET-CE-004`.
-/

namespace Effect4Test.Counterexamples.Target.TypeScriptRender

open Effect4.Target.TypeScript

def hostileString : String := "\"\\\n\r\tλ"

#guard Render.quoted house0 hostileString = "\"\\\"\\\\\\n\\r\\tλ\""

def longField : List (String × Expr) :=
  [("field", .str "a value longer than a formatter width should inspect")]

#guard Render.expr house0 0 (.object longField) =
  "{ field: \"a value longer than a formatter width should inspect\" }"

#guard Render.expr house0 0 (.objectML longField) =
  "{\n  field: \"a value longer than a formatter width should inspect\",\n}"

def rawEscapeHatch : Decl := .raw "arbitrary host text"

#guard Render.decl house0 rawEscapeHatch = "arbitrary host text\n"

#guard Effect4.Target.TypeScript.Schema.jsonSource
    (.obj [("__proto__", .str "data")]) =
  "Object.fromEntries([[\"__proto__\", \"data\"]])"

end Effect4Test.Counterexamples.Target.TypeScriptRender
