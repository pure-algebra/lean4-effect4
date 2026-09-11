import Test.Codegen.SchemaGenerationContract

/-! Emit fresh results from the public codec, not copies of the expected JSON. -/
open Effect4 Effect4.Program

def main (args : List String) : IO Unit := do
  let [output] := args | throw (IO.userError "expected one output path")
  let entries ← Test.Codegen.SchemaGenerationContract.codecCases.mapM fun (name, t, v, _) => do
    let some j := Ty.encode t v | throw (IO.userError ("codec refused " ++ name))
    pure (name, j)
  IO.FS.writeFile output
    ("// Fresh Lean codec output. Do not edit.\nexport default " ++
      Codegen.Schema.jsonSource (.obj entries) ++ ";\n")
