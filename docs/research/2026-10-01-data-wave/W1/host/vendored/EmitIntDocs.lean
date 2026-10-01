import Test.Codegen.SchemaGenerationContract

/-! Seat W1, the host case of row 179's ninth key: the battery's transcriptions of rc.112's own
`Schema.Int` and `Schema.Int.check(Schema.isGreaterThanOrEqualTo(0))` documents
(`Test/Codegen/SchemaGenerationContract.lean`, `rcIntDocument`, `rcNatDocument`), with the production
reader's answer on each, as a TypeScript module for `int-twin.ts`. Run from the worktree root:
`lake env lean -M4096 --run docs/research/2026-10-01-data-wave/W1/host/vendored/EmitIntDocs.lean <out.ts>`. -/

open Effect4 Effect4.Program Test.Codegen.SchemaGenerationContract

def docOf (r : Representation) : String :=
  Codegen.Schema.documentSource { representation := r, references := [] }

def main (args : List String) : IO Unit := do
  let [output] := args | throw (IO.userError "expected one output path")
  IO.FS.writeFile output
    ("// Fresh Lean output (seat W1). Do not edit.\n" ++
     "export const intDoc = " ++ docOf rcIntDocument ++ ";\n" ++
     "export const natDoc = " ++ docOf rcNatDocument ++ ";\n" ++
     "export const leanReadsInt = " ++
       toString (Schema.Bridge.ofSchema rcIntDocument == some .int) ++ ";\n" ++
     "export const leanReadsNat = " ++
       toString (Schema.Bridge.ofSchema rcNatDocument == some .nat) ++ ";\n")
