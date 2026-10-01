import Effect4.Codegen.Schema
import Effect4.Schema.Bridge

/-! Seat W1, the host twin of `E4-SCHEMA-CE-061`: Lean's `Exit` and `Cause` documents, written by
the production `Bridge.schema` after row 128's commit, and one written with the defect id before it
(`effect/schema/Defect`), as a TypeScript module for `defect-twin.ts`. Run from the worktree root:
`lake env lean -M4096 --run docs/research/2026-10-01-data-wave/W1/host/EmitDefectDocs.lean <out.ts>`. -/

open Effect4 Effect4.Program

def docOf (r : Representation) : String :=
  Codegen.Schema.documentSource { representation := r, references := [] }

/-- The `Exit` document with the defect slot as `Bridge.defectRep` wrote it before row 128's commit. -/
def exitBefore : Representation :=
  .declaration ⟨"effect/schema/Exit", .null⟩ none
    [Schema.Bridge.schema .bool, Schema.Bridge.schema .string,
     .declaration ⟨"effect/schema/Defect", .null⟩ none [] []] []

def main (args : List String) : IO Unit := do
  let [output] := args | throw (IO.userError "expected one output path")
  IO.FS.writeFile output
    ("// Fresh Lean output (seat W1). Do not edit.\n" ++
     "export const exitDoc = " ++ docOf (Schema.Bridge.schema (.exitOf .bool .string)) ++ ";\n" ++
     "export const causeDoc = " ++ docOf (Schema.Bridge.schema (.causeOf .string)) ++ ";\n" ++
     "export const exitDocBefore = " ++ docOf exitBefore ++ ";\n")
