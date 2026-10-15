import Tools.TyVectors
import Effect4.Codegen.Types
import TypeScript.Render

/-!
# The codegen review's type-spelling probe (2026-10-15)

`make check-target` asks tsgo about the strings `Ty.renderRaw` prints (`tools/Tools/TyVectors.lean`,
`tools/Tools/RowTypes.lean`). A printed module spells a type through another printer:
`Codegen.Types.ofTy`, rendered by the pinned package (`TypeScript.Render.type`). This probe reads
every type of the assignability vectors and counts where the two spellings differ. A finite
evaluation; it asserts nothing. Run from the repository root, through the shared slot:

    lake env lean -M4096 docs/research/2026-10-15-codegen-review/probes/TypeSpellings.lean
-/

open Effect4.Program

namespace CodegenReviewTypes

/-- Every type that a vector names, once, in order of first use. -/
def vectorTypes : List Ty :=
  Tools.TyVectors.allPairs.foldl (fun acc (_, a, b) =>
    let acc := if acc.contains a then acc else acc ++ [a]
    if acc.contains b then acc else acc ++ [b]) []

/-- The printed module's spelling of a type: `ofTy`, rendered by the pinned package. -/
def printed (t : Ty) : Option String :=
  (Effect4.Codegen.Types.ofTy t).map (TypeScript.Render.type TypeScript.house0)

/-- The probe's lines: the counts, then each type whose two spellings differ. -/
def report : List String :=
  let rows := vectorTypes.map fun t => (t.renderRaw, printed t)
  let differ := rows.filter fun (raw, out) => out != some raw
  s!"probe: types {rows.length}, spellings differ at {differ.length}" ::
    differ.map fun (raw, out) => s!"probe: differ\trenderRaw {raw}\tprinted {out.getD "(no printed form)"}"

#eval IO.println (String.intercalate "\n" report)

end CodegenReviewTypes
