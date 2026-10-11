import Tools.View.Build
import Tools.View.FlowSpecimen
import Tools.View.Specimen
import Tools.View.Output

open Tools.View

def savePages (out : System.FilePath) (name : String) (pages : List Page) : IO Unit := do
  let folder := out / name
  IO.FS.createDirAll folder
  for (page, i) in pages.zipIdx do
    let (w, h) := pageSize 1280 page
    let calls := pageCalls {} 1280 page
    IO.FS.writeFile (folder / s!"{i}.svg") (svg {} w.toNat h.toNat 1 (lowerAll 1 calls))
    IO.FS.writeFile (folder / s!"{i}.draw")
      ("\n".intercalate (stream {} w.toNat h.toNat 2 (lowerAll 2 calls)))
    IO.FS.writeFile (folder / s!"{i}.txt") ("\n".intercalate (pageText page))
  IO.println s!"{name}: {pages.length} pages"

def main (args : List String) : IO Unit := do
  let [out] := args | throw (IO.userError "Snapshot needs one output directory")
  for (name, program) in Effect4.Program.Wire.Corpus.all do
    let some requests := Build.requests program | throw (IO.userError s!"No build for {name}")
    savePages out name ((Build.frames name requests).map (·.page))
  savePages out "flows" FlowSpecimen.frames
  savePages out "specimen" Specimen.frames
