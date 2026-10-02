import Tools.Semantics

open Tools.Semantics

def main (args : List String) : IO UInt32 := do
  let [outdir] := args | IO.eprintln "usage: Semantics <output-directory>"; return 1
  match ← loadReport registry with
  | .error errors =>
    for error in errors do IO.eprintln error
    return 1
  | .ok report =>
    let dir : System.FilePath := outdir
    IO.FS.createDirAll dir
    IO.FS.writeFile (dir / "semantics.json") (report.pretty ++ "\n")
    IO.FS.writeFile (dir / "semantics.md") (renderMarkdown report)
    return 0
