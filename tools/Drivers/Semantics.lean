import Tools.SemanticsDocument
import Tools.Document.Html

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
    let doc := report.document
    if let .error errors := doc.check then
      for error in errors do IO.eprintln s!"semantics document: {error}"
      return 1
    let html ← match Tools.Document.Html.Document.html doc with
      | .ok page => pure page
      | .error why => IO.eprintln s!"semantics document: {why}"; return 1
    IO.FS.writeFile (dir / "semantics.json") (report.toJson.pretty ++ "\n")
    IO.FS.writeFile (dir / "semantics.md") doc.markdown
    IO.FS.writeFile (dir / "semantics.html") html
    return 0
