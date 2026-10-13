import Tools.SemanticsDocument
import Tools.Document.Json

open Tools.Semantics

/-- `Semantics OUT` writes into `OUT` the report as JSON (`semantics.json`), its document as
Markdown (`semantics.md`, committed as `generated/semantics.md`) and its document as the JSON
contract (`document.json`, `effect4-document/1`), which the documentation site splits into pages
(`tools/Drivers/Site.lean`, decisions row 363). -/
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
    IO.FS.writeFile (dir / "semantics.json") (report.toJson.pretty ++ "\n")
    IO.FS.writeFile (dir / "semantics.md") doc.markdown
    IO.FS.writeFile (dir / "document.json") ((Tools.Document.Json.Document.json doc).compress ++ "\n")
    return 0
