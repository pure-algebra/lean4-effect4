import Tools.SemanticsDocument
import Tools.Document.Html
import Tools.Site

open Tools.Semantics

/-- `Semantics OUT` writes the report's JSON, Markdown and page into `OUT`; `Semantics OUT SITE`
also writes the semantics page of the documentation site into `SITE/semantics/`, with its
document as JSON and the report as `report.json` (decisions row 363). -/
def main (args : List String) : IO UInt32 := do
  let (outdir, site) ← match args with
    | [o] => pure (o, none)
    | [o, s] => pure (o, some s)
    | _ => IO.eprintln "usage: Semantics <output-directory> [<site-directory>]"; return 1
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
    let css ← IO.FS.readFile Tools.Document.Html.sheetPath
    let html ← match Tools.Document.Html.Document.html doc (.inline css) with
      | .ok page => pure page
      | .error why => IO.eprintln s!"semantics document: {why}"; return 1
    IO.FS.writeFile (dir / "semantics.json") (report.toJson.pretty ++ "\n")
    IO.FS.writeFile (dir / "semantics.md") doc.markdown
    IO.FS.writeFile (dir / "semantics.html") html
    if let some site := site then
      let page : Tools.Site.Page := { path := ["semantics"], doc }
      if let .error why ← Tools.Site.writePage site page then
        IO.eprintln s!"semantics site page: {why}"; return 1
      IO.FS.writeFile ((site : System.FilePath) / "semantics" / "report.json") (report.toJson.compress ++ "\n")
    return 0
