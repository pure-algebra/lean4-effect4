import Tools.Site
import Tools.Document.Specimen

/-!
# The documentation site (decisions row 363)

    lake env lean --run tools/Drivers/Site.lean SITE REPORT

Builds the site as one value (`Tools.Site.Site`) and writes every file of it into the folder
`SITE`. Its pages:

* the landing page, at the root;
* the semantics report, split into pages: a page for each concept and each section of the
  report, and a page for each requirement under the plan. The report's document is read from
  `REPORT/document.json`, which `lake exe semantics-report REPORT` writes, and the report itself
  is copied as `semantics/report.json`;
* the document specimen;
* the contents page, every page by section.

Its other files: the page's rules (`page.css`, after the design language's check), the looks
(`looks.css`: the dark base and the paper look, read from its token file at each run), the pages and their parts (`site.json`), the host's `_headers`, and the page for a
missing path (`404.html`). `make site` runs the report when its sources changed, then this, into a
fresh folder, and puts it at `.lake/gen/site`.
-/

open Tools.Document Tools.Site Tools.View

/-- The landing page. -/
def landing : Document where
  title := "Effect4"
  producer := ["tools/Drivers/Site.lean", "make site"]
  body := [
    .para [.text "Effect4 is Effect's runtime written in Lean as a model with defined semantics. ",
      .text "A program is data: a typed term that Lean checks, runs on a reference machine, lowers to OCaml ",
      .text "and prints as TypeScript."],
    .para [.text "Each claim about that runtime carries its evidence: a theorem that is ", .status "proved",
      .text ", a theorem proved ", .status "modulo", .text " named goals, or a planned ", .status "goal",
      .text " stated with its proof to come."],
    .part "start" "Start here" [
      .items [
        [.link "semantics/" "Semantics evidence", .text ": every claim by concept, its status and its Lean statement, ",
         .text "and the plan of goals that the open requirements rest on."],
        [.link "specimen/" "Document specimen", .text ": every kind of block and status mark, as the pages draw them."],
        [.link "contents/" "Contents", .text ": every page of the site."]]],
    .part "contract" "For a framework" [
      .para [.text "Every page is also its document as JSON, in the format ", .code "effect4-document/1", .text " (",
        .link "semantics/document.json" "the first page of the semantics", .text "), and ",
        .link "site.json" "site.json", .text " lists the pages with their parts. The report behind the semantics pages is ",
        .link "semantics/report.json" "report.json", .text "."]]]

/-- Where the semantics report splits: every part of its first page but the legend of statuses,
and every requirement under the plan. -/
def semanticsCut (path : List String) (key : String) : Bool :=
  (path == ["semantics"] && key != "statuses") || path == ["semantics", "plan"]

/-- The page for a path the site does not have. Its links start at the root, since the host
serves it at any path. -/
def notFound (s : Site) : Except String String := do
  let doc : Document := { title := "Not found", body := [.para [.text "No page stands at this path. ",
    .link "/" "The site's first page", .text " and ", .link "/contents/" "every page", .text " are there."]] }
  let shell : Shell := {
    tabTitle := "Not found · Effect4", styles := .files "/looks.css" "/page.css", home := "/"
    sections := s.sections.map fun q => sectionItem ("/" ++ folders q.path) q.doc.title none }
  return text (render shell doc.title (← blocks Html.fragment doc))

def main (args : List String) : IO UInt32 := do
  let [site, report] := args | IO.eprintln "usage: Site SITE REPORT"; return 2
  let dir : System.FilePath := site
  let report : System.FilePath := report
  let semantics ← match Lean.Json.parse (← IO.FS.readFile (report / "document.json")) >>= Json.Document.reads with
    | .ok d => pure d
    | .error why => IO.eprintln s!"{report / "document.json"}: {why}"; return 1
  let pages := [({ path := [], doc := landing, space := "landing" } : Page)] ++
    split semanticsCut ["semantics"] "semantics" semantics ++
    [{ path := ["specimen"], doc := Specimen.specimen, space := "specimen" }]
  let files := ["page.css", "looks.css", "site.json", "_headers", "404.html", "semantics/report.json"]
  let draft : Site := { pages, files }
  let s : Site := { draft with pages := pages ++ [{ path := ["contents"], doc := contents draft, space := "contents" }] }
  let css ← IO.FS.readFile Html.sheetPath
  if let some why := Html.Sheet.problem css then
    IO.eprintln s!"{Html.sheetPath} refused at {why}"; return 1
  IO.FS.createDirAll dir
  let errors ← s.write dir
  unless errors.isEmpty do
    for e in errors do IO.eprintln e
    return 1
  IO.FS.writeFile (dir / "page.css") css
  IO.FS.writeFile (dir / "looks.css") (looksCss (← Tokens.lookFile "paper"))
  IO.FS.writeFile (dir / "_headers") headers
  match Lean.Json.parse (← IO.FS.readFile (report / "semantics.json")) with
  | .ok j => IO.FS.writeFile (dir / "semantics" / "report.json") (j.compress ++ "\n")
  | .error why => IO.eprintln s!"{report / "semantics.json"}: {why}"; return 1
  match notFound s with
  | .ok html => IO.FS.writeFile (dir / "404.html") html
  | .error why => IO.eprintln s!"404: {why}"; return 1
  IO.println s!"site: {s.pages.length} pages in {dir}"
  return 0
