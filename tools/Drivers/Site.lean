import Tools.Site
import Tools.Document.Specimen

/-!
# The documentation site's own pages (decisions row 363)

    lake env lean --run tools/Drivers/Site.lean SITE

Writes into the folder `SITE` every file of the site that the semantics report does not: the
landing page, the document specimen, the page for a missing path (`404.html`), the page's rules
(`page.css`, after the design language's check), the looks (`looks.css`) and the host's
`_headers`. The semantics report writes its own page (`lake exe semantics-report OUT SITE`).
`make site` runs both into a fresh folder and puts it at `.lake/gen/site`.
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
        [.link "specimen/" "Document specimen", .text ": every kind of block and status mark, as the pages draw them."]]],
    .part "contract" "For a framework" [
      .para [.text "Every page is also its document as JSON, in the format ", .code "effect4-document/1", .text ": ",
        .link "semantics/document.json" "the semantics page", .text " and ",
        .link "specimen/document.json" "the specimen", .text ". The report behind the semantics page is ",
        .link "semantics/report.json" "report.json", .text "."]]]

/-- The page for a path the site does not have. -/
def notFound : Document where
  title := "Not found"
  body := [.para [.text "No page stands at this path. ", .link "/" "The site's first page", .text "."]]

def main (args : List String) : IO UInt32 := do
  let [site] := args | IO.eprintln "usage: Site SITE"; return 2
  let dir : System.FilePath := site
  IO.FS.createDirAll dir
  let css ← IO.FS.readFile Html.sheetPath
  if let some why := Html.Sheet.problem css then
    IO.eprintln s!"{Html.sheetPath} refused at {why}"; return 1
  IO.FS.writeFile (dir / "page.css") css
  IO.FS.writeFile (dir / "looks.css") looksCss
  IO.FS.writeFile (dir / "_headers") headers
  let mut ok := true
  for p in [({ path := [], doc := landing } : Page), { path := ["specimen"], doc := Specimen.specimen }] do
    if let .error why ← writePage dir p then IO.eprintln why; ok := false
  match Html.Document.html notFound (.link "/page.css" (some "/looks.css")) {} Look.paper with
  | .ok html => IO.FS.writeFile (dir / "404.html") html
  | .error why => IO.eprintln s!"404: {why}"; ok := false
  IO.println s!"site: the landing page, the specimen and the host's files in {dir}"
  return if ok then 0 else 1
