import Tools.Site
import Tools.Document.Specimen
import Tools.Document.Markdown
import Tools.Document.Sheet

/-!
# The documentation site (decisions row 363)

    lake env lean --run tools/Drivers/Site.lean SITE REPORT

Builds the site as one value (`Tools.Site.Site`) and writes every file of it into the folder
`SITE`. The written copy is Markdown under `docs/site/` (its `README.md` says how to write it),
read at every build (`Tools.Document.Markdown`). Its pages:

* the landing page, at the root (`docs/site/landing.md`);
* the guides (`docs/site/guides/*.md`, in the order of their file names, each at its name with
  the leading digits and dash taken off), under a page that lists them;
* the semantics report, split into pages: a page for each concept and each section of the
  report, and a page for each requirement under the plan. A concept's or a requirement's copy
  (`docs/site/concepts/<id>.md`, `docs/site/requirements/<id>.md`) stands on its page after the
  page's opening summary. The report's document is read from
  `REPORT/document.json`, which `lake exe semantics-report REPORT` writes, and the report itself
  is copied as `semantics/report.json`;
* the document specimen;
* the contents page, every page by section.

Its other files: the page's rules (`page.css`, after the design language's check), the looks
(`looks.css`: the dark base and the paper look, read from its token file at each run), the two
faces with their licences (`fonts/`, copied from `vendor/fonts/`), the pages and their parts (`site.json`), the host's `_headers`, and the page for a
missing path (`404.html`). `make site` runs the report when its sources changed, then this, into a
fresh folder, and puts it at `.lake/gen/site`.
-/

open Tools.Document Tools.Site Tools.View

/-- The folder of the site's written copy. -/
def copyDir : System.FilePath := "docs/site"

/-- A file of copy read as a document, its keys prefixed by `keyPrefix`; a refusal names the file
and the line. -/
def readCopy (path : System.FilePath) (keyPrefix : String) : IO Document := do
  match Markdown.read path.toString keyPrefix (← IO.FS.readFile path) with
  | .ok d => return d
  | .error why => throw (IO.userError why)

/-- The Markdown files of a folder in the order of their names, its `README.md` left out; none
when the folder is missing. -/
def copyFiles (dir : System.FilePath) : IO (List System.FilePath) := do
  unless ← dir.isDir do return []
  let names := ((← dir.readDir).filter fun e => e.fileName.endsWith ".md" && e.fileName != "README.md").map (·.path)
  return (names.qsort (·.toString < ·.toString)).toList

/-- A file's name with its extension and its leading digits and dash taken off: `01-reading.md`
is `reading`. -/
def guideSlug (f : System.FilePath) : String :=
  let stem := f.fileStem.getD ""
  ((stem.dropWhile Char.isDigit).dropWhile (· == '-')).toString

/-- The copy of the page whose key is `key`, as a part after the page's opening summary; refused
when no page has the key. -/
def place (pages : List Page) (key : String) (copy : Document) : Except String (List Page) :=
  if !(pages.any (·.key == some key)) then .error s!"copy for {key}: no page has this key" else
  .ok (pages.map fun p => if p.key != some key then p else
    { p with doc := { p.doc with
      body := p.doc.body.take 1 ++ [.part ("about:" ++ key) copy.title copy.body] ++ p.doc.body.drop 1 } })

/-- The page that lists the guides, each with its opening paragraph. -/
def guidesPage (guides : List Page) : Page where
  path := ["guides"]
  space := "guides"
  doc := { title := "Guides", producer := ["docs/site/guides/", "make site"], body := [
    .para [.text "Each guide explains one part of the site or of the semantics, in plain words."],
    .items (guides.map fun g =>
      let summary : Line := match g.doc.body with
        | .para l :: _ => .text ": " :: l
        | _ => []
      .link (g.path.getLast! ++ "/") g.doc.title :: summary)] }

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
  try run args catch e => IO.eprintln e; return 1
where run (args : List String) : IO UInt32 := do
  let [site, report] := args | IO.eprintln "usage: Site SITE REPORT"; return 2
  let dir : System.FilePath := site
  let report : System.FilePath := report
  let semantics ← match Lean.Json.parse (← IO.FS.readFile (report / "document.json")) >>= Json.Document.reads with
    | .ok d => pure d
    | .error why => IO.eprintln s!"{report / "document.json"}: {why}"; return 1
  let landing ← readCopy (copyDir / "landing.md") ""
  let guides ← (← copyFiles (copyDir / "guides")).mapM fun f => do
    return ({ path := ["guides", guideSlug f], doc := ← readCopy f "", space := "guides:" ++ guideSlug f } : Page)
  let mut semanticsPages := split semanticsCut ["semantics"] "semantics" semantics
  for (folder, keyOf) in [("concepts", fun (id : String) => "concept:" ++ id), ("requirements", fun id => "req:" ++ id)] do
    for f in ← copyFiles (copyDir / folder) do
      let key := keyOf (f.fileStem.getD "")
      match place semanticsPages key (← readCopy f s!"about:{key}:") with
      | .ok ps => semanticsPages := ps
      | .error why => IO.eprintln s!"{f}: {why}"; return 1
  let pages := [({ path := [], doc := { landing with producer := landing.producer ++ ["make site"] }, space := "landing" } : Page)] ++
    (if guides.isEmpty then [] else guidesPage guides :: guides) ++ semanticsPages ++
    [{ path := ["specimen"], doc := Specimen.specimen, space := "specimen" }]
  let fonts := ["source-serif-4/source-serif-4-latin-opsz-normal.woff2", "source-serif-4/source-serif-4-latin-opsz-italic.woff2",
    "source-serif-4/LICENSE", "jetbrains-mono/jetbrains-mono-latin-wght-normal.woff2", "jetbrains-mono/LICENSE", "README.md"]
  let files := ["page.css", "looks.css", "site.json", "_headers", "404.html", "semantics/report.json"] ++
    fonts.map ("fonts/" ++ ·)
  let draft : Site := { pages, files }
  let s : Site := { draft with pages := pages ++ [{ path := ["contents"], doc := contents draft, space := "contents" }] }
  let css ← IO.FS.readFile Sheet.path
  if let some why := Sheet.problem css then
    IO.eprintln s!"{Sheet.path} refused: {why}"; return 1
  IO.FS.createDirAll dir
  let errors ← s.write dir
  unless errors.isEmpty do
    for e in errors do IO.eprintln e
    return 1
  IO.FS.writeFile (dir / "page.css") css
  IO.FS.writeFile (dir / "looks.css") (looksCss (← Tokens.lookFile "paper"))
  IO.FS.writeFile (dir / "_headers") headers
  for f in fonts do
    let target := dir / "fonts" / f
    if let some parent := target.parent then IO.FS.createDirAll parent
    IO.FS.writeBinFile target (← IO.FS.readBinFile ((("vendor/fonts" : System.FilePath)) / f))
  match Lean.Json.parse (← IO.FS.readFile (report / "semantics.json")) with
  | .ok j => IO.FS.writeFile (dir / "semantics" / "report.json") (j.compress ++ "\n")
  | .error why => IO.eprintln s!"{report / "semantics.json"}: {why}"; return 1
  match notFound s with
  | .ok html => IO.FS.writeFile (dir / "404.html") html
  | .error why => IO.eprintln s!"404: {why}"; return 1
  IO.println s!"site: {s.pages.length} pages in {dir}"
  return 0
