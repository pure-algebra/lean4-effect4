import Tools.Reference
import Tools.Document.Sheet

/-!
# The reference pages (`generated/reference/`)

    lake env lean --run tools/Drivers/Reference.lean OUT [REPORT]

Builds the reference set (`Tools.Reference.site`) and writes every file of it into the folder
`OUT`: each page's `index.html`, `index.md` and `document.json`, the set's `site.json`, the page's
rules (`page.css`, after the design language's check) and the looks (`looks.css`, the paper look
read from its token file, the data face from `vendor/fonts/`). `scripts/generate.py --only
reference` runs it into a fresh folder and installs the files under `generated/reference/`.

The inputs it reads at the run:

* the dictionary, `docs/core/controlled-english.md`, and every file its anchors name;
* the semantics report's document: `REPORT/document.json` when `REPORT` is given (the folder that
  `make gen-semantics` writes, `.lake/gen/semantics-report`), else the committed
  `generated/reference/semantics/document.json`, which this driver wrote from a report before;
  each is read through `Document.reads`, so a document that does not write back the same JSON is
  refused;
* each pinned file of the vendored sources, which must hold its pin's last line.

Every other page is Lean data, folded at the run. The run refuses, and writes nothing, when a pin
names a line its file lacks, when the rules fail their check, or when the set fails
`Site.checked`.
-/

open Tools.Document Tools.Site Tools.Reference Tools.View

/-- The committed semantics document of the set. -/
def committedSemantics : System.FilePath := "generated/reference/semantics/document.json"

/-- The text of a file of the repository, by its path; none when no file stands there. -/
def readFile? (path : String) : IO (Option String) := do
  let p : System.FilePath := path
  if ← p.isDir then return none
  try return some (← IO.FS.readFile p) catch _ => return none

def main (args : List String) : IO UInt32 := do
  try run args catch e => IO.eprintln e; return 1
where run (args : List String) : IO UInt32 := do
  let (out, report) ← match args with
    | [out] => pure (out, none)
    | [out, report] => pure (out, some report)
    | _ => IO.eprintln "usage: Reference OUT [REPORT]"; return 2
  let dir : System.FilePath := out
  -- the semantics report's document
  let source : System.FilePath := match report with
    | some r => (r : System.FilePath) / "document.json"
    | none => committedSemantics
  let semantics ← match Lean.Json.parse (← IO.FS.readFile source) >>= Json.Document.reads with
    | .ok d => pure d
    | .error why => IO.eprintln s!"{source}: {why}"; return 1
  -- the dictionary, with the text of every file its anchors name, each read once
  let es := entries (← IO.FS.readFile "docs/core/controlled-english.md")
  let paths := (es.flatMap fun e => e.anchors.map (·.path)).eraseDups
  let texts ← paths.mapM fun p => return (p, ← readFile? p)
  let dictionaryPage := dictionary es fun p => (texts.lookup p).join
  -- the pins: each file holds its pin's last line
  let docs := [forms, native, marks, refusals]
  for p in pins docs do
    let path := vendorSrc ++ p.file
    match ← readFile? path with
    | none => IO.eprintln s!"pin {p.file}:{p.first}: no file at {path}"; return 1
    | some t =>
      unless p.first ≤ p.last && p.last ≤ (t.splitOn "\n").length do
        IO.eprintln s!"pin {p.file}:{p.first}-{p.last}: {path} has {(t.splitOn "\n").length} lines"; return 1
  let s := site dictionaryPage semantics (pinnedFiles docs)
  let css ← IO.FS.readFile Sheet.path
  if let some why := Sheet.problem css then
    IO.eprintln s!"{Sheet.path} refused: {why}"; return 1
  IO.FS.createDirAll dir
  let errors ← s.write dir
  unless errors.isEmpty do
    for e in errors do IO.eprintln e
    return 1
  IO.FS.writeFile (dir / "page.css") css
  IO.FS.writeFile (dir / "looks.css") (looksCss (← Tokens.lookFile "paper") "../../vendor/fonts/")
  IO.println s!"reference: {s.pages.length} pages in {dir}"
  return 0
