import Tools.View.GlyphSheet
import Tools.View.CellSheet
import Tools.View.Tube.Sheet
import Tools.View.Tube.GlyphPage
import Tools.View.Tube.Measure
import Tools.View.Tokens

/-!
# The vocabulary of marks and the value pictures, as studio pages (VS-1, VS-2, decisions row 367)

`lake env lean --run tools/Drivers/GlyphSheet.lean OUT` writes four pages:

* `OUT/glyphs.html`: every mark of `Tools.View.Glyph` drawn, and each sort's constructors with
  their marks;
* `OUT/cells.html`: the Queue's cell drawn by its type, step by step (`Tools.View.CellSheet`);
* `OUT/tubes.html`: the tube language, its morphs, and the Queue as plumbing (`Tools.View.Tube.Sheet`);
* `OUT/tube-glyphs.html`: every mark of the vocabulary as a figure of tubes, and the morphs a run
  makes (`Tools.View.Tube.GlyphPage`).

Each stands in the site's shell and the base look. The studio serves them (`tools/view/out/docs/`),
and the viewer shows one after each build. Viewing ergonomics only: no test, and nothing reads
the output.

It also writes `OUT/measure.tsv`, every figure's bytes, animations and path bytes
(`Tools.View.Tube.Measure`), and prints each page's largest figures and the milliseconds its
writing took. A studio page is measured, never refused; a figure that a documentation page would
refuse is marked.
-/

open Tools.View Tools.View.Glyph Whatwg.Html

/-- One page: its blocks checked where they stand, in the shell, with its contents from the
blocks' sections. -/
def page (out : System.FilePath) (file title : String) (blocks : List RawNode) (css : String) :
    IO (UInt32 × List Tube.Measure.Row) := do
  let t0 ← IO.monoMsNow
  let paper ← Tokens.lookFile "paper"
  let parts := blocks.filterMap fun
    | .element "section" attrs (.element "h2" _ (.text t :: _) :: _) => (attrs.lookup "id").map (·, t)
    | _ => none
  let shell : Tools.Site.Shell := {
    tabTitle := title
    home := "../index.html"
    styles := .inlineLooks (Tools.Document.Html.looks {} paper ++ Tokens.rules ++ css) "../../../Tools/Document/page.css"
    toc := parts.map fun (k, t) => Tools.Site.tocItem k t [] }
  match blocks.mapM fun n => (Child.check n : Except _ (Child Tools.Site.InMain)) |>.mapError (·.describe n) with
  | .ok checked =>
    let text := Tools.Site.text (Tools.Site.render shell title checked)
    IO.FS.writeFile (out / file) text
    let rows := Tube.Measure.rowsOfList file 0 blocks
    let inFigures := rows.foldl (· + ·.bytes) 0
    let films := (rows.filter (·.film)).length
    let ms := (← IO.monoMsNow) - t0
    IO.println s!"{file}: {out / file}: {text.utf8ByteSize} bytes, {rows.length} figures ({films} films) holding {inFigures}, written in {ms} ms"
    for r in ((rows.toArray.qsort (·.bytes > ·.bytes)).toList.take 3) do
      let over := match ({} : Tube.Measure.Limits).check r with | .ok _ => "" | .error _ => ", over a documentation page's limit"
      IO.println s!"  {r.bytes} bytes, {r.animations} animations, {r.pathBytes} of paths: {r.figure}{over}"
    if inFigures > text.utf8ByteSize then
      IO.eprintln s!"{file}: refused: its figures hold {inFigures} bytes, more than the page's {text.utf8ByteSize}"
      return (1, rows)
    return (0, rows)
  | .error why => IO.eprintln s!"{file}: refused: {why}"; return (1, [])

def main (args : List String) : IO UInt32 := do
  let [out] := args | IO.eprintln "usage: GlyphSheet OUT"; return 2
  let out : System.FilePath := out
  IO.FS.createDirAll out
  let pages ← [("glyphs.html", "The vocabulary of marks", sheetBlocks, contactCss),
    ("cells.html", "The Queue's cell, drawn by its type", CellSheet.blocks, CellSheet.css),
    ("tubes.html", "One body: the tube language", Tube.Sheet.blocks, Tube.Sheet.css),
    ("tube-glyphs.html", "Every mark as tubes", Tube.GlyphPage.blocks, Tube.GlyphPage.css)].mapM
    fun (file, title, blocks, css) => page out file title blocks css
  IO.FS.writeFile (out / "measure.tsv")
    ("\n".intercalate (Tube.Measure.HEAD :: (pages.flatMap (·.2)).map (·.line)) ++ "\n")
  return pages.foldl (fun a p => max a p.1) 0
