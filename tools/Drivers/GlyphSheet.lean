import Tools.View.GlyphSheet
import Tools.View.CellSheet
import Tools.View.Tokens

/-!
# The vocabulary of marks and the value pictures, as studio pages (VS-1, VS-2, decisions row 367)

`lake env lean --run tools/Drivers/GlyphSheet.lean OUT` writes two pages:

* `OUT/glyphs.html`: every mark of `Tools.View.Glyph` drawn, and each sort's constructors with
  their marks;
* `OUT/cells.html`: the Queue's cell drawn by its type, step by step (`Tools.View.CellSheet`).

Both stand in the site's shell and the base look. The studio serves them (`tools/view/out/docs/`),
and the viewer shows one after each build. Viewing ergonomics only: no test, and nothing reads
the output.
-/

open Tools.View Tools.View.Glyph Whatwg.Html

/-- One page: its blocks checked where they stand, in the shell, with its contents from the
blocks' sections. -/
def page (out : System.FilePath) (file title : String) (blocks : List RawNode) (css : String) :
    IO UInt32 := do
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
    IO.FS.writeFile (out / file) (Tools.Site.text (Tools.Site.render shell title checked))
    IO.println s!"{file}: {out / file}"
    return 0
  | .error why => IO.eprintln s!"{file}: refused: {why}"; return 1

def main (args : List String) : IO UInt32 := do
  let [out] := args | IO.eprintln "usage: GlyphSheet OUT"; return 2
  let out : System.FilePath := out
  IO.FS.createDirAll out
  let a ← page out "glyphs.html" "The vocabulary of marks" sheetBlocks contactCss
  let b ← page out "cells.html" "The Queue's cell, drawn by its type" CellSheet.blocks CellSheet.css
  return max a b
