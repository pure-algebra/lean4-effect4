import Tools.View.GlyphSheet
import Tools.View.Tokens

/-!
# The vocabulary of marks, as a studio page (VS-1, decisions row 367)

`lake env lean --run tools/Drivers/GlyphSheet.lean OUT` writes `OUT/glyphs.html`: every mark of
`Tools.View.Glyph` drawn, and each sort's constructors with their marks, in the site's shell and
the base look. The studio serves it (`tools/view/out/docs/`), and the viewer shows it after each
build. Viewing ergonomics only: it is no test, and nothing reads its output.
-/

open Tools.View Tools.View.Glyph Whatwg.Html

def main (args : List String) : IO UInt32 := do
  let [out] := args | IO.eprintln "usage: GlyphSheet OUT"; return 2
  let out : System.FilePath := out
  IO.FS.createDirAll out
  let paper ← Tokens.lookFile "paper"
  let parts := sheetBlocks.filterMap fun
    | .element "section" attrs (.element "h2" _ (.text t :: _) :: _) => (attrs.lookup "id").map (·, t)
    | _ => none
  let shell : Tools.Site.Shell := {
    tabTitle := "The vocabulary of marks"
    home := "../index.html"
    styles := .inlineLooks (Tools.Document.Html.looks {} paper ++ Tokens.rules) "../../../Tools/Document/page.css"
    toc := parts.map fun (k, t) => Tools.Site.tocItem k t [] }
  match sheetBlocks.mapM fun n => (Child.check n : Except _ (Child Tools.Site.InMain)) |>.mapError (·.describe n) with
  | .ok blocks =>
    IO.FS.writeFile (out / "glyphs.html") (Tools.Site.text (Tools.Site.render shell "The vocabulary of marks" blocks))
    IO.println s!"glyphs: {out / "glyphs.html"}"
    return 0
  | .error why => IO.eprintln s!"glyphs: refused: {why}"; return 1
