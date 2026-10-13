import Tools.Site
import Tools.Document.Specimen
import Tools.Document.Sheet

/-!
# The document specimen (decisions row 362, DOC-1 of the docs audit)

    lake env lean --run tools/Drivers/DocSpecimen.lean OUT

Writes one small document that holds every block kind, parts nested to the sixth heading level,
every status word, references, code in three languages and a wide table, through the shell and the HTML
fold of every page of the site (`Tools.Site`, checked by the HTML Standard's content model):

* `OUT/specimen.html`, the dark look with the paper look for a light preference, as the page is;
* `OUT/specimen-dark.html` and `OUT/specimen-paper.html`, each in one look whatever the preference.

The pages link the page's rules (`tools/Tools/Document/page.css`) where the semantics page inlines
them, so an edit of the rules shows in the studio with no run; the rules' check runs here too. The
paper look is read from its token file at each run (`Tokens.lookFile`), over the dark base, so a
token edit shows after `tools/view/v -d` with no build. It imports no law module. The studio shows the two looks side by
side. Viewing ergonomics only: it is no test, and nothing reads its output.
-/

open Tools.Document Tools.Document.Specimen Tools.View

def main (args : List String) : IO UInt32 := do
  let [out] := args | IO.eprintln "usage: DocSpecimen OUT"; return 2
  let out : System.FilePath := out
  IO.FS.createDirAll out
  if let some why := Sheet.problem (← IO.FS.readFile Sheet.path) then
    IO.eprintln s!"{Sheet.path} refused: {why}"
  let dark : Look := {}
  let paper ← Tokens.lookFile "paper"
  let write (name : String) (base light : Look) : IO Bool := do
    let shell : Tools.Site.Shell := {
      tabTitle := specimen.title
      home := "../index.html"
      styles := .inlineLooks (Tools.Document.Html.looks base light ++ Tokens.rules)
        "../../../Tools/Document/page.css" }
    match Tools.Site.blocks Tools.Document.Html.fragment specimen with
    | .ok blocks => IO.FS.writeFile (out / name) (Tools.Site.text (Tools.Site.render shell specimen.title blocks)); return true
    | .error why => IO.eprintln s!"{name}: {why}"; return false
  let a ← write "specimen.html" dark paper
  let b ← write "specimen-dark.html" dark dark
  let c ← write "specimen-paper.html" paper paper
  IO.println s!"docs: the specimen in {out}"
  return if a && b && c then 0 else 1
