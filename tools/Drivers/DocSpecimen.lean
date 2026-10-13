import Tools.Document.Html

/-!
# The document specimen (decisions row 362, DOC-1 of the docs audit)

    lake env lean --run tools/Drivers/DocSpecimen.lean OUT

Writes one small document that holds every block kind, parts nested to the sixth heading level,
every status word, references, code in three languages and a wide table, through the same HTML fold
as the semantics page (`Tools.Document.Html`, checked by the HTML Standard's content model):

* `OUT/specimen.html`, the dark look with the paper look for a light preference, as the page is;
* `OUT/specimen-dark.html` and `OUT/specimen-paper.html`, each in one look whatever the preference.

It imports no law module, so it rebuilds in seconds after an edit of the HTML fold or its
stylesheet. The studio shows the two looks side by side (`tools/view/v -d`). Viewing ergonomics
only: it is no test, and nothing reads its output.
-/

open Tools.Document Tools.View

/-- A line with a word of every status. -/
def statuses : Line :=
  ["proved", "modulo", "goal", "wanted", "open", "refuted", "absent", "assumed", "missing"].foldr
    (fun w acc => .status w :: .text " " :: acc) []

/-- Every block kind, in parts nested to the sixth level. -/
def specimen : Document where
  title := "Document specimen"
  producer := ["tools/Drivers/DocSpecimen.lean", "tools/view/v -d"]
  body := [
    .para [.text "A paragraph of running text, with ", .code "inline code", .text ", a reference to ",
      .ref "tables" "the table part", .text ", and a status: ", .status "proved",
      .text ". A line long enough to show the measure of a paragraph at the page's width, so the ",
      .text "length of a line can be judged against the type's size and the leading between lines."],
    .part "statuses" "Every status" [
      .para [.text "Each mark is a shape, with no hue (decisions row 354, point 2):"],
      .para statuses,
      .fields [("proved", [.status "proved", .text " filled"]), ("modulo", [.status "modulo", .text " half"]),
        ("goal", [.status "goal", .text " hollow"]), ("open", [.status "open", .text " dashed"]),
        ("refuted", [.status "refuted", .text " the cross"])]],
    .part "blocks" "Every block kind" [
      .para [.text "Fields, a list, and code in three languages."],
      .fields [("concept", [.code "reactive-scheduling"]), ("claim", [.ref "statuses" "random-descent"]),
        ("a field with a long label that wraps", [.text "and a value that runs on for a while to wrap"])],
      .items [[.text "a first item"], [.text "a second item, with ", .code "code"],
        [.text "a third item, with a status ", .status "modulo"]],
      .code "lean" "theorem complete_unique (eqv : Equivalence R) (bis : Bisim step R)\n    (dia : Diamond step R) : R t1 t2 ∧ c1.length = c2.length := by\n  exact ⟨hR, hl⟩",
      .code "mermaid" "flowchart LR\n  A[edit] --> B[build]\n  B --> C[look]",
      .code "text" "a plain text block\n  with its indentation kept"],
    .part "tables" "A wide table" [
      .table ["claim", "role", "status", "pointer", "a long column header"]
        [[[.code "random-descent"], [.text "fundamentalProperty"], [.status "proved"],
          [.code "Effect4.Machine.Descent.complete_unique"], [.text "a long cell that wraps"]],
         [[.code "keys-once"], [.text "preservation"], [.status "proved"],
          [.code "Effect4.Run.session_keys_once"], [.text "—"]],
         [[.code "schedule-independent"], [.text "fundamentalProperty"], [.status "absent"],
          [.text "—"], [.ref "statuses" "see the statuses"]]]],
    .part "depth" "Nesting, level 2" [
      .para [.text "Each part's heading level is its depth."],
      .part "depth-3" "Level 3" [
        .part "depth-4" "Level 4" [
          .part "depth-5" "Level 5" [
            .part "depth-6" "Level 6" [.para [.text "The deepest heading."]]]]]]]

def main (args : List String) : IO UInt32 := do
  let [out] := args | IO.eprintln "usage: DocSpecimen OUT"; return 2
  let out : System.FilePath := out
  IO.FS.createDirAll out
  let write (name : String) (base light : Look) : IO Bool := do
    match Tools.Document.Html.Document.html specimen base light with
    | .ok html => IO.FS.writeFile (out / name) html; return true
    | .error why => IO.eprintln s!"{name}: {why}"; return false
  let a ← write "specimen.html" {} Look.paper
  let b ← write "specimen-dark.html" {} {}
  let c ← write "specimen-paper.html" Look.paper Look.paper
  IO.println s!"docs: the specimen in {out}"
  return if a && b && c then 0 else 1
