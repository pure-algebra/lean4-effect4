import Tools.Document

/-!
# Tools.Document.Specimen — one document with every block kind

A small document that holds every block kind, parts nested to the sixth heading level, every status
word, references, code in three languages and a wide table. The document specimen
(`tools/Drivers/DocSpecimen.lean`) and the documentation site (`tools/Drivers/Site.lean`) write it,
so a change of a fold or of the page's rules shows on every kind at once (decisions rows 362, 363).
-/

namespace Tools.Document.Specimen

open Tools.Document

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
      .text ". A line long enough to show the measure of a paragraph at the page's width. ",
      .text "Its length can be judged against the type's size and the leading between lines."],
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
    .part "figure" "A figure" [
      .para [.text "A graph as data, drawn by the view's layout. A node links to the part it opens, a goal is lit, ",
        .text "and the figure is also given in words."],
      .graph "fig:specimen" "A claim proved modulo one goal, through two steps; an arrow goes to a node the proof reaches first."
        [{ key := "claim", label := "decision_preserves", status := "modulo", ref := some "statuses" },
         { key := "loop", label := "loop_preserves", status := "modulo" },
         { key := "deliver", label := "deliver_preserves", status := "modulo", detail := "2 steps" },
         { key := "goal", label := "countdown_parks", status := "goal", ref := some "tables" },
         { key := "base", label := "frame_typing", status := "proved" }]
        [("claim", "loop"), ("claim", "deliver"), ("loop", "goal"), ("deliver", "goal"), ("deliver", "base")]],
    .part "depth" "Nesting, level 2" [
      .para [.text "Each part's heading level is its depth."],
      .part "depth-3" "Level 3" [
        .part "depth-4" "Level 4" [
          .part "depth-5" "Level 5" [
            .part "depth-6" "Level 6" [.para [.text "The deepest heading."]]]]]]]

end Tools.Document.Specimen
