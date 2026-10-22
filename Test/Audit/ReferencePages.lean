import Tools.Reference
import Tools.Document.Json

/-!
# The reference pages read back

Each page of the reference set (`Tools.Reference`, written to `generated/reference/` by
`tools/Drivers/Reference.lean`) is a document, and its JSON is the contract a reader outside Lean
reads. Each line is a finite evaluation at the pages as they are built from the tree's data
(decisions row 301): the page passes `Document.check`, and its JSON reads back through
`Document.reads`, which writes the read document again and compares the bytes. The dictionary page
is built from a two-row fixture, since its real input is a file. Every value stands inside its
`#guard`, so the battery declares nothing.
-/

namespace Test.Audit.ReferencePages

open Tools.Document Tools.Reference

-- forms, native, marks and refusals: each passes its check and reads back
#guard [forms, native, marks, refusals].all fun d =>
  (d.check matches .ok ()) && (Json.Document.reads (Json.Document.json d) matches .ok _)

-- the dictionary page, from a fixture: a declaration, a word, and two paths with no file
#guard
  let text := "## 3. The dictionary\n\n### 3.1 A part\n\n" ++
    "| Term | Meaning here | Tree anchor | Literature | Do not use | Qualifier |\n" ++
    "| --- | --- | --- | --- | --- | --- |\n" ++
    "| **a** | m | `f` (`src/A.lean`); `g` (`src/A.lean`) | — | — | — |\n" ++
    "| **b** | m | `docs/B.md`; `h` (`src/C.lean`) | — | — | — |\n\n## 4. Next\n"
  let files := [("src/A.lean", "def f := 1\n-- g\n")]
  let d := dictionary (entries text) (files.lookup ·)
  (d.check matches .ok ()) && (Json.Document.reads (Json.Document.json d) matches .ok _) &&
    ((entries text).flatMap (·.anchors)).map (fun a => (find a (files.lookup a.path)).text) ==
      ["declaration", "word", "no file", "no file"]

-- the index, with a row per page
#guard
  let d := index [("forms", ["Effect4.Program.arms"], rows forms)]
  (d.check matches .ok ()) && (Json.Document.reads (Json.Document.json d) matches .ok _)

end Test.Audit.ReferencePages
