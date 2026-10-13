import Tools.Site
import Tools.Document.Markdown
import Tools.Document.Sheet

/-!
# Controls of the documentation site's checks

The site's checks run before any file is written (`Tools.Site.Site.checked`, decisions row 363):
the documents' own (`Site.check`), then `lean4-whatwg`'s check of the rendered site
(`Whatwg.Html.Content.Site.errors`, its answer to ask W6), which reads every `href` of every page,
the shell's too. A node folded from data enters the typed shell only where the content model
admits it (`Whatwg.Html.Child.check`, the answer to ask W1). Each line is a control that shows
where a check refuses, or a finite evaluation that no theorem covers (decisions row 301). The
site's code reads text, so every value stands inside its `#guard` and the battery declares nothing
(the axiom gate).

Each guard builds the same site: a root page, a document of two parts, one referring to the
other, split at its top-level parts under `/s/`, the contents page and the two style files that
every page's shell links.
-/

namespace Test.Audit.SiteControls

open Tools.Document Tools.Site

-- the split: the section, then a page for each part; the site passes every check
#guard
  let s : Site := { files := ["looks.css", "page.css"], pages := { path := [], doc := { title := "Root", body := [] } } ::
    (split (fun path _ => path == ["s"]) ["s"] "s"
      { title := "Source", body := [.part "a" "A" [.para [.ref "b" "to B"]], .part "b" "B" [.para [.text "B"]]] }) ++
    [{ path := ["contents"], doc := { title := "Contents", body := [] } }] }
  s.pages.map (·.path) == [[], ["s"], ["s", "a"], ["s", "b"], ["contents"]] && s.problems.isEmpty

-- a reference to a part made a page links to that page's folder, from its sibling
#guard
  let s : Site := { files := ["looks.css", "page.css"], pages := { path := [], doc := { title := "Root", body := [] } } ::
    (split (fun path _ => path == ["s"]) ["s"] "s"
      { title := "Source", body := [.part "a" "A" [.para [.ref "b" "to B"]], .part "b" "B" [.para [.text "B"]]] }) ++
    [{ path := ["contents"], doc := { title := "Contents", body := [] } }] }
  (s.at? ["s", "a"]).map (fun p => target (keyIndex s) p "b") == some "../b/"

-- control: a link to no page or file of the site, located by the elements along its path
#guard
  let s : Site := { files := ["looks.css", "page.css"], pages := { path := [], doc := { title := "Root", body := [] } } ::
    (split (fun path _ => path == ["s"]) ["s"] "s"
      { title := "Source", body := [.part "a" "A" [.para [.ref "b" "to B"]], .part "b" "B" [.para [.text "B"]]] }) ++
    [{ path := ["contents"], doc := { title := "Contents", body := [] } }] }
  ({ s with pages := s.pages ++
      [{ path := ["x"], doc := { title := "X", body := [.para [.link "../nowhere/" "dead"]] } }] } : Site).problems
    == ["/x/: link `../nowhere/` leads to `/nowhere/`: no page or file of the site: at html/body[1]/main[2]/p[1]/a[0]"]

-- control: a link to a page of the site whose tree has no such fragment
#guard
  let s : Site := { files := ["looks.css", "page.css"], pages := { path := [], doc := { title := "Root", body := [] } } ::
    (split (fun path _ => path == ["s"]) ["s"] "s"
      { title := "Source", body := [.part "a" "A" [.para [.ref "b" "to B"]], .part "b" "B" [.para [.text "B"]]] }) ++
    [{ path := ["contents"], doc := { title := "Contents", body := [] } }] }
  ({ s with pages := s.pages ++
      [{ path := ["x"], doc := { title := "X", body := [.para [.link "../s/b/#gone" "gone"]] } }] } : Site).problems
    == ["/x/: link `../s/b/#gone` leads to `/s/b/`, and `#gone` names no identifier of that page: at html/body[1]/main[2]/p[1]/a[0]"]

-- control: the shell links the contents page and the style files, so a site without them is refused
#guard
  let s : Site := { files := ["looks.css", "page.css"], pages := { path := [], doc := { title := "Root", body := [] } } ::
    (split (fun path _ => path == ["s"]) ["s"] "s"
      { title := "Source", body := [.part "a" "A" [.para [.ref "b" "to B"]], .part "b" "B" [.para [.text "B"]]] }) ++
    [{ path := ["contents"], doc := { title := "Contents", body := [] } }] }
  !({ s with files := [] } : Site).problems.isEmpty &&
    !({ s with pages := s.pages.filter (·.path != ["contents"]) } : Site).problems.isEmpty

-- control: a reference resolves in its own space only
#guard
  let s : Site := { files := ["looks.css", "page.css"], pages := { path := [], doc := { title := "Root", body := [] } } ::
    (split (fun path _ => path == ["s"]) ["s"] "s"
      { title := "Source", body := [.part "a" "A" [.para [.ref "b" "to B"]], .part "b" "B" [.para [.text "B"]]] }) ++
    [{ path := ["contents"], doc := { title := "Contents", body := [] } }] }
  ({ s with pages := s.pages ++
      [{ path := ["y"], space := "other", doc := { title := "Y", body := [.para [.ref "b" "B"]] } }] } : Site).problems
    == ["/y/: reference b: no part has this key"]

-- control: a page whose parent is no page
#guard
  let s : Site := { files := ["looks.css", "page.css"], pages := { path := [], doc := { title := "Root", body := [] } } ::
    (split (fun path _ => path == ["s"]) ["s"] "s"
      { title := "Source", body := [.part "a" "A" [.para [.ref "b" "to B"]], .part "b" "B" [.para [.text "B"]]] }) ++
    [{ path := ["contents"], doc := { title := "Contents", body := [] } }] }
  (({ s with pages := s.pages ++ [{ path := ["z", "deep"], doc := { title := "Z", body := [] } }] } : Site).problems.head?)
    == some "/z/deep/: no page above it"

-- control: the content model refuses a block where the shell's `main` would hold it
#guard !(Whatwg.Html.Child.check (.element "p" [] [.element "div" [] []]) : Except _ (Whatwg.Html.Child InMain)).toBool

/-! ## The written copy (`docs/site/`, `Tools.Document.Markdown`) -/

-- a heading's key, a reference, a link and a status word in braces
#guard match Tools.Document.Markdown.read "f.md" "p:" "# T\n\n## A part {#a}\n\nSee [it](#a), [x](../x/) and {goal}." with
  | .ok d => d.title == "T" && (Tools.Site.keys d) == ["p:a"] &&
      (match d.body with
       | [.part "p:a" "A part" [.para l]] => l == [.text "See ", .ref "a" "it", .text ", ", .link "../x/" "x",
           .text " and ", .status "goal", .text "."]
       | _ => false)
  | .error _ => false

-- control: a table is refused at its line
#guard match Tools.Document.Markdown.read "f.md" "" "# T\n\n| a | b |" with
  | .error why => why == "f.md:3: a table is not part of the subset: write a list"
  | .ok _ => false

-- control: a heading that skips a level is refused
#guard (Tools.Document.Markdown.read "f.md" "" "# T\n\n### Deep").toBool == false

-- an underscore inside a word is text (`Σ_app`); control: one that opens a word is emphasis
#guard (Tools.Document.Markdown.read "f.md" "" "# T\n\nThe part Σ_app of a context.").toBool &&
  !(Tools.Document.Markdown.read "f.md" "" "# T\n\nAn _emphasis_ here.").toBool

/-! ## The page's rules (`page.css`, `Tools.Document.Sheet`), read by CSS Syntax 3's tokens -/

-- control: a shadow is refused at its declaration, located under its rule
#guard Tools.Document.Sheet.problem ".note { color: var(--e4-ink); box-shadow: 0 0 1px var(--e4-ink) }" ==
  some "`.note` › `box-shadow: 0 0 1px var(--e4-ink)`: an ornament with no meaning (box-shadow)"

-- a comment is no token, and a selector no declaration: neither writes a colour
#guard (Tools.Document.Sheet.problem "/* #fff */ #main { color: var(--e4-ink) }").isNone

-- control: a colour in a value, inside a function and under an at-rule, is refused
#guard (Tools.Document.Sheet.problem "@media print { p { border: 1px solid rgb(0 0 0) } }").isSome

-- an `@font-face` rule names its family; control: any other rule takes the look's
#guard (Tools.Document.Sheet.problem "@font-face { font-family: \"X\" }").isNone &&
  (Tools.Document.Sheet.problem "p { font-family: \"X\" }").isSome

end Test.Audit.SiteControls
