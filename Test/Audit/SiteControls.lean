import Tools.Site

/-!
# Controls of the documentation site's checks

The site's checks run before any file is written (`Tools.Site.Site.check`, decisions row 363), and
a node folded from data enters the typed shell only where the content model admits it
(`Whatwg.Html.Child.check`, the package's answer to ask W1). Each line is a control that shows where a check refuses, or a finite
evaluation that no theorem covers (decisions row 301). The site's code reads text, so every value
stands inside its `#guard` and the battery declares nothing (the axiom gate).

Each guard builds the same site: a root page, and a document of two parts, one referring to the
other, split at its top-level parts under `/s/`.
-/

namespace Test.Audit.SiteControls

open Tools.Document Tools.Site

-- the split: the section, then a page for each part; the site passes its checks
#guard
  let s : Site := { pages := { path := [], doc := { title := "Root", body := [] } } ::
    (split (fun path _ => path == ["s"]) ["s"] "s"
      { title := "Source", body := [.part "a" "A" [.para [.ref "b" "to B"]], .part "b" "B" [.para [.text "B"]]] }) }
  s.pages.map (·.path) == [[], ["s"], ["s", "a"], ["s", "b"]] && s.check.isEmpty

-- a reference to a part made a page links to that page's folder, from its sibling
#guard
  let s : Site := { pages := { path := [], doc := { title := "Root", body := [] } } ::
    (split (fun path _ => path == ["s"]) ["s"] "s"
      { title := "Source", body := [.part "a" "A" [.para [.ref "b" "to B"]], .part "b" "B" [.para [.text "B"]]] }) }
  (s.at? ["s", "a"]).map (fun p => target (keyIndex s) p "b") == some "../b/"

-- control: a link to no page or file of the site
#guard
  let s : Site := { pages := { path := [], doc := { title := "Root", body := [] } } ::
    (split (fun path _ => path == ["s"]) ["s"] "s"
      { title := "Source", body := [.part "a" "A" [.para [.ref "b" "to B"]], .part "b" "B" [.para [.text "B"]]] }) }
  ({ s with pages := s.pages ++
      [{ path := ["x"], doc := { title := "X", body := [.para [.link "../nowhere/" "dead"]] } }] } : Site).check
    == ["/x/: link ../nowhere/: no page or file of the site"]

-- control: a reference resolves in its own space only
#guard
  let s : Site := { pages := { path := [], doc := { title := "Root", body := [] } } ::
    (split (fun path _ => path == ["s"]) ["s"] "s"
      { title := "Source", body := [.part "a" "A" [.para [.ref "b" "to B"]], .part "b" "B" [.para [.text "B"]]] }) }
  ({ s with pages := s.pages ++
      [{ path := ["y"], space := "other", doc := { title := "Y", body := [.para [.ref "b" "B"]] } }] } : Site).check
    == ["/y/: reference b: no part has this key"]

-- control: a page whose parent is no page
#guard
  let s : Site := { pages := [{ path := [], doc := { title := "Root", body := [] } }] }
  ({ s with pages := s.pages ++ [{ path := ["z", "deep"], doc := { title := "Z", body := [] } }] } : Site).check
    == ["/z/deep/: no page above it"]

-- control: the content model refuses a block where the shell's `main` would hold it
#guard !(Whatwg.Html.Child.check (.element "p" [] [.element "div" [] []]) : Except _ (Whatwg.Html.Child InMain)).toBool

end Test.Audit.SiteControls
