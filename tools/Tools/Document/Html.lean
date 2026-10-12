import Tools.Document
import Whatwg.Html.Print.Render
import Whatwg.Html.Content.Valid
import Whatwg.Html.Content.Explain

/-!
# Tools.Document.Html — a document as one HTML page

The HTML fold of `Tools.Document`. It builds a `Whatwg.Html.RawNode` tree. The HTML Standard's
content model checks the tree (`Whatwg.Html.Content.validIn`, from `lean4-whatwg`), and its located
refusal (`Content.explain`, complete by `explain_none_iff`) names a refused node. The standard's
fragment serialization algorithm writes it (`Whatwg.Html.Print.renderDoc`). Tag and attribute names
are this module's. Document content reaches only text nodes and attribute values, which the
serializer escapes.

The page:

* is one file: an inline stylesheet, no script, no remote resource;
* opens with a `header` holding the title and a `nav` of the top-level parts;
* makes a part a `section` whose `id` is its key, headed `h2` to `h6` by nesting;
* makes fields a `dl`, items a `ul`, and code a `pre` around a `code` element of class
  `language-…`, the HTML Standard's convention for naming a code element's language;
* scrolls a wide table inside a focusable region labelled by its columns;
* marks a status as a `span` whose `data-status` holds the word, which the stylesheet colours;
* follows the reader's light or dark preference.
-/

namespace Tools.Document.Html
open Whatwg.Html

/-- A fragment identifier for a key: its UTF-8 bytes, a byte outside the URL fragment's safe
characters percent-encoded. -/
def fragment (key : String) : String :=
  "#" ++ String.join (key.toUTF8.toList.map fun b =>
    let c := Char.ofNat b.toNat
    if b.toNat < 128 && (c.isAlphanum || "-._~:@!$'()*+,;=/?".contains c) then c.toString
    else
      let digits := String.ofList (Nat.toDigits 16 b.toNat)
      "%" ++ (if digits.length == 1 then "0" ++ digits else digits).toUpper)

private def el (tag : String) (children : List RawNode) (attrs : List (String × String) := []) : RawNode :=
  .element tag attrs children

def inline : Inline → RawNode
  | .text s => .text s
  | .code s => el "code" [.text s]
  | .ref k label => el "a" [.text label] [("href", fragment k)]
  | .status w => el "span" [.text w] [("class", "status"), ("data-status", w)]

def line (l : Line) : List RawNode := l.map inline

/-- The HTML algebra. Its carrier takes the nesting depth, which fixes a section's heading level. -/
def algebra : Algebra (Nat → List RawNode) where
  para l _ := [el "p" (line l)]
  fields rs _ := [el "dl" (rs.flatMap fun (k, v) => [el "dt" [.text k], el "dd" (line v)])]
  items ls _ := [el "ul" (ls.map fun l => el "li" (line l))]
  code lang body _ := [el "pre" [el "code" [.text body] [("class", "language-" ++ lang)]]]
  table hs rs _ :=
    if rs.isEmpty then [] else
      let head := el "thead" [el "tr" (hs.map fun h => el "th" [.text h] [("scope", "col")])]
      let body := el "tbody" (rs.map fun r => el "tr" (r.map fun c => el "td" (line c)))
      [el "div" [el "table" [head, body]]
        [("class", "scroll"), ("role", "region"), ("tabindex", "0"),
         ("aria-label", "Table: " ++ ", ".intercalate hs)]]
  part k t body depth :=
    [el "section" (el ("h" ++ toString (min 6 depth)) [.text t] :: (body.flatMap (· (depth + 1)))) [("id", k)]]

/-- The page's stylesheet: system fonts, a readable measure, and colours for both schemes. -/
def style : String := "
:root { color-scheme: light dark; --ink: #1d2733; --muted: #556270; --line: #d5dde6; --paper: #fff;
  --panel: #f3f6f9; --link: #0b5cad; --proved: #1f7a3a; --modulo: #8a5a00; --open: #a3262a; }
@media (prefers-color-scheme: dark) { :root { --ink: #dde4ec; --muted: #9aa8b6; --line: #33404d;
  --paper: #12171d; --panel: #1b222a; --link: #7ab8ff; --proved: #6fd18a; --modulo: #e3b25a; --open: #ff8a8a; } }
* { box-sizing: border-box; }
body { margin: 0; background: var(--paper); color: var(--ink);
  font: 16px/1.55 system-ui, -apple-system, \"Segoe UI\", sans-serif; }
header, main { max-width: 72rem; margin: 0 auto; padding: 0 clamp(1rem, 4vw, 2.5rem); }
header { padding-top: 2rem; border-bottom: 1px solid var(--line); }
nav ol { display: flex; flex-wrap: wrap; gap: .25rem 1rem; padding: 0; list-style: none; }
h1, h2, h3, h4, h5, h6 { line-height: 1.25; scroll-margin-top: 1rem; }
section > h2 { margin-top: 2.5rem; padding-top: 1rem; border-top: 1px solid var(--line); }
p, dd, li { max-width: 80ch; overflow-wrap: anywhere; }
a { color: var(--link); text-underline-offset: .15em; }
:focus-visible { outline: 3px solid var(--link); outline-offset: 2px; }
code, pre { font-family: ui-monospace, SFMono-Regular, Menlo, Consolas, monospace; font-size: .9em; }
:not(pre) > code { background: var(--panel); padding: .05em .3em; border-radius: .25rem; overflow-wrap: anywhere; }
pre { background: var(--panel); border: 1px solid var(--line); border-radius: .4rem; padding: .8rem 1rem;
  white-space: pre-wrap; overflow-wrap: anywhere; }
dl { display: grid; grid-template-columns: max-content 1fr; gap: .2rem 1rem; }
dt { color: var(--muted); }
dd { margin: 0; }
.scroll { overflow-x: auto; border: 1px solid var(--line); border-radius: .4rem; margin: 1rem 0; }
table { border-collapse: collapse; width: 100%; min-width: 40rem; font-size: .92rem; }
th, td { text-align: left; vertical-align: top; padding: .45rem .7rem; border-bottom: 1px solid var(--line); }
th { background: var(--panel); }
td code { overflow-wrap: normal; }
.status { font-weight: 600; }
.status[data-status=proved] { color: var(--proved); }
.status[data-status=modulo], .status[data-status=wanted], .status[data-status=goal] { color: var(--modulo); }
.status[data-status=open], .status[data-status=refuted] { color: var(--open); }
@media print { .scroll { overflow: visible; } }
"

/-- The page: the head, then a header with the title and the parts' navigation, then the parts. -/
def page (d : Document) : RawNode :=
  let tops := d.body.filterMap fun
    | .part k t _ => some (el "li" [el "a" [.text t] [("href", fragment k)]])
    | _ => none
  el "html" [
    el "head" [
      el "meta" [] [("charset", "utf-8")],
      el "meta" [] [("name", "viewport"), ("content", "width=device-width, initial-scale=1")],
      el "title" [.text d.title],
      el "style" [.text style]],
    el "body" [
      el "header" ([el "h1" [.text d.title]] ++
        (if tops.isEmpty then [] else [el "nav" [el "ol" tops] [("aria-label", "Contents")]])),
      el "main" ((Block.foldList algebra d.body).flatMap (· 2))]]
    [("lang", "en")]

/-- A refusal in words: the element names along its path, from the root, then its reason. -/
def describe (tree : RawNode) (r : Content.Refusal) : String :=
  let names := (List.range (r.path.length + 1)).filterMap fun k =>
    match tree.at? (r.path.take k) with
    | some (.element name _ _) => some name
    | _ => none
  "/" ++ "/".intercalate names ++ ": " ++ r.reason.describe

/-- The document as an HTML page: its checks, then the content model, then the serializer. -/
def Document.html (d : Document) : Except String String := do
  if let .error errors := d.check then throw ("document refused: " ++ "; ".intercalate errors)
  let tree := page d
  unless Content.validIn Content.Ctx.document tree do
    throw ("HTML refused: " ++
      ((Content.explain Content.Ctx.document tree).map (describe tree)).getD
        "the content model refuses the tree")
  return Print.renderDoc tree

end Tools.Document.Html
