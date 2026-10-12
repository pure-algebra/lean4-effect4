import Tools.Document
import Tools.View.Tokens
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
* marks a status as a `span` whose `data-status` holds the word; the stylesheet draws the mark of
  its shape before the word, keyed on that attribute (`rules`; decisions row 354, point 2);
* takes its colours, the families of its faces, the weight of its rules and its corners from the
  looks (`Tools.View.Look`), as their CSS custom properties (`Tools.View.Tokens.declarations`): the
  dark look is the base, and a reader who prefers light, and print, get the paper look (row 354,
  point 3).
-/

namespace Tools.Document.Html
open Whatwg.Html
open Tools.View (Look)

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

/-! ## The stylesheet -/

/-- The page's own rules, which read the looks' custom properties: the ground, the ink and the
rule's colour; the families of the name, data, label and title faces; the weight of a rule and of a
frame; the radius of a corner. The band behind a code block and a table's head is the look's band:
the rule's colour at the band's tone over the ground, as the view draws the band behind a lit row.
A measure, a size and a space are the page's.

**The status marks** (decisions row 354, point 2) are drawn here once, before the word of a status,
keyed on its `data-status`: a mark of the promise-and-keeping family, in `currentColor` and with no
hue. Proved is a filled circle; modulo a circle filled on its left half; a planned goal a hollow
circle, and so is `wanted`, whose claim's pointer is a planned goal; open a dashed circle; refuted
the failure cross `×` of the notation. A circle's outline is the look's frame. A circle is a
pseudo-element with no content, which a screen reader does not read; the cross is text with an
empty alternative (`content: "×" / ""`), after a plain `content` for a browser without the
alternative. A circle's fill is a background, so print and a forced-colours mode are told to keep
it. The word beside the mark names the status, to a reader and to an agent. `absent`, `assumed`
and `missing` take no mark. -/
def rules : String := "
:root { --band: color-mix(in srgb, var(--e4-color-rule) calc(var(--e4-tone-band) * 100%), var(--e4-color-ground)); }
* { box-sizing: border-box; }
body { margin: 0; background: var(--e4-color-ground); color: var(--e4-color-ink);
  font: 16px/1.55 var(--e4-font-name-family); }
header, main { max-width: 72rem; margin: 0 auto; padding: 0 clamp(1rem, 4vw, 2.5rem); }
header { padding-top: 2rem; border-bottom: var(--e4-stroke-rule) solid var(--e4-color-rule); }
nav ol { display: flex; flex-wrap: wrap; gap: .25rem 1rem; padding: 0; list-style: none; }
h1, h2, h3, h4, h5, h6 { font-family: var(--e4-font-title-family); line-height: 1.25; scroll-margin-top: 1rem; }
section > h2 { margin-top: 2.5rem; padding-top: 1rem; border-top: var(--e4-stroke-rule) solid var(--e4-color-rule); }
p, dd, li { max-width: 80ch; overflow-wrap: anywhere; }
a { color: inherit; text-underline-offset: .15em; }
:focus-visible { outline: 3px solid var(--e4-color-ink); outline-offset: 2px; }
code, pre { font-family: var(--e4-font-data-family); font-size: .9em; }
:not(pre) > code { background: var(--band); padding: .05em .3em; border-radius: var(--e4-stroke-radius);
  overflow-wrap: anywhere; }
pre { background: var(--band); border: var(--e4-stroke-rule) solid var(--e4-color-rule);
  border-radius: var(--e4-stroke-radius); padding: .8rem 1rem; white-space: pre-wrap; overflow-wrap: anywhere; }
dl { display: grid; grid-template-columns: max-content 1fr; gap: .2rem 1rem; }
dt { font-family: var(--e4-font-label-family); font-style: var(--e4-font-label-style); }
dd { margin: 0; }
.scroll { overflow-x: auto; border: var(--e4-stroke-rule) solid var(--e4-color-rule);
  border-radius: var(--e4-stroke-radius); margin: 1rem 0; }
table { border-collapse: collapse; width: 100%; min-width: 40rem; font-size: .92rem; }
th, td { text-align: left; vertical-align: top; padding: .45rem .7rem;
  border-bottom: var(--e4-stroke-rule) solid var(--e4-color-rule); }
th { background: var(--band); }
td code { overflow-wrap: normal; }
.status { white-space: nowrap; }
.status:is([data-status=proved], [data-status=modulo], [data-status=goal], [data-status=wanted],
  [data-status=open])::before { content: \"\"; display: inline-block; box-sizing: border-box;
  width: .7em; height: .7em; margin-right: .35em; vertical-align: -.05em;
  border: var(--e4-stroke-frame) solid currentColor; border-radius: 50%;
  -webkit-print-color-adjust: exact; print-color-adjust: exact; forced-color-adjust: none; }
.status[data-status=proved]::before { background: currentColor; }
.status[data-status=modulo]::before { background: linear-gradient(to right, currentColor 50%, transparent 50%); }
.status[data-status=open]::before { border-style: dashed; }
.status[data-status=refuted]::before { content: \"×\"; content: \"×\" / \"\"; display: inline-block;
  width: .7em; margin-right: .35em; text-align: center; }
@media print { .scroll { overflow: visible; } }
"

/-- The declarations of `light` that are not the base's: those a light scheme changes. -/
def changed (base light : List String) : List String := light.filter fun d => !base.contains d

/-- **The page's stylesheet**: the base look's custom properties on the root; for a reader who
prefers light, and for print, the declarations in which the light look differs; then the page's
rules, which read them (decisions row 354, point 3). -/
def style (base light : Look) : String :=
  Tools.View.Tokens.cssRule ":root" (Tools.View.Tokens.declarations base) ++
    "@media (prefers-color-scheme: light), print {\n" ++
    Tools.View.Tokens.cssRule ":root"
      (changed (Tools.View.Tokens.declarations base) (Tools.View.Tokens.declarations light)) ++
    "}\n" ++ rules

/-! ## The page -/

/-- The page: the head, then a header with the title and the parts' navigation, then the parts. -/
def page (d : Document) (base light : Look) : RawNode :=
  let tops := d.body.filterMap fun
    | .part k t _ => some (el "li" [el "a" [.text t] [("href", fragment k)]])
    | _ => none
  el "html" [
    el "head" [
      el "meta" [] [("charset", "utf-8")],
      el "meta" [] [("name", "viewport"), ("content", "width=device-width, initial-scale=1")],
      el "title" [.text d.title],
      el "style" [.text (style base light)]],
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

/-- The document as an HTML page in two looks, the dark base and the paper look for a light scheme:
its checks, then the content model, then the serializer. -/
def Document.html (d : Document) (base : Look := {}) (light : Look := Look.paper) : Except String String := do
  if let .error errors := d.check then throw ("document refused: " ++ "; ".intercalate errors)
  let tree := page d base light
  unless Content.validIn Content.Ctx.document tree do
    throw ("HTML refused: " ++
      ((Content.explain Content.Ctx.document tree).map (describe tree)).getD
        "the content model refuses the tree")
  return Print.renderDoc tree

end Tools.Document.Html
