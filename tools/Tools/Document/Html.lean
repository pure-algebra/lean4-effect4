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
  | .link href label => el "a" [.text label] [("href", href)]
  | .status w => el "span" [.text w] [("class", "status"), ("data-status", w)]

def line (l : Line) : List RawNode := l.map inline

/-- The HTML algebra. Its carrier takes the nesting depth, which fixes a section's heading level. -/
def algebra : Algebra (Nat → List RawNode) where
  para l _ := [el "p" (line l)]
  fields rs _ := [el "dl" (rs.flatMap fun (k, v) => [el "dt" [.text k], el "dd" (line v)])]
  items ls _ := [el "ul" (ls.map fun l => el "li" (line l))]
  code lang body _ :=
    let block := el "pre" [el "code" [.text body] [("class", "language-" ++ lang)]]
    -- A diagram's source folds away until the design language draws it (row 354, point 8).
    if lang == "mermaid" then
      [el "details" [el "summary" [.text s!"Diagram source (Mermaid, {(body.splitOn "\n").length} lines)"], block]
        [("class", "diagram")]]
    else [block]
  table hs rs _ :=
    if rs.isEmpty then [] else
      let head := el "thead" [el "tr" (hs.map fun h => el "th" [.text h] [("scope", "col")])]
      let body := el "tbody" (rs.map fun r => el "tr" (r.map fun c => el "td" (line c)))
      [el "div" [el "table" [head, body]]
        [("class", "scroll"), ("role", "region"), ("tabindex", "0"),
         ("aria-label", "Table: " ++ ", ".intercalate hs)]]
  part k t body depth :=
    let heading := el ("h" ++ toString (min 6 depth))
      [.text t, el "a" [.text "#"] [("class", "self"), ("href", fragment k), ("aria-label", "Link to " ++ t)]]
    [el "section" (heading :: (body.flatMap (· (depth + 1)))) [("id", k)]]

/-! ## The stylesheet -/

/-- The file of the page's own rules (`page.css`), from the repository's root. The rules read the
looks' custom properties: the ground, the ink and the
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
def sheetPath : System.FilePath := "tools/Tools/Document/page.css"

/-- Where a page's rules stand: the text of `page.css`, inlined in the page's `style` element, or
a link to the file, for a page that follows edits of it (the document specimen,
`tools/Drivers/DocSpecimen.lean`) or a page of the site (`Tools.Site`), with the looks inlined or
linked as a file of their own. -/
inductive Sheet where
  | inline (css : String)
  | link (href : String) (looks : Option String)

/-- The text with its comments taken out. -/
private def uncomment : List Char → List Char
  | '/' :: '*' :: rest =>
    let rec skip : List Char → List Char
      | '*' :: '/' :: more => uncomment more
      | _ :: more => skip more
      | [] => []
    skip rest
  | c :: rest => c :: uncomment rest
  | [] => []

private def isHex (c : Char) : Bool := c.isDigit || ('a' ≤ c && c ≤ 'f') || ('A' ≤ c && c ≤ 'F')

/-- A `#` and three to eight hex digits after a space, a colon, a comma or a bracket. -/
private def hexColour : List Char → Bool
  | c :: d :: rest =>
    let digits := rest.takeWhile isHex
    (d == '#' && (c == ' ' || c == ':' || c == ',' || c == '(') && 3 ≤ digits.length &&
      digits.length ≤ 8 && !(((rest.drop digits.length).head?.map Char.isAlphanum).getD false)) ||
      hexColour (d :: rest)
  | _ => false

/-- What in one line of rules is a literal colour or family, if anything. -/
private def lineProblem (line : String) : Option String :=
  let colourFns := ["rgb(", "rgba(", "hsl(", "hsla(", "hwb(", "lab(", "lch(", "oklab(", "oklch("]
  let after (key : String) : List String := ((line.splitOn key).drop 1).map (·.trimAscii.toString)
  if hexColour (' ' :: line.toList) then some "a literal colour"
  else if colourFns.any (fun f => (line.splitOn f).length > 1) then some "a literal colour"
  else if (after "font-family:").any (fun v => !v.startsWith "var(") then some "a literal family"
  else if (after " font:").any (fun v => ((v.splitOn "var(--e4-font-").length ≤ 1)) then
    some "a font without the look's family"
  else none

/-- **The design language's rule for the page's rules** (decisions row 354, point 1: the look is the
only data of a colour, a face or a timing): the first line of `css` that writes a literal colour or a
family not taken from the look, with its number, or none. -/
def Sheet.problem (css : String) : Option String :=
  let lines := (String.ofList (uncomment css.toList)).splitOn "\n"
  (lines.zipIdx.findSome? fun (line, n) =>
    (lineProblem line).map fun what => s!"line {n + 1}: {what}: {line.trimAscii}")

/-- The declarations of `light` that are not the base's: those a light scheme changes. -/
def changed (base light : List String) : List String := light.filter fun d => !base.contains d

/-- **The page's looks**: the base look's custom properties on the root; for a reader who prefers
light, and for print, the declarations in which the light look differs (decisions row 354,
point 3). The page's rules read them. -/
def looks (base light : Look) : String :=
  Tools.View.Tokens.cssRule ":root" (Tools.View.Tokens.declarations base) ++
    "@media (prefers-color-scheme: light), print {\n" ++
    Tools.View.Tokens.cssRule ":root"
      (changed (Tools.View.Tokens.declarations base) (Tools.View.Tokens.declarations light)) ++
    "}\n"

/-- The head's elements that style a page: the looks and the inlined rules in one `style`, or the
looks and a link to the rules. -/
def styleNodes (base light : Look) : Sheet → List RawNode
  | .inline css => [el "style" [.text (looks base light ++ css)]]
  | .link href none => [el "style" [.text (looks base light)], el "link" [] [("rel", "stylesheet"), ("href", href)]]
  | .link href (some lk) =>
    [el "link" [] [("rel", "stylesheet"), ("href", lk)], el "link" [] [("rel", "stylesheet"), ("href", href)]]

/-! ## The page -/

/-- The page: the head, then a header with the title and the parts' navigation, then the parts. -/
def page (d : Document) (base light : Look) (sheet : Sheet) : RawNode :=
  let tops := d.body.filterMap fun
    | .part k t _ => some (el "li" [el "a" [.text t] [("href", fragment k)]])
    | _ => none
  el "html" [
    el "head" ([
      el "meta" [] [("charset", "utf-8")],
      el "meta" [] [("name", "viewport"), ("content", "width=device-width, initial-scale=1")],
      el "title" [.text d.title]] ++ styleNodes base light sheet),
    el "body" ([
      el "a" [.text "Skip to the content"] [("class", "skip"), ("href", "#content")],
      el "header" ([el "h1" [.text d.title]] ++
        (if tops.isEmpty then [] else [el "nav" [el "ol" tops] [("aria-label", "Contents")]])),
      el "main" ((Block.foldList algebra d.body).flatMap (· 2)) [("id", "content")]] ++
      (if d.producer.isEmpty then [] else
        [el "footer" [el "p" [.text "Provenance"] [("class", "label")],
          el "ul" (d.producer.map fun line => el "li" [.text line])]]))]
    [("lang", "en")]

/-- A refusal in words: the element names along its path, from the root, then its reason. -/
def describe (tree : RawNode) (r : Content.Refusal) : String :=
  let names := (List.range (r.path.length + 1)).filterMap fun k =>
    match tree.at? (r.path.take k) with
    | some (.element name _ _) => some name
    | _ => none
  "/" ++ "/".intercalate names ++ ": " ++ r.reason.describe

/-- The document as an HTML page in two looks, the dark base and the paper look for a light scheme,
with the page's rules (`page.css`, read by the caller): its checks, the rules' check, then the
content model, then the serializer. -/
def Document.html (d : Document) (sheet : Sheet) (base : Look := {}) (light : Look := Look.paper) :
    Except String String := do
  if let .error errors := d.check then throw ("document refused: " ++ "; ".intercalate errors)
  if let .inline css := sheet then
    if let some why := Sheet.problem css then throw (s!"{sheetPath} refused at " ++ why)
  let tree := page d base light sheet
  unless Content.validIn Content.Ctx.document tree do
    throw ("HTML refused: " ++
      ((Content.explain Content.Ctx.document tree).map (describe tree)).getD
        "the content model refuses the tree")
  return Print.renderDoc tree

end Tools.Document.Html
