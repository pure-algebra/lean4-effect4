import Tools.Document
import Tools.Document.Figure
import Tools.View.Tokens
import Whatwg.Html.Print.Render
import Whatwg.Html.Content.Valid
import Whatwg.Html.Content.Explain

/-!
# Tools.Document.Html — a document's blocks as HTML

The HTML fold of `Tools.Document`. It builds `Whatwg.Html.RawNode` trees, which the site's typed
shell (`Tools.Site`) admits where they stand: the HTML Standard's content model checks each one
(`Whatwg.Html.Content.validIn`, from `lean4-whatwg`), and its located refusal (`Content.explain`,
complete by `explain_none_iff`) names a refused node. Tag and attribute names are this module's.
Document content reaches only text nodes and attribute values, which the serializer escapes.

The blocks:

* a part is a `section` whose `id` is its key, headed `h2` to `h6` by nesting, its key beside
  its title as a link to itself;
* fields are a `dl`, items a `ul`, and code a `pre` around a `code` element of class
  `language-…`, the HTML Standard's convention for naming a code element's language; a Lean
  statement of more than eight lines folds into a `details` under its first line;
* a wide table scrolls inside a focusable region labelled by its columns;
* a figure is a `figure` around its picture, an SVG drawn by the view's layout whose nodes link
  (`Tools.Document.Figure`), and its caption, then the figure in words: each node, linked, with
  its status mark and the nodes it points to, for a reader who does not see the picture;
* a status is a `span` whose `data-status` holds the word; the stylesheet draws the mark of its
  shape before the word, keyed on that attribute (`page.css`; decisions row 354, point 2);
* a reference is a link whose target the caller resolves: a part of the same page by its
  fragment, or a part of another page of the site.

The page's colours, the families of its faces, the weight of its rules and its corners are the
looks' (`Tools.View.Look`), as their CSS custom properties (`Tools.View.Tokens.declarations`): the
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

/-- Code's text, with a place to break after each dot of a qualified name: a name with no space
breaks between its components (`Effect4.Program.Typed.…`) and nowhere else. -/
def codeText (s : String) : List RawNode :=
  if s.any Char.isWhitespace || !s.contains '.' then [.text s] else
    let parts := s.splitOn "."
    (parts.zipIdx.flatMap fun (p, i) =>
      if i + 1 == parts.length then [.text p] else [.text (p ++ "."), el "wbr" []])

/-- Inline content, with the link of a reference from `target`. -/
def inline (target : String → String) : Inline → RawNode
  | .text s => .text s
  | .code s => el "code" (codeText s)
  | .ref k label => el "a" [.text label] [("href", target k)]
  | .link href label => el "a" [.text label] [("href", href)]
  | .status w => el "span" [.text w] [("class", "status"), ("data-status", w)]

def line (target : String → String) (l : Line) : List RawNode := l.map (inline target)

/-- The HTML algebra, with the link of a reference from `target`. Its carrier takes the nesting
depth, which fixes a section's heading level. -/
def algebra (target : String → String := fragment) : Algebra (Nat → List RawNode) where
  para l _ := [el "p" (line target l)]
  fields rs _ := [el "dl" (rs.flatMap fun (k, v) => [el "dt" [.text k], el "dd" (line target v)])]
  items ls _ := [el "ul" (ls.map fun l => el "li" (line target l))]
  code lang body _ :=
    let block := el "pre" [el "code" [.text body] [("class", "language-" ++ lang)]]
    let lines := body.splitOn "\n"
    -- A diagram's source folds away; a figure (`Block.graph`) draws a graph (row 365).
    if lang == "mermaid" then
      [el "details" [el "summary" [.text s!"Diagram source (Mermaid, {lines.length} lines)"], block]
        [("class", "diagram")]]
    -- A long statement folds under its first line (row 366, point 6).
    else if lang == "lean" && lines.length > 8 then
      [el "details" [el "summary" [el "code" [.text ((lines.head?.getD "").trimAscii.toString ++ " …")],
          .text s!" ({lines.length} lines)"], block] [("class", "statement")]]
    else [block]
  table hs rs _ :=
    if rs.isEmpty then [] else
      let head := el "thead" [el "tr" (hs.map fun h => el "th" [.text h] [("scope", "col")])]
      let body := el "tbody" (rs.map fun r => el "tr" (r.map fun c => el "td" (line target c)))
      [el "div" [el "table" [head, body]]
        [("class", "scroll"), ("role", "region"), ("tabindex", "0"),
         ("aria-label", "Table: " ++ ", ".intercalate hs)]]
  graph k caption ns es _ :=
    let pic := (Figure.picture (fun r => some (target r)) ns es).toRaw
    let name (n : GraphNode) : RawNode := match n.ref with
      | some r => el "a" [.text n.label] [("href", target r)]
      | none => .text n.label
    let word (n : GraphNode) : List RawNode :=
      let next := es.filterMap fun (a, b) => if a == n.key then (ns.find? (·.key == b)).map (·.label) else none
      [name n] ++
        (if n.status.isEmpty then [] else [.text " ", el "span" [.text n.status] [("class", "status"), ("data-status", n.status)]]) ++
        (if n.detail.isEmpty then [] else [.text (", " ++ n.detail)]) ++
        (if next.isEmpty then [] else [.text (" → " ++ ", ".intercalate next)])
    [el "figure" [
        el "div" [pic] [("class", "scroll"), ("role", "region"), ("tabindex", "0"), ("aria-label", "Figure: " ++ caption)],
        el "figcaption" [.text caption]] [("id", k), ("class", "graph")],
     el "details" [el "summary" [.text "The figure in words"], el "ul" (ns.map fun n => el "li" (word n))]
       [("class", "words")]]
  part k t body depth :=
    -- the part's key beside its title: its identity, linked to itself (row 366, point 4)
    let heading := el ("h" ++ toString (min 6 depth))
      [.text t, el "a" [.text k] [("class", "key"), ("href", fragment k)]]
    [el "section" (heading :: (body.flatMap (· (depth + 1)))) [("id", k)]]

/-! ## The stylesheet -/

/-- The file of the page's own rules (`page.css`), from the repository's root. Every page of the
site links it. The rules read the
looks' custom properties: the ground, the ink and the
rule's colour; the families of the name, data, label and title faces; the weight of a rule and of a
frame; the radius of a corner. The band behind a code block and a table's head is the look's band:
the rule's colour at the band's tone over the ground, as the view draws the band behind a lit row.
A measure, a size and a space are the page's.

**The status marks** (decisions row 354, point 2) are drawn here once, before the word of a status,
keyed on its `data-status`: a mark of the promise-and-keeping family, in `currentColor` and with no
hue. Proved is a filled circle; modulo a circle filled on its left half; a planned goal (`goal`, a
claim's or a plan node's) a hollow circle; open a dashed circle; refuted
the failure cross `×` of the notation. A circle's outline is the look's frame. A circle is a
pseudo-element with no content, which a screen reader does not read; the cross is text with an
empty alternative (`content: "×" / ""`), after a plain `content` for a browser without the
alternative. A circle's fill is a background, so print and a forced-colours mode are told to keep
it. The word beside the mark names the status, to a reader and to an agent. `absent`, `assumed`
and `missing` take no mark. -/
def sheetPath : System.FilePath := "tools/Tools/Document/page.css"

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

/-- What in one line of rules is a literal colour or family, or an ornament with no meaning (a
shadow, a gradient, a filter: decisions row 366, point 3), if anything. An `@font-face` rule names
the family it defines, so its line may write one. -/
private def lineProblem (line : String) : Option String :=
  let colourFns := ["rgb(", "rgba(", "hsl(", "hsla(", "hwb(", "lab(", "lch(", "oklab(", "oklch("]
  let ornaments := ["box-shadow", "text-shadow", "gradient(", "filter:"]
  let has (key : String) : Bool := (line.splitOn key).length > 1
  let after (key : String) : List String := ((line.splitOn key).drop 1).map (·.trimAscii.toString)
  if hexColour (' ' :: line.toList) then some "a literal colour"
  else if colourFns.any has then some "a literal colour"
  else if let some o := ornaments.find? has then some s!"an ornament with no meaning ({o})"
  else if has "@font-face" then none
  else if (after "font-family:").any (fun v => !v.startsWith "var(") then some "a literal family"
  else if (after " font:").any (fun v => ((v.splitOn "var(--e4-font-").length ≤ 1)) then
    some "a font without the look's family"
  else none

/-- **The design language's rule for the page's rules** (decisions row 354, point 1: the look is the
only data of a colour, a face or a timing; row 366, point 3: no ornament without a meaning): the
first line of `css` that writes a literal colour, a family not taken from the look, a shadow, a
gradient or a filter, with its number, or none. -/
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

/-- A refusal in words: the element names along its path, from the root, then its reason. -/
def describe (tree : RawNode) (r : Content.Refusal) : String :=
  let names := (List.range (r.path.length + 1)).filterMap fun k =>
    match tree.at? (r.path.take k) with
    | some (.element name _ _) => some name
    | _ => none
  "/" ++ "/".intercalate names ++ ": " ++ r.reason.describe

end Tools.Document.Html
