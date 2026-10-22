import Tools.Document
import Tools.Document.Figure
import Tools.View.Tokens
import Whatwg.Html.Print.Render
import Whatwg.Html.Content.Valid
import Whatwg.Html.Content.Explain
import Whatwg.Html.Node.Region.Words

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
* a wide table scrolls inside a focusable region named by its columns (`regionRaw`, lean4-whatwg's
  scrollable region, ask W13);
* a figure is a `figure` around its picture, an SVG drawn by the view's layout whose nodes link
  (`Tools.Document.Figure`), in a region named by the figure's caption, and the caption; then its
  description, headed `description`, which the figure names (`aria-describedby`): each node,
  linked, with its status mark and the nodes it points to, for a reader who does not see the
  picture. The package writes the pair (`Region.withWordsRaw`, ask W13): the identifiers come
  from the figure's key, written once, and the words follow the figure, so the caption stays
  beside the picture;
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
      [regionRaw (.label ("Table: " ++ ", ".intercalate hs)) [el "table" [head, body]] (some "scroll")]
  graph k caption ns es _ :=
    -- a node's anchor, the figure's key before its own: one id a page, however many figures draw it
    let pic := (Figure.picture (fun r => some (target r)) (fun key => some (Figure.anchorIn k key)) ns es).toRaw
    let name (n : GraphNode) : RawNode := match n.ref with
      | some r => el "a" [.text n.label] [("href", target r)]
      | none => .text n.label
    let word (n : GraphNode) : List RawNode :=
      let next := es.filterMap fun (a, b) => if a == n.key then (ns.find? (·.key == b)).map (·.label) else none
      [name n] ++
        (if n.status.isEmpty then [] else [.text " ", el "span" [.text n.status] [("class", "status"), ("data-status", n.status)]]) ++
        (if n.detail.isEmpty then [] else [.text (", " ++ n.detail)]) ++
        (if next.isEmpty then [] else [.text (" → " ++ ", ".intercalate next)])
    Region.withWordsRaw k [pic] [.text caption] "description"
      [el "ul" (ns.map fun n => el "li" (word n))] (some "graph") (some "scroll")
  part k t body depth :=
    -- the part's key beside its title: its identity, linked to itself (row 366, point 4)
    let heading := el ("h" ++ toString (min 6 depth))
      [.text t, el "a" [.text k] [("class", "key"), ("href", fragment k)]]
    [el "section" (heading :: (body.flatMap (· (depth + 1)))) [("id", k)]]

/-! ## The looks (the page's rules are `Tools.Document.Sheet`) -/

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

end Tools.Document.Html
