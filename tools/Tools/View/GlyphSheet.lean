import Tools.View.Glyph
import Tools.Site

/-!
# Tools.View.GlyphSheet — the vocabulary of marks, drawn (VS-1, row 367)

A specimen of the marks of `Tools.View.Glyph`: each mark drawn once, with its glyph in text and
what it draws, and each sort's constructors with the mark the table gives them. The page is the
site's shell (`Tools.Site.render`) and every block passes the HTML Standard's content model where
it stands (`Child.check`), the marks' SVG included. The studio shows it beside the other
specimens (`tools/Drivers/GlyphSheet.lean`).

A mark is drawn on a grid of 24 by 24 in the ink's colour (`currentColor`), with the stroke of a
rule: so it takes the look of the page that holds it. What is promised is hollow and what is kept
is filled (row 354, point 2).
-/

namespace Tools.View.Glyph
open Whatwg.Html

private def el (tag : String) (children : List RawNode) (attrs : List (String × String) := []) : RawNode :=
  .element tag attrs children

private def path (d : String) (extra : List (String × String) := []) : RawNode := el "path" [] (("d", d) :: extra)
private def rect (x y w h : String) (extra : List (String × String) := []) : RawNode :=
  el "rect" [] ([("x", x), ("y", y), ("width", w), ("height", h)] ++ extra)
private def circle (cx cy r : String) (extra : List (String × String) := []) : RawNode :=
  el "circle" [] ([("cx", cx), ("cy", cy), ("r", r)] ++ extra)
private def filled : List (String × String) := [("fill", "currentColor")]
private def dashed (pattern : String) : List (String × String) := [("stroke-dasharray", pattern)]

/-- The parts of a mark's drawing, on a grid of 24. -/
def Shape.parts : Shape → List RawNode
  | .box => [rect "4" "6" "16" "12" [("rx", "2")]]
  | .value => [path "M3 12 H14", circle "17" "12" "3" filled]
  | .series => [rect "2" "8" "7" "8" [("rx", "1.5")], path "M9 12 H15", rect "15" "8" "7" "8" [("rx", "1.5")]]
  | .parallel => [rect "4" "4" "16" "6" [("rx", "1.5")], rect "4" "14" "16" "6" [("rx", "1.5")]]
  | .block => [rect "4" "3" "16" "18" [("rx", "2")], path "M8 8 H16 M8 12 H16 M8 16 H13"]
  | .alternative => [path "M3 12 H8 L14 6 H21 M8 12 L14 18 H21"]
  | .loop => [path "M5 15 H17 A4 4 0 0 0 17 7 H8", path "M10 4.5 L7.5 7 L10 9.5"]
  | .region => [path "M4 9 V5 A1 1 0 0 1 5 4 H9 M15 4 H19 A1 1 0 0 1 20 5 V9 M20 15 V19 A1 1 0 0 1 19 20 H15 M9 20 H5 A1 1 0 0 1 4 19 V15"]
  | .bracket => [path "M8 4 H4 V20 H8 M16 4 H20 V20 H16"]
  | .openBracket => [path "M8 4 H4 V20 H8", path "M11 4 H20 M11 20 H20" (dashed "1.5 2.5")]
  | .rail => [path "M3 10 H21 M3 14 H21"]
  | .arrow => [path "M5 5 L17 17 M10 17 H17 V10"]
  | .blockedArrow => [path "M4 12 H17 M18 6 V18"]
  | .spider => [path "M3 12 H11 M11 12 L20 6 M11 12 H21 M11 12 L20 18", circle "11" "12" "2.5" filled]
  | .rest => [path "M3 12 H21" (dashed "1 3")]
  | .hollowBox => [rect "7" "7" "10" "10"]
  | .filledBox => [rect "7" "7" "10" "10" filled]
  | .hollowDot => [circle "12" "12" "5"]
  | .filledDot => [circle "12" "12" "5" filled]
  | .port => [path "M3 12 H10 M14 6 A6 6 0 0 1 14 18"]
  | .probe => [circle "10" "10" "5", path "M14 14 L20 20"]
  | .call => [rect "3" "5" "18" "14" [("rx", "1.5")], path "M8 5 V19 M16 5 V19"]
  | .library => [rect "7" "3" "13" "15" [("rx", "1.5")], path "M4 6 V21 H16"]
  | .cross => [path "M7 7 L17 17 M17 7 L7 17"]
  | .hash => [path "M10 5 L8 19 M16 5 L14 19 M5 9.5 H19 M5 14.5 H19"]
  | .reasons => [path "M3 8 L8 13 M8 8 L3 13", path "M11 10.5 H16 M17 7 V14", path "M3 18 H21"]
  | .exitBar => [path "M10 4 V20", path "M14 4 V20" [("stroke-width", "3")]]
  | .hole => [circle "12" "12" "6" (dashed "2.5 2")]
  | .enter => [path "M8 6 L18 12 L8 18 Z" filled]
  | .barLine => [path "M12 2 V22" [("stroke-width", "2")]]
  | .fermata => [path "M4 16 A8 8 0 0 1 20 16", circle "12" "14" "1.5" filled]
  | .caesura => [path "M6 19 L11 5 M13 19 L18 5"]
  | .panel => [path "M3 7 H6 M3 12 H6 M3 17 H6" [("stroke-opacity", "0.55")], path "M10 7 H20 M10 12 H17 M10 17 H19"]
  | .cells => [path "M4 7 V17" [("stroke-opacity", "0.55")], circle "9" "12" "1.75" filled, circle "14.5" "12" "1.75" filled, circle "20" "12" "1.75" filled]
  | .slot => [path "M5 14 V18 H19 V14" [("stroke-opacity", "0.55")], circle "12" "11" "2.5" filled]
  | .tag => [path "M3 12 H8 M8 12 L11.5 7 H20 A1 1 0 0 1 21 8 V16 A1 1 0 0 1 20 17 H11.5 Z", circle "13" "12" "1.25" filled]
  | .atom => [path "M9 5 H15 M12 5 V19 M9 19 H15"]

/-- **A mark, drawn**: an SVG picture in the ink's colour, hidden from a screen reader, since the
word beside it names it. -/
def Shape.draw (s : Shape) (size : Nat := 24) : RawNode :=
  el "svg" s.parts
    [("viewBox", "0 0 24 24"), ("width", toString size), ("height", toString size), ("class", "mark"),
     ("aria-hidden", "true"), ("fill", "none"), ("stroke", "currentColor"), ("stroke-width", "1.5"),
     ("stroke-linecap", "round"), ("stroke-linejoin", "round")]

/-- Every shape, in the order of its constructors. -/
def Shape.all : List Shape :=
  [.box, .value, .series, .parallel, .block, .alternative, .loop, .region, .bracket, .openBracket,
   .rail, .arrow, .blockedArrow, .spider, .rest, .hollowBox, .filledBox, .hollowDot, .filledDot,
   .port, .probe, .call, .library, .cross, .hash, .reasons, .exitBar, .hole, .enter, .barLine,
   .fermata, .caesura, .panel, .cells, .slot, .tag, .atom]

-- `Shape.all` lists every shape once, in the order of its constructors
#guard Shape.all.map (·.ctorIdx) == List.range shapeNames.length

private def table' (heads : List String) (rows : List (List RawNode)) (label : String) : RawNode :=
  el "div" [el "table" [
      el "thead" [el "tr" (heads.map fun h => el "th" [.text h] [("scope", "col")])],
      el "tbody" (rows.map fun r => el "tr" (r.map fun c => el "td" [c]))]]
    [("class", "scroll"), ("role", "region"), ("tabindex", "0"), ("aria-label", label)]

private def code (s : String) : RawNode := el "code" [.text s]

/-- A constructor's name as the table writes it: its type and its own name. -/
def short (n : Lean.Name) : String :=
  match n.componentsRev with
  | c :: t :: _ => s!"{t}.{c}"
  | _ => n.toString

private def part (k title : String) (body : List RawNode) (level : String := "h2") : RawNode :=
  el "section" (el level [.text title, el "a" [.text k] [("class", "key"), ("href", "#" ++ k)]] :: body) [("id", k)]

/-- Every kind, in the order of its constructors. -/
def Kind.all : List Kind := [.body, .vessel, .container, .wire, .bond, .force, .cadence]

-- `Kind.all` lists every kind once, in the order of its constructors
#guard Kind.all.map (·.ctorIdx) == List.range (ctors_of% Kind).length

private def kindName (k : Kind) : String := (reprStr k).replace "Tools.View.Glyph.Kind." ""
private def primName (p : Primitive) : String := (reprStr p).replace "Tools.View.Glyph.Primitive." ""

/-- A kind's motion grammar, in words: enter, change, leave, each with its primitive. -/
def Grammar.words (g : Grammar) : String :=
  s!"enters: {g.enter.how} ({primName g.enter.primitive}); changes: {g.change.how} ({primName g.change.primitive}); leaves: {g.leave.how} ({primName g.leave.primitive})"

/-- The sheet's blocks: the verdict, the marks large, the marks with what they draw, then each
sort's constructors. -/
def sheetBlocks : List RawNode :=
  let total := (sorts.map (·.ctors.length)).foldl (· + ·) 0
  let verdict := if problems.isEmpty then
      "The check of semiotic clarity passes: every constructor has one mark, no two constructors of one sort are drawn alike, no word is drawn by two marks, and every mark draws something."
    else "The check of semiotic clarity refuses: " ++ "; ".intercalate problems ++ "."
  let uses (s : Shape) := (table.filter (·.shape == s)).length
  [el "p" [.text s!"One mark for each constructor of the sorts the pictures fold (decisions row 367, point 6): {total} constructors in {sorts.length} sorts, drawn by {Shape.all.length} marks. What is promised is hollow and what is kept is filled."],
   el "p" [.text verdict],
   part "kinds" "The marks, by kind" (el "p" [.text "Each mark has a physical kind, and its motion follows from the kind: how it enters, changes and leaves, each by one primitive that CSS states exactly (translate, scale, clip, opacity), within one beat."] ::
     Kind.all.map fun k =>
       part ("kind-" ++ kindName k) (kindName k) [el "p" [.text (k.means ++ ". " ++ k.grammar.words ++ ".")],
         el "ul" ((Shape.all.filter (·.kind == k)).map fun s =>
           el "li" [s.draw 72, code ((shapeNames.getD s.ctorIdx .anonymous).componentsRev.headD .anonymous).toString])
           [("class", "contact")]] "h3"),
   part "marks" "The marks" [table' ["Mark", "Text", "Name", "Kind", "Draws", "Rows"]
     (Shape.all.map fun s => [s.draw 36, code s.glyph, code ((shapeNames.getD s.ctorIdx .anonymous).componentsRev.headD .anonymous).toString, .text (kindName s.kind), .text s.means, .text (toString (uses s))])
     "Table: Mark, Text, Name, Kind, Draws, Rows"]] ++
  sorts.map fun srt =>
    let rows := srt.ctors.filterMap fun c => table.find? (·.ctor == c)
    part ("sort-" ++ srt.name.replace " " "-") srt.name [table' ["Mark", "Constructor", "Variant", "Word", "Draws"]
      (rows.map fun r => [r.shape.draw, code (short r.ctor), .text r.variant, .text r.word, .text r.means])
      s!"Table: the {srt.name}'s constructors"]

/-- The studio's rule for the large marks: a grid of six, each mark over its name. The site does
not use it. -/
def contactCss : String :=
  ".contact { display: grid; grid-template-columns: repeat(6, minmax(0, 1fr)); gap: 1.5rem 1rem; " ++
  "list-style: none; padding: 0; max-width: none; }\n" ++
  ".contact li { display: flex; flex-direction: column; align-items: center; gap: 0.5rem; }\n"

end Tools.View.Glyph
