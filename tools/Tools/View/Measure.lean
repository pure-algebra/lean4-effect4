import Whatwg.Html.Print.Render

/-!
# Tools.View.Measure — what each figure costs, and the limits a documentation page holds

Slice M1 of the motion plan (`docs/research/2026-10-13-motion-everywhere/README.md`, §6 and §7).
A page's figures are read from the blocks it writes: each `figure` element is one row, with its
bytes as the printer writes them, its animation elements and the bytes of its path data (a path's
`d`, an animated `d`'s `values`, a motion's `path`). The bytes are the printer's own, so a figure's
row is the length of its text in the written page.

The limits are the plan's proposal (§6.3), as data: a still of 25 KB, a film of 250 KB, a page of
1 MB. A documentation page is refused at a figure over its limit, by the figure's name; a studio
page is measured and reported, never refused. The owner rules the numbers.
-/

namespace Tools.View.Measure
open Whatwg.Html

/-- **One figure's cost** on a page: its caption's first words, its bytes, its animation elements
and its path data's bytes. A figure with an animation is a film. -/
structure Row where
  page : String
  figure : String
  bytes : Nat
  animations : Nat
  pathBytes : Nat
deriving Repr, BEq, Inhabited

/-- A figure with any animation element is a film; any other is a still. -/
def Row.film (r : Row) : Bool := r.animations > 0

/-- The elements that animate. -/
def ANIMATIONS : List String := ["animate", "animateTransform", "animateMotion", "set"]

/-- The bytes of an element's own path data: a path's `d`, a motion's `path`, and the `values`
of an animation of `d`. -/
def pathOf (tag : String) (attrs : List (String × String)) : Nat :=
  let at_ (k : String) := ((attrs.lookup k).map String.utf8ByteSize).getD 0
  at_ "d" + at_ "path" + (if tag == "animate" && attrs.lookup "attributeName" == some "d" then at_ "values" else 0)

mutual
/-- The animation elements and the path bytes under a node. -/
def costOf : RawNode → Nat × Nat
  | .element tag attrs children =>
    let (a, p) := costsOf children
    (a + (if ANIMATIONS.contains tag then 1 else 0), p + pathOf tag attrs)
  | _ => (0, 0)
/-- The same, summed over a forest. -/
def costsOf : List RawNode → Nat × Nat
  | [] => (0, 0)
  | n :: ns => let (a, p) := costOf n; let (b, q) := costsOf ns; (a + b, p + q)
end

mutual
/-- The text under a node, its pieces in order. -/
def wordsOf : RawNode → List String
  | .element _ _ children => wordsOfList children
  | .text t => [t]
  | _ => []
/-- The same over a forest. -/
def wordsOfList : List RawNode → List String
  | [] => []
  | n :: ns => wordsOf n ++ wordsOfList ns
end

/-- A figure's name: the first six words of its caption, or its place on the page. -/
def nameOf (children : List RawNode) (index : Nat) : String :=
  let caption := children.filterMap fun
    | .element "figcaption" _ cs => some (" ".intercalate (wordsOfList cs))
    | _ => none
  match caption with
  | c :: _ => " ".intercalate (((c.splitOn " ").filter (· ≠ "")).take 6)
  | [] => s!"figure {index}"

mutual
/-- **The rows of a page's figures**, in the order they stand, numbered from `k`: each `figure`
element is one row and is not entered further. -/
def rowsOf (page : String) (k : Nat) : RawNode → List Row
  | n@(.element "figure" _ children) =>
    let (a, p) := costOf n
    [{ page, figure := nameOf children k, bytes := (Print.render n).utf8ByteSize, animations := a, pathBytes := p }]
  | .element _ _ children => rowsOfList page k children
  | _ => []
/-- The same over a forest, the numbering carried along. -/
def rowsOfList (page : String) (k : Nat) : List RawNode → List Row
  | [] => []
  | n :: ns => let here := rowsOf page k n; here ++ rowsOfList page (k + here.length) ns
end

/-- **The limits** of a documentation page, in bytes as the printer writes them (the plan's §6.3,
proposed). -/
structure Limits where
  still : Nat := 25000
  film : Nat := 250000
  page : Nat := 1000000
deriving Repr, Inhabited

/-- **A figure against its limit**: admitted, or refused by its page, its name, its size and the
limit it passes. -/
def Limits.check (l : Limits) (r : Row) : Except String Unit :=
  let (kind, lim) := if r.film then ("film", l.film) else ("still", l.still)
  if r.bytes ≤ lim then .ok ()
  else .error s!"{r.page}: \"{r.figure}\": a {kind} of {r.bytes} bytes, over its limit of {lim}"

/-- A row as a line of the report: page, figure, kind, bytes, animations, path bytes. -/
def Row.line (r : Row) : String :=
  "\t".intercalate [r.page, r.figure, if r.film then "film" else "still", toString r.bytes,
    toString r.animations, toString r.pathBytes]

/-- The report's head line. -/
def HEAD : String := "page\tfigure\tkind\tbytes\tanimations\tpath bytes"

-- a still and a film, named by their captions; the film's path data counts its animated `d`
#guard
  let still := RawNode.element "figure" [] [.element "svg" [] [.element "path" [("d", "M0,0h10")] []],
    .element "figcaption" [] [.text "A pipe with its units"]]
  let film := RawNode.element "figure" [] [.element "svg" [] [.element "path" [("d", "M0,0h10")]
      [.element "animate" [("attributeName", "d"), ("values", "M0,0h10;M0,0h20")] []]],
    .element "figcaption" [] [.text "A morph"]]
  let rs := rowsOfList "p" 0 [.element "section" [] [still, film]]
  rs.map (fun r => (r.figure, r.film, r.animations, r.pathBytes)) ==
    [("A pipe with its units", false, 0, 7), ("A morph", true, 1, 22)]
-- a figure's bytes are the printer's
#guard
  let n := RawNode.element "figure" [] [.element "figcaption" [] [.text "x"]]
  (rowsOf "p" 0 n).map (·.bytes) == [(Print.render n).utf8ByteSize]
-- the red control: a film over its limit is refused by its name; one within it is admitted
#guard match ({ film := 10 } : Limits).check { page := "q", figure := "A long run", bytes := 11, animations := 1, pathBytes := 0 } with
  | .error why => why == "q: \"A long run\": a film of 11 bytes, over its limit of 10"
  | .ok _ => false
#guard (({ film := 10 } : Limits).check { page := "q", figure := "A run", bytes := 10, animations := 1, pathBytes := 0 }).isOk

end Tools.View.Measure
