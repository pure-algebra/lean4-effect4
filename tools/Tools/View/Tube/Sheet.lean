import Tools.View.Tube.Queue

/-!
# Tools.View.Tube.Sheet — the tube language, as the studio page `tubes.html`

Three parts: the one body and its laws, as plates; morphs, as films, each between glyphs of the
one body; and the Queue's run, played and then command by command. Viewing ergonomics only:
nothing reads the page.
-/

namespace Tools.View.Tube.Sheet
open Tools.View Tools.View.Tube Whatwg.Html

private def el (tag : String) (children : List RawNode) (attrs : List (String × String) := []) : RawNode :=
  .element tag attrs children

/-- Whole pixels, in thousandths. -/
def px (n : Nat) : Nat := n * 1000
def pxi (n : Int) : Int := n * 1000

/-- A quarter turn and a half turn, in millionths of a radian. -/
def Q : Int := 1570796
def HALF : Int := 3141593

/-- An arc's length for a radius in pixels and a turn: `r · |θ|`, in thousandths. -/
def arc (r : Nat) (θ : Int) : Nat := r * θ.natAbs / 1000

/-- A figure with its caption. -/
def figure (pic : SvgNode) (caption : String) : RawNode :=
  el "figure" [pic.toRaw, el "figcaption" [.text caption]] [("class", "tube")]

/-- `n` units packed against a tube's end. -/
def packed (key : String) (t : Tube) (n : Nat) (from_ : Int := t.length) : List Mark :=
  (List.range n).map fun (k : Nat) => unitOf s!"{key}{k}" t (from_ - (k * unitLen t.bore : Nat))

/-! ## The one body -/

def plateRun : SvgNode :=
  let t := straight (pxi 20) (pxi 26) 0 8000 (px 340)
  still 380 52 (bodyOf "t" t ++ packed "u" t 5)

def plateBends : SvgNode :=
  let t : Tube := ⟨pxi 20, pxi 24, 0, 8000,
    [⟨px 110, 0⟩, ⟨arc 24 Q, Q⟩, ⟨px 22, 0⟩, ⟨arc 24 Q, -Q⟩, ⟨px 150, 0⟩]⟩
  still 380 120 (bodyOf "t" t ++ packed "u" t 7)

def plateJunction : SvgNode :=
  let main := straight (pxi 20) (pxi 86) 0 8000 (px 340)
  let branch : Tube := ⟨pxi 150, pxi 86, -Q / 2, 8000, [⟨px 34, 0⟩, ⟨arc 30 (Q / 2), Q / 2⟩, ⟨px 160, 0⟩]⟩
  still 380 110 (bodyOf "main" main ++ bodyOf "branch" branch ++ packed "a" main 3 ++
    packed "b" branch 3)

def plateAmount : SvgNode :=
  let a := straight (pxi 20) (pxi 30) 0 8000 (px 120)
  let v := straight (pxi 140) (pxi 30) 0 16000 (px 80)
  let b := straight (pxi 220) (pxi 30) 0 4000 (px 140)
  still 380 60 (bodyOf "a" a ++ bodyOf "v" v ++ bodyOf "b" b ++
    packed "ua" a 2 ++ packed "uv" v 2 (pxi 74) ++ packed "ub" b 2)

def plateValve : SvgNode :=
  let a := straight (pxi 20) (pxi 24) 0 8000 (px 340)
  let b := straight (pxi 20) (pxi 66) 0 8000 (px 340)
  still 380 90 (bodyOf "a" a ++ bodyOf "b" b ++
    [collarOf "ca" a (pxi 200) (px 8), collarOf "cb" b (pxi 200) (px 8), plugOf "p" b (pxi 201) (px 6)] ++
    packed "ua" a 3 ++ packed "ub" b 3 (pxi 201))

/-- A span of chord `c` pixels from `x`, under `n` units. -/
def span (x : Nat) (c : Nat) (n : Nat) : Tube :=
  let α := min Queue.SAG_MAX (Queue.SAG0 + Queue.SAG_PER * n)
  ⟨pxi x, pxi 22, α, 8000, [⟨((px c : Int) * ONE / sinc α).toNat, -2 * α⟩]⟩

def plateWeight : SvgNode :=
  let spans := [(14, 0), (138, 2), (262, 4)]
  still 380 70 (spans.flatMap fun (x, n) =>
    let t := span x 104 n
    bodyOf s!"s{x}" t ++ [collarOf s!"a{x}" t 0 (px 5), collarOf s!"b{x}" t ((t.length : Int) - px 5) (px 5)] ++
      packed s!"u{x}" t n ((t.length : Int) - px 5))

/-! ## A queue's strategy is its plumbing -/

/-- A drain from a point on a tube: a branch that leaves at 45° below it and turns straight down,
open at its end. -/
def drain (t : Tube) (s : Nat) : Tube :=
  let (p, h) := t.at s
  ⟨p.1, p.2, h + Q / 2, 8000, [⟨px 8, 0⟩, ⟨arc 24 (Q / 2), Q / 2⟩, ⟨px 22, 0⟩]⟩

/-- **The three strategies of a bounded queue**, each a full vessel of capacity three: a float
valve that holds offers back (backpressure); an overflow before the vessel, down which a new
offer runs away (dropping); a relief at the vessel's front, down which the oldest is pushed
(sliding). -/
def plateStrategy (kind : String) : SvgNode :=
  let l := Queue.Layout.of 3 2 1
  let m : Living.Organism.Marking := ⟨3, [1, 2, 3], if kind == "bounded" then [(9, [4, 5])] else [], [], [], none⟩
  let ms := Queue.picture l [1, 2, 3, 4, 5] [] [] m
  if kind == "bounded" then still l.W 60 ms else
  let line := (ms.filter fun mk => !(mk.key.startsWith "valve") && !(mk.key.startsWith "m4") && !(mk.key.startsWith "m5"))
  let inlet := l.inlet 0
  let d := if kind == "dropping" then drain inlet (inlet.length - px 40) else drain (l.outlet) (px 14)
  still l.W 92 (line ++ bodyOf "drain" d ++ [unitOf "lost" d (d.length - px 4 : Nat)])

/-! ## Morphs -/

/-- **Any route into any other**: one tube of three pieces, straight, an elbow, a U and an S. -/
def filmRoutes : SvgNode :=
  let at_ (ps : List Piece) : Tube := ⟨pxi 24, pxi 34, 0, 8000, ps⟩
  let shapes : List (List Piece) :=
    [[⟨px 100, 0⟩, ⟨px 100, 0⟩, ⟨px 100, 0⟩],
     [⟨px 100, 0⟩, ⟨arc 40 Q, Q⟩, ⟨px 60, 0⟩],
     [⟨px 100, 0⟩, ⟨arc 40 HALF, HALF⟩, ⟨px 60, 0⟩],
     [⟨px 60, 0⟩, ⟨arc 40 Q, Q⟩, ⟨arc 40 Q, -Q⟩]]
  film "f-routes" 380 140 (shapes.map fun ps => let t := at_ ps; bodyOf "t" t ++ packed "u" t 3)

/-- **A queue closing into a circuit**: the outlet runs round and back into the inlet, so what
the vessel lets out comes back to it, and the count of the circuit holds (a semaphore's permits).
The inlet is given from the vessel and reversed, so both pipes stay on the vessel. -/
def filmCircuit : SvgNode :=
  let vessel := straight (pxi 150) (pxi 34) 0 16000 (px 80)
  let r : Nat := 34
  let open_ : List Mark :=
    let inlet : Tube := ⟨pxi 150, pxi 34, HALF, 8000, [⟨px 130, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩]⟩
    let outlet : Tube := ⟨pxi 230, pxi 34, 0, 8000, [⟨px 130, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩]⟩
    bodyOf "in" inlet (fromEnd := true) ++ bodyOf "out" outlet ++ packed "o" outlet 2
  let closed : List Mark :=
    let inlet : Tube := ⟨pxi 150, pxi 34, HALF, 8000, [⟨px 20, 0⟩, ⟨arc r HALF, -HALF⟩, ⟨px 60, 0⟩]⟩
    let outlet : Tube := ⟨pxi 230, pxi 34, 0, 8000, [⟨px 20, 0⟩, ⟨arc r HALF, HALF⟩, ⟨px 60, 0⟩]⟩
    bodyOf "in" inlet (fromEnd := true) ++ bodyOf "out" outlet ++ packed "o" outlet 2
  let body := bodyOf "vessel" vessel ++ packed "v" vessel 3 (pxi 75)
  film "f-circuit" 380 180 [body ++ open_, body ++ closed] (beat := 1400)

/-- **A branch grows from nothing**: a tube of no length at its root, mixed into the branch. -/
def filmBranch : SvgNode :=
  let main := straight (pxi 20) (pxi 86) 0 8000 (px 340)
  let branch : Tube := ⟨pxi 150, pxi 86, -Q / 2, 8000, [⟨px 34, 0⟩, ⟨arc 30 (Q / 2), Q / 2⟩, ⟨px 160, 0⟩]⟩
  let a := bodyOf "main" main ++ packed "a" main 3
  film "f-branch" 380 110 [a, a ++ bodyOf "branch" branch, a ++ bodyOf "branch" branch ++ packed "b" branch 3]

/-! ## The Queue -/

/-- The Queue's run, played, and then each command still. -/
def queueBlocks (sc : CellSheet.Scene) (id : String) : List RawNode :=
  match Queue.run sc with
  | .error why => [el "p" [.text ("The scene stops: " ++ why)]]
  | .ok (l, fs) =>
    [figure (film id l.W l.H (fs.map (·.2)) (beat := 1000))
       s!"Capacity {sc.capacity}: the whole run, one command a second (click to play it again)."] ++
    fs.map fun (words, ms) => figure (still l.W l.H ms) words

/-- **The page's blocks.** -/
def blocks : List RawNode :=
  [el "p" [.text "One body for every glyph: a tube, a centreline swept by one width, drawn with one pen. Its wall, its lumen and its contents are three strokes of one path, every wall laid before every lumen, so where tubes meet the lumen is one. A unit of contents is one amount in every tube; the pipework is the program's invariants, and the contents its state. Any glyph turns into any other by a morph of what each tube is, its lengths and its turns, and every moment of a morph keeps the bend law (docs/research/2026-10-13-tube-language/README.md)."],
   el "h2" [.text "The one body"],
   figure plateRun "A run and its units: each unit the same amount, a meniscus between, packed against the outlet end.",
   figure plateBends "Every bend at one radius, whatever the tube: the units follow the centreline round.",
   figure plateJunction "A junction is one lumen: every wall is laid first, then every lumen over them.",
   figure plateAmount "One amount everywhere: a unit is 24 px long in a pipe of 8, 12 in a vessel of 16, 48 in a pipe of 4.",
   figure plateValve "A valve is a plug in the lumen: open above, closed below with three units waiting behind it.",
   figure plateWeight "A span bends under what it holds: no unit, two, four; its ends turn in proportion to its load.",
   el "h2" [.text "A strategy is plumbing"],
   figure (plateStrategy "bounded") "Backpressure: a float valve closes when the vessel is full, and offers wait behind it, weighing on the inlet.",
   figure (plateStrategy "dropping") "Dropping: an overflow before the vessel; an offer that finds it full runs away down it.",
   figure (plateStrategy "sliding") "Sliding: a relief at the vessel's front; a new offer pushes the oldest out down it.",
   el "h2" [.text "Any glyph into any other"],
   figure filmRoutes "One tube of three pieces: straight, an elbow, a U, an S. Every moment keeps the bend law (click to play again).",
   figure filmCircuit "A queue closing into a circuit: what leaves the vessel comes back to it, so the count holds, as a semaphore's permits do.",
   figure filmBranch "A branch grows from its root, then carries units.",
   el "h2" [.text "The Queue, capacity 2"]] ++
  queueBlocks CellSheet.scene "f-queue2" ++
  [el "h2" [.text "The Queue, capacity 13"]] ++
  queueBlocks CellSheet.large "f-queue13"

def css : String :=
  Tube.css ++
  "figure.tube { margin: 0 0 1.5rem; max-width: none; }\n" ++
  "figure.tube figcaption { font-size: 0.8rem; opacity: 0.6; font-style: italic; }\n"

end Tools.View.Tube.Sheet
