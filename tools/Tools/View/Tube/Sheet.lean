import Tools.View.Tube.Queue

/-!
# Tools.View.Tube.Sheet — the tube language, as the studio page `tubes.html`

Four parts: the one body and its laws, as plates; a queue's strategy as its plumbing; morphs, as
films, each between glyphs of the one body; and the Queue's runs, played and then command by
command. Every picture is drawn at one pixel to the pixel. A film's last picture stands for it
where the reader prefers reduced motion. Viewing ergonomics only: nothing reads the page.
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

/-- The widths of a pipe's and a vessel's contents on this page. -/
def PIPE : Nat := 12000
def VESSEL : Nat := 16000

/-- A figure with its caption. -/
def figure (pic : SvgNode) (caption : String) : RawNode :=
  el "figure" [pic.toRaw, el "figcaption" [.text caption]] [("class", "tube")]

/-- **A film's figure**: the film, and its last picture still for a reader who prefers reduced
motion. -/
def filmFigure (id : String) (W H : Nat) (pictures : List Picture) (caption : String)
    (beat : Nat := 1000) : RawNode :=
  let last := (pictures.getLast?).getD default
  el "figure"
    [el "div" [(film id W H pictures beat).toRaw] [("class", "tube-anim")],
     el "div" [(still W H last.marks).toRaw] [("class", "tube-end")],
     el "figcaption" [.text caption]] [("class", "tube tube-film")]

/-- `n` units packed against a tube's end, or against `from_`. -/
def packed (key : String) (t : Tube) (n : Nat) (from_ : Int := t.length) : List Mark :=
  (List.range n).map fun (k : Nat) => unitOf s!"{key}{k}" t (from_ - (k * unitLen t.bore : Nat))

/-- A picture of marks alone. -/
def pic (ms : List Mark) : Picture := { marks := ms }

/-! ## The one body -/

def plateRun : SvgNode :=
  let t := straight (pxi 24) (pxi 28) 0 PIPE (px 672)
  still 720 56 (bodyOf "t" t ++ packed "u" t 6)

def plateBends : SvgNode :=
  let t : Tube := ⟨pxi 24, pxi 30, 0, PIPE,
    [⟨px 200, 0⟩, ⟨arc 40 Q, Q⟩, ⟨px 30, 0⟩, ⟨arc 40 Q, -Q⟩, ⟨px 324, 0⟩]⟩
  still 720 170 (bodyOf "t" t ++ packed "u" t 8)

/-- A wye: a branch leaves the main at 45° and turns to run beside it. -/
def wye (y : Int) : Tube :=
  ⟨pxi 300, pxi y, -Q / 2, PIPE, [⟨px 40, 0⟩, ⟨arc 48 (Q / 2), Q / 2⟩, ⟨px 320, 0⟩]⟩

def plateJunction : SvgNode :=
  let main := straight (pxi 24) (pxi 112) 0 PIPE (px 672)
  let branch := wye 112
  still 720 140 (bodyOf "main" main ++ bodyOf "branch" branch ++ packed "a" main 4 ++ packed "b" branch 4)

def plateAmount : SvgNode :=
  let a := straight (pxi 24) (pxi 28) 0 PIPE (px 216)
  let v := straight (pxi 240) (pxi 28) 0 VESSEL (px 160)
  let b := straight (pxi 400) (pxi 28) 0 4000 (px 296)
  still 720 56 (bodyOf "a" a ++ bodyOf "v" v ++ bodyOf "b" b ++
    packed "ua" a 2 ++ packed "uv" v 2 (pxi 154) ++ packed "ub" b 2)

def plateValve : SvgNode :=
  let a := straight (pxi 24) (pxi 28) 0 PIPE (px 672)
  let b := straight (pxi 24) (pxi 80) 0 PIPE (px 672)
  still 720 108 (bodyOf "a" a ++ bodyOf "b" b ++
    [collarOf "ca" a (pxi 397) (px 14), collarOf "cb" b (pxi 397) (px 14), plugOf "p" b (pxi 400) (px 8)] ++
    packed "ua" a 3 ++ packed "ub" b 3 (pxi 400))

/-- A span of chord `c` pixels from `x`, under `n` units. -/
def span (x : Nat) (c : Nat) (n : Nat) : Tube :=
  let α := Queue.slope n
  ⟨pxi x, pxi 26, α, PIPE, [⟨((px c : Int) * ONE / sinc α).toNat, -2 * α⟩]⟩

def plateWeight : SvgNode :=
  let spans := [(24, 0), (258, 2), (492, 4)]
  still 720 80 (spans.flatMap fun (x, n) =>
    let t := span x 204 n
    bodyOf s!"s{x}" t ++
      [collarOf s!"a{x}" t 0 (px 8), collarOf s!"b{x}" t ((t.length : Int) - px 8) (px 8)] ++
      packed s!"u{x}" t n ((t.length : Int) - px 9))

/-! ## A queue's strategy is its plumbing -/

/-- A drain from a point on a tube: a branch that leaves at 45° below it, turns straight down,
and runs off the picture to the world. -/
def drain (t : Tube) (s : Nat) : Tube :=
  let (p, h) := t.at s
  ⟨p.1, p.2, h + Q / 2, PIPE, [⟨px 6, 0⟩, ⟨arc 30 (Q / 2), Q / 2⟩, ⟨px 90, 0⟩]⟩

/-- **The three strategies of a bounded queue**, each a full vessel of capacity three: a float
valve that holds offers back (backpressure); an overflow before the vessel, down which a new
offer runs away (dropping); a relief at the vessel's front, down which the oldest is pushed
(sliding). -/
def plateStrategy (kind : String) : SvgNode :=
  let l := Queue.Layout.of 3 2 1
  let m : Marking := ⟨3, [1, 2, 3], if kind == "bounded" then [(9, [4, 5])] else [], [], [], none⟩
  let ms := (Queue.picture l [1, 2, 3, 4, 5] [] none m).marks
  if kind == "bounded" then still l.W Queue.HEIGHT ms else
  let line := ms.filter fun mk => !(mk.key.startsWith "valve") && !(mk.key.startsWith "m4") &&
    !(mk.key.startsWith "m5")
  let inlet := l.inlet 0
  let d := if kind == "dropping" then drain inlet (inlet.length - px 60) else drain l.outlet (px 18)
  still l.W 100 (line ++ bodyOf "drain" d (round := false) ++ [unitOf "lost" d (pxi 60)])

/-! ## Morphs -/

/-- **Any route into any other**: one tube of three pieces, straight, an elbow, a U and an S. -/
def filmRoutes : RawNode :=
  let at_ (ps : List Piece) : Tube := ⟨pxi 40, pxi 40, 0, PIPE, ps⟩
  let shapes : List (List Piece) :=
    [[⟨px 200, 0⟩, ⟨px 200, 0⟩, ⟨px 200, 0⟩],
     [⟨px 200, 0⟩, ⟨arc 60 Q, Q⟩, ⟨px 140, 0⟩],
     [⟨px 200, 0⟩, ⟨arc 60 HALF, HALF⟩, ⟨px 140, 0⟩],
     [⟨px 120, 0⟩, ⟨arc 60 Q, Q⟩, ⟨arc 60 Q, -Q⟩]]
  filmFigure "f-routes" 720 200 (shapes.map fun ps => let t := at_ ps; pic (bodyOf "t" t ++ packed "u" t 3))
    "One tube of three pieces: straight, an elbow, a U, an S. Every moment keeps the bend law (click to play again)."

/-- **A queue closing into a circuit**: the outlet runs round and back into the inlet, so what
the vessel lets out comes back to it, and the count of the circuit holds (a semaphore's permits).
The inlet is given from the vessel and reversed, so both pipes stay on the vessel; the pipes pass
through a pose half curled on the way, so the picture stays in its room. -/
def filmCircuit : RawNode :=
  let vessel := straight (pxi 300) (pxi 40) 0 VESSEL (px 120)
  let r : Nat := 50
  let form (inPs outPs : List Piece) : List Mark :=
    let inlet : Tube := ⟨pxi 300, pxi 40, HALF, PIPE, inPs⟩
    let outlet : Tube := ⟨pxi 420, pxi 40, 0, PIPE, outPs⟩
    bodyOf "in" inlet (fromEnd := true) ++ bodyOf "out" outlet ++ packed "o" outlet 2 (pxi 120)
  let body := bodyOf "vessel" vessel ++ packed "v" vessel 3 (pxi 114)
  let open_ := form [⟨px 260, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩] [⟨px 260, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩]
  let half := form [⟨px 30, 0⟩, ⟨arc r Q, -Q⟩, ⟨px 90, 0⟩] [⟨px 30, 0⟩, ⟨arc r Q, Q⟩, ⟨px 90, 0⟩]
  let closed := form [⟨px 30, 0⟩, ⟨arc r HALF, -HALF⟩, ⟨px 90, 0⟩] [⟨px 30, 0⟩, ⟨arc r HALF, HALF⟩, ⟨px 90, 0⟩]
  filmFigure "f-circuit" 720 200 [pic (body ++ open_), { marks := body ++ closed, via := half }]
    "A queue closing into a circuit: what leaves the vessel comes back to it, so the count holds, as a semaphore's permits do."
    (beat := 1600)

/-- **A branch grows from nothing**: a tube of no length at its root, mixed into the branch. -/
def filmBranch : RawNode :=
  let main := straight (pxi 24) (pxi 112) 0 PIPE (px 672)
  let branch := wye 112
  let a := bodyOf "main" main ++ packed "a" main 4
  filmFigure "f-branch" 720 140
    [pic a, pic (a ++ bodyOf "branch" branch), pic (a ++ bodyOf "branch" branch ++ packed "b" branch 4)]
    "A branch grows from its root, then carries units."

/-! ## The Queue -/

/-- The Queue's run, played, and then each command still. -/
def queueBlocks (sc : CellSheet.Scene) (id : String) : List RawNode :=
  match Queue.run sc with
  | .error why => [el "p" [.text ("The scene stops: " ++ why)]]
  | .ok (l, fs) =>
    [filmFigure id l.W Queue.HEIGHT (fs.map (·.2))
       s!"Capacity {sc.capacity}: the whole run, one command a second (click to play it again)."] ++
    fs.map fun (words, p) => figure (still l.W Queue.HEIGHT p.marks) words

/-- **The page's blocks.** -/
def blocks : List RawNode :=
  [el "p" [.text "One body for every glyph: a tube, a centreline swept by one width, drawn with one pen. Its wall, its lumen and its contents are strokes of one path, every wall laid before every lumen, so where tubes meet the lumen is one. A unit of contents is one amount in every tube, a pill with a meniscus at each end. The pipework is the program's invariants, and the contents its state. Any glyph turns into any other by a morph of what each tube is, its lengths and its turns, and every moment of a morph keeps the bend law. A step is the kit's join of two pictures, each change on the kit's transition and its spring (docs/research/2026-10-13-tube-language/README.md)."],
   el "h2" [.text "The one body"],
   figure plateRun "A run and its units: each unit the same amount, a meniscus between, packed against the outlet end.",
   figure plateBends "Every bend at one radius, whatever the tube: the units follow the centreline round.",
   figure plateJunction "A junction is one lumen: every wall is laid first, then every lumen over them.",
   figure plateAmount "One amount everywhere: a unit is 32 px long in a pipe of 12, 24 in a vessel of 16, 96 in a pipe of 4.",
   figure plateValve "A valve is a plug in the lumen: open above, closed below with three units waiting behind it.",
   figure plateWeight "A span bends under what it holds: no unit, two, four; its ends turn in proportion to its load.",
   el "h2" [.text "A strategy is plumbing"],
   figure (plateStrategy "bounded") "Backpressure: a float valve closes when the vessel is full, and offers wait behind it, weighing on the inlet.",
   figure (plateStrategy "dropping") "Dropping: an overflow before the vessel; an offer that finds it full runs away down it.",
   figure (plateStrategy "sliding") "Sliding: a relief at the vessel's front; a new offer pushes the oldest out down it.",
   el "h2" [.text "Any glyph into any other"],
   filmRoutes, filmCircuit, filmBranch,
   el "h2" [.text "The Queue, capacity 2"]] ++
  queueBlocks CellSheet.scene "f-queue2" ++
  [el "h2" [.text "The Queue, capacity 13"]] ++
  queueBlocks CellSheet.large "f-queue13"

def css : String :=
  Tube.css ++ filmCss ++
  "figure.tube { margin: 0 0 1.5rem; max-width: none; }\n" ++
  "figure.tube figcaption { font-size: 0.8rem; opacity: 0.6; font-style: italic; }\n"

end Tools.View.Tube.Sheet
