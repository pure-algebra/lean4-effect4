import Tools.View.Tube.Glyphs
import Tools.View.Tube.Sheet
import Tools.View.GlyphSheet

/-!
# Tools.View.Tube.GlyphPage — the peg vocabulary, as the studio page `tube-glyphs.html`

The static cards use `Glyphs.pegStill`. The constructor table uses the same cached cards.
The motion studies retain the tube renderer until their changing structures have peg transitions.
Each film has a final still for readers who prefer reduced motion (`Sheet.filmFigure`).
The page is a view. Nothing reads its output.
-/

namespace Tools.View.Tube.GlyphPage
open Tools.View Tools.View.Tube Tools.View.Tube.Glyphs Whatwg.Html
open Tools.View.Glyph (Shape Kind sorts table shapeNames)

private def el (tag : String) (children : List RawNode) (attrs : List (String × String) := []) :
    RawNode :=
  .element tag attrs children

private def code (s : String) : RawNode := el "code" [.text s]

/-- A mark's name, as its constructor is written. -/
def name (s : Shape) : String :=
  ((shapeNames.getD s.ctorIdx .anonymous).componentsRev.headD .anonymous).toString

/-- A kind's name. -/
def kindName : Kind → String
  | .body => "body" | .vessel => "vessel" | .container => "container" | .wire => "wire"
  | .bond => "bond" | .force => "force" | .cadence => "cadence"

/-- **A kind's family, in one sentence**: the plumbing element it is and what its contents mean.
The builders' docstrings in `Tools.View.Tube.Glyphs` say it in full. -/
def Kind.rule : Kind → String
  | .body => "A body is a closed piece of line and its payload: a value carries a unit, a collar names it, a tap an air gap above it reads it, and a failure is a fitting that nothing flows through."
  | .vessel => "A vessel holds one unit, hollow while it is promised and filled once it is kept; a pipe that enters it brings what it waits on."
  | .container => "A container is a fine tube that encloses: hooks round a scope, corners round a region, rails along a span, the rows of a block, a library or a record, the lane of a list."
  | .wire => "A wire is a pipe that carries: it steps on, merges by a solid wye, divides into arms by one, returns to an earlier point by a solid join, or is parted by an air gap for a turn."
  | .bond => "A bond relates lanes: a fork starts a lane an air gap from its parent, a completion fills a header whose taps each hold their own copy across an air gap, and a port loops to the world."
  | .force => "A force is a surge along a pipe that a stop, set across its way an air gap short of it, holds."
  | .cadence => "A cadence is a thin strut across the staff, which stops an air gap short of it: it stands in time and carries nothing."

/-- A section with its heading and its key, as the vocabulary page has it. -/
private def titled (k title : String) (body : List RawNode) (level : String := "h2") : RawNode :=
  el "section" (el level [.text title, el "a" [.text k] [("class", "key"), ("href", "#" ++ k)]] :: body)
    [("id", k)]

/-- A mark's figure as the pen draws it: its marks, and its joins. -/
def drawn (s : Shape) : List Mark := (draw s).picture.marks
def joinsOf (s : Shape) : List Join := (draw s).picture.joins

/-- A mark's peg figure, or the body whose tangent is refused. -/
def still (s : Shape) : RawNode :=
  match Glyphs.pegStill s with
  | .ok svg => svg.toRaw
  | .error i => el "p" [.text s!"The peg figure {name s} has no tangent at body {i}."]

/-- **Every mark's still, drawn once.** A mark stands on many cards (its family's, and each
constructor's that it draws), and a card reads its still here, so the pen draws each figure once. -/
def stills : List (Shape × RawNode) := shapes.map fun s => (s, still s)

/-- A figure in a card, over its caption: the mark's still from `stills`. -/
private def card (s : Shape) (caption : List RawNode) : RawNode :=
  let picture := match stills.find? (·.1 == s) with
    | some (_, picture) => picture
    | none => still s
  el "figure" [picture, el "figcaption" caption]

/-! ## Films -/

/-- Every mark of a list moved by `(dx, dy)` thousandths of a pixel. A move keeps every piece, so
it keeps the bend law. -/
def shift (dx dy : Int) (ms : List Mark) : List Mark :=
  ms.map fun m => { m with tube := { m.tube with x := m.tube.x + dx, y := m.tube.y + dy } }

/-- **A unit along a line of tubes**, its slot's front at the volume `v` from the line's start:
one mark for each tube, where the front stands in that tube, `(v − the volume before it) / its
contents width`, by `Queue.fronts`. A unit off a tube's length draws nothing there, so the unit
flows from one tube into the next, shortening where the next is wider, as water does. -/
def flow (key : String) (line : List (String × Tube)) (v : Int) : List Mark :=
  (line.zip (Queue.fronts (line.map (·.2)) v)).map fun ((k, t), front) => unitOf (key ++ "@" ++ k) t front

/-- The vessel of a figure a cell to the right, in a picture two cells wide. -/
def vesselX : Int := vesselFigure.fed.x + px 96

/-- The pipe that leads to it from the picture's left, long enough for a unit to travel. -/
def longInlet : Tube := tube (px 12) (px 48) E PIPE [⟨(vesselX - px 12).toNat, 0⟩]

/-- A vessel's figure a cell to the right, its pipe drawn from the picture's left. -/
def fedFigure (s : Shape) : List Mark :=
  (shift (px 96) 0 (drawn s)).map fun m => if part m.key == "b" then { m with tube := into longInlet true } else m

/-- **A value arrives at a vessel by its pipe**: the unit's marks near the start of the long pipe,
then seated in the vessel's slot. -/
def arrival : List Mark × List Mark :=
  let vessel := { vesselFigure.fed with x := vesselX }
  let line := [("b", longInlet), ("main", vessel)]
  let start : Int := 40000 * (PIPE : Int) / 1000
  let seated : Int := Queue.volume longInlet + ((vesselFigure.L - HEADROOM) * contents VESSEL / 1000 : Nat)
  (flow "a" line start, flow "a" line seated)

/-- The inside of a promised unit leaves as the value arrives: late in the beat. -/
def late (ms : List Mark) : List Mark :=
  ms.map fun m =>
    if m.key == "h" then { m with move := { delay := 450, duration := 450, ease := settle } } else m

/-- **A promise kept**: a parked fiber's vessel, its unit hollow; the answer comes down the pipe
and the hollow fills. -/
def keptFrames : List Picture :=
  complete [late (fedFigure .hollowBox) ++ arrival.1,
            (fedFigure .hollowBox).filter (·.key != "h") ++ arrival.2]

/-- **A hole filled by a value**: a frame's empty vessel, and a value that flows into it. -/
def filledFrames : List Picture :=
  complete [fedFigure .hole ++ arrival.1, fedFigure .hole ++ arrival.2]

/-- **A scope opened and closed**: its first hook grows, then its second. -/
def closedFrames : List Picture := complete [[], drawn .openBracket, drawn .bracket]

/-- **A fork joined**: the parent's lane; the child's lane starts beside it, an air gap away; the
lanes fold into a completion whose header carries the exit and whose taps each hold a copy. -/
def joinedFrames : List Picture :=
  complete [(drawn .arrow).filter (part ·.key == "main"), drawn .arrow, drawn .spider]

/-- **An interrupt held by a rail, landing at its end**, in a picture three cells wide, five
pictures: the interrupt's surge comes along the lane while the fiber's work runs under the rail;
the surge is held at the rail's start while the work runs on to the rail's end, in one motion over
two beats; the surge is let go and runs past the rail's end; it lands and is spent there, then the
lane draws back, and then a stop is set across the lane, an air gap past the lane's end: one
thing after another within the beat. -/
def heldFrames : List Picture :=
  let lane (to_ : Int) := tube (px 12) (px 48) E PIPE [⟨(to_ - px 12).toNat, 0⟩]
  let stopX := px 222
  let ended := stopX - (apart PIPE THIN : Nat)
  let rails := bodyOf "r1" (tube (px 96) (px 24) E FINE [run 96]) ++
    bodyOf "r2" (tube (px 96) (px 72) E FINE [run 96])
  let frame (to_ unit : Int) (moveUnit : Timing) (surge : Int × Nat) (moveSurge : Timing)
      (stop : List Mark) (moveLane : Timing) :=
    let t := lane to_
    (bodyOf "main" t).map (fun m => { m with move := moveLane }) ++ rails ++
      [{ unitAt "u" t unit with move := moveUnit }] ++
      (surgeOf "s" t surge.1 surge.2).map (fun m => { m with move := moveSurge }) ++ stop
  let now : Timing := { ease := settle }
  -- the work's run under the rail, one motion over two beats: the two halves of a smoothstep
  let gather : Timing := { ease := .cubic 0 500 }
  let finish : Timing := { ease := .cubic 500 1000 }
  let go : Timing := { ease := .cubic 0 1000 }
  -- the last beat in turn: the surge spent at the lane's end, the lane drawn back, the stop set
  let spend : Timing := { duration := 400, ease := settle }
  let draw : Timing := { delay := 300, duration := 400, ease := settle }
  let set : Timing := { delay := 650, duration := 350, ease := settle }
  let stop := (bodyOf "stop" (tube stopX (px 24) S THIN [run 48])).map fun m => { m with move := set }
  complete [frame (px 276) (px 96) now (px 6, 18000) now [] now,
    frame (px 276) (px 126) gather (px 48, 18000) now [] now,
    frame (px 276) (px 156) finish (px 48, 18000) now [] now,
    frame (px 276) (px 156) now (px 180, 18000) go [] now,
    frame ended (px 156) now (ended - px 1, 0) spend stop draw]

/-- **Any mark into any other**: six marks of five kinds, each morphing into the next. -/
def anyShapes : List Shape := [.box, .loop, .spider, .fermata, .hollowDot, .region]
def anyFrames : List Picture :=
  (complete (anyShapes.map drawn)).zip anyShapes |>.map fun (p, s) => { p with joins := joinsOf s }

/-- Every picture of every film on the page. -/
def filmPictures : List Picture :=
  keptFrames ++ filledFrames ++ closedFrames ++ joinedFrames ++ heldFrames ++ anyFrames

-- every tube of every picture of every film keeps the bend law, so every moment of every film
-- keeps it (`step_ok`); a finite check of the page's own pictures, which no theorem covers
#guard filmPictures.all fun p => p.marks.all fun m => decide m.tube.ok

def filmKept : RawNode :=
  Sheet.filmFigure "f-kept" (2 * SIDE) SIDE keptFrames
    "A promise kept: the answer comes down the pipe of the hollow box, and its unit, hollow, fills (hollowBox into filledBox; click a film to play it again)."

def filmFilled : RawNode :=
  Sheet.filmFigure "f-filled" (2 * SIDE) SIDE filledFrames
    "A hole filled by a value: the value flows down the pipe into the empty vessel (hole into filledBox)."

def filmClosed : RawNode :=
  Sheet.filmFigure "f-closed" SIDE SIDE closedFrames
    "A scope opened, its close owed, then closed: the first hook grows, then the second (openBracket into bracket)."

def filmJoined : RawNode :=
  Sheet.filmFigure "f-joined" SIDE SIDE joinedFrames
    "A fork joined: the child's lane starts an air gap from the parent's; then the lanes fold into a completion whose taps each hold a copy (arrow into spider)."

def filmHeld : RawNode :=
  Sheet.filmFigure "f-held" (3 * SIDE) SIDE heldFrames
    "An interrupt held by a rail: its surge comes along the lane and is held at the rail's start while the work runs under the rail; when the work reaches the rail's end, the surge runs past it and is spent there, a stop across the lane, and the lane ends (blockedArrow and rail)."

def filmAny : RawNode :=
  Sheet.filmFigure "f-any" SIDE SIDE anyFrames
    "Any mark into any other: box, loop, spider, fermata, hollowDot, region; every moment keeps the bend law (morph_ok)." (beat := 1200)

/-! ## The page -/

/-- **The page's blocks.** -/
def blocks : List RawNode :=
  let total := (sorts.map (·.ctors.length)).foldl (· + ·) 0
  [el "p" [.text s!"The vocabulary on the peg grid: {shapes.length} marks of seven kinds. Each static card uses signed pegs and their string outline. The motion studies below still use tube transitions. Their bend law is morph_ok in tools/Tools/View/Tube/Glyphs.lean."],
   titled "families" "The families"
     (Glyph.Kind.all.map fun k =>
       titled ("family-" ++ kindName k) (kindName k)
         [el "p" [.text (Kind.rule k ++ " " ++ k.means.capitalize ++ ".")],
          el "div" ((shapes.filter (·.kind == k)).map fun s =>
            card s [code (name s), .text (" " ++ s.glyph)]) [("class", "glyph-grid")]] "h3"),
   titled "morphs" "The morphs a run makes"
     [el "p" [.text "Each film is the kit's join of one picture and the next, a beat each: what two figures share morphs, the rest grows from its root or shrinks to it. Click a film to play it again."],
      el "div" [filmKept, filmFilled, filmClosed, filmJoined, filmAny] [("class", "film-grid")],
      filmHeld],
   titled "sorts" "Every sort"
     (el "p" [.text s!"Each constructor of the {sorts.length} sorts the pictures fold, {total} in all, with its mark's figure."] ::
      sorts.map fun srt =>
        let rows := srt.ctors.filterMap fun c => table.find? (·.ctor == c)
        titled ("sort-" ++ srt.name.replace " " "-") srt.name
          [el "div" (rows.map fun r =>
            card r.shape ([code (Glyph.short r.ctor), .text (" " ++ r.word)] ++
              (if r.variant.isEmpty then [] else [.text (" (" ++ r.variant ++ ")")])))
            [("class", "glyph-grid")]] "h3")]

/-- The page's rules: the tube pen's, the films', and the grids of figures. -/
def css : String :=
  Sheet.css ++
  ".glyph-grid { display: grid; grid-template-columns: repeat(auto-fill, minmax(112px, 1fr)); " ++
  "gap: 1rem 0.75rem; max-width: none; }\n" ++
  ".glyph-grid figure { margin: 0; display: flex; flex-direction: column; align-items: center; gap: 0.35rem; }\n" ++
  ".glyph-grid figcaption { font-size: 0.75rem; text-align: center; line-height: 1.3; }\n" ++
  ".film-grid { display: grid; grid-template-columns: repeat(auto-fill, minmax(220px, 1fr)); gap: 1.5rem; " ++
  "max-width: none; }\n"

end Tools.View.Tube.GlyphPage
