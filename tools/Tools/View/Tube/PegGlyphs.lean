import Tools.View.Glyph
import Tools.View.Tube.PegFigure

/-! # The glyph vocabulary on the slot grid

Every shape has a peg figure. The static consumer uses this vocabulary directly.
The old tube figures remain the films' motion carrier.
The distinction is explicit: peg figures carry still skeletons and a marking.
-/

namespace Tools.View.Tube.PegGlyphs
open Tools.View.Glyph (Shape)

def peg (x y radius : Int) : GridPeg := ⟨⟨x, y⟩, radius⟩

def line (x y x' y' radius : Int) : Skeleton :=
  Skeleton.segment ⟨x, y⟩ ⟨x', y'⟩ radius

/-- An authored closed contour, represented by the run constructors of the same skeleton. -/
def chain (p : GridPeg) : List GridPeg → Skeleton
  | [] => .cap p
  | q :: qs => .run p (chain q qs)

def body (s : Skeleton) (solid : Bool := false) (level : Nat := 0) : PegBody := ⟨s, level, solid⟩
def unit (x y : Int) (hollow : Bool := false) (level : Nat := 0) : PegUnit :=
  ⟨peg x y 5, hollow, level⟩

def piece : Skeleton := line 2 4 6 4 10
def sealed : Skeleton := Skeleton.vessel ⟨3, 4⟩ 3

/-- A vessel follows its slots. Its inlet changes width through the peg radii. -/
def fed : Skeleton := .run (peg 1 4 10) (.run (peg 5 4 14) (.cap (peg 6 4 14)))

/-- A U-shaped contour has one convex turn and one concave turn. -/
def hook (x : Int) : Skeleton :=
  .run (peg x 2 7) (.bend (peg x 4 31) (peg x 4 (-17)) (.cap (peg x 6 7)))

def hookLeft (x : Int) : Skeleton :=
  .run (peg x 2 7) (.bend (peg x 4 (-17)) (peg x 4 31) (.cap (peg x 6 7)))

/-- The fork keeps two tines and one stem in one contour, without a blend. -/
def tuningFork (radius : Int) : Skeleton :=
  .run (peg 4 7 10)
    (.fork (peg 3 6 (-1)) [peg 4 3 (-17)] [peg 5 6 (-1)]
      (.run (peg 4 3 31) (.cap (peg 2 1 radius)))
      (.run (peg 6 1 radius) (.cap (peg 4 3 31))))

def enclosure : Skeleton :=
  chain (peg 2 2 7) [peg 6 2 7, peg 6 6 7, peg 2 6 7]

/-- All glyphs share one grid and one signed-peg renderer. -/
def draw : Shape → PegFigure
  | .box => ⟨[body piece], []⟩
  | .value => ⟨[body piece], [unit 5 4]⟩
  | .atom => ⟨[], [unit 4 4]⟩
  | .call => ⟨[body piece, body (line 2 3 2 5 5) true 1,
      body (line 6 3 6 5 5) true 1], []⟩
  | .tag => ⟨[body (line 3 4 5 4 10), body (line 3 3 3 5 5) true 1], []⟩
  | .probe => ⟨[body piece, body (line 4 1 4 2 5)], []⟩
  | .enter => ⟨[body enclosure], [unit 4 2]⟩
  | .cross => ⟨[body (line 2 2 6 6 7) false 1, body (line 2 6 3 5 7),
      body (line 5 3 6 2 7)], []⟩
  | .hash => ⟨[body (line 1 3 3 3 10), body (line 5 5 7 5 10)], []⟩
  | .reasons => ⟨[body (.cap (peg 1 4 7)), body (.cap (peg 4 4 7)),
      body (.cap (peg 7 4 7))], []⟩
  | .hollowDot => ⟨[body sealed], [unit 4 4 true]⟩
  | .filledDot => ⟨[body sealed], [unit 4 4]⟩
  | .hollowBox => ⟨[body fed], [unit 6 4 true]⟩
  | .filledBox => ⟨[body fed], [unit 6 4]⟩
  | .hole => ⟨[body fed], []⟩
  | .slot => ⟨[body (.run (peg 2 3 14) (.bend (peg 4 3 (-10)) (peg 4 3 38)
      (.cap (peg 6 3 14))))], [unit 4 5]⟩
  | .openBracket => ⟨[body (hookLeft 3)], []⟩
  | .bracket => ⟨[body (hookLeft 3), body (hook 5)], []⟩
  | .region => ⟨[body (line 1 2 3 2 7), body (line 1 2 1 4 7),
      body (line 5 6 7 6 7), body (line 7 4 7 6 7)], []⟩
  | .rail => ⟨[body (line 1 3 7 3 7), body (line 1 5 7 5 7)], []⟩
  | .block => ⟨[body (line 1 2 7 2 7), body (line 1 4 7 4 7),
      body (line 1 6 5 6 7)], []⟩
  | .library => ⟨[body (line 1 2 7 2 7), body (line 1 4 7 4 7),
      body (line 1 6 7 6 7), body (line 2 1 2 3 5) true 1,
      body (line 2 3 2 5 5) true 1], []⟩
  | .panel => ⟨[body (.cap (peg 1 2 5)), body (line 3 2 7 2 7),
      body (.cap (peg 1 4 5)), body (line 3 4 7 4 7),
      body (.cap (peg 1 6 5)), body (line 3 6 7 6 7)], []⟩
  | .cells => ⟨[body (Skeleton.vessel ⟨2, 4⟩ 5)], [unit 3 4, unit 5 4]⟩
  | .series => ⟨[body (line 1 4 7 4 10)], [unit 4 4]⟩
  | .parallel => ⟨[body (tuningFork 5)], []⟩
  | .alternative => ⟨[body (tuningFork 7)], []⟩
  | .loop => ⟨[body (line 1 2 7 2 10), body enclosure], []⟩
  | .rest => ⟨[body (line 1 4 3 4 10), body (line 5 4 7 4 10)], []⟩
  | .arrow => ⟨[body (line 1 2 7 2 10), body (line 2 4 7 6 10)], []⟩
  | .spider => ⟨[body (line 1 2 7 2 10), body (line 2 4 2 6 10),
      body (line 4 4 4 6 10), body (line 6 4 6 6 10)],
      [unit 3 2, unit 2 5, unit 4 5, unit 6 5]⟩
  | .port => ⟨[body (hookLeft 5)], [unit 5 2, unit 5 6 true]⟩
  | .blockedArrow => ⟨[body (line 1 4 4 4 10),
      body (line 3 4 4 4 14), body (line 6 2 6 6 5) true], []⟩
  | .barLine => ⟨[body (line 4 1 4 7 5) true, body (line 1 4 3 4 5),
      body (line 5 4 7 4 5)], []⟩
  | .exitBar => ⟨[body (line 1 4 3 4 5), body (line 4 1 4 7 5) true,
      body (line 6 1 6 7 10) true], []⟩
  | .fermata => ⟨[body (.run (peg 2 4 5) (.bend (peg 4 4 29) (peg 4 4 (-19))
      (.cap (peg 6 4 5)))) true,
      body (line 1 6 7 6 5), body (.cap (peg 4 4 5)) true], []⟩
  | .caesura => ⟨[body (line 2 6 4 2 5) true, body (line 4 6 6 2 5) true], []⟩

end Tools.View.Tube.PegGlyphs
