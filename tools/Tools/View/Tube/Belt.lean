import Tools.View.SceneBridge
import Whatwg.Svg.Scene.Belt
import Tools.View.Tube.Trig

/-! # The pen's tuple interface to kit peg geometry

The kit owns pegs, the integer belt, and its laws.
This module keeps the tuple vectors and cubic results used by the pen.
The connector changes records alone. Rounded checks remain finite probes.
The placement note is `docs/research/2026-10-13-peg-adapter-plan.md`.
-/

namespace Tools.View.Tube

abbrev Peg := Whatwg.Svg.Scene.Peg

namespace Belt

def isqrt := Whatwg.Svg.Scene.Belt.isqrt

def dot (u v : Int × Int) : Int :=
  Whatwg.Svg.Scene.Belt.dot (SceneBridge.vec u) (SceneBridge.vec v)

def cross (u v : Int × Int) : Int :=
  Whatwg.Svg.Scene.Belt.cross (SceneBridge.vec u) (SceneBridge.vec v)

def unit (v : Int × Int) : Int × Int :=
  SceneBridge.point (Whatwg.Svg.Scene.Belt.unit (SceneBridge.vec v))

def normal (p q : Peg) : Option (Int × Int) :=
  (Whatwg.Svg.Scene.Belt.normal p q).map SceneBridge.point

def half (σ : Int) (u v : Int × Int) : Int × Int :=
  SceneBridge.point (Whatwg.Svg.Scene.Belt.half σ (SceneBridge.vec u) (SceneBridge.vec v))

def line (a b : Int × Int) : Cubic :=
  SceneBridge.fromCubic (Whatwg.Svg.Scene.Belt.line (SceneBridge.vec a) (SceneBridge.vec b))

end Belt
open Belt

def Peg.at (p : Peg) (u : Int × Int) : Int × Int :=
  SceneBridge.point (Whatwg.Svg.Scene.Peg.at p (SceneBridge.vec u))

def Peg.piece (p : Peg) (h : Int) (a b : Int × Int) : Cubic :=
  SceneBridge.fromCubic (Whatwg.Svg.Scene.Peg.piece p h (SceneBridge.vec a) (SceneBridge.vec b))

def Peg.arc (p : Peg) (u v : Int × Int) : List Cubic :=
  (Whatwg.Svg.Scene.Peg.arc p (SceneBridge.vec u) (SceneBridge.vec v)).map SceneBridge.fromCubic

def Belt.normals (ps : List Peg) : Option (List (Int × Int)) :=
  (Whatwg.Svg.Scene.Belt.normals ps).map (List.map SceneBridge.point)

def Belt.withNormals (ps : List Peg) (ns : List (Int × Int)) : List Cubic :=
  (Whatwg.Svg.Scene.Belt.withNormals ps (ns.map SceneBridge.vec)).map
    SceneBridge.fromCubic

def belt (ps : List Peg) : Option (List Cubic) :=
  (Whatwg.Svg.Scene.belt ps).map (List.map SceneBridge.fromCubic)

abbrev Peg.inset (w : Int) (p : Peg) : Peg := Whatwg.Svg.Scene.Peg.inset w p
def Peg.move (d : Int × Int) (p : Peg) : Peg := Whatwg.Svg.Scene.Peg.move (SceneBridge.vec d) p

def Belt.outlines (w : Int) (ps : List Peg) : Option (List Cubic × List Cubic) :=
  (Whatwg.Svg.Scene.Belt.outlines w ps).map SceneBridge.paths

/-- Transport the kit's exact inset law across the tuple connector. -/
theorem normal_inset (w : Int) (p q : Peg) : normal (p.inset w) (q.inset w) = normal p q := by
  exact congrArg (Option.map SceneBridge.point) (Whatwg.Svg.Scene.normal_inset w p q)

/-- Transport the kit's exact translation law across the tuple connector. -/
theorem normal_move (d : Int × Int) (p q : Peg) : normal (p.move d) (q.move d) = normal p q := by
  exact congrArg (Option.map SceneBridge.point)
    (Whatwg.Svg.Scene.normal_move (SceneBridge.vec d) p q)

def chained (cs : List Cubic) : Bool :=
  Whatwg.Svg.Scene.chained (cs.map SceneBridge.cubic)

def Cubic.still (c : Cubic) : Bool := Whatwg.Svg.Scene.ICubic.still (SceneBridge.cubic c)

def handles (a b : Cubic) : (Int × Int) × (Int × Int) :=
  let h := Whatwg.Svg.Scene.handles (SceneBridge.cubic a) (SceneBridge.cubic b)
  (SceneBridge.point h.1, SceneBridge.point h.2)

def smooth (tol : Int) (cs : List Cubic) : Bool :=
  Whatwg.Svg.Scene.smooth tol (cs.map SceneBridge.cubic)

def insetBy (w tol : Int) (outline casing : List Cubic) : Bool :=
  Whatwg.Svg.Scene.insetBy w tol (outline.map SceneBridge.cubic) (casing.map SceneBridge.cubic)
/-! ## Guards: a pipe, a taper, a bend, a belt round rings -/

/-- A pipe: two pegs of one size, a body of ten pixels' half width. -/
def pipe : List Peg := [⟨⟨24000, 24000⟩, 10000⟩, ⟨⟨144000, 24000⟩, 10000⟩]

/-- A taper: two pegs of two sizes. -/
def taper : List Peg := [⟨⟨24000, 24000⟩, 14000⟩, ⟨⟨144000, 24000⟩, 7000⟩]

/-- A bend of a quarter turn about `(60000, 48000)`, radius 24 px, half width 7: the outer wall
round a convex peg, the inner round a concave one. -/
def bend : List Peg :=
  [⟨⟨18000, 24000⟩, 7000⟩, ⟨⟨60000, 48000⟩, 31000⟩, ⟨⟨84000, 96000⟩, 7000⟩,
   ⟨⟨60000, 48000⟩, -17000⟩]

/-- Four rings and a string round them, as in the reference. -/
def rings : List Peg :=
  [⟨⟨36000, 36000⟩, 15000⟩, ⟨⟨120000, 36000⟩, 15000⟩, ⟨⟨120000, 96000⟩, 11000⟩,
   ⟨⟨36000, 96000⟩, 15000⟩]

#guard [pipe, taper, bend, rings].all fun ps =>
  match belt ps, belt (ps.map (Peg.inset 2000)) with
  | some o, some c => o.length == 5 * ps.length && chained o && chained c &&
      smooth 3 o && smooth 3 c && insetBy 2000 2 o c
  | _, _ => false

-- A belt of moved pegs is the belt moved.
#guard [pipe, taper, bend, rings].all fun ps =>
  belt (ps.map (Peg.move (12000, -24000))) == (belt ps).map (List.map (Cubic.move 12000 (-24000)))

-- Pegs one inside the other share no tangent: no belt. Pegs placed to touch, rounded a thousandth
-- of a pixel into each other, touch.
#guard belt [⟨⟨0, 0⟩, 20000⟩, ⟨⟨5000, 0⟩, 5000⟩] == none
#guard (normal ⟨⟨0, 0⟩, 19000⟩ ⟨⟨18248, 14000⟩, -4000⟩).isSome

end Tools.View.Tube
