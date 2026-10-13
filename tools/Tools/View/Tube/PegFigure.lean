import Tools.View.Tube.Skeleton

/-! # The peg picture as data

Bodies carry skeletons. Units carry the slot marking.
The grid action changes positions alone.
`PegRender` owns the SVG boundary.
-/

namespace Tools.View.Tube

/-- One skeleton's depth and whether the pen draws it in solid ink. -/
structure PegBody where
  skeleton : Skeleton
  level : Nat := 0
  solid : Bool := false
deriving Repr, DecidableEq, Inhabited

/-- A unit at a slot peg. A hollow unit shows an outstanding reply. -/
structure PegUnit where
  peg : GridPeg
  hollow : Bool := false
  level : Nat := 0
deriving Repr, DecidableEq, Inhabited

/-- A figure stores its still skeletons and its slot marking. -/
structure PegFigure where
  bodies : List PegBody := []
  units : List PegUnit := []
deriving Repr, DecidableEq, Inhabited

def PegBody.move (d : GridPoint) (b : PegBody) : PegBody :=
  { b with skeleton := b.skeleton.move d }

def PegUnit.move (d : GridPoint) (u : PegUnit) : PegUnit := { u with peg := u.peg.move d }

def PegFigure.move (d : GridPoint) (f : PegFigure) : PegFigure :=
  ⟨f.bodies.map (PegBody.move d), f.units.map (PegUnit.move d)⟩

end Tools.View.Tube
