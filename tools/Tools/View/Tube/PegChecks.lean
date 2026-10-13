import Tools.View.Tube.Glyphs

/-! # Finite controls for the authored peg vocabulary

These checks observe rounded cubic data at the twelve-pixel slot step.
They claim no exact real-curve theorem and no machine-state relation.
-/

namespace Tools.View.Tube.PegChecks
open Tools.View.Tube.Glyphs

-- Every authored body has tangents and closed outline and casing paths.
#guard shapes.all fun s => (pegFigure s).check

-- The finite rounding bounds cover every authored contour, including single-peg bodies.
#guard shapes.all fun s => (pegFigure s).bodies.all fun b =>
  match pegOutlines 12000 LINE b.skeleton.tour with
  | some (outer, inner) => smooth 3 outer && smooth 3 inner && insetBy LINE 2 outer inner
  | none => false

-- Every control point of each authored body remains inside the 96-pixel cell.
#guard shapes.all fun s => (pegFigure s).bodies.all fun b =>
  match pegOutlines 12000 LINE b.skeleton.tour with
  | some (outer, _) => outer.all fun c => [c.p0, c.p1, c.p2, c.p3].all fun p =>
      0 ≤ p.1 && p.1 ≤ 96000 && 0 ≤ p.2 && p.2 ≤ 96000
  | none => false

-- Different vocabulary shapes keep different peg data.
#guard shapes.all fun s => shapes.all fun t => s == t || pegFigure s != pegFigure t

-- The casing reuses the normals of the standalone belt calculation.
#guard [pipe, taper, bend, rings].all fun ps =>
  Belt.outlines LINE ps == do
    let outer ← belt ps
    let inner ← belt (ps.map (Peg.inset LINE))
    pure (outer, inner)

-- A contained peg has no tangent. A single cap still renders as a full circle.
#guard (pegOutlines 12000 LINE [⟨⟨0, 0⟩, 20⟩, ⟨⟨0, 0⟩, 5⟩]).isNone
#guard (pegOutlines 12000 LINE [⟨⟨4, 4⟩, 5⟩]).isSome

-- The fork revisits its outer bend. Adjacent normalization keeps both separate visits.
#guard ((PegGlyphs.tuningFork 7).tour.map (GridPeg.toPeg 12000)).eraseReps.length ==
  (PegGlyphs.tuningFork 7).tour.length
#guard match pegOutlines 12000 LINE (PegGlyphs.tuningFork 7).tour with
  | some (outer, _) => outer.length == 5 * (PegGlyphs.tuningFork 7).tour.length
  | none => false

end Tools.View.Tube.PegChecks
