import Tools.View.Tube.PegFigure
import Tools.View.Tube.Draw

/-! # Static peg figures

The renderer computes a body's tour once, then shares its tangent normals with its casing.
The output is SVG. The data carries no rendering function.
Rounded tangent checks are finite probes, rather than real-curve theorems.
-/

namespace Tools.View.Tube
open Tools.View Whatwg.Html

/-- A single peg has two semicircles. A tour shares its casing's normals. -/
def pegOutlines (step inset : Int) (tour : List GridPeg) : Option (List Cubic × List Cubic) :=
  let ps := (tour.map (GridPeg.toPeg step)).eraseReps
  match ps with
  | [] => some ([], [])
  | [p] =>
    let circle (q : Peg) := q.arc (ONE, 0) (-ONE, 0) ++ q.arc (-ONE, 0) (ONE, 0)
    some (circle p, circle (p.inset inset))
  | _ => Belt.outlines inset ps

/-- A finite path check: every tour has tangents and both rounded paths chain. -/
def PegFigure.check (f : PegFigure) (step : Int := 12000) : Bool :=
  f.bodies.all fun b =>
    match pegOutlines step LINE b.skeleton.tour with
    | some (outer, inner) => chained outer && chained inner
    | none => false

/-- A body without a tangent reports its index to the caller. -/
def PegFigure.nodes (f : PegFigure) (step : Int := 12000) : Except Nat (List SvgNode) := do
  let levels := (f.bodies.map (·.level) ++ f.units.map (·.level)).foldl max 0
  let bodies ← f.bodies.zipIdx.mapM fun (b, i) => do
    let some (outer, inner) := pegOutlines step LINE b.skeleton.tour | throw i
    pure (b.level, [fillNode outer "tube-body" []] ++
      if b.solid then [] else [fillNode inner "tube-ground" []])
  let units := f.units.map fun u =>
    match pegOutlines step LINE [u.peg] with
    | none => (u.level, [])
    | some (outer, inner) => (u.level, [fillNode outer "tube-fluid" []] ++
        if u.hollow then [fillNode inner "tube-ground" []] else [])
  pure <| (List.range (levels + 1)).flatMap fun level =>
    (bodies.filter (·.1 == level)).flatMap (·.2) ++
    (units.filter (·.1 == level)).flatMap (·.2)

/-- Draw a figure at one pixel to the pixel, or report its body's failed tangent. -/
def PegFigure.still (W H : Nat) (f : PegFigure) (step : Int := 12000) : Except Nat SvgNode := do
  let nodes ← f.nodes step
  pure <| Svg.Frame.svg { width := W, height := H, ratio := 1 } [.className "tube-view"] nodes

end Tools.View.Tube
